// server.js — Site2PDF + Site2Images (ZIP) + STOP (MAX-REALISTIC)
// Obiettivo immagini: più vicino possibile al 100% realistico (HTML + CSS + JS + caroselli + lazy)
// - Cattura immagini da:
//   1) response del browser (tutto ciò che la pagina scarica davvero, incl. CSS background, fetch, xhr)
//   2) DOM (img/srcset/picture/lazy/meta/icon/style inline)
//   3) CSS (scarica i fogli CSS, parse url(...), inclusi CDN)
//   4) JS (scarica script, parse url immagini "hard-coded", inclusi CDN)
//   5) data:image base64 (inline) dal DOM (non passano da network)
// - Dedupe "best quality": per ogni chiave canonica (stessa immagine con varianti) tiene SOLO la migliore
//   sostituendo su disco (non appendiamo due volte nello zip).
// - STOP reale: POST /api/stop/:jobId interrompe fetch, chiude browser, finalizza error.
// NOTE REALTÀ: non esiste il 100% assoluto.
// - Se un sito NON richiede mai un’immagine (es. slide mai aperta, asset generato server-side solo su click), non puoi prenderla.
// - Canvas/WebGL non sono "file immagini" scaricabili se non esportati dal sito.

import express from "express";
import { chromium } from "playwright";
import TurndownService from "turndown";
import MarkdownIt from "markdown-it";
import crypto from "crypto";
import dns from "dns/promises";
import archiver from "archiver";
import fs from "fs";
import os from "os";
import path from "path";
import { fileURLToPath } from "url";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

// -----------------------
// Config
// -----------------------
const CONCURRENCY = Math.max(1, Math.min(Number(process.env.CONCURRENCY || 4), 10));
const MIN_TEXT_CHARS = Math.max(0, Number(process.env.MIN_TEXT_CHARS || 200));

const GOTO_TIMEOUT_FAST = Math.max(8000, Number(process.env.GOTO_TIMEOUT_FAST || 20000));
const GOTO_TIMEOUT_SAFE = Math.max(12000, Number(process.env.GOTO_TIMEOUT_SAFE || 45000));
const CF_WAIT_MS = Math.max(20000, Number(process.env.CF_WAIT_MS || 90000)); // aspetta fino a 90s


const FREE_AFTER_DOWNLOAD = String(process.env.FREE_AFTER_DOWNLOAD || "1") !== "0";

// Download tuning
const IMG_DL_CONCURRENCY = Math.max(1, Math.min(Number(process.env.IMG_DL_CONCURRENCY || 8), 16));
const MAX_TEXT_ASSET_BYTES = Math.max(200_000, Math.min(Number(process.env.MAX_TEXT_ASSET_BYTES || 2_000_000), 10_000_000)); // CSS/JS max bytes to parse
const MAX_URL_CANDIDATES = Math.max(2_000, Math.min(Number(process.env.MAX_URL_CANDIDATES || 30_000), 200_000)); // safety

const app = express();
app.use(express.json({ limit: "2mb" }));
app.use(
  express.static(__dirname, {
    setHeaders(res, filePath) {
      if (filePath.endsWith(".css")) res.setHeader("Content-Type", "text/css; charset=utf-8");
    },
  })
);

app.get("/", (req, res) => {
  res.sendFile(path.join(process.cwd(), "index.html"));
});

// -----------------------
// Markdown pipeline
// -----------------------
const md = new MarkdownIt({ html: false, linkify: true, breaks: true });
const turndown = new TurndownService({
  headingStyle: "atx",
  codeBlockStyle: "fenced",
  bulletListMarker: "-",
});
turndown.addRule("removeImages", { filter: "img", replacement: () => "" });

// -----------------------
// Utils
// -----------------------
function safeFilename(s) {
  return (s || "document")
    .toLowerCase()
    .replace(/[^a-z0-9-_]+/gi, "-")
    .replace(/-+/g, "-")
    .replace(/^-|-$/g, "")
    .slice(0, 90);
}

function escapeHtml(str) {
  return String(str)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#039;");
}

function isIpV4(hostname) {
  return /^\d{1,3}(\.\d{1,3}){3}$/.test(hostname);
}
function isIpV6(hostname) {
  return hostname.includes(":");
}

function isPrivateIpV4(ip) {
  const parts = ip.split(".").map((x) => Number(x));
  if (parts.some((n) => Number.isNaN(n) || n < 0 || n > 255)) return true;
  const [a, b] = parts;
  if (a === 10) return true;
  if (a === 127) return true;
  if (a === 0) return true;
  if (a === 192 && b === 168) return true;
  if (a === 172 && b >= 16 && b <= 31) return true;
  if (a === 169 && b === 254) return true;
  return false;
}

function isPrivateIpV6(ip) {
  const v = ip.toLowerCase();
  if (v === "::" || v === "::1") return true;
  if (v.startsWith("fe8") || v.startsWith("fe9") || v.startsWith("fea") || v.startsWith("feb")) return true;
  if (v.startsWith("fc") || v.startsWith("fd")) return true;
  return false;
}

const dnsCache = new Map(); // hostname -> boolean (isPrivate)
async function resolvesToPrivateIp(hostname) {
  if (dnsCache.has(hostname)) return dnsCache.get(hostname);

  let isPriv = true;
  try {
    if (isIpV4(hostname)) isPriv = isPrivateIpV4(hostname);
    else if (isIpV6(hostname)) isPriv = true;
    else {
      const addrs = await dns.lookup(hostname, { all: true, verbatim: true });
      isPriv = false;
      for (const a of addrs) {
        if (a.family === 4 && isPrivateIpV4(a.address)) isPriv = true;
        if (a.family === 6 && isPrivateIpV6(a.address)) isPriv = true;
        if (isPriv) break;
      }
    }
  } catch {
    isPriv = true;
  }

  dnsCache.set(hostname, isPriv);
  return isPriv;
}

function normalizeUrl(u) {
  try {
    const url = new URL(u);
    url.hash = "";
    if (url.pathname !== "/" && url.pathname.endsWith("/")) url.pathname = url.pathname.slice(0, -1);
    return url.toString();
  } catch {
    return null;
  }
}

async function assertUrlAllowed(u) {
  let url;
  try {
    url = new URL(u);
  } catch {
    throw new Error("URL non valido");
  }

  if (!["http:", "https:"].includes(url.protocol)) throw new Error("Protocollo non consentito");
  const host = (url.hostname || "").toLowerCase();
  if (!host) throw new Error("Host mancante");
  if (host === "localhost") throw new Error("Host bloccato");

  if (isIpV6(host)) throw new Error("Host IPv6 bloccato");
  if (isIpV4(host) && isPrivateIpV4(host)) throw new Error("IP privato bloccato");

  const privateByDns = await resolvesToPrivateIp(host);
  if (privateByDns) throw new Error("Host risolve a IP privato (bloccato)");

  return true;
}

function parsePatterns(v) {
  if (!Array.isArray(v)) return [];
  return v.map((x) => String(x).trim()).filter(Boolean);
}
function matchesAny(str, patterns = []) {
  return patterns.some((p) => str.includes(p));
}

function isProbablyFileUrl(u) {
  return /\.(pdf|zip|rar|7z|mp4|mp3)(\?|#|$)/i.test(u);
}

function launchArgsForOs() {
  if (process.platform === "linux") return ["--no-sandbox", "--disable-setuid-sandbox"];
  return [];
}

function ensureNotCanceled(job) {
  if (job.cancelRequested) throw new Error("Job annullato dall'utente");
  if (job.status && job.status !== "running") throw new Error("Job non più in running");
}

function looksLikeCloudflare(title, textOrHtml) {
  const t = (title || "").toLowerCase();
  const s = (textOrHtml || "").toLowerCase();
  return (
    t.includes("just a moment") ||
    s.includes("just a moment") ||
    s.includes("verify you are human") ||
    s.includes("verification successful") ||
    s.includes("waiting for") ||
    s.includes("cdn-cgi") ||
    s.includes("challenge-platform") ||
    s.includes("cf-browser-verification")
  );
}

async function waitOutCloudflare(page, maxMs = CF_WAIT_MS) {
  const start = Date.now();
  while (Date.now() - start < maxMs) {
    const snap = await page.evaluate(() => {
      const title = document.title || "";
      const text = (document.body?.innerText || "").slice(0, 2500);
      const hasCf = !!document.querySelector(
        'form[action*="cdn-cgi"], iframe[src*="cdn-cgi"], script[src*="cdn-cgi"], div[id*="cf-"], input[name="cf-turnstile-response"]'
      );
      return { title, text, hasCf };
    });

    const challenge = looksLikeCloudflare(snap.title, snap.text) || snap.hasCf;

    if (!challenge) return true;

    // aspetta e riprova
    await page.waitForTimeout(1500);
  }
  return false;
}


function safeZipNameFromUrl(siteUrl) {
  try {
    const u = new URL(siteUrl);
    const name = (u.hostname + u.pathname)
      .toLowerCase()
      .replace(/[^a-z0-9]+/g, "-")
      .replace(/-+/g, "-")
      .replace(/^-|-$/g, "")
      .slice(0, 80);
    return name || "site";
  } catch {
    return "site";
  }
}

function extFromContentType(ct) {
  const s = String(ct || "").toLowerCase().split(";")[0].trim();
  const map = {
    "image/jpeg": "jpg",
    "image/jpg": "jpg",
    "image/png": "png",
    "image/webp": "webp",
    "image/gif": "gif",
    "image/svg+xml": "svg",
    "image/avif": "avif",
    "image/bmp": "bmp",
    "image/x-ms-bmp": "bmp",
    "image/tiff": "tiff",
    "image/x-icon": "ico",
    "image/vnd.microsoft.icon": "ico",
    "image/heic": "heic",
    "image/heif": "heif",
    "image/apng": "apng",
  };
  return map[s] || "";
}

function extFromUrl(u) {
  try {
    const p = new URL(u).pathname;
    const last = p.split("/").pop() || "";
    const m = last.match(/\.([a-z0-9]{1,5})$/i);
    if (!m) return "";
    const ext = m[1].toLowerCase();
    const ok = ["jpg", "jpeg", "png", "webp", "gif", "svg", "avif", "bmp", "tif", "tiff", "ico", "heic", "heif", "apng"];
    if (!ok.includes(ext)) return "";
    if (ext === "jpeg") return "jpg";
    if (ext === "tif") return "tiff";
    return ext;
  } catch {
    return "";
  }
}

// -----------------------
// Dedupe "best quality" per immagine
// -----------------------
function canonicalImageKey(rawUrl) {
  try {
    const u = new URL(rawUrl);
    u.hash = "";
    u.hostname = u.hostname.toLowerCase();

    let p = u.pathname;

    // WordPress / suffix comuni
    p = p.replace(/-scaled(?=\.[a-z0-9]{2,5}$)/i, "");
    p = p.replace(/@\dx(?=\.[a-z0-9]{2,5}$)/i, "");
    p = p.replace(/-\d{2,5}x\d{2,5}(?=\.[a-z0-9]{2,5}$)/i, "");
    p = p.replace(/_\d{2,5}x\d{2,5}(?=\.[a-z0-9]{2,5}$)/i, "");

    // Ignora token comuni, ma conserva parametri "qualità/dimensioni"
    const keep = [];
    const keysToKeep = ["w", "width", "h", "height", "q", "quality", "dpr", "fm", "format"];
    for (const k of keysToKeep) {
      const v = u.searchParams.get(k);
      if (v) keep.push(`${k}=${v}`);
    }
    keep.sort();

    return `${u.origin}${p}?${keep.join("&")}`.toLowerCase();
  } catch {
    return String(rawUrl || "");
  }
}

function getNumericParam(urlObj, names) {
  for (const n of names) {
    const v = urlObj.searchParams.get(n);
    if (!v) continue;
    const num = Number(String(v).replace(/[^\d.]/g, ""));
    if (!Number.isNaN(num) && num > 0) return num;
  }
  return 0;
}

function scoreImageUrl(rawUrl) {
  // Score da URL (dimensioni/qualità/formato) + (poi aggiungiamo buf.length)
  try {
    const u = new URL(rawUrl);

    const w = getNumericParam(u, ["w", "width", "dw", "sw", "imgw", "maxw", "mw"]);
    const h = getNumericParam(u, ["h", "height", "dh", "sh", "imgh", "maxh", "mh"]);
    const q = getNumericParam(u, ["q", "quality", "qlt"]);
    const dpr = getNumericParam(u, ["dpr", "devicePixelRatio", "dpi"]);

    const area = w && h ? w * h : w ? w * 1000 : 0;

    const fmt = (u.searchParams.get("fm") || u.searchParams.get("format") || "").toLowerCase();
    const pathExt = (u.pathname.split(".").pop() || "").toLowerCase();
    const format = fmt || pathExt;

    let formatBonus = 0;
    if (format.includes("avif")) formatBonus = 60_000;
    else if (format.includes("webp")) formatBonus = 40_000;
    else if (format.includes("png")) formatBonus = 12_000;

    const qBonus = q ? Math.min(100, q) * 250 : 0;
    const dprBonus = dpr ? Math.min(6, dpr) * 6000 : 0;

    const path = u.pathname.toLowerCase();
    const thumbPenalty = /(thumb|thumbnail|small|_sm|_xs|\/sm\/|\/thumbs\/)/i.test(path) ? -20_000 : 0;

    return area + formatBonus + qBonus + dprBonus + thumbPenalty;
  } catch {
    return 0;
  }
}

function sha1(buf) {
  return crypto.createHash("sha1").update(buf).digest("hex");
}

function stableKeyHash(key) {
  return crypto.createHash("sha1").update(String(key)).digest("hex").slice(0, 18);
}

// -----------------------
// HTML for PDF (solo testo)
// -----------------------
function makePrintableHtml(innerHtml) {
  return `<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <style>
    @page { margin: 22mm 18mm; }
    body { font-family: system-ui, -apple-system, Segoe UI, Roboto, Arial, sans-serif; font-size: 12pt; line-height: 1.55; }
    h1,h2,h3 { line-height: 1.25; margin: 0.6em 0 0.2em; }
    p { margin: 0.6em 0; }
    a { word-break: break-word; }
    pre { padding: 10px; overflow: auto; border-radius: 8px; background: #f4f4f4; }
    code { font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", monospace; font-size: 10.5pt; }
    blockquote { padding-left: 12px; border-left: 3px solid #ddd; margin-left: 0; color: #444; }
    table { border-collapse: collapse; width: 100%; }
    td, th { border: 1px solid #ddd; padding: 6px; vertical-align: top; }
    img, svg, video, audio, iframe, canvas { display: none !important; }
  </style>
</head>
<body>
${innerHtml}
</body>
</html>`;
}

function buildCombinedHtml(sections) {
  const body = sections
    .map(
      (s) => `
<section style="page-break-after: always;">
  <h1>${escapeHtml(s.title || "Pagina")}</h1>
  <p style="font-size:10pt;color:#555;">Fonte: <a href="${s.url}">${s.url}</a></p>
  <hr/>
  ${s.html || ""}
</section>`
    )
    .join("\n");

  return makePrintableHtml(body);
}

// -----------------------
// Playwright blocking
// -----------------------
function shouldAbortTracker(url) {
  return /doubleclick|googletagmanager|google-analytics|facebook\.com\/tr|hotjar|clarity\.ms|segment\.com/i.test(url);
}

async function configureBlocking(page, profile /* "fast" | "safe" */) {
  await page.route("**/*", (route) => {
    const req = route.request();
    const type = req.resourceType();
    const url = req.url();

    if (shouldAbortTracker(url)) return route.abort();

    if (profile === "fast") {
      if (["image", "media", "font", "stylesheet", "script"].includes(type)) return route.abort();
    } else {
      if (["image", "media", "font"].includes(type)) return route.abort();
    }

    return route.continue();
  });
}

// -----------------------
// Text extractors
// -----------------------
function pickMainSelectors() {
  return ["article", "main", '[role="main"]', ".content", ".post", ".article", "#content", "#main", "body"];
}
function stripTagsToTextLen(html) {
  return String(html || "").replace(/<[^>]+>/g, " ").replace(/\s+/g, " ").trim().length;
}

async function extractDomContent(page) {
  return await page.evaluate((selectors) => {
    const sel = selectors.find((s) => document.querySelector(s)) || "body";
    const pick = document.querySelector(sel) || document.body;

    const root = pick.cloneNode(true);

    root.querySelectorAll("header, nav, footer, aside, form, noscript").forEach((el) => el.remove());
    root
      .querySelectorAll('[role="banner"], [role="navigation"], [role="contentinfo"], [role="complementary"]')
      .forEach((el) => el.remove());

    root.querySelectorAll("img, video, audio, picture, source, iframe, svg, canvas").forEach((el) => el.remove());
    root.querySelectorAll("script, style, link[rel='stylesheet']").forEach((el) => el.remove());
    root.querySelectorAll("[style]").forEach((el) => el.removeAttribute("style"));

    const badRe =
      /(nav|menu|header|footer|sidebar|aside|cookie|consent|banner|breadcrumb|newsletter|modal|popup|drawer|offcanvas|toolbar|sticky|share|social|ads|advert|promo)/i;

    root.querySelectorAll("*").forEach((el) => {
      const id = el.id || "";
      const cls = (typeof el.className === "string" ? el.className : "") || "";
      const aria = el.getAttribute("aria-label") || "";
      if (badRe.test(id) || badRe.test(cls) || badRe.test(aria)) el.remove();
    });

    let html = root.innerHTML || "";

    const textLen = html.replace(/<[^>]+>/g, " ").replace(/\s+/g, " ").trim().length;
    if (textLen < 200) {
      const b = document.body?.cloneNode(true);
      if (b) {
        b.querySelectorAll("header, nav, footer, aside, form, noscript").forEach((el) => el.remove());
        b.querySelectorAll("img, video, audio, picture, source, iframe, svg, canvas").forEach((el) => el.remove());
        b.querySelectorAll("script, style, link[rel='stylesheet']").forEach((el) => el.remove());
        b.querySelectorAll("[style]").forEach((el) => el.removeAttribute("style"));
        html = b.innerHTML || html;
      }
    }

    return { title: document.title || "pagina", contentHtml: html };
  }, pickMainSelectors());
}

async function extractSectionAuto(job, fastPage, safePage, url) {
  ensureNotCanceled(job);

  // FAST
  await fastPage.goto(url, { waitUntil: "domcontentloaded", timeout: GOTO_TIMEOUT_FAST });
  ensureNotCanceled(job);

  const fastData = await extractDomContent(fastPage);
  const fastTextLen = stripTagsToTextLen(fastData.contentHtml);
  const fastLooksCf = looksLikeCloudflare(fastData.title, (fastData.contentHtml || "").slice(0, 8000));


  if (!fastLooksCf && fastTextLen >= MIN_TEXT_CHARS)  {
    const markdown = turndown.turndown(fastData.contentHtml || "");
    const rendered = md.render(markdown);
    return { title: fastData.title || "pagina", url, html: rendered };
  }

  // SAFE
 await safePage.goto(url, { waitUntil: "domcontentloaded", timeout: GOTO_TIMEOUT_SAFE });

// aspetta Cloudflare (fino a CF_WAIT_MS)
const ok = await waitOutCloudflare(safePage, CF_WAIT_MS);
if (!ok) throw new Error("Cloudflare non superato entro il tempo massimo");

// un attimo extra per SPA
try { await safePage.waitForTimeout(800); } catch {}


  ensureNotCanceled(job);

  const safeData = await extractDomContent(safePage);
  const safeTextLen = stripTagsToTextLen(safeData.contentHtml);

  const useSafe = fastLooksCf || safeTextLen > fastTextLen;

  const markdown = turndown.turndown((useSafe ? safeData.contentHtml : fastData.contentHtml) || "");
  const rendered = md.render(markdown);

  return {
    title: (useSafe ? safeData.title : fastData.title) || "pagina",
    url,
    html: rendered,
  };
}

// -----------------------
// Images: page interactions
// -----------------------
async function autoScroll(page) {
  try {
    await page.evaluate(async () => {
      await new Promise((resolve) => {
        let total = 0;
        const step = 900;
        const timer = setInterval(() => {
          window.scrollBy(0, step);
          total += step;
          if (total > document.body.scrollHeight + 2500) {
            clearInterval(timer);
            window.scrollTo(0, 0);
            resolve();
          }
        }, 220);
      });
    });
  } catch {}
}

async function primeLazy(page) {
  // Prova a forzare lazy/caroselli
  try {
    await page.evaluate(() => {
      // forza eager su immagini
      document.querySelectorAll("img[loading='lazy']").forEach((img) => img.setAttribute("loading", "eager"));
      // tenta di "svelare" lazy libs classiche
      document.querySelectorAll("img[data-src], img[data-lazy-src], img[data-original]").forEach((img) => {
        const ds = img.getAttribute("data-src") || img.getAttribute("data-lazy-src") || img.getAttribute("data-original");
        if (ds && !img.getAttribute("src")) img.setAttribute("src", ds);
      });
    });
  } catch {}
}

async function clickCarouselLike(page) {
  // vari tentativi (swiper/slick/next/arrow)
  try {
    for (let i = 0; i < 10; i++) {
      await page.evaluate(() => {
        const candidates = [
          ".swiper-button-next",
          ".slick-next",
          "[data-testid*='next' i]",
          "button[aria-label*='next' i]",
          "button[title*='next' i]",
          "button[class*='next' i]",
          "a[aria-label*='next' i]",
          "a[title*='next' i]",
        ];
        for (const sel of candidates) {
          const el = document.querySelector(sel);
          if (el) {
            el.dispatchEvent(new MouseEvent("click", { bubbles: true, cancelable: true }));
            return;
          }
        }

        // fallback: cerca bottoni con ">" o "→"
        const btns = Array.from(document.querySelectorAll("button,a,div")).slice(0, 400);
        const hit = btns.find((x) => {
          const t = (x.textContent || "").trim();
          return t === ">" || t === "→" || t.toLowerCase() === "next";
        });
        if (hit) hit.dispatchEvent(new MouseEvent("click", { bubbles: true, cancelable: true }));
      });

      await page.waitForTimeout(420);

      // anche frecce tastiera
      try {
        await page.keyboard.press("ArrowRight");
        await page.waitForTimeout(220);
      } catch {}
    }
  } catch {}
}

// -----------------------
// URL extraction helpers (DOM/CSS/JS/data:)
// -----------------------
function looksLikeImageUrl(u) {
  return /\.(png|jpe?g|webp|gif|svg|avif|bmp|tiff?|ico|heic|heif|apng)(\?|#|$)/i.test(u);
}

function extractUrlsFromText(text) {
  const out = new Set();
  if (!text) return out;

  // url(...) in CSS
  const urlRe = /url\(\s*['"]?([^'")\s]+)['"]?\s*\)/gi;
  for (let m; (m = urlRe.exec(text)); ) {
    const u = m[1];
    if (!u) continue;
    out.add(u);
  }

  // raw absolute/relative that look like images
  const rawRe = /((https?:\/\/|\/)[^\s"'()<>]+?\.(?:png|jpe?g|webp|gif|svg|avif|bmp|tiff?|ico|heic|heif|apng)(?:\?[^\s"'<>)]*)?)/gi;
  for (let m; (m = rawRe.exec(text)); ) {
    const u = m[1];
    if (!u) continue;
    out.add(u);
  }

  return out;
}

function resolveToAbs(baseUrl, maybeUrl) {
  try {
    const abs = new URL(maybeUrl, baseUrl);
    abs.hash = "";
    if (!["http:", "https:"].includes(abs.protocol)) return null;
    return abs.toString();
  } catch {
    return null;
  }
}

function dataUrlToBuffer(dataUrl) {
  try {
    const m = String(dataUrl).match(/^data:(image\/[a-z0-9.+-]+);base64,(.+)$/i);
    if (!m) return null;
    const contentType = m[1].toLowerCase();
    const b64 = m[2];
    const buf = Buffer.from(b64, "base64");
    return { buf, contentType };
  } catch {
    return null;
  }
}

// -----------------------
// Fetch helpers (Node 18+)
// -----------------------
async function fetchWithTimeout(url, ms, signal, method = "GET") {
  const controller = new AbortController();
  const t = setTimeout(() => controller.abort(), ms);

  const sig =
    signal && AbortSignal.any
      ? AbortSignal.any([signal, controller.signal])
      : signal
      ? signal
      : controller.signal;

  try {
    return await fetch(url, {
      method,
      signal: sig,
      redirect: "follow",
      headers: {
        "User-Agent":
          "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome Safari",
        Accept: "*/*",
      },
    });
  } finally {
    clearTimeout(t);
  }
}

async function downloadBinary(url, signal, maxBytes = 0) {
  // maxBytes=0 -> no cap (ma non consigliato per roba non immagine)
  const res = await fetchWithTimeout(url, 30000, signal, "GET");
  if (!res.ok) return null;

  const ct = (res.headers.get("content-type") || "").toLowerCase();
  const cl = Number(res.headers.get("content-length") || 0);

  if (maxBytes && cl && cl > maxBytes) return null;

  const ab = await res.arrayBuffer();
  const buf = Buffer.from(ab);
  if (maxBytes && buf.length > maxBytes) return null;

  return { buf, contentType: ct };
}

// -----------------------
// Crawl site
// -----------------------
async function extractInternalLinks(page, baseUrl) {
  const base = new URL(baseUrl);

  const hrefs = await page.evaluate(() =>
    Array.from(document.querySelectorAll("a[href]")).map((a) => a.getAttribute("href"))
  );

  const out = new Set();
  for (const h of hrefs) {
    if (!h) continue;
    try {
      const u = new URL(h, base);
      if (u.origin !== base.origin) continue;
      u.hash = "";
      const s = u.toString();
      if (isProbablyFileUrl(s)) continue;
      const norm = normalizeUrl(s);
      if (norm) out.add(norm);
    } catch {}
  }

  return Array.from(out);
}

async function crawlSite(browser, startUrl, { maxPages, maxDepth, includePatterns, excludePatterns }, onProgress) {
  const HARD_MAX_PAGES = 80;
  maxPages = Math.max(1, Math.min(Number(maxPages) || 25, HARD_MAX_PAGES));
  maxDepth = Math.max(0, Math.min(Number(maxDepth) || 2, 6));

  const visited = new Set();
  const queue = [{ url: normalizeUrl(startUrl), depth: 0 }].filter(Boolean);
  const results = [];

  const page = await browser.newPage({ javaScriptEnabled: true });
  await configureBlocking(page, "safe");

  while (queue.length && results.length < maxPages) {
    const item = queue.shift();
    if (!item) continue;

    const { url, depth } = item;
    if (!url || visited.has(url)) continue;
    visited.add(url);

    const uo = new URL(url);
    const pathish = uo.pathname;

    if (excludePatterns.length && matchesAny(pathish, excludePatterns)) continue;
    if (includePatterns.length && !matchesAny(pathish, includePatterns)) continue;

    results.push(url);
    onProgress?.({
      phase: "crawl",
      current: results.length,
      total: maxPages,
      message: `Trovata pagina ${results.length}/${maxPages}`,
    });

    if (depth >= maxDepth) continue;

    try {
      await page.goto(url, { waitUntil: "domcontentloaded", timeout: 25000 });
      try {
        await page.waitForLoadState("networkidle", { timeout: 3000 });
      } catch {}
      try {
        await page.waitForTimeout(700);
      } catch {}

      const links = await extractInternalLinks(page, startUrl);

      for (const link of links) {
        if (results.length + queue.length >= maxPages * 3) break;
        if (visited.has(link)) continue;

        const lu = new URL(link);
        const su = new URL(startUrl);
        if (lu.origin !== su.origin) continue;

        if (excludePatterns.length && matchesAny(lu.pathname, excludePatterns)) continue;
        if (includePatterns.length && !matchesAny(lu.pathname, includePatterns)) continue;

        queue.push({ url: link, depth: depth + 1 });
      }
    } catch {}
  }

  await page.close();
  return results;
}

// -----------------------
// Worker pool
// -----------------------
async function runWithWorkerPool(items, workerCount, workerFn) {
  const results = new Array(items.length).fill(null);
  let nextIndex = 0;

  async function worker(workerId) {
    while (true) {
      const i = nextIndex++;
      if (i >= items.length) break;
      results[i] = await workerFn(items[i], i, workerId);
    }
  }

  const workers = Array.from({ length: workerCount }, (_, id) => worker(id));
  await Promise.all(workers);
  return results;
}

// -----------------------
// SSE Jobs
// -----------------------
const jobs = new Map();

function createJob() {
  const id = crypto.randomBytes(8).toString("hex");
  const job = {
    id,
    status: "running",
    percent: 0,
    message: "Avvio...",
    total: 0,
    current: 0,
    createdAt: Date.now(),
    sseClients: new Set(),

    // artifacts
    pdfBuffer: null,
    filename: null,
    error: null,
    abortController: null,
    zipPath: null,

    // images temp
    tmpDir: null,

    // STOP support
    cancelRequested: false,
    browserRef: null,
  };
  jobs.set(id, job);
  return job;
}

function sendSse(job, data) {
  const payload = `data: ${JSON.stringify(data)}\n\n`;
  for (const res of job.sseClients) {
    try {
      res.write(payload);
    } catch {}
  }
}

function updateJob(job, patch) {
  Object.assign(job, patch);
  sendSse(job, {
    status: job.status,
    percent: job.percent,
    message: job.message,
    current: job.current,
    total: job.total,
  });
}

// cleanup old jobs
setInterval(() => {
  const now = Date.now();
  for (const [id, job] of jobs.entries()) {
    if (now - job.createdAt > 20 * 60 * 1000) {
      for (const res of job.sseClients) {
        try {
          res.end();
        } catch {}
      }
      // cleanup tmp
      if (job.tmpDir) {
        try {
          fs.rmSync(job.tmpDir, { recursive: true, force: true });
        } catch {}
      }
      // cleanup zip
      if (job.zipPath) {
        try {
          fs.unlinkSync(job.zipPath);
        } catch {}
      }
      jobs.delete(id);
    }
  }
}, 60 * 1000);

// -----------------------
// Job: PDF
// -----------------------
async function runPdfJob(job, body) {
  let browser;
  let context;

  try {
    const mode = body.mode || (body.url ? "single" : null);
    if (!mode) throw new Error("Manca mode/url");

    updateJob(job, { message: "Avvio browser...", percent: 2 });

   browser = await chromium.launch({
  headless: true,
  args: [
    ...launchArgsForOs(),
    "--disable-blink-features=AutomationControlled",
    "--no-first-run",
    "--no-default-browser-check",
  ],
});

    job.browserRef = browser;
    context = await browser.newContext({
  locale: "it-IT",
  timezoneId: "Europe/Rome",
  viewport: { width: 1365, height: 900 },
  userAgent:
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
  extraHTTPHeaders: {
    "Accept-Language": "it-IT,it;q=0.9,en;q=0.8",
  },
});

await context.addInitScript(() => {
  Object.defineProperty(navigator, "webdriver", { get: () => undefined });
  Object.defineProperty(navigator, "languages", { get: () => ["it-IT", "it", "en-US", "en"] });
  Object.defineProperty(navigator, "plugins", { get: () => [1, 2, 3, 4, 5] });
});


    // 1) URLs
    let urls = [];
    let titleForFile = "documento";

    if (mode === "single") {
      const url = normalizeUrl(body.url);
      if (!url) throw new Error("Manca url / url non valido");
      await assertUrlAllowed(url);
      urls = [url];
      updateJob(job, { message: "1 pagina in coda", percent: 8, total: 1, current: 0 });
    } else if (mode === "list") {
      if (!Array.isArray(body.urls)) throw new Error("Manca urls (array)");
      urls = body.urls.map((u) => normalizeUrl(String(u).trim())).filter(Boolean).slice(0, 40);
      if (!urls.length) throw new Error("Lista vuota");
      for (const u of urls) await assertUrlAllowed(u);
      titleForFile = "lista-pagine";
      updateJob(job, { message: `Lista pronta (${urls.length} pagine)`, percent: 8, total: urls.length, current: 0 });
    } else if (mode === "site") {
      const startUrl = normalizeUrl(body.startUrl);
      if (!startUrl) throw new Error("Manca startUrl / startUrl non valido");
      await assertUrlAllowed(startUrl);

      const includePatterns = parsePatterns(body.includePatterns);
      const excludePatterns = parsePatterns(body.excludePatterns);

      updateJob(job, { message: "Scansione link del sito...", percent: 6 });

      urls = await crawlSite(
        browser,
        startUrl,
        { maxPages: body.maxPages ?? 25, maxDepth: body.maxDepth ?? 2, includePatterns, excludePatterns },
        (p) => {
          const crawlPct = 6 + Math.min(18, Math.round((p.current / p.total) * 18));
          updateJob(job, {
            message: p.message,
            percent: crawlPct,
            current: p.current,
            total: Math.min(Number(body.maxPages) || 25, 80),
          });
        }
      );

      if (!urls.length) throw new Error("Nessuna pagina trovata (controlla include/exclude)");
      titleForFile = "sito";
      updateJob(job, {
        message: `Trovate ${urls.length} pagine. Estraggo testo (AUTO) ${CONCURRENCY}x...`,
        percent: 24,
        total: urls.length,
        current: 0,
      });
    } else {
      throw new Error("mode non supportata");
    }

    ensureNotCanceled(job);

    // 2) Worker pages: una coppia per worker
    const workerCount = Math.min(CONCURRENCY, urls.length);

    const fastPages = await Promise.all(
  Array.from({ length: workerCount }, () => context.newPage())
);
const safePages = await Promise.all(
  Array.from({ length: workerCount }, () => context.newPage())
);

// disabilita JS solo sulle fast
await Promise.all(fastPages.map((p) => p.setJavaScriptEnabled(false)));
await Promise.all(safePages.map((p) => p.setJavaScriptEnabled(true)));


    await Promise.all(fastPages.map((p) => configureBlocking(p, "fast")));
    await Promise.all(safePages.map((p) => configureBlocking(p, "safe")));

    let completed = 0;
    const total = urls.length;

    const extracted = await runWithWorkerPool(urls, workerCount, async (u, index, workerId) => {
      ensureNotCanceled(job);

      updateJob(job, {
        message: `Leggo pagina ${completed + 1}/${total}...`,
        percent: 24 + Math.round((completed / Math.max(1, total)) * 56),
        current: completed,
        total,
      });

      const fp = fastPages[workerId];
      const sp = safePages[workerId];

      try {
        const section = await extractSectionAuto(job, fp, sp, u);
        return section;
      } catch {
        return null;
      } finally {
        completed++;
      }
    });

    await Promise.all([...fastPages, ...safePages].map((p) => p.close()));

    const sections = extracted.filter(Boolean);
    if (!sections.length) throw new Error("Non sono riuscito a estrarre testo dalle pagine richieste");

    if (mode === "single" && sections[0]?.title) titleForFile = sections[0].title;

    ensureNotCanceled(job);
    updateJob(job, { message: "Creo PDF...", percent: 86, current: sections.length, total });

    // 3) PDF
    const combinedHtml = buildCombinedHtml(sections);
    const pdfPage = await context.newPage();
await pdfPage.setJavaScriptEnabled(false);

    await pdfPage.emulateMedia({ media: "screen" });
    await pdfPage.setContent(combinedHtml, { waitUntil: "domcontentloaded", timeout: 25000 });

    const pdfBuffer = await pdfPage.pdf({
      format: "A4",
      printBackground: false,
      preferCSSPageSize: true,
      timeout: 0,
    });

    await pdfPage.close();

    job.pdfBuffer = pdfBuffer;
    job.filename = safeFilename(titleForFile) + ".pdf";

    updateJob(job, { status: "done", message: "Pronto ✅", percent: 100, current: sections.length, total });
  } catch (e) {
    job.error = String(e?.message || e);
    updateJob(job, { status: "error", message: job.error, percent: 100 });
 } finally {
  job.browserRef = null;
  try { await context?.close(); } catch {}
  if (browser) {
    try { await browser.close(); } catch {}
  }
}

}

// -----------------------
// Job: Images -> ZIP (MAX-REALISTIC)
// -----------------------
async function runImagesJob(job, body) {
  let browser;

  // temp registry: canonicalKey -> best { score, filePath, ext, url, bytes }
  const bestByKey = new Map();

  // URL candidates
  const urlCandidates = new Map(); // canonicalKey -> { url, scoreUrlOnly }

  function considerUrlCandidate(rawUrl) {
    if (!rawUrl) return;
    if (job.cancelRequested) return;

    // ignore data: here, handled elsewhere
    if (/^data:image\//i.test(rawUrl)) return;

    const key = canonicalImageKey(rawUrl);
    const s = scoreImageUrl(rawUrl);

    const prev = urlCandidates.get(key);
    if (!prev || s > prev.scoreUrlOnly) urlCandidates.set(key, { url: rawUrl, scoreUrlOnly: s });
  }

  function considerBufferCandidate({ url, buf, contentType }) {
    if (!buf || !buf.length) return;
    if (job.cancelRequested) return;

    const ext = extFromUrl(url) || extFromContentType(contentType) || "img";
    const key = url ? canonicalImageKey(url) : sha1(buf);
    const urlScore = url ? scoreImageUrl(url) : 0;

    // score finale: urlScore + dimensione (molto importante per qualità reale)
    const finalScore = urlScore + buf.length;

    const prev = bestByKey.get(key);
    if (prev && prev.score >= finalScore) return;

    // write/overwrite on disk
    const keyHash = stableKeyHash(key);
    const filePath = path.join(job.tmpDir, `${keyHash}.${ext}`);

    try {
      fs.writeFileSync(filePath, buf);
      bestByKey.set(key, { score: finalScore, filePath, ext, url: url || "", bytes: buf.length });
    } catch {
      // ignore
    }
  }

  function considerDataImage(dataUrl) {
    const parsed = dataUrlToBuffer(dataUrl);
    if (!parsed) return;
    const ext = extFromContentType(parsed.contentType) || "img";
    const fakeUrl = `data.${ext}`;
    considerBufferCandidate({ url: fakeUrl, buf: parsed.buf, contentType: parsed.contentType });
  }

  // parse CSS/JS to find image URLs
  async function collectFromCssText(cssText, baseUrl) {
    const found = extractUrlsFromText(cssText);
    for (const u of found) {
      if (urlCandidates.size > MAX_URL_CANDIDATES) break;
      const abs = resolveToAbs(baseUrl, u);
      if (!abs) continue;
      if (looksLikeImageUrl(abs) || /\/image\/|\/images\//i.test(abs) || /format=|fm=|w=|width=/i.test(abs)) {
        considerUrlCandidate(abs);
      }
    }
  }

  async function collectFromJsText(jsText, baseUrl) {
    const found = extractUrlsFromText(jsText);
    for (const u of found) {
      if (urlCandidates.size > MAX_URL_CANDIDATES) break;
      const abs = resolveToAbs(baseUrl, u);
      if (!abs) continue;
      if (looksLikeImageUrl(abs)) considerUrlCandidate(abs);
    }
  }

  async function downloadAndConsider(url, minBytes, signal) {
    ensureNotCanceled(job);
    try {
      await assertUrlAllowed(url);
    } catch {
      return;
    }

    // HEAD best effort per filtro size/tipo
    try {
      const head = await fetchWithTimeout(url, 12000, signal, "HEAD");
      const ct = (head.headers.get("content-type") || "").toLowerCase();
      const cl = Number(head.headers.get("content-length") || 0);
      if (ct && !ct.includes("image/")) return;
      if (minBytes && cl && cl < minBytes) return;
    } catch {
      // ignore
    }

    const r = await downloadBinary(url, signal, 0);
    if (!r) return;
    if (r.contentType && !r.contentType.includes("image/")) return;
    if (minBytes && r.buf.length < minBytes) return;

    considerBufferCandidate({ url, buf: r.buf, contentType: r.contentType });
  }

  async function downloadTextAsset(url, signal) {
    // usato per CSS/JS: limita dimensione
    ensureNotCanceled(job);
    try {
      await assertUrlAllowed(url);
    } catch {
      return null;
    }
    const r = await downloadBinary(url, signal, MAX_TEXT_ASSET_BYTES);
    if (!r) return null;
    // solo testi
    const ct = r.contentType || "";
    if (
      !(ct.includes("text/") || ct.includes("javascript") || ct.includes("ecmascript") || ct.includes("json") || ct.includes("css"))
    ) {
      // se content-type è vuoto o generico, proviamo lo stesso ma con cap già applicato
    }
    return r.buf.toString("utf-8");
  }

  try {
    const mode = body.mode || (body.url ? "single" : null);
    if (!mode) throw new Error("Manca mode/url");

    const minKB = Math.max(0, Number(body.minKB || 0));
    const minBytes = Math.floor(minKB * 1024);

    updateJob(job, { message: "Avvio browser...", percent: 2 });

    browser = await chromium.launch({ headless: true, args: launchArgsForOs() });
    job.browserRef = browser;

    // tmp dir
    job.tmpDir = path.join(os.tmpdir(), `site2images-${job.id}`);
    fs.mkdirSync(job.tmpDir, { recursive: true });

    // 1) URLs
    let urls = [];
    let nameBase = "site";

    if (mode === "single") {
      const url = normalizeUrl(body.url);
      if (!url) throw new Error("URL non valido");
      await assertUrlAllowed(url);
      urls = [url];
      nameBase = safeZipNameFromUrl(url);
      updateJob(job, { message: "1 pagina in coda", percent: 8, total: 1, current: 0 });
    } else if (mode === "list") {
      if (!Array.isArray(body.urls)) throw new Error("Manca urls (array)");
      urls = body.urls.map((u) => normalizeUrl(String(u).trim())).filter(Boolean).slice(0, 40);
      if (!urls.length) throw new Error("Lista vuota");
      for (const u of urls) await assertUrlAllowed(u);
      nameBase = "lista";
      updateJob(job, { message: `Lista pronta (${urls.length})`, percent: 8, total: urls.length, current: 0 });
    } else if (mode === "site") {
      const startUrl = normalizeUrl(body.startUrl);
      if (!startUrl) throw new Error("startUrl non valido");
      await assertUrlAllowed(startUrl);

      const includePatterns = parsePatterns(body.includePatterns);
      const excludePatterns = parsePatterns(body.excludePatterns);

      updateJob(job, { message: "Scansione link del sito...", percent: 6 });

      urls = await crawlSite(
        browser,
        startUrl,
        { maxPages: body.maxPages ?? 25, maxDepth: body.maxDepth ?? 2, includePatterns, excludePatterns },
        (p) => {
          const crawlPct = 6 + Math.min(18, Math.round((p.current / p.total) * 18));
          updateJob(job, {
            message: p.message,
            percent: crawlPct,
            current: p.current,
            total: Math.min(Number(body.maxPages) || 25, 80),
          });
        }
      );

      if (!urls.length) throw new Error("Nessuna pagina trovata");
      nameBase = safeZipNameFromUrl(startUrl);

      updateJob(job, {
        message: `Trovate ${urls.length} pagine. Cerco immagini...`,
        percent: 24,
        total: urls.length,
        current: 0,
      });
    } else {
      throw new Error("mode non supportata");
    }

    ensureNotCanceled(job);

    // ZIP output
    const zipFileName = `${safeFilename(nameBase)}.zip`;
    const zipPath = path.join(os.tmpdir(), `${job.id}-${zipFileName}`);
    job.zipPath = zipPath;
    job.filename = zipFileName;

    const output = fs.createWriteStream(zipPath);
    const archive = archiver("zip", { zlib: { level: 6 } });

    archive.on("warning", (err) => console.warn("ARCHIVER warning:", err?.message || err));
    archive.on("error", (err) => {
      console.error("ARCHIVER error:", err?.message || err);
      try {
        output.destroy(err);
      } catch {}
    });

    archive.pipe(output);

    // Abort controller per fetch manuali
    const abortController = new AbortController();
    job.abortController = abortController;

    // 2) Setup pages + response listener
    const pageWorkers = Math.min(CONCURRENCY, urls.length);
    const pages = await Promise.all(Array.from({ length: pageWorkers }, () => browser.newPage({ javaScriptEnabled: true })));

    await Promise.all(
      pages.map(async (p) => {
        // performance: blocca media/font, tracker
        await p.route("**/*", (route) => {
          const req = route.request();
          const type = req.resourceType();
          const url = req.url();

          if (shouldAbortTracker(url)) return route.abort();
          if (["media", "font"].includes(type)) return route.abort();

          return route.continue();
        });

        // Cattura immagini dalle response (incl. CSS background / fetch / xhr)
        p.on("response", async (resp) => {
          try {
            if (job.cancelRequested) return;
            if (job.status !== "running") return;

            const headers = resp.headers();
            const ct = String(headers["content-type"] || "").toLowerCase();
            if (!ct.startsWith("image/")) return;

            const cl = Number(headers["content-length"] || 0);
            if (minBytes && cl && cl < minBytes) return;

            const buf = await resp.body();
            if (!buf || !buf.length) return;
            if (minBytes && buf.length < minBytes) return;

            considerBufferCandidate({ url: resp.url(), buf, contentType: ct });
          } catch {}
        });
      })
    );

    // 3) Scan pages: DOM + CSS + JS + data:image
    let scannedPages = 0;

    await runWithWorkerPool(urls, pageWorkers, async (pageUrl, idx, wid) => {
      ensureNotCanceled(job);

      updateJob(job, {
        message: `Scansiono pagina ${scannedPages + 1}/${urls.length}`,
        percent: 24 + Math.round((scannedPages / Math.max(1, urls.length)) * 40),
        current: scannedPages,
        total: urls.length,
      });

      const p = pages[wid];

      try {
        await p.setViewportSize({ width: 1365, height: 900 });
      } catch {}

      try {
        await p.goto(pageUrl, { waitUntil: "domcontentloaded", timeout: GOTO_TIMEOUT_SAFE });

        // lascia montare SPA/lazy
        try {
          await p.waitForLoadState("networkidle", { timeout: 3500 });
        } catch {}
        try {
          await p.waitForTimeout(700);
        } catch {}

        // prime lazy
        await primeLazy(p);

        // scroll + caroselli
        await autoScroll(p);
        await clickCarouselLike(p);
        await autoScroll(p);

        // ---------- DOM candidates ----------
        const domData = await p.evaluate(() => {
          const outUrls = new Set();
          const outData = new Set();

          const pickBestFromSrcset = (srcset) => {
            if (!srcset || typeof srcset !== "string") return null;
            const items = srcset
              .split(",")
              .map((x) => x.trim())
              .map((x) => {
                const [u, d] = x.split(/\s+/);
                if (!u) return null;
                let score = 0;
                if (d) {
                  if (d.endsWith("w")) score = parseInt(d, 10) || 0;
                  else if (d.endsWith("x")) score = Math.round((parseFloat(d) || 0) * 100000);
                } else score = 1;
                return { u, score };
              })
              .filter(Boolean);
            if (!items.length) return null;
            items.sort((a, b) => b.score - a.score);
            return items[0].u;
          };

          const firstNonEmpty = (...vals) => {
            for (const v of vals) {
              if (typeof v === "string" && v.trim()) return v.trim();
            }
            return null;
          };

          const pushMaybe = (u) => {
            if (!u) return;
            const s = String(u).trim();
            if (!s) return;
            if (s.startsWith("data:image/")) outData.add(s);
            else outUrls.add(s);
          };

          const pickBestImgUrl = (img) => {
            const ss =
              img.getAttribute("data-srcset") ||
              img.getAttribute("data-lazy-srcset") ||
              img.getAttribute("data-srcset2") ||
              img.getAttribute("srcset");

            const bestFromSs = pickBestFromSrcset(ss);

            const dataOriginal = img.getAttribute("data-original");
            const dataSrc = img.getAttribute("data-src");
            const dataLazy = img.getAttribute("data-lazy-src");
            const dataUrl = img.getAttribute("data-url");
            const src = img.getAttribute("src");

            return firstNonEmpty(bestFromSs, dataOriginal, dataSrc, dataLazy, dataUrl, src);
          };

          const pickBestPictureUrl = (picture) => {
            const candidates = [];
            picture.querySelectorAll("source").forEach((s) => {
              const ss = s.getAttribute("srcset");
              const best = pickBestFromSrcset(ss);
              if (best) candidates.push(best);
            });
            const img = picture.querySelector("img");
            if (img) {
              const bestImg = pickBestImgUrl(img);
              if (bestImg) candidates.push(bestImg);
            }
            return candidates[0] || null;
          };

          document.querySelectorAll("picture").forEach((pic) => pushMaybe(pickBestPictureUrl(pic)));
          document.querySelectorAll("img").forEach((img) => {
            if (img.closest("picture")) return;
            pushMaybe(pickBestImgUrl(img));
          });

          // og/twitter images
          document.querySelectorAll('meta[property="og:image"], meta[name="twitter:image"]').forEach((m) => pushMaybe(m.getAttribute("content")));

          // icons / apple touch icons
          document
            .querySelectorAll('link[rel~="icon"], link[rel="shortcut icon"], link[rel="apple-touch-icon"], link[rel="mask-icon"]')
            .forEach((l) => pushMaybe(l.getAttribute("href")));

          // inline style url(...)
          document.querySelectorAll("[style]").forEach((el) => {
            const st = el.getAttribute("style") || "";
            const re = /url\(\s*['"]?([^'")\s]+)['"]?\s*\)/gi;
            for (let m; (m = re.exec(st)); ) pushMaybe(m[1]);
          });

          // computed background-image (limite per performance)
          const els = Array.from(document.querySelectorAll("*")).slice(0, 4000);
          for (const el of els) {
            const bg = getComputedStyle(el).backgroundImage || "";
            const re = /url\(\s*['"]?([^'")\s]+)['"]?\s*\)/gi;
            for (let m; (m = re.exec(bg)); ) pushMaybe(m[1]);
          }

          // inline <style> text
          document.querySelectorAll("style").forEach((st) => {
            const txt = st.textContent || "";
            const re = /url\(\s*['"]?([^'")\s]+)['"]?\s*\)/gi;
            for (let m; (m = re.exec(txt)); ) pushMaybe(m[1]);
          });

          // linked CSS and scripts
          const cssLinks = Array.from(document.querySelectorAll('link[rel="stylesheet"][href]')).map((x) => x.getAttribute("href")).filter(Boolean);
          const scriptSrcs = Array.from(document.querySelectorAll("script[src]")).map((x) => x.getAttribute("src")).filter(Boolean);
          const inlineScripts = Array.from(document.querySelectorAll("script:not([src])"))
            .map((s) => s.textContent || "")
            .filter((t) => t && t.length);

          return {
            urls: Array.from(outUrls),
            dataImages: Array.from(outData),
            cssLinks,
            scriptSrcs,
            inlineScripts,
          };
        });

        // data:image inline
        for (const d of domData.dataImages) considerDataImage(d);

        // resolve DOM urls to absolute
        for (const u of domData.urls) {
          if (urlCandidates.size > MAX_URL_CANDIDATES) break;
          const abs = resolveToAbs(pageUrl, u);
          if (abs) considerUrlCandidate(abs);
        }

        // ---------- CSS files ----------
        for (const cssHref of domData.cssLinks.slice(0, 120)) {
          if (urlCandidates.size > MAX_URL_CANDIDATES) break;
          const absCss = resolveToAbs(pageUrl, cssHref);
          if (!absCss) continue;

          const cssText = await downloadTextAsset(absCss, abortController.signal);
          if (!cssText) continue;

          await collectFromCssText(cssText, absCss);
        }

        // ---------- Inline scripts ----------
        for (const scr of domData.inlineScripts.slice(0, 40)) {
          if (urlCandidates.size > MAX_URL_CANDIDATES) break;
          await collectFromJsText(scr, pageUrl);
        }

        // ---------- External scripts ----------
        for (const jsSrc of domData.scriptSrcs.slice(0, 120)) {
          if (urlCandidates.size > MAX_URL_CANDIDATES) break;
          const absJs = resolveToAbs(pageUrl, jsSrc);
          if (!absJs) continue;

          const jsText = await downloadTextAsset(absJs, abortController.signal);
          if (!jsText) continue;

          await collectFromJsText(jsText, absJs);
        }
      } catch {
        // ignore page errors
      } finally {
        scannedPages++;
      }

      return null;
    });

    // cleanup pages routes and close
    for (const p of pages) {
      try {
        await p.unroute("**/*");
      } catch {}
    }
    await Promise.all(pages.map((p) => p.close()));

    ensureNotCanceled(job);

    // 4) Download best URL per canonical key (manual fetch) — massima qualità
    const uniqueBestUrls = Array.from(urlCandidates.values())
      .map((x) => x.url)
      .filter(Boolean);

    // dedupe by canonical key again (should already)
    const bestUrlByKey = new Map();
    for (const u of uniqueBestUrls) {
      const k = canonicalImageKey(u);
      const s = scoreImageUrl(u);
      const prev = bestUrlByKey.get(k);
      if (!prev || s > prev.s) bestUrlByKey.set(k, { url: u, s });
    }
    const finalUrlList = Array.from(bestUrlByKey.values()).map((x) => x.url);

    updateJob(job, {
      message: `Download immagini (best quality) da URL trovate: ${finalUrlList.length}...`,
      percent: 66,
      current: 0,
      total: finalUrlList.length,
    });

    let processed = 0;

    await runWithWorkerPool(finalUrlList, Math.min(IMG_DL_CONCURRENCY, Math.max(1, finalUrlList.length)), async (imgUrl) => {
      ensureNotCanceled(job);

      updateJob(job, {
        message: `Scarico best ${processed + 1}/${finalUrlList.length}... (salvate finora: ${bestByKey.size})`,
        percent: 66 + Math.round((processed / Math.max(1, finalUrlList.length)) * 26),
        current: processed,
        total: finalUrlList.length,
      });

      try {
        await downloadAndConsider(imgUrl, minBytes, abortController.signal);
      } catch {
        // ignore
      } finally {
        processed++;
      }
      return null;
    });

    ensureNotCanceled(job);

    // 5) Se non abbiamo nulla -> errore
    const savedCount = bestByKey.size;
    if (savedCount === 0) throw new Error("Nessuna immagine salvata (il sito potrebbe bloccare hotlink/CORS o non caricare immagini)");

    // 6) Build ZIP (numerazione stabile, dedupe già fatto)
    updateJob(job, {
      message: `Creo ZIP... (immagini uniche migliori: ${savedCount})`,
      percent: 94,
      current: 0,
      total: savedCount,
    });

    // ordina per dimensione decrescente (prima le più grosse)
    const items = Array.from(bestByKey.values()).sort((a, b) => (b.bytes || 0) - (a.bytes || 0));

    let n = 0;
    for (const it of items) {
      ensureNotCanceled(job);
      n++;

      const ext = it.ext || "img";
      const fileName = `${String(n).padStart(5, "0")}.${ext}`;
      archive.file(it.filePath, { name: `${safeFilename(nameBase)}/${fileName}` });

      if (n % 25 === 0) {
        updateJob(job, {
          message: `Creo ZIP... ${n}/${savedCount}`,
          percent: 94 + Math.round((n / Math.max(1, savedCount)) * 5),
          current: n,
          total: savedCount,
        });
      }
    }

    // finalize zip
    await new Promise((resolve, reject) => {
      output.on("close", resolve);
      output.on("finish", resolve);
      output.on("error", reject);
      archive.on("error", reject);
      archive.finalize();
    });

    updateJob(job, {
      status: "done",
      message: `ZIP pronto ✅ (immagini uniche migliori: ${savedCount})`,
      percent: 100,
      current: savedCount,
      total: savedCount,
    });
  } catch (e) {
    job.error = String(e?.message || e);
    updateJob(job, { status: "error", message: job.error, percent: 100 });
  } finally {
    // STOP/fetch abort
    try {
      job.abortController?.abort();
    } catch {}
    job.abortController = null;

    // close browser
    job.browserRef = null;
    if (browser) {
      try {
        await browser.close();
      } catch {}
    }

    // cleanup tmp on error
    if (job.status !== "done" && job.tmpDir) {
      try {
        fs.rmSync(job.tmpDir, { recursive: true, force: true });
      } catch {}
      job.tmpDir = null;
    }
  }
}

// -----------------------
// API
// -----------------------
app.post("/api/pdf/start", (req, res) => {
  const job = createJob();
  updateJob(job, { message: "Job creato", percent: 1 });
  runPdfJob(job, req.body || {});
  res.json({ jobId: job.id });
});

app.post("/api/images/start", (req, res) => {
  const job = createJob();
  updateJob(job, { message: "Job creato", percent: 1 });
  runImagesJob(job, req.body || {});
  res.json({ jobId: job.id });
});

// SSE events
app.get("/api/events/:jobId", (req, res) => {
  const job = jobs.get(req.params.jobId);
  if (!job) return res.status(404).end();

  res.setHeader("Content-Type", "text/event-stream");
  res.setHeader("Cache-Control", "no-cache");
  res.setHeader("Connection", "keep-alive");

  res.write(
    `data: ${JSON.stringify({
      status: job.status,
      percent: job.percent,
      message: job.message,
      current: job.current,
      total: job.total,
    })}\n\n`
  );

  job.sseClients.add(res);
  req.on("close", () => job.sseClients.delete(res));
});

// STOP
app.post("/api/stop/:jobId", async (req, res) => {
  const job = jobs.get(req.params.jobId);
  if (!job) return res.status(404).json({ error: "Job non trovato" });

  if (job.status !== "running") return res.json({ ok: true, status: job.status });

  job.cancelRequested = true;

  try {
    job.abortController?.abort();
  } catch {}

  updateJob(job, { status: "error", message: "Job annullato.", percent: job.percent });

  try {
    await job.browserRef?.close();
  } catch {}

  for (const c of job.sseClients) {
    try {
      c.end();
    } catch {}
  }
  job.sseClients.clear();

  res.json({ ok: true });
});

app.get("/api/pdf/download/:jobId", (req, res) => {
  const job = jobs.get(req.params.jobId);
  if (!job) return res.status(404).json({ error: "Job non trovato" });

  if (job.status === "error") return res.status(500).json({ error: job.error || "Errore" });
  if (job.status !== "done" || !job.pdfBuffer) return res.status(425).json({ error: "Non pronto ancora" });

  res.setHeader("Content-Type", "application/pdf");
  res.setHeader("Content-Disposition", `attachment; filename="${job.filename || "documento.pdf"}"`);
  res.send(job.pdfBuffer);

  if (FREE_AFTER_DOWNLOAD) job.pdfBuffer = null;
});

app.get("/api/images/download/:jobId", (req, res) => {
  const job = jobs.get(req.params.jobId);
  if (!job) return res.status(404).json({ error: "Job non trovato" });

  if (job.status === "error") return res.status(500).json({ error: job.error || "Errore" });
  if (job.status !== "done" || !job.zipPath) return res.status(425).json({ error: "Non pronto ancora" });

  res.setHeader("Content-Type", "application/zip");
  res.setHeader("Content-Disposition", `attachment; filename="${job.filename || "images.zip"}"`);

  const rs = fs.createReadStream(job.zipPath);
  rs.on("error", () => res.status(500).end());
  rs.pipe(res);

  rs.on("close", () => {
    // cleanup zip + tmp
    if (FREE_AFTER_DOWNLOAD) {
      try {
        fs.unlinkSync(job.zipPath);
      } catch {}
      job.zipPath = null;

      if (job.tmpDir) {
        try {
          fs.rmSync(job.tmpDir, { recursive: true, force: true });
        } catch {}
        job.tmpDir = null;
      }
    }
  });
});

const PORT = process.env.PORT || 3000;
app.listen(PORT, () => {
  console.log(`Server running on port ${PORT}`);
});

