// server.js — Site2PDF + Site2Images (ZIP) + STOP (FIXED)
// - PDF solo testo (single/list/site) con AUTO fast->safe
// - Immagini (single/list/site) -> scarica ZIP (una "cartella") con nome sito
// - Filtro min KB
// - “Qualità massima”: prende il candidato migliore da srcset/picture/lazy
// - Supporta tutti i formati image/* (estensione da URL o Content-Type)
// - SSE progress (counter coerenti: found / processed / downloaded)
// - STOP reale: POST /api/stop/:jobId

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
const CONCURRENCY = Math.max(1, Math.min(Number(process.env.CONCURRENCY || 4), 8));
const MIN_TEXT_CHARS = Math.max(200, Number(process.env.MIN_TEXT_CHARS || 2));

const GOTO_TIMEOUT_FAST = Math.max(8000, Number(process.env.GOTO_TIMEOUT_FAST || 20000));
const GOTO_TIMEOUT_SAFE = Math.max(12000, Number(process.env.GOTO_TIMEOUT_SAFE || 35000));

const FREE_AFTER_DOWNLOAD = String(process.env.FREE_AFTER_DOWNLOAD || "1") !== "0";

const app = express();
app.use(express.json({ limit: "2mb" }));
app.use(express.static(__dirname, {
  setHeaders(res, filePath) {
    if (filePath.endsWith(".css")) res.setHeader("Content-Type", "text/css; charset=utf-8");
  },
}));

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
  if (a === 169 && b === 254) return true; // link-local
  return false;
}

function isPrivateIpV6(ip) {
  const v = ip.toLowerCase();
  if (v === "::" || v === "::1") return true;
  if (v.startsWith("fe8") || v.startsWith("fe9") || v.startsWith("fea") || v.startsWith("feb")) return true; // fe80::/10 approx
  if (v.startsWith("fc") || v.startsWith("fd")) return true; // fc00::/7
  return false;
}

async function resolvesToPrivateIp(hostname) {
  if (isIpV4(hostname)) return isPrivateIpV4(hostname);
  if (isIpV6(hostname)) return true; // prudente: blocca literal IPv6

  try {
    const addrs = await dns.lookup(hostname, { all: true, verbatim: true });
    for (const a of addrs) {
      if (a.family === 4 && isPrivateIpV4(a.address)) return true;
      if (a.family === 6 && isPrivateIpV6(a.address)) return true;
    }
  } catch {
    return true;
  }
  return false;
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
  return /\.(pdf|zip|rar|7z|mp4|mp3|css|js)(\?|#|$)/i.test(u);
}

function launchArgsForOs() {
  if (process.platform === "linux") return ["--no-sandbox", "--disable-setuid-sandbox"];
  return [];
}

function ensureNotCanceled(job) {
  if (job.cancelRequested) throw new Error("Job annullato dall'utente");
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
// Dedupe "universale": stessa immagine con URL diversi -> tieni solo la migliore
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

    // Per CDN “trasformativi” alcuni path cambiano:
    // creiamo una key che ignora token/expire/signature ma considera dimensioni
    const keep = [];
    const keysToKeep = ["w","width","h","height","q","quality","dpr","fm","format"];
    for (const k of keysToKeep) {
      const v = u.searchParams.get(k);
      if (v) keep.push(`${k}=${v}`);
    }
    keep.sort();

    return `${u.origin}${p}?${keep.join("&")}`.toLowerCase();
  } catch {
    return rawUrl;
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
  try {
    const u = new URL(rawUrl);

    const w = getNumericParam(u, ["w", "width", "dw", "sw", "imgw", "maxw", "mw"]);
    const h = getNumericParam(u, ["h", "height", "dh", "sh", "imgh", "maxh", "mh"]);
    const q = getNumericParam(u, ["q", "quality", "qlt"]);
    const dpr = getNumericParam(u, ["dpr", "devicePixelRatio", "dpi"]);

    const area = (w && h) ? (w * h) : (w ? w * 1000 : 0);

    const fmt = (u.searchParams.get("fm") || u.searchParams.get("format") || "").toLowerCase();
    const pathExt = (u.pathname.split(".").pop() || "").toLowerCase();
    const format = fmt || pathExt;

    let formatBonus = 0;
    if (format.includes("avif")) formatBonus = 50000;
    else if (format.includes("webp")) formatBonus = 30000;
    else if (format.includes("png")) formatBonus = 10000;

    const qBonus = q ? Math.min(100, q) * 200 : 0;
    const dprBonus = dpr ? Math.min(5, dpr) * 5000 : 0;

    const path = u.pathname.toLowerCase();
    const thumbPenalty =
      /(thumb|thumbnail|small|_sm|_xs|\/sm\/|\/thumbs\/)/i.test(path) ? -15000 : 0;

    return area + formatBonus + qBonus + dprBonus + thumbPenalty;
  } catch {
    return 0;
  }
}

function dedupeBestImages(urls) {
  const bestByKey = new Map();

  for (const raw of urls) {
    const key = canonicalImageKey(raw);
    const s = scoreImageUrl(raw);

    const prev = bestByKey.get(key);
    if (!prev || s > prev.score) {
      bestByKey.set(key, { url: raw, score: s });
    }
  }

  return Array.from(bestByKey.values())
    .sort((a, b) => b.score - a.score)
    .map((x) => x.url);
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

  if (fastTextLen >= MIN_TEXT_CHARS) {
    const markdown = turndown.turndown(fastData.contentHtml || "");
    const rendered = md.render(markdown);
    return { title: fastData.title || "pagina", url, html: rendered };
  }

  // SAFE
  await safePage.goto(url, { waitUntil: "domcontentloaded", timeout: GOTO_TIMEOUT_SAFE });
  try {
    await safePage.waitForLoadState("networkidle", { timeout: 2500 });
  } catch {}
  try {
    await safePage.waitForTimeout(600);
  } catch {}

  ensureNotCanceled(job);

  const safeData = await extractDomContent(safePage);
  const safeTextLen = stripTagsToTextLen(safeData.contentHtml);

  const useSafe = safeTextLen > fastTextLen;
  const markdown = turndown.turndown((useSafe ? safeData.contentHtml : fastData.contentHtml) || "");
  const rendered = md.render(markdown);

  return {
    title: (useSafe ? safeData.title : fastData.title) || "pagina",
    url,
    html: rendered,
  };
}

// -----------------------
// Images: extract max quality URLs
// -----------------------
async function extractImageUrls(page, pageUrl) {
  const base = new URL(pageUrl);

  const urls = await page.evaluate(() => {
    const out = [];

    const pickBestFromSrcset = (srcset) => {
      if (!srcset || typeof srcset !== "string") return null;

      const items = srcset
        .split(",")
        .map((x) => x.trim())
        .map((x) => {
          const [u, d] = x.split(/\s+/);
          if (!u) return null;

          let score = 0;

          // descriptor: "800w" or "2x"
          if (d) {
            if (d.endsWith("w")) score = parseInt(d, 10) || 0;
            else if (d.endsWith("x")) score = Math.round((parseFloat(d) || 0) * 100000);
          } else {
            // no descriptor -> small score
            score = 1;
          }

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

    const pickBestImgUrl = (img) => {
      // srcset priority (also lazy variants)
      const ss =
        img.getAttribute("data-srcset") ||
        img.getAttribute("data-lazy-srcset") ||
        img.getAttribute("data-srcset2") ||
        img.getAttribute("srcset");

      const bestFromSs = pickBestFromSrcset(ss);

      // common lazy attributes
      const dataOriginal = img.getAttribute("data-original");
      const dataSrc = img.getAttribute("data-src");
      const dataLazy = img.getAttribute("data-lazy-src");
      const dataUrl = img.getAttribute("data-url");
      const src = img.getAttribute("src");

      // choose ONE best
      return firstNonEmpty(
        bestFromSs,
        dataOriginal,
        dataSrc,
        dataLazy,
        dataUrl,
        src
      );
    };

    const pickBestPictureUrl = (picture) => {
      // best among all <source srcset>, fallback to <img>
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

      // If we collected multiple, pick "best" by reusing srcset scoring when possible:
      // Here we just prefer longer (often full URL) is not reliable; better pick first source-best if exists.
      // We'll prefer the first candidate from sources (they come first), otherwise img.
      return candidates[0] || null;
    };

    // 1) <picture> first (avoid double counting the inner <img>)
    document.querySelectorAll("picture").forEach((pic) => {
      const best = pickBestPictureUrl(pic);
      if (best) out.push(best);
    });

    // 2) <img> that are NOT inside picture
    document.querySelectorAll("img").forEach((img) => {
      if (img.closest("picture")) return;
      const best = pickBestImgUrl(img);
      if (best) out.push(best);
    });

    // 3) Social meta (usually already best)
    document.querySelectorAll('meta[property="og:image"], meta[name="twitter:image"]').forEach((m) => {
      const c = m.getAttribute("content");
      if (c && c.trim()) out.push(c.trim());
    });

    // 4) Inline background-image (one per element)
    document.querySelectorAll("[style]").forEach((el) => {
      const st = el.getAttribute("style") || "";
      const m = st.match(/background-image\s*:\s*url\(["']?([^"')]+)["']?\)/i);
      if (m && m[1]) out.push(m[1].trim());
    });

    return out.filter(Boolean);
  });

  // resolve + dedupe absolute
  const out = new Set();
  for (const u of urls) {
    try {
      const abs = new URL(u, base);
      abs.hash = "";
      if (!["http:", "https:"].includes(abs.protocol)) continue;
      out.add(abs.toString());
    } catch {}
  }
  return Array.from(out);
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
    return await fetch(url, { method, signal: sig, redirect: "follow" });
  } finally {
    clearTimeout(t);
  }
}


async function downloadImageIfBigEnough(url, minBytes, signal) {
  // HEAD best-effort
  try {
    const head = await fetchWithTimeout(url, 12000, signal, "HEAD");
    const ct = head.headers.get("content-type") || "";
    const cl = Number(head.headers.get("content-length") || 0);
    if (ct && !ct.toLowerCase().includes("image/")) return null;
    if (cl && cl < minBytes) return null;
  } catch {
    // ignore
  }

  const res = await fetchWithTimeout(url, 25000, signal);
  if (!res.ok) return null;

  const ct = res.headers.get("content-type") || "";
  if (!ct.toLowerCase().includes("image/")) return null;

  const buf = Buffer.from(await res.arrayBuffer());
  if (buf.length < minBytes) return null;

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
  const HARD_MAX_PAGES = 60;
  maxPages = Math.max(1, Math.min(Number(maxPages) || 25, HARD_MAX_PAGES));
  maxDepth = Math.max(0, Math.min(Number(maxDepth) || 2, 5));

  const visited = new Set();
  const queue = [{ url: normalizeUrl(startUrl), depth: 0 }].filter(Boolean);
  const results = [];

  const page = await browser.newPage({ javaScriptEnabled: false });
  await configureBlocking(page, "fast");

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
      await page.goto(url, { waitUntil: "domcontentloaded", timeout: 20000 });
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
zipArchive: null,
zipOutput: null,


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
      jobs.delete(id);
    }
  }
}, 60 * 1000);

// -----------------------
// Job: PDF
// -----------------------
async function runPdfJob(job, body) {
  let browser;

  try {
    const mode = body.mode || (body.url ? "single" : null);
    if (!mode) throw new Error("Manca mode/url");

    updateJob(job, { message: "Avvio browser...", percent: 2 });

    browser = await chromium.launch({ headless: true, args: launchArgsForOs() });
    job.browserRef = browser;

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
      urls = body.urls.map((u) => normalizeUrl(String(u).trim())).filter(Boolean).slice(0, 30);
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
          const crawlPct = 6 + Math.min(16, Math.round((p.current / p.total) * 16));
          updateJob(job, {
            message: p.message,
            percent: crawlPct,
            current: p.current,
            total: Math.min(Number(body.maxPages) || 25, 60),
          });
        }
      );

      if (!urls.length) throw new Error("Nessuna pagina trovata (controlla include/exclude)");
      titleForFile = "sito";
      updateJob(job, {
        message: `Trovate ${urls.length} pagine. Estraggo testo (AUTO) ${CONCURRENCY}x...`,
        percent: 22,
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
      Array.from({ length: workerCount }, () => browser.newPage({ javaScriptEnabled: false }))
    );
    const safePages = await Promise.all(
      Array.from({ length: workerCount }, () => browser.newPage({ javaScriptEnabled: true }))
    );

    await Promise.all(fastPages.map((p) => configureBlocking(p, "fast")));
    await Promise.all(safePages.map((p) => configureBlocking(p, "safe")));

    let completed = 0;
    const total = urls.length;

    const extracted = await runWithWorkerPool(urls, workerCount, async (u, index, workerId) => {
      ensureNotCanceled(job);

      updateJob(job, {
        message: `Leggo pagina ${completed + 1}/${total}...`,
        percent: 22 + Math.round((completed / Math.max(1, total)) * 60),
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
    updateJob(job, { message: "Creo PDF...", percent: 85, current: sections.length, total });

    // 3) PDF
    const combinedHtml = buildCombinedHtml(sections);
    const pdfPage = await browser.newPage({ javaScriptEnabled: false });
    await pdfPage.emulateMedia({ media: "screen" });
    await pdfPage.setContent(combinedHtml, { waitUntil: "domcontentloaded", timeout: 20000 });

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
    if (browser) {
      try {
        await browser.close();
      } catch {}
    }
  }
}

// -----------------------
// Job: Images -> ZIP (counter FIXED)
// -----------------------
async function runImagesJob(job, body) {
  let browser;

  try {
    const mode = body.mode || (body.url ? "single" : null);
    if (!mode) throw new Error("Manca mode/url");

    const minKB = Math.max(0, Number(body.minKB || 0));
    const minBytes = Math.floor(minKB * 1024);

    updateJob(job, { message: "Avvio browser...", percent: 2 });

    browser = await chromium.launch({ headless: true, args: launchArgsForOs() });
    job.browserRef = browser;

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
      urls = body.urls.map((u) => normalizeUrl(String(u).trim())).filter(Boolean).slice(0, 30);
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
          const crawlPct = 6 + Math.min(16, Math.round((p.current / p.total) * 16));
          updateJob(job, {
            message: p.message,
            percent: crawlPct,
            current: p.current,
            total: Math.min(Number(body.maxPages) || 25, 60),
          });
        }
      );

      if (!urls.length) throw new Error("Nessuna pagina trovata");
      nameBase = safeZipNameFromUrl(startUrl);

      updateJob(job, {
        message: `Trovate ${urls.length} pagine. Cerco immagini...`,
        percent: 22,
        total: urls.length,
        current: 0,
      });
    } else {
      throw new Error("mode non supportata");
    }

    ensureNotCanceled(job);

    // 2) Estrai URL immagini (JS on)
    const pageWorkers = Math.min(CONCURRENCY, urls.length);
    const pages = await Promise.all(
      Array.from({ length: pageWorkers }, () => browser.newPage({ javaScriptEnabled: true }))
    );
    await Promise.all(pages.map((p) => configureBlocking(p, "safe")));

    let scannedPages = 0;
    const imageUrlSet = new Set();

    await runWithWorkerPool(urls, pageWorkers, async (u, idx, wid) => {
      ensureNotCanceled(job);

      updateJob(job, {
        message: `Scansiono immagini ${scannedPages + 1}/${urls.length}...`,
        percent: 22 + Math.round((scannedPages / Math.max(1, urls.length)) * 35),
        current: scannedPages,
        total: urls.length,
      });

      const p = pages[wid];

      try {
        await p.goto(u, { waitUntil: "domcontentloaded", timeout: GOTO_TIMEOUT_SAFE });
        try {
          await p.waitForLoadState("networkidle", { timeout: 2000 });
        } catch {}
        const imgs = await extractImageUrls(p, u);
        imgs.forEach((x) => imageUrlSet.add(x));
      } catch {}

      scannedPages++;
      return null;
    });

    await Promise.all(pages.map((p) => p.close()));

let imageUrls = Array.from(imageUrlSet);

// qui tieni solo la versione "migliore" per ogni immagine
imageUrls = dedupeBestImages(imageUrls);

const foundTotal = imageUrls.length;

    if (!foundTotal) throw new Error("Nessuna immagine trovata");

    ensureNotCanceled(job);
updateJob(job, {
  message: `Trovate ${foundTotal} immagini. Download + ZIP (min ${minKB}KB)...`,
  percent: 60,
  current: 0,
  total: foundTotal,
});

// 3) ZIP su disco (ANTI-FREEZE)
const zipFileName = `${safeFilename(nameBase)}.zip`;
const zipPath = path.join(os.tmpdir(), `${job.id}-${zipFileName}`);
job.zipPath = zipPath;
job.filename = zipFileName;

const output = fs.createWriteStream(zipPath);
const archive = archiver("zip", { zlib: { level: 6 } });
job.zipArchive = archive;
job.zipOutput = output;


archive.on("warning", (err) => console.warn("ARCHIVER warning:", err?.message || err));
archive.on("error", (err) => {
  console.error("ARCHIVER error:", err?.message || err);
  try { output.destroy(err); } catch {}
});

archive.pipe(output);

// controller per abort dei fetch (serve anche per stop)
const abortController = new AbortController();
job.abortController = abortController;

let processed = 0;
let downloaded = 0;

await runWithWorkerPool(imageUrls, Math.min(CONCURRENCY, 8), async (imgUrl) => {
  ensureNotCanceled(job);

  updateJob(job, {
    message: `Scarico immagini ${processed + 1}/${foundTotal}... (salvate: ${downloaded})`,
    percent: 60 + Math.round((processed / Math.max(1, foundTotal)) * 35),
    current: processed,
    total: foundTotal,
  });

  try {
    const r = await downloadImageIfBigEnough(imgUrl, minBytes, abortController.signal);
    if (!r) return null;

    const u = new URL(imgUrl);
    const baseName = (u.pathname.split("/").pop() || "image").split("?")[0] || "image";
    const cleanBase = baseName.replace(/[^a-z0-9._-]+/gi, "-").slice(0, 80) || "image";

    const ext = extFromUrl(imgUrl) || extFromContentType(r.contentType) || "img";
    const finalFile = cleanBase.includes(".") ? cleanBase : `${cleanBase}.${ext}`;

    const numbered = `${String(downloaded).padStart(4, "0")}-${finalFile}`;
    archive.append(r.buf, { name: `${safeFilename(nameBase)}/${numbered}` });

    downloaded++;
  } catch {
    // skip
  } finally {
    processed++;
  }

  return null;
});

// finalize (aspetta che il file sia chiuso davvero)
await new Promise((resolve, reject) => {
  output.on("close", resolve);
  output.on("finish", resolve);
  output.on("error", reject);
  archive.on("error", reject);
  archive.finalize();
});

// qui sotto DEVE esserci il tuo updateJob done (quello che avevi)



    updateJob(job, {
      status: "done",
      message: `ZIP pronto ✅ (salvate: ${downloaded}/${foundTotal})`,
      percent: 100,
      current: foundTotal,
      total: foundTotal,
    });
  } catch (e) {
    job.error = String(e?.message || e);
    updateJob(job, { status: "error", message: job.error, percent: 100 });
  } finally {
    // pulizia riferimenti (STOP/fetch abort)
    try { job.abortController?.abort(); } catch {}
    try { job.zipArchive?.abort(); } catch {}
try { job.zipOutput?.destroy(); } catch {}

job.abortController = null;
job.zipArchive = null;
job.zipOutput = null;



if (job.status !== "done" && job.zipPath) {
  try { fs.unlinkSync(job.zipPath); } catch {}
  job.zipPath = null;
}

    job.browserRef = null;
    if (browser) {
      try {
        await browser.close();
      } catch {}
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

// SSE events (vale per qualunque job)
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

// STOP (vale per qualunque job)
app.post("/api/stop/:jobId", async (req, res) => {
  const job = jobs.get(req.params.jobId);
  if (!job) return res.status(404).json({ error: "Job non trovato" });

  if (job.status !== "running") return res.json({ ok: true, status: job.status });

  job.cancelRequested = true;
  try { job.abortController?.abort(); } catch {}
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
    if (FREE_AFTER_DOWNLOAD) {
      try { fs.unlinkSync(job.zipPath); } catch {}
      job.zipPath = null;
    }
  });
});

const PORT = process.env.PORT || 3000;
app.listen(PORT, () => {
  console.log(`Server running on port ${PORT}`);
});


