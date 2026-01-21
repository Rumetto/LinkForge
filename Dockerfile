FROM mcr.microsoft.com/playwright:v1.46.0-jammy

WORKDIR /app

COPY package*.json ./
RUN npm ci

COPY . .

ENV PORT=8080
EXPOSE 8080

CMD ["node", "server.js"]
