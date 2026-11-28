#!/usr/bin/env node
/**
 * Export one of the book's animated SVGs without reimplementing its mathematics.
 *
 * Usage: node Blueprint/Tools/export-figure-gif.mjs PAGE_URL FIGURE_ID OUTPUT_DIR
 * Requires Chrome, Node with WebSocket, and Python with Pillow. Serve the built
 * book over HTTP first. The interactive book remains the source: its pause control and
 * reduced-motion behavior cannot be carried into a GIF.
 */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdir, mkdtemp, realpath, rename, rm, writeFile } from 'node:fs/promises';
import { spawn } from 'node:child_process';
import path from 'node:path';

const [page, id, requestedOutput] = process.argv.slice(2);
assert.ok(page && id && requestedOutput,
  'Usage: export-figure-gif.mjs PAGE_URL FIGURE_ID OUTPUT_DIR');
assert.match(id, /^[a-z0-9-]+$/);
assert.ok(['http:', 'https:'].includes(new URL(page).protocol));
const root = await realpath(process.cwd());
const localOut = path.join(root, '_out');
assert.equal(await realpath(localOut), localOut, 'The built _out directory must be local.');
const output = path.resolve(requestedOutput);
assert.ok(output.startsWith(`${localOut}/`), 'Output must be inside the local _out directory.');
// Check the existing ancestor before creating anything through a possible symlink.
let ancestor = output;
for (;;) {
  try {
    const resolved = await realpath(ancestor);
    assert.ok(resolved === localOut || resolved.startsWith(`${localOut}/`),
      'Output ancestor resolves outside _out.');
    break;
  } catch (error) {
    if (error.code !== 'ENOENT') throw error;
    ancestor = path.dirname(ancestor);
  }
}
await mkdir(output, { recursive: true });
assert.ok((await realpath(output)).startsWith(`${localOut}/`), 'Output resolves outside _out.');
const work = await mkdtemp(path.join(output, `.frames-${id}-`));
const staged = path.join(work, 'artifacts');
await mkdir(staged);
const published = path.join(output, path.basename(work).replace('.frames-', ''));
const chrome = spawn(process.env.CHROME_BIN || 'google-chrome', [
  '--headless=new', '--no-sandbox', '--disable-gpu', '--remote-debugging-port=0',
  `--user-data-dir=${work}/chrome-profile`, 'about:blank',
], { stdio: ['ignore', 'ignore', 'pipe'] });
let socket, pack;
const pending = new Map();
const exceptions = [];
const exited = child => !child?.pid || child.exitCode !== null || child.signalCode !== null;
const stopChild = async child => {
  if (exited(child)) return true;
  const wait = ms => new Promise(resolve => {
    const done = () => { clearTimeout(timer); resolve(); };
    const timer = setTimeout(() => { child.off('exit', done); resolve(); }, ms);
    child.once('exit', done);
  });
  child.kill('SIGTERM');
  await wait(3000);
  if (!exited(child)) {
    child.kill('SIGKILL');
    await wait(3000);
  }
  return exited(child);
};
try {
  const endpoint = await new Promise((resolve, reject) => {
    const timeout = setTimeout(() => reject(Error('Chrome did not start.')), 30000);
    let logs = '';
    chrome.stderr.on('data', data => {
      logs += data;
      const match = logs.match(/DevTools listening on (ws:\/\/\S+)/);
      if (match) { clearTimeout(timeout); resolve(match[1]); }
    });
    chrome.on('error', error => { clearTimeout(timeout); reject(error); });
    chrome.on('exit', code => {
      clearTimeout(timeout);
      reject(Error(`Chrome exited ${code}: ${logs.slice(-2000)}`));
    });
  });
  socket = new WebSocket(endpoint);
  await new Promise((resolve, reject) => {
    socket.addEventListener('open', resolve, { once: true });
    socket.addEventListener('error', reject, { once: true });
  });
  let sequence = 0;
  socket.addEventListener('message', event => {
    const message = JSON.parse(event.data);
    if (message.method === 'Runtime.exceptionThrown') exceptions.push(message.params);
    const waiter = pending.get(message.id);
    if (waiter) {
      clearTimeout(waiter.timeout);
      pending.delete(message.id);
      message.error ? waiter.reject(Error(JSON.stringify(message.error))) :
        waiter.resolve(message.result);
    }
  });
  const send = (method, params = {}, sessionId) => new Promise((resolve, reject) => {
    const number = ++sequence;
    const timeout = setTimeout(() => {
      pending.delete(number);
      reject(Error(`Chrome timed out: ${method}`));
    }, 30000);
    pending.set(number, { resolve, reject, timeout });
    socket.send(JSON.stringify({ id: number, method, params, sessionId }));
  });
  const { targetId } = await send('Target.createTarget', { url: 'about:blank' });
  const { sessionId } = await send('Target.attachToTarget', { targetId, flatten: true });
  const call = (method, params = {}) => send(method, params, sessionId);
  const evaluate = async expression => {
    const result = await call('Runtime.evaluate',
      { expression, returnByValue: true, awaitPromise: true });
    if (result.exceptionDetails) throw Error(JSON.stringify(result.exceptionDetails));
    return result.result.value;
  };
  await call('Runtime.enable');
  await call('Page.enable');
  await call('Emulation.setDeviceMetricsOverride',
    { width: 1440, height: 1100, deviceScaleFactor: 1, mobile: false });
  // Start from a stable first frame even if the user's desktop permits motion.
  await call('Emulation.setEmulatedMedia',
    { features: [{ name: 'prefers-reduced-motion', value: 'reduce' }] });
  await call('Page.navigate', { url: page });
  const selector = `[data-leanpde-figure="${id}"]`;
  let ready = false;
  for (let i = 0; i < 150; i++) {
    ready = await evaluate(`document.readyState === 'complete' &&
      !!document.querySelector(${JSON.stringify(selector)})?.querySelector('svg')`);
    if (ready) break;
    await new Promise(resolve => setTimeout(resolve, 100));
  }
  assert.ok(ready, `Figure ${id} did not load at ${page}.`);
  const metadata = await evaluate(`(async () => {
    await document.fonts.ready;
    const figure = document.querySelector(${JSON.stringify(selector)});
    const svg = figure.querySelector('svg');
    const durations = [...new Set([...svg.querySelectorAll('animate, animateTransform')]
      .map(node => node.getAttribute('dur')))];
    const caption = figure.querySelector('figcaption').cloneNode(true);
    caption.querySelector('button')?.remove();
    const css = getComputedStyle(svg);
    const typography = Object.fromEntries(['font-family', 'font-size', 'font-weight',
      'font-style', 'font-stretch', 'line-height', 'letter-spacing', 'color']
      .map(name => [name, css.getPropertyValue(name)]));
    const palette = Object.fromEntries(['surface', 'ink', 'muted', 'accent', 'accent-2',
      'band', 'warn'].map(role => {
        const name = '--leanpde-fig-' + role;
        return [name, css.getPropertyValue(name)];
      }));
    // Keep the actual SVG, fonts and theme, but remove neighboring page furniture
    // from this disposable browser document before taking compositor screenshots.
    for (const style of document.body.querySelectorAll('style,link[rel="stylesheet"]'))
      document.head.append(style);
    document.body.replaceChildren(figure);
    Object.assign(document.body.style, {display: 'block', margin: '0', padding: '0',
      width: '960px', maxWidth: 'none', minHeight: '0', height: 'auto'});
    Object.assign(figure.style, {display: 'block', position: 'static', float: 'none',
      margin: '0', padding: '0', border: '0', transform: 'none', overflow: 'visible',
      width: '960px', maxWidth: 'none'});
    for (const [name, value] of Object.entries({...typography, ...palette}))
      figure.style.setProperty(name, value);
    Object.assign(svg.style, {width: '960px', maxWidth: 'none', height: 'auto'});
    for (const [name, value] of Object.entries(typography))
      svg.style.setProperty(name, value);
    window.scrollTo({left: 0, top: 0, behavior: 'instant'});
    svg.pauseAnimations();
    svg.setCurrentTime(0);
    await new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(resolve)));
    const box = svg.getBoundingClientRect();
    if (!svg.isConnected || figure.parentElement !== document.body ||
        Math.abs(box.width - 960) > 0.1 || !Number.isFinite(box.height) || box.height <= 0)
      throw Error('The original SVG could not be isolated for capture.');
    return {title: figure.querySelector('strong').textContent, typography, palette,
      theme: document.documentElement.dataset.theme,
      caption: caption.textContent.trim(), alt: svg.getAttribute('aria-label'),
      viewBox: svg.getAttribute('viewBox'), durations,
      exportBox: {x: box.x, y: box.y, width: box.width, height: box.height}};
  })()`);
  assert.equal(metadata.durations.length, 1, 'Export requires a common animation period.');
  assert.match(metadata.durations[0], /^\d+(\.\d+)?s$/);
  const seconds = Number.parseFloat(metadata.durations[0]);
  const fps = 10;
  assert.ok(seconds > 0 && seconds <= 30);
  const frames = Math.round(seconds * fps);
  assert.ok(frames >= 2 && Math.abs(frames - seconds * fps) < 1e-8,
    'The animation period must contain at least two whole 100-ms frames.');
  const hashes = new Set();
  for (let frame = 0; frame < frames; frame++) {
    const clip = await evaluate(`(async () => {
      const svg = document.querySelector(${JSON.stringify(selector)}).querySelector('svg');
      svg.setCurrentTime(${frame / fps});
      await new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(resolve)));
      const box = svg.getBoundingClientRect();
      return {x: box.x + scrollX, y: box.y + scrollY,
        width: box.width, height: box.height, scale: 1};
    })()`);
    const { data } = await call('Page.captureScreenshot',
      { format: 'png', captureBeyondViewport: true, clip });
    const bytes = Buffer.from(data, 'base64');
    hashes.add(createHash('sha256').update(bytes).digest('hex'));
    await writeFile(path.join(work, `${String(frame).padStart(4, '0')}.png`), bytes);
    if (frame === 0) await writeFile(path.join(staged, `${id}.png`), bytes);
  }
  assert.ok(hashes.size > 1, 'The export did not capture any motion.');
  assert.deepEqual(exceptions, [], 'Browser raised a JavaScript exception.');
  // One palette for the whole loop prevents stationary text from flickering.
  pack = spawn('python3', ['-c', `
from pathlib import Path
import sys
from PIL import Image
source, output, name, fps = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3], int(sys.argv[4])
frames = [Image.open(p).convert("RGB") for p in sorted(source.glob("*.png"))]
samples = frames[::max(1, len(frames) // 12)]
sheet = Image.new("RGB", (frames[0].width, frames[0].height * len(samples)))
for index, frame in enumerate(samples):
    sheet.paste(frame, (0, index * frame.height))
palette = sheet.quantize(colors=256)
indexed = [frame.quantize(palette=palette, dither=Image.Dither.NONE) for frame in frames]
target = output / (name + ".gif")
indexed[0].save(target, save_all=True, append_images=indexed[1:],
                duration=1000 // fps, loop=0, optimize=False, disposal=1)
with Image.open(target) as result:
    assert result.n_frames > 1
    total = 0
    for index in range(result.n_frames):
        result.seek(index)
        total += result.info["duration"]
    assert total == len(frames) * (1000 // fps)
contact = Image.new("RGB", (frames[0].width, frames[0].height * 3))
for row, index in enumerate((0, len(frames) // 3, 2 * len(frames) // 3)):
    contact.paste(frames[index], (0, row * frames[0].height))
contact.save(output / (name + "-contact.png"))
`, work, staged, id, String(fps)], { stdio: 'inherit' });
  await new Promise((resolve, reject) => {
    const timer = setTimeout(() => reject(Error('Pillow packing timed out.')), 60000);
    pack.once('error', error => { clearTimeout(timer); reject(error); });
    pack.once('exit', (code, signal) => {
      clearTimeout(timer);
      code === 0 ? resolve() : reject(Error(`Pillow exited ${code ?? signal}`));
    });
  });
  await writeFile(path.join(staged, `${id}.json`), JSON.stringify({
    ...metadata, page, id, seconds, fps, frames, distinctFrames: hashes.size,
    generatedAt: new Date().toISOString(),
    method: 'Browser snapshots of the Blueprint SVG at evenly spaced SVG animation times.',
  }, null, 2) + '\n');
  // Publish the complete validated set together, leaving previous exports intact.
  await rename(staged, published);
  console.log(`Exported ${id}: ${frames} frames, ${seconds}s, GIF and PNG in ${published}`);
} finally {
  for (const waiter of pending.values()) clearTimeout(waiter.timeout);
  socket?.close();
  const stopped = await Promise.all([stopChild(pack), stopChild(chrome)]);
  if (stopped.every(Boolean)) await rm(work, { recursive: true, force: true, maxRetries: 5, retryDelay: 200 });
  else {
    console.error(`A child did not exit; retained its working directory: ${work}`);
    process.exitCode = 1;
  }
}
