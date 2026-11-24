// mend: the CLI SPEC.md specifies. Node 22, standard library only.
// It reads a patch in one of four formats (unified diff, SEARCH/REPLACE blocks,
// V4A, JSON edits), finds the lines each edit names at the first of three
// matching tiers, and writes every change or none. No network, no clock,
// no randomness, no model calls: a scripted program, fully deterministic.
//
// Run as `node main.ts [options] [PATCH]` in the root of a tree of text files.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

/** A patch's lines: split at \n, one trailing \r removed, no empty piece after a final \n. */
function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** A file as lines: its line break, its lines, and whether it ends with a break. */
interface FileData {
  lines: string[];
  br: '\r\n' | '\n';
  finalBreak: boolean;
}

function parseFile(text: string): FileData {
  if (text === '') return { lines: [], br: '\n', finalBreak: false };
  const nl = text.indexOf('\n');
  const br: '\r\n' | '\n' = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const finalBreak = text.endsWith(br);
  const parts = text.split(br);
  if (finalBreak) parts.pop();
  return { lines: parts, br, finalBreak };
}

function serializeFile(f: FileData): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.finalBreak ? f.br : '');
}

/** Tier equality of two lines: 0 exact, 1 trailing whitespace off, 2 both ends off. */
function stripTrail(s: string): string {
  return s.replace(/[ \t]+$/, '');
}
function stripBoth(s: string): string {
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}
function lineEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return stripTrail(a) === stripTrail(b);
  return stripBoth(a) === stripBoth(b);
}
function leadingWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
}

/** Every position where O occurs in lines at one tier; occurrences may overlap. */
function occurrences(lines: string[], o: string[], tier: number): number[] {
  const out: number[] = [];
  if (o.length === 0) return out;
  for (let i = 0; i + o.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (!lineEq(lines[i + j]!, o[j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier (0, then 1, then 2; only 0 when strict) where O occurs, with its positions. */
function findTier(lines: string[], o: string[], strict: boolean): { tier: number; at: number[] } | null {
  const top = strict ? 0 : 2;
  for (let t = 0; t <= top; t++) {
    const at = occurrences(lines, o, t);
    if (at.length > 0) return { tier: t, at };
  }
  return null;
}

/** One line of a hunk or chunk body: context (in both old and new), old, or new. */
type Item = { kind: 'ctx' | 'old' | 'new'; text: string };

function oldLines(items: Item[]): string[] {
  return items.filter((x) => x.kind !== 'new').map((x) => x.text);
}
function newLines(items: Item[]): string[] {
  return items.filter((x) => x.kind !== 'old').map((x) => x.text);
}

/**
 * The lines that replace the matched old lines: a context line is written as
 * the file's own matched line, never the patch's; at tier 2 every other line
 * is re-indented from the old lines' leading whitespace to the file's.
 */
function buildNew(items: Item[], fileLines: string[], pos: number, tier: number): string[] {
  const o = oldLines(items);
  const out: string[] = [];
  const f0 = fileLines[pos] ?? '';
  const p0 = o.length > 0 ? o[0]! : '';
  const fLead = leadingWs(f0);
  const pLead = leadingWs(p0);
  let oi = 0;
  for (const it of items) {
    if (it.kind === 'old') {
      oi++;
      continue;
    }
    if (it.kind === 'ctx') {
      out.push(fileLines[pos + oi]!);
      oi++;
      continue;
    }
    let t = it.text;
    if (tier === 2 && t !== '' && t.trim() !== '' && t.startsWith(pLead)) t = fLead + t.slice(pLead.length);
    out.push(t);
  }
  return out;
}

/** Replace the old lines at pos with the new ones, keeping the file's break style. */
function spliceAt(f: FileData, pos: number, items: Item[], tier: number): FileData {
  const o = oldLines(items);
  const rep = buildNew(items, f.lines, pos, tier);
  const lines = [...f.lines.slice(0, pos), ...rep, ...f.lines.slice(pos + o.length)];
  return { lines, br: f.br, finalBreak: f.finalBreak };
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

/** One edit: it changes the tree or throws Fail; a move edit reports its pair. */
type EditResult = { move?: [string, string] };
type Edit = (tree: Tree) => EditResult | void;

/** Detect the patch format (SPEC section 4); null when none matches. */
function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const readExisting = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = readExisting(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const norm = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = norm(before);
      const old = norm(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + norm(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = readExisting(tree);
      const f = parseFile(before);
      if (line < 0 || line > f.lines.length) throw new Fail('no-match', p);
      const lines = [...f.lines.slice(0, line), ...add, ...f.lines.slice(line)];
      tree.now.set(p, serializeFile({ lines, br: f.br, finalBreak: f.finalBreak }));
    };
  }
  return null;
}

/** All JSON edits of a patch: one array, or one object per line (SPEC section 9). */
function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/** A unified hunk: its old start line, its body items, and whether a `\` line follows its last context or new line. */
interface Hunk {
  a: number;
  items: Item[];
  noBreak: boolean;
}

interface Section {
  oldPath: string | null;
  newPath: string | null;
  create: boolean;
  remove: boolean;
  hunks: Hunk[];
}

/** A `--- <path>` / `+++ <path>` path: up to the first tab, surrounding spaces removed. */
function headerPath(s: string): string | null {
  const t = s.split('\t')[0]!.trim();
  if (t === '/dev/null') return null;
  if (t.startsWith('a/') || t.startsWith('b/')) return t.slice(2);
  return t;
}

/** Turn hunk body lines into items, noting a `\` line after the last context or new line. */
function bodyItems(body: string[]): { items: Item[]; noBreak: boolean } {
  const items: Item[] = [];
  let noBreak = false;
  for (let k = 0; k < body.length; k++) {
    const b = body[k]!;
    if (b.startsWith('\\')) continue;
    if (b === '') items.push({ kind: 'ctx', text: '' });
    else if (b[0] === ' ') items.push({ kind: 'ctx', text: b.slice(1) });
    else if (b[0] === '-') items.push({ kind: 'old', text: b.slice(1) });
    else if (b[0] === '+') items.push({ kind: 'new', text: b.slice(1) });
  }
  for (let k = body.length - 1; k >= 0; k--) {
    const b = body[k]!;
    if (b.startsWith('\\')) continue;
    if (b === '' || b[0] === ' ' || b[0] === '+') {
      noBreak = k + 1 < body.length && body[k + 1]!.startsWith('\\');
    }
    break;
  }
  return { items, noBreak };
}

/** Apply one hunk to a file's lines, following SPEC section 6. */
function applyHunk(f: FileData, h: Hunk, d: number, strict: boolean, path: string): FileData {
  const o = oldLines(h.items);
  if (o.length === 0) {
    const at = Math.min(h.a + d, f.lines.length);
    const atEnd = at === f.lines.length;
    const rep = newLines(h.items);
    const lines = [...f.lines.slice(0, at), ...rep, ...f.lines.slice(at)];
    return { lines, br: f.br, finalBreak: atEnd ? !h.noBreak : f.finalBreak };
  }
  const found = findTier(f.lines, o, strict);
  if (!found) throw new Fail('no-match', path);
  const target = h.a - 1 + d;
  let best = found.at[0]!;
  let bestDist = Math.abs(best - target);
  for (const p of found.at) {
    const dist = Math.abs(p - target);
    if (dist < bestDist) {
      best = p;
      bestDist = dist;
    }
  }
  const touchedEnd = best + o.length === f.lines.length;
  const after = spliceAt(f, best, h.items, found.tier);
  return { ...after, finalBreak: touchedEnd ? !h.noBreak : f.finalBreak };
}

/** One unified section as one edit (SPEC section 6). */
function sectionEdit(sec: Section, strict: boolean): Edit {
  return (tree) => {
    if (sec.create) {
      const p = sec.newPath!;
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      const made: string[] = [];
      for (const h of sec.hunks) for (const it of h.items) if (it.kind === 'new') made.push(it.text);
      const last = sec.hunks[sec.hunks.length - 1];
      const noBreak = last !== undefined && last.noBreak;
      tree.now.set(p, made.length === 0 ? '' : made.join('\n') + (noBreak ? '' : '\n'));
      return;
    }
    if (sec.remove) {
      const p = sec.oldPath!;
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) === null) throw new Fail('missing', p);
      tree.now.set(p, null);
      return;
    }
    const oldP = sec.oldPath!;
    const move = sec.newPath !== null && sec.newPath !== sec.oldPath;
    const newP = move ? sec.newPath! : oldP;
    if (!safe(oldP)) throw new Fail('unsafe', oldP);
    if (move && !safe(newP)) throw new Fail('unsafe', newP);
    const before = tree.get(oldP);
    if (before === null) throw new Fail('missing', oldP);
    if (move && tree.get(newP) !== null) throw new Fail('exists', newP);
    let fd = parseFile(before);
    let d = 0;
    for (const h of sec.hunks) {
      const oLen = oldLines(h.items).length;
      const nLen = newLines(h.items).length;
      fd = applyHunk(fd, h, d, strict, oldP);
      d += nLen - oLen;
    }
    if (move) {
      tree.now.set(newP, serializeFile(fd));
      tree.now.set(oldP, null);
      return { move: [oldP, newP] };
    }
    tree.now.set(oldP, serializeFile(fd));
  };
}

/** Parse a unified patch into one edit per section (SPEC section 6). */
function parseUnified(lines: string[], strict: boolean): Edit[] {
  const n = lines.length;
  const edits: Edit[] = [];
  const isDiffGit = (l: string): boolean => l.startsWith('diff --git ');
  const isPairAt = (idx: number): boolean =>
    idx < n && lines[idx]!.startsWith('--- ') && (lines[idx + 1] ?? '').startsWith('+++ ');
  const diffPaths = (l: string): [string, string] | null => {
    const m = /^diff --git a\/(\S+) b\/(\S+)$/.exec(l.trimEnd());
    return m ? [m[1]!, m[2]!] : null;
  };
  let i = 0;
  while (i < n) {
    let dg: [string, string] | null = null;
    if (isDiffGit(lines[i]!)) {
      dg = diffPaths(lines[i]!);
      if (dg === null) throw new Exit2(`error: parse ${i + 1}`);
      i++;
    } else if (lines[i]!.startsWith('@@')) {
      throw new Exit2(`error: parse ${i + 1}`);
    } else if (!isPairAt(i)) {
      i++;
      continue;
    }
    const sec: Section = { oldPath: dg ? dg[0] : null, newPath: dg ? dg[1] : null, create: false, remove: false, hunks: [] };
    let pairSeen = false;
    while (i < n) {
      const l = lines[i]!;
      if (l.startsWith('@@')) break;
      if (isDiffGit(l)) break;
      if (l.startsWith('--- ')) {
        if (!pairSeen && (lines[i + 1] ?? '').startsWith('+++ ')) {
          sec.oldPath = headerPath(l.slice(4));
          sec.newPath = headerPath(lines[i + 1]!.slice(4));
          pairSeen = true;
          i += 2;
          continue;
        }
        if (!pairSeen) throw new Exit2(`error: parse ${i + 2}`);
        break;
      }
      if (l.startsWith('+++ ')) {
        sec.newPath = headerPath(l.slice(4));
        i++;
        continue;
      }
      if (l.startsWith('rename from ') && !pairSeen) {
        sec.oldPath = l.slice(12).trim();
        i++;
        continue;
      }
      if (l.startsWith('rename to ') && !pairSeen) {
        sec.newPath = l.slice(10).trim();
        i++;
        continue;
      }
      if (l.startsWith('new file mode')) {
        sec.create = true;
        i++;
        continue;
      }
      if (l.startsWith('deleted file mode')) {
        sec.remove = true;
        i++;
        continue;
      }
      i++;
    }
    while (i < n) {
      const l = lines[i]!;
      if (isDiffGit(l) || isPairAt(i)) break;
      if (!l.startsWith('@@')) {
        i++;
        continue;
      }
      const hm = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(l);
      if (!hm) throw new Exit2(`error: parse ${i + 1}`);
      const hunk: Hunk = { a: parseInt(hm[1]!, 10), items: [], noBreak: false };
      i++;
      const body: string[] = [];
      while (i < n) {
        const b = lines[i]!;
        if (isDiffGit(b) || isPairAt(i)) break;
        if (b.startsWith('@@')) break;
        if (b === '' || b[0] === ' ' || b[0] === '-' || b[0] === '+' || b[0] === '\\') {
          body.push(b);
          i++;
          continue;
        }
        break;
      }
      while (body.length > 0 && body[body.length - 1] === '') body.pop();
      const parsed = bodyItems(body);
      hunk.items = parsed.items;
      hunk.noBreak = parsed.noBreak;
      sec.hunks.push(hunk);
    }
    edits.push(sectionEdit(sec, strict));
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

/** One SEARCH/REPLACE block as one edit (SPEC section 7). */
function srEdit(path: string, oldL: string[], newL: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldL.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, newL.length === 0 ? '' : newL.join('\n') + '\n');
      return;
    }
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    const f = parseFile(before);
    const found = findTier(f.lines, oldL, strict);
    if (!found) throw new Fail('no-match', path);
    if (found.at.length > 1) throw new Fail('ambiguous', path);
    const pos = found.at[0]!;
    const items: Item[] = [
      ...oldL.map((t): Item => ({ kind: 'old', text: t })),
      ...newL.map((t): Item => ({ kind: 'new', text: t })),
    ];
    const rep = buildNew(items, f.lines, pos, found.tier);
    const lines = [...f.lines.slice(0, pos), ...rep, ...f.lines.slice(pos + oldL.length)];
    tree.now.set(path, serializeFile({ lines, br: f.br, finalBreak: f.finalBreak }));
  };
}

/** Parse SEARCH/REPLACE blocks into edits (SPEC section 7). */
function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const n = lines.length;
  const edits: Edit[] = [];
  let lastEnd = 0;
  let prevPath: string | null = null;
  let i = 0;
  while (i < n) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchLine = i + 1;
    let path: string | null = null;
    for (let j = i - 1; j >= lastEnd; j--) {
      const l = lines[j]!;
      if (blank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchLine}`);
      path = prevPath;
    }
    let eq = -1;
    for (let j = i + 1; j < n; j++) {
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') break;
    }
    if (eq < 0) throw new Exit2(`error: parse ${searchLine}`);
    let rep = -1;
    for (let j = eq + 1; j < n; j++) {
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (rep < 0) throw new Exit2(`error: parse ${searchLine}`);
    edits.push(srEdit(path, lines.slice(i + 1, eq), lines.slice(eq + 1, rep), strict));
    prevPath = path;
    lastEnd = rep + 1;
    i = rep + 1;
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

/** One V4A chunk: its anchor (null: no @@ line, '': empty anchor), its body, and whether it is end-of-file. */
interface VChunk {
  anchor: string | null;
  eof: boolean;
  items: Item[];
}

type VSection =
  | { kind: 'add'; path: string; made: string[] }
  | { kind: 'delete'; path: string }
  | { kind: 'update'; path: string; moveTo: string | null; chunks: VChunk[]; updateLine: number };

/** One V4A section as one edit (SPEC section 8). */
function vSectionEdit(sec: VSection, strict: boolean): Edit {
  return (tree) => {
    if (sec.kind === 'add') {
      if (!safe(sec.path)) throw new Fail('unsafe', sec.path);
      if (tree.get(sec.path) !== null) throw new Fail('exists', sec.path);
      tree.now.set(sec.path, sec.made.length === 0 ? '' : sec.made.join('\n') + '\n');
      return;
    }
    if (sec.kind === 'delete') {
      if (!safe(sec.path)) throw new Fail('unsafe', sec.path);
      if (tree.get(sec.path) === null) throw new Fail('missing', sec.path);
      tree.now.set(sec.path, null);
      return;
    }
    if (!safe(sec.path)) throw new Fail('unsafe', sec.path);
    if (sec.moveTo !== null && !safe(sec.moveTo)) throw new Fail('unsafe', sec.moveTo);
    const before = tree.get(sec.path);
    if (before === null) throw new Fail('missing', sec.path);
    if (sec.moveTo !== null && tree.get(sec.moveTo) !== null) throw new Fail('exists', sec.moveTo);
    let fd = parseFile(before);
    let cursor = 0;
    for (const ch of sec.chunks) {
      if (ch.anchor !== null && ch.anchor !== '') {
        let foundIdx = -1;
        const top = strict ? 0 : 2;
        for (let t = 0; t <= top && foundIdx < 0; t++) {
          for (let k = cursor; k < fd.lines.length; k++) {
            if (lineEq(fd.lines[k]!, ch.anchor, t)) {
              foundIdx = k;
              break;
            }
          }
        }
        if (foundIdx < 0) throw new Fail('no-match', sec.path);
        cursor = foundIdx + 1;
      }
      const o = oldLines(ch.items);
      if (o.length === 0) {
        const at = ch.eof ? fd.lines.length : cursor;
        const rep = newLines(ch.items);
        const lines = [...fd.lines.slice(0, at), ...rep, ...fd.lines.slice(at)];
        fd = { lines, br: fd.br, finalBreak: fd.finalBreak };
        cursor = at + rep.length;
        continue;
      }
      let found: { tier: number; at: number[] } | null = null;
      const top = strict ? 0 : 2;
      for (let t = 0; t <= top; t++) {
        const at = occurrences(fd.lines, o, t).filter((p) => p >= cursor && (!ch.eof || p + o.length === fd.lines.length));
        if (at.length > 0) {
          found = { tier: t, at };
          break;
        }
      }
      if (!found) throw new Fail('no-match', sec.path);
      const pos = found.at[0]!;
      const rep = buildNew(ch.items, fd.lines, pos, found.tier);
      const lines = [...fd.lines.slice(0, pos), ...rep, ...fd.lines.slice(pos + o.length)];
      fd = { lines, br: fd.br, finalBreak: fd.finalBreak };
      cursor = pos + rep.length;
    }
    if (sec.moveTo !== null) {
      tree.now.set(sec.moveTo, serializeFile(fd));
      tree.now.set(sec.path, null);
      return { move: [sec.path, sec.moveTo] };
    }
    tree.now.set(sec.path, serializeFile(fd));
  };
}

/** Parse a V4A patch into one edit per section (SPEC section 8). */
function parseV4a(lines: string[], strict: boolean): Edit[] {
  const n = lines.length;
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = n - 1; k >= 0; k--) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${n + 1}`);
  const edits: Edit[] = [];
  const isSectionStart = (l: string): boolean =>
    l.startsWith('*** Add File:') || l.startsWith('*** Delete File:') || l.startsWith('*** Update File:');
  let i = first + 1;
  while (i < last) {
    const l = lines[i]!;
    if (blank(l)) {
      i++;
      continue;
    }
    if (!isSectionStart(l)) throw new Exit2(`error: parse ${i + 1}`);
    const startLine = i + 1;
    let j = i + 1;
    while (j < last && !isSectionStart(lines[j]!)) j++;
    const raw = lines.slice(i + 1, j);
    while (raw.length > 0 && blank(raw[raw.length - 1]!)) raw.pop();
    if (l.startsWith('*** Add File:')) {
      const path = l.slice('*** Add File:'.length).trim();
      const made: string[] = [];
      for (let k = 0; k < raw.length; k++) {
        const r = raw[k]!;
        if (r === '') made.push('');
        else if (r[0] === '+') made.push(r.slice(1));
        else throw new Exit2(`error: parse ${i + 2 + k}`);
      }
      edits.push(vSectionEdit({ kind: 'add', path, made }, strict));
    } else if (l.startsWith('*** Delete File:')) {
      const path = l.slice('*** Delete File:'.length).trim();
      for (let k = 0; k < raw.length; k++) {
        if (!blank(raw[k]!)) throw new Exit2(`error: parse ${i + 2 + k}`);
      }
      edits.push(vSectionEdit({ kind: 'delete', path }, strict));
    } else {
      const path = l.slice('*** Update File:'.length).trim();
      let moveTo: string | null = null;
      let k = 0;
      while (k < raw.length && blank(raw[k]!)) k++;
      if (k < raw.length && raw[k]!.startsWith('*** Move to:')) {
        moveTo = raw[k]!.slice('*** Move to:'.length).trim();
        k++;
      }
      const chunks: VChunk[] = [];
      while (k < raw.length) {
        // A blank line right before an @@ header is a separator, not a body
        // line; anywhere else a blank line starts the chunk as an empty
        // context line.
        if (blank(raw[k]!)) {
          let m = k;
          while (m < raw.length && blank(raw[m]!)) m++;
          if (m < raw.length && raw[m]!.startsWith('@@')) {
            k = m;
          }
        }
        if (k >= raw.length) break;
        let anchor: string | null = null;
        if (raw[k]!.startsWith('@@')) {
          anchor = raw[k]!.slice(2).trim();
          k++;
        }
        const body: string[] = [];
        let eof = false;
        while (k < raw.length) {
          const b = raw[k]!;
          if (b.startsWith('@@')) break;
          if (b.trim() === '*** End of File') {
            eof = true;
            k++;
            break;
          }
          if (b === '' || b[0] === ' ' || b[0] === '-' || b[0] === '+') {
            body.push(b);
            k++;
            continue;
          }
          throw new Exit2(`error: parse ${i + 2 + k}`);
        }
        const items: Item[] = [];
        for (const b of body) {
          if (b === '') items.push({ kind: 'ctx', text: '' });
          else if (b[0] === ' ') items.push({ kind: 'ctx', text: b.slice(1) });
          else if (b[0] === '-') items.push({ kind: 'old', text: b.slice(1) });
          else if (b[0] === '+') items.push({ kind: 'new', text: b.slice(1) });
        }
        chunks.push({ anchor, eof, items });
      }
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${startLine}`);
      edits.push(vSectionEdit({ kind: 'update', path, moveTo, chunks, updateLine: startLine }, strict));
    }
    i = j;
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

/** The CLI itself (SPEC sections 1, 2 and 10). */
function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else edits = parseV4a(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  const moves: [string, string][] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      const r = edit(tree);
      if (r && r.move) moves.push(r.move);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) {
    return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  }
  const rows: { key: string; line: string }[] = [];
  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  for (const [oldP, newP] of moves) {
    const dIdx = rows.findIndex((r) => r.line === `D ${oldP}`);
    const aIdx = rows.findIndex((r) => r.line === `A ${newP}`);
    if (dIdx >= 0 && aIdx >= 0) {
      rows.splice(Math.max(dIdx, aIdx), 1);
      rows.splice(Math.min(dIdx, aIdx), 1);
      rows.push({ key: newP, line: `R ${oldP} -> ${newP}` });
    }
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const out = [...rows.map((r) => r.line), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`];
  if (!check) {
    for (const p of [...tree.now.keys()]) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
