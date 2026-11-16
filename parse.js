// parse.js — a fast, dependency-free drop-in for marked 18.1.3 (default options, GFM on).
//
// Written from scratch from the CommonMark 0.31.2 and GFM 0.29 specs and from marked's
// observable output on probe inputs. parse(markdown) returns exactly the HTML marked
// 18.1.3 renders for the same input with its default options.
//
// Architecture: streaming index scanner over the source string. Blocks are recognised
// line by line (lines are [start, end) index ranges, never split copies) and emit HTML
// chunks straight into one output array. Inline content is scanned with a cursor and
// charCodeAt dispatch; delimiter runs go through a small stack (CommonMark flanking
// rules) and links/images are resolved lazily when ']' is reached.

export function parse(markdown) {
  SRC = markdown.replace(/\r\n?/g, '\n');
  const n = SRC.length;
  if (n === 0) return '';
  LINES.length = 0;
  let s = 0;
  while (s < n) {
    let e = SRC.indexOf('\n', s);
    const nl = e >= 0;
    if (!nl) e = n;
    LINES.push({ s, e, pad: 0, col: 0, nl });
    s = e + 1;
  }
  REFS = new Map();
  LINK_SEQ = 0;
  OUT.length = 0;
  parseBlocksInto(LINES, OUT, false, false, false);
  const html = OUT.join('');
  REFS = null;
  return html;
}

// ---------------------------------------------------------------- per-call state
let SRC = '';
const LINES = []; // [{s, e, pad}] line views into SRC
let REFS = null; // Map<normalised label, {href, title}>
const OUT = []; // string chunks
let LINK_SEQ = 0; // increments per formed link/image, for delimiter scoping

// ---------------------------------------------------------------- character helpers
const CC_SPACE = 32, CC_TAB = 9, CC_LT = 60, CC_GT = 62, CC_AMP = 38, CC_HASH = 35,
  CC_BQUOTE = 96, CC_TILDE = 126, CC_STAR = 42, CC_UNDER = 95, CC_LBRACKET = 91,
  CC_RBRACKET = 93, CC_BSLASH = 92, CC_EXCLAM = 33, CC_LT2 = 60;

function isSpace(c) { return c === 32 || c === 9; }
function isDigit(c) { return c >= 48 && c <= 57; }
function isAlpha(c) { return (c >= 65 && c <= 90) || (c >= 97 && c <= 122); }
function isAlnum(c) { return isAlpha(c) || isDigit(c); }
// ASCII punctuation (CommonMark): !"#$%&'()*+,-./:;<=>?@[\]^_`{|}~
function isAsciiPunct(c) {
  return (c >= 33 && c <= 47) || (c >= 58 && c <= 64) ||
    (c >= 91 && c <= 96) || (c >= 123 && c <= 126);
}
// Unicode whitespace (CommonMark): space, tab, LF, VT, FF, CR, NBSP, Ogham, en/em spaces,
// line/paragraph separators, narrow NBSP, medium math space, ideographic space, BOM.
function isUnicodeSpace(c) {
  return c === 32 || c === 9 || c === 10 || c === 11 || c === 12 || c === 13 ||
    c === 0xA0 || c === 0x1680 || (c >= 0x2000 && c <= 0x200A) ||
    c === 0x2028 || c === 0x2029 || c === 0x202F || c === 0x205F ||
    c === 0x3000 || c === 0xFEFF;
}
// Unicode punctuation: ASCII punctuation or general categories P / S. ASCII is the
// fast path; non-ASCII consults a small cache filled by a property-escape test.
const PUNCT_CACHE = new Map();
const PUNCT_RE = /[\p{P}\p{S}]/u;
function isUnicodePunct(c) {
  if (c < 128) return isAsciiPunct(c);
  let v = PUNCT_CACHE.get(c);
  if (v === undefined) {
    v = PUNCT_RE.test(String.fromCharCode(c));
    PUNCT_CACHE.set(c, v);
  }
  return v;
}

// A line is blank when it holds only spaces/tabs (plus any virtual pad spaces).
function isBlankLine(ln) {
  let i = ln.s;
  while (i < ln.e) {
    const c = SRC.charCodeAt(i);
    if (c !== 32 && c !== 9) return false;
    i++;
  }
  return true;
}

// A line view is {s, e, pad, col}: s/e bound the source text, pad counts virtual
// spaces before it (the remainder of a tab cut by an indent removal — the tab itself
// is not in the view), and col is the absolute column of SRC[s]. The view's start
// column, for indent measurement, is col - pad. Tabs expand to the next multiple of
// 4 in absolute columns, so nested views stay correct.
function lineStartCol(ln) { return ln.col - (ln.pad || 0); }

// First non-space char of a line view. Returns {off, col} with col the absolute
// column; the line's indent is col - lineStartCol(ln).
function firstNonSpace(ln) {
  let col = ln.col, off = ln.s;
  while (off < ln.e) {
    const c = SRC.charCodeAt(off);
    if (c === 32) { col++; off++; }
    else if (c === 9) { col += 4 - (col & 3); off++; }
    else break;
  }
  return { off, col };
}

// Remove n columns from the start of a line view (indent removal for list items /
// blockquotes). Returns a new view {s, e, pad, col}. A tab cut by the removal leaves
// its remainder as virtual pad spaces, with s moved past the tab.
function removeIndent(ln, n) {
  const startCol = lineStartCol(ln);
  const target = startCol + n;
  const p = ln.pad || 0;
  if (target <= startCol) return { s: ln.s, e: ln.e, pad: p, col: ln.col, nl: ln.nl, lazy: ln.lazy, notBlank: ln.notBlank };
  if (target - startCol <= p) {
    return { s: ln.s, e: ln.e, pad: p - (target - startCol), col: ln.col, nl: ln.nl, lazy: ln.lazy, notBlank: ln.notBlank };
  }
  let col = ln.col, off = ln.s;
  while (off < ln.e && col < target) {
    const c = SRC.charCodeAt(off);
    if (c === 32) { col++; off++; }
    else if (c === 9) {
      const nc = col + 4 - (col & 3);
      if (nc > target) return { s: off + 1, e: ln.e, pad: nc - target, col: nc, nl: ln.nl, lazy: ln.lazy, notBlank: ln.notBlank };
      col = nc; off++;
    } else break;
  }
  return { s: off, e: ln.e, pad: 0, col, nl: ln.nl, lazy: ln.lazy, notBlank: ln.notBlank };
}

// Fenced-code dedent: like removeIndent, except a tab straddling the target
// column is dropped entirely (marked emits no spaces for it), while indented
// code keeps the tab remainder as pad.
function removeIndentFenced(ln, n) {
  const startCol = lineStartCol(ln);
  const target = startCol + n;
  const p = ln.pad || 0;
  if (target <= startCol) return { s: ln.s, e: ln.e, pad: p, col: ln.col, nl: ln.nl, lazy: ln.lazy, notBlank: ln.notBlank };
  if (target - startCol <= p) {
    return { s: ln.s, e: ln.e, pad: p - (target - startCol), col: ln.col, nl: ln.nl, lazy: ln.lazy, notBlank: ln.notBlank };
  }
  let col = ln.col, off = ln.s;
  while (off < ln.e && col < target) {
    const c = SRC.charCodeAt(off);
    if (c === 32) { col++; off++; }
    else if (c === 9) {
      const nc = col + 4 - (col & 3);
      if (nc > target) return { s: off + 1, e: ln.e, pad: 0, col: nc, nl: ln.nl, lazy: ln.lazy, notBlank: ln.notBlank };
      col = nc; off++;
    } else break;
  }
  // a tab exactly at the dedent target is the first content char: expand it
  // to spaces (to the next multiple of 4) only when it sits on a tab stop
  // (absolute column multiple of 4); otherwise the tab stays literal
  if (off < ln.e && SRC.charCodeAt(off) === 9 && (col & 3) === 0) {
    const nc = col + 4 - (col & 3);
    return { s: off + 1, e: ln.e, pad: nc - col, col: nc, nl: ln.nl, lazy: ln.lazy, notBlank: ln.notBlank };
  }
  return { s: off, e: ln.e, pad: 0, col, nl: ln.nl, lazy: ln.lazy, notBlank: ln.notBlank };
}

// Cut a line view to start at absolute column `target`, consuming whatever
// characters lie before it (leading spaces, a list marker, the whitespace after
// it). Unlike removeIndent, this does not stop at non-whitespace: the marker
// itself must be consumed to reach the item's content column. A tab straddling
// `target` leaves its remainder as pad.
function cutToCol(ln, target) {
  const startCol = lineStartCol(ln);
  if (target <= startCol) return { s: ln.s, e: ln.e, pad: ln.pad || 0, col: ln.col, nl: ln.nl, lazy: ln.lazy, notBlank: ln.notBlank };
  const p = ln.pad || 0;
  if (target - startCol <= p) {
    return { s: ln.s, e: ln.e, pad: p - (target - startCol), col: ln.col, nl: ln.nl, lazy: ln.lazy, notBlank: ln.notBlank };
  }
  let col = ln.col, off = ln.s;
  while (off < ln.e && col < target) {
    const c = SRC.charCodeAt(off);
    if (c === 32) { col++; off++; }
    else if (c === 9) {
      const nc = col + 4 - (col & 3);
      if (nc > target) return { s: off + 1, e: ln.e, pad: nc - target, col: nc, nl: ln.nl, lazy: ln.lazy, notBlank: ln.notBlank };
      col = nc; off++;
    } else { col++; off++; }
  }
  if (off < ln.e && SRC.charCodeAt(off) === 9) {
    const nc = col + 4 - (col & 3);
    return { s: off + 1, e: ln.e, pad: nc - col, col: nc, nl: ln.nl, lazy: ln.lazy, notBlank: ln.notBlank };
  }
  return { s: off, e: ln.e, pad: 0, col, nl: ln.nl, lazy: ln.lazy, notBlank: ln.notBlank };
}

// ---------------------------------------------------------------- escaping
// Escape &, <, >, ", ' in SRC[a..b) — the text escaper used for plain text runs.
// '&' is left alone when it starts a valid entity reference (&name; / &#123; / &#x1a;),
// because the inline scanner emits those through the entity path; this escaper only
// runs on plain runs that contain no entity start, so a plain '&' here is literal.
function escRange(str, a, b, out) {
  let i = a, j;
  while (i < b) {
    const c = str.charCodeAt(i);
    if (c === 38) { // &
      out.push('&amp;'); i++;
    } else if (c === 60) { out.push('&lt;'); i++; }
    else if (c === 62) { out.push('&gt;'); i++; }
    else if (c === 34) { out.push('&quot;'); i++; }
    else if (c === 39) { out.push('&#39;'); i++; }
    else {
      j = i + 1;
      while (j < b) {
        const d = str.charCodeAt(j);
        if (d === 38 || d === 60 || d === 62 || d === 34 || d === 39) break;
        j++;
      }
      out.push(str.slice(i, j));
      i = j;
    }
  }
}

// Decode a numeric character reference body ('#65' / '#x41' / '#X41') to a character,
// or U+FFFD for 0, surrogates and values above U+10FFFF (marked's observable output).
function decodeNumeric(body) {
  let n;
  if (body.charCodeAt(1) === 120 || body.charCodeAt(1) === 88) n = parseInt(body.slice(2), 16);
  else n = parseInt(body.slice(1), 10);
  if (!n || n > 0x10FFFF || (n >= 0xD800 && n <= 0xDFFF)) return '\uFFFD';
  return String.fromCodePoint(n);
}

// Is the '&' at str[i] the start of an entity reference (named or numeric, with ';')?
// Returns the index just past ';', or -1.
function entityEnd(str, i, end) {
  // str[i] === '&'
  let j = i + 1;
  if (j >= end) return -1;
  const c = str.charCodeAt(j);
  if (c === 35) { // # numeric: decimal 1-7 digits, hex 1-6 digits (CommonMark);
    // more digits than that is not an entity at all (&#87654321; stays literal)
    j++;
    let hex = false;
    if (j < end && (str.charCodeAt(j) === 120 || str.charCodeAt(j) === 88)) { hex = true; j++; }
    const ds = j;
    const maxDigits = hex ? 6 : 7;
    while (j < end && j - ds < maxDigits) {
      const d = str.charCodeAt(j);
      const ok = hex
        ? (d >= 48 && d <= 57) || (d >= 65 && d <= 70) || (d >= 97 && d <= 102)
        : (d >= 48 && d <= 57);
      if (!ok) break;
      j++;
    }
    if (j === ds || j >= end || str.charCodeAt(j) !== 59) return -1;
    return j + 1;
  }
  if (!isAlpha(c)) return -1;
  while (j < end && isAlnum(str.charCodeAt(j))) j++;
  if (j >= end || str.charCodeAt(j) !== 59) return -1;
  return j + 1;
}

// Percent-encode a URL the way marked's cleanUrl does: control chars, DEL,
// non-ASCII (UTF-8), space and " < > ` { } | ^ [ ] are encoded; % and the rest pass
// through untouched (so b%20c stays b%20c, and a tab becomes %09).
function pctUtf8(cp) {
  if (cp < 0x80) return '%' + cp.toString(16).toUpperCase().padStart(2, '0');
  if (cp < 0x800) {
    return '%' + ((cp >> 6) | 0xC0).toString(16).toUpperCase()
      + '%' + ((cp & 0x3F) | 0x80).toString(16).toUpperCase();
  }
  if (cp < 0x10000) {
    return '%' + ((cp >> 12) | 0xE0).toString(16).toUpperCase()
      + '%' + (((cp >> 6) & 0x3F) | 0x80).toString(16).toUpperCase()
      + '%' + ((cp & 0x3F) | 0x80).toString(16).toUpperCase();
  }
  return '%' + ((cp >> 18) | 0xF0).toString(16).toUpperCase()
    + '%' + (((cp >> 12) & 0x3F) | 0x80).toString(16).toUpperCase()
    + '%' + (((cp >> 6) & 0x3F) | 0x80).toString(16).toUpperCase()
    + '%' + ((cp & 0x3F) | 0x80).toString(16).toUpperCase();
}
function percentEncodeUrl(href) {
  let out = '';
  for (let i = 0; i < href.length; i++) {
    const c = href.charCodeAt(i);
    if (c === 32 || c === 34 || c === 60 || c === 62 || c === 96 || c === 92 ||
        c === 123 || c === 125 || c === 124 || c === 94 || c === 91 || c === 93 ||
        c < 32 || c === 127) {
      out += '%' + c.toString(16).toUpperCase().padStart(2, '0');
    } else if (c < 128) {
      out += href[i];
    } else if (c >= 0xD800 && c <= 0xDBFF && i + 1 < href.length &&
               href.charCodeAt(i + 1) >= 0xDC00 && href.charCodeAt(i + 1) <= 0xDFFF) {
      out += pctUtf8(0x10000 + ((c - 0xD800) << 10) + (href.charCodeAt(i + 1) - 0xDC00));
      i++;
    } else if (c >= 0xD800 && c <= 0xDFFF) {
      out += '%EF%BF%BD'; // lone surrogate -> U+FFFD
    } else {
      out += pctUtf8(c);
    }
  }
  return out;
}

// Attribute-escape that keeps valid entity references intact (&copy; / &#65; stay
// as-is); used for link titles, explicit-link hrefs (after percent-encoding) and
// fenced-code languages.
function escAttrEnt(s) {
  let out = '';
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === 38) {
      const e = entityEnd(s, i, s.length);
      if (e > 0) { out += s.slice(i, e); i = e - 1; }
      else out += '&amp;';
    } else if (c === 60) out += '&lt;';
    else if (c === 62) out += '&gt;';
    else if (c === 34) out += '&quot;';
    else if (c === 39) out += '&#39;';
    else out += s[i];
  }
  return out;
}

// Clean a link destination the way marked does: percent-encode, then entity-aware
// attribute-escape. Observed: '<b c>' -> 'b%20c', unicode -> %XX, '&copy;' and
// '&#38;' kept, lone '&' -> '&amp;', "'" -> '&#39;'.
function cleanUrl(href) {
  return escAttrEnt(percentEncodeUrl(href));
}

// Autolink href: percent-encode, then escape every '&' (no entity preservation).
function autolinkHref(href) {
  const enc = percentEncodeUrl(href);
  const out = [];
  escRange(enc, 0, enc.length, out);
  return out.join('');
}

// ---------------------------------------------------------------- inline parsing
const SPECIAL_RE = /[`*_![\\<&~\]\n]/g;

// Delimiter placeholder kinds
const OP_DELIM = 0, OP_LINK = 1, OP_AUTOLINK = 2;

// Inline-scan a string range, appending HTML chunks to `out`.
function inlineTo(str, a, b, out) {
  const ops = [];    // strings and placeholder objects, in order
  const delims = []; // delimiter placeholders, in scan order
  const openers = []; // link/image opener placeholders, in scan order
  let i = a;
  while (i < b) {
    SPECIAL_RE.lastIndex = i;
    const m = SPECIAL_RE.exec(str);
    const j = (m !== null && m.index < b) ? m.index : b;
    if (j > i) { let inLink = false; for (let q = 0; q < openers.length; q++) if (openers[q].active) { inLink = true; break; } i = emitPlain(str, i, j, b, ops, delims, inLink); continue; }
    // special char at i
    const c = str.charCodeAt(i);
    if (c === 96) { // ` code span
      // a code span inside a link's text may not extend past the link's ']'
      let lim = b;
      for (let q = openers.length - 1; q >= 0; q--) {
        if (openers[q].active) {
          const lc = findLinkClose(str, openers[q].textStart, b);
          if (lc > 0) lim = lc;
          break;
        }
      }
      i = scanCodeSpan(str, i, lim, ops);
    } else if (c === 42 || c === 95 || c === 126) { // * _ ~
      i = scanDelim(str, i, b, a, ops, delims);
    } else if (c === 91) { // [
      const ph = { t: OP_LINK, img: false, open: null, altFrom: -1, altTo: -1, href: '', title: '' };
      ops.push(ph);
      openers.push({ ph, textStart: i + 1, active: true, phOpIdx: ops.length - 1 });
      i++;
    } else if (c === 33) { // !
      if (i + 1 < b && str.charCodeAt(i + 1) === 91) {
        const ph = { t: OP_LINK, img: true, open: null, altFrom: -1, altTo: -1, href: '', title: '' };
        ops.push(ph);
        openers.push({ ph, textStart: i + 2, active: true, phOpIdx: ops.length - 1 });
        i += 2;
      } else { ops.push('!'); i++; }
    } else if (c === 93) { // ]
      i = scanCloseBracket(str, i, b, ops, openers, delims);
    } else if (c === 92) { // backslash
      if (i + 1 < b) {
        const d = str.charCodeAt(i + 1);
        if (isAsciiPunct(d)) { const tmp = []; escRange(str, i + 1, i + 2, tmp); ops.push(tmp.join('')); i += 2; }
        else if (d === 10) {
          ops.push('<br>'); i += 2;
          while (i < b && (str.charCodeAt(i) === 32 || str.charCodeAt(i) === 9)) i++;
        }
        else { ops.push('\\'); i++; }
      } else { ops.push('\\'); i++; }
    } else if (c === 60) { // < raw HTML / autolink
      i = scanLt(str, i, b, ops);
    } else if (c === 38) { // & entity
      const e = entityEnd(str, i, b);
      if (e > 0) {
        if (str.charCodeAt(i + 1) === 35) {
          const ch = decodeNumeric(str.slice(i + 1, e - 1));
          { const tmp = []; escRange(ch, 0, ch.length, tmp); ops.push(tmp.join('')); }
        } else ops.push(str.slice(i, e));
        i = e;
      } else { ops.push('&amp;'); i++; }
    } else if (c === 10) { // newline: soft or hard break
      // 2+ trailing spaces -> hard break '<br>' (spaces consumed, no '\n');
      // fewer -> soft break (spaces kept, '\n' emitted)
      const last = ops[ops.length - 1];
      if (typeof last === 'string') {
        let k = last.length;
        while (k > 0 && last.charCodeAt(k - 1) === 32) k--;
        if (last.length - k >= 2) {
          ops[ops.length - 1] = last.slice(0, k);
          ops.push('<br>');
          i++;
          while (i < b && (str.charCodeAt(i) === 32 || str.charCodeAt(i) === 9)) i++;
          continue;
        } else ops.push('\n');
      } else ops.push('\n');
      i++;
    } else { ops.push(str[i]); i++; } // ~ single, etc.
  }
  processEmphasis(delims);
  renderOps(ops, out);
}

// Plain run [i, j): escape it, but first look for GFM extended autolinks inside it.
// An autolink may extend past j (up to b); returns the position to continue from.
function emitPlain(str, i, j, b, ops, delims, inLink) {
  let pos = i;
  for (;;) {
    // next autolink candidate inside [pos, j)
    let k = -1, kind = 0;
    const kw = str.indexOf('www.', pos);
    if (kw >= 0 && kw < j) { k = kw; kind = 1; }
    const ks = str.indexOf('://', pos);
    if (ks >= 0 && ks < j && (k < 0 || ks < k)) { k = ks; kind = 2; }
    const ka = str.indexOf('@', pos);
    if (ka >= 0 && ka < j && (k < 0 || ka < k)) { k = ka; kind = 3; }
    if (k < 0) break;
    let r = null;
    if (kind === 1) r = matchWww(str, k, b, inLink);
    else if (kind === 2) r = matchScheme(str, k, b, inLink);
    else r = matchEmail(str, k, b, delims);
    if (r === null) { escRange(str, pos, k + 1, ops); pos = k + 1; continue; }
    // a scheme prefix (xmpp:, etc.) before the email makes the whole thing a
    // scheme link, not a mailto: link (the URL may carry a path past the domain)
    if (kind === 3) {
      const sp = schemePrefixStart(str, r.start);
      if (sp >= 0) {
        // a scheme+email link carries at most one path segment past the domain
        let e = r.end;
        if (e < b && str.charCodeAt(e) === 47) {
          e++;
          while (e < b) {
            const c = str.charCodeAt(e);
            if (c === 32 || c === 9 || c === 10 || c === 60 || c < 32 || c === 47 || (inLink && (c === 91 || c === 93))) break;
            e++;
          }
        }
        r = { start: sp, end: trimAutolinkEnd(str, sp, e), scheme: true };
      }
    }
    const start = r.start, end = r.end;
    // preceding char must be start / whitespace / punctuation
    if (start > 0) {
      const pc = str.charCodeAt(start - 1);
      if (!isUnicodeSpace(pc) && !isUnicodePunct(pc)) { escRange(str, pos, k + 1, ops); pos = k + 1; continue; }
    }
    let href;
    if (kind === 1) href = 'http://' + str.slice(start, end);
    else if (kind === 2 || r.scheme) href = str.slice(start, end);
    else href = str.slice(start, start + 7) === 'mailto:' ? str.slice(start, end) : 'mailto:' + str.slice(start, end);
    // An email's local part may reach back across '_' delimiters into text already
    // emitted as plain runs (e.g. a.b-c_d@a.b): rewind those ops into the link. The
    // rewound region holds only local-part chars, which escRange never escapes, so
    // string lengths there equal source lengths and truncating by chars is exact.
    if (start < pos) {
      let need = pos - start;
      while (need > 0 && ops.length > 0) {
        const op = ops[ops.length - 1];
        if (typeof op === 'string') {
          if (need >= op.length) { ops.pop(); need -= op.length; }
          else { ops[ops.length - 1] = op.slice(0, op.length - need); need = 0; }
        } else if (op.t === OP_DELIM && op.ch === 95) {
          ops.pop();
          const di = delims.indexOf(op);
          if (di >= 0) delims.splice(di, 1);
          need -= op.len;
        } else break;
      }
    } else if (pos < start) escRange(str, pos, start, ops);
    ops.push({ t: OP_AUTOLINK, html: '<a href="' + autolinkHref(href) + '">' + escTextOf(str.slice(start, end)) + '</a>', text: escTextOf(str.slice(start, end)) });
    pos = end;
    if (pos >= j) return pos;
  }
  if (pos < j) escRange(str, pos, j, ops);
  return j;
}

// Escape a plain string (used for autolink display text).
function escTextOf(s) {
  const out = [];
  escRange(s, 0, s.length, out);
  return out.join('');
}

// Code span starting at str[i] === '`'. Returns position after it.
// Find the ']' matching a link opener whose text starts at `from` (bracket
// depth counting, skipping escapes and code spans). Returns the index of the
// matching ']' or -1.
function findLinkClose(str, from, b) {
  let depth = 1, j = from;
  while (j < b) {
    const c = str.charCodeAt(j);
    if (c === 92 && j + 1 < b) { j += 2; continue; }
    if (c === 96) {
      let L = 0;
      while (j + L < b && str.charCodeAt(j + L) === 96) L++;
      let q = j + L, found = -1, closeStart = -1;
      for (;;) {
        q = str.indexOf('`', q);
        if (q < 0 || q >= b) break;
        let r = 0;
        while (q + r < b && str.charCodeAt(q + r) === 96) r++;
        if (r === L) { found = q + r; closeStart = q; break; }
        q += r;
      }
      // only skip a code span whose content has no backtick at all: a
      // backtick inside the span breaks marked's bracket matching, so the
      // ']' inside it is treated as the link's closing bracket
      if (found > 0 && str.indexOf('`', j + L) >= closeStart) { j = found; continue; }
      j += L; continue;
    }
    if (c === 91) depth++;
    else if (c === 93) {
      depth--;
      if (depth === 0) return j;
    }
    j++;
  }
  return -1;
}

function scanCodeSpan(str, i, b, ops) {
  let L = 0;
  while (i + L < b && str.charCodeAt(i + L) === 96) L++;
  let p = i + L;
  for (;;) {
    p = str.indexOf('`', p);
    if (p < 0 || p >= b) { ops.push(str.slice(i, i + L)); return i + L; }
    let r = 0;
    while (p + r < b && str.charCodeAt(p + r) === 96) r++;
    if (r === L) {
      let content = str.slice(i + L, p);
      if (content.indexOf('\n') >= 0) content = content.replace(/\n/g, ' ');
      if (content.length >= 2 && content.charCodeAt(0) === 32 && content.charCodeAt(content.length - 1) === 32 && /\S/.test(content)) {
        content = content.slice(1, -1);
      }
      ops.push('<code>');
      const tmp = [];
      escRange(content, 0, content.length, tmp);
      ops.push(tmp.join(''));
      ops.push('</code>');
      return p + r;
    }
    p += r;
  }
}

// Delimiter run (*, _, ~) starting at str[i]. Returns position after the run.
function scanDelim(str, i, b, a, ops, delims) {
  const ch = str.charCodeAt(i);
  let L = 0;
  while (i + L < b && str.charCodeAt(i + L) === ch) L++;
  // (a single '~' is a real delimiter: ~x~ forms <del>x</del>)
  const before = i > a ? str.charCodeAt(i - 1) : 32;
  const after = i + L < b ? str.charCodeAt(i + L) : 32;
  const beforeWS = isUnicodeSpace(before), afterWS = isUnicodeSpace(after);
  const beforePunct = isUnicodePunct(before), afterPunct = isUnicodePunct(after);
  const leftFlanking = !afterWS && (!afterPunct || beforeWS || beforePunct);
  const rightFlanking = !beforeWS && (!beforePunct || afterWS || afterPunct);
  let canOpen, canClose;
  if (ch === 95) {
    canOpen = leftFlanking && (!rightFlanking || beforePunct);
    canClose = rightFlanking && (!leftFlanking || afterPunct);
  } else {
    canOpen = leftFlanking;
    canClose = rightFlanking;
  }
  const ph = {
    t: OP_DELIM, ch, len: L, olen: L, canOpen, canClose, active: true,
    open: [], close: [], pos: i, blocked: false, linkId: 0,
  };
  ops.push(ph);
  delims.push(ph);
  return i + L;
}

// CommonMark emphasis resolution over the delimiter placeholders.
function processEmphasis(delims) {
  let i = 0;
  while (i < delims.length) {
    const closer = delims[i];
    if (!closer.active || !closer.canClose || closer.len === 0) { i++; continue; }
    if (closer.ch === 126 && closer.len >= 3) { i++; continue; } // ~~~ never strikes
    // look back for an opener
    let j = i - 1, found = false, blockedEm = false;
    while (j >= 0) {
      const opener = delims[j];
      // a delimiter flagged by a strong open-only/both pair blocks an <em>
      // (use 1) pairing across it for this closer only (one shot: clear the
      // flag so a later closer can pass); a <strong> (use 2) pairing may pass
      if (opener.blocksLookback && opener.ch === closer.ch) { opener.blocksLookback = false; blockedEm = true; j--; continue; }
      // a delimiter inside a formed pair, or inside a different link, cannot
      // pair with this closer (it would cross an emphasis / link boundary)
      if (opener.blocked || opener.linkId !== closer.linkId) { j--; continue; }
      if (opener.active && opener.ch === closer.ch && opener.canOpen && opener.len > 0) {
        if (closer.ch === 126 && opener.len >= 3) { j--; continue; } // ~~~ never strikes
        // odd rule (rule of 3): skip this opener when the opener can close
        // or the closer can open and the lengths sum to a multiple of 3
        // (unless both lengths are multiples of 3).
        if (opener.canClose || closer.canOpen) {
          const sum = opener.len + closer.len;
          if (sum % 3 === 0 && (opener.len % 3 !== 0 || closer.len % 3 !== 0)) { j--; continue; }
        }
        const use = (opener.len >= 2 && closer.len >= 2) ? 2 : 1;
        if (blockedEm && use === 1) { j--; continue; }
        const tag = closer.ch === 126 ? 'del' : use === 2 ? 'strong' : 'em';
        // a strong pair whose opener is open-only and whose closer can both
        // open and close blocks the NEXT closer's lookback past it (one shot):
        // marked leaves the outer delimiter literal in "*a **b**c*"
        if (use === 2 && opener.canOpen && !opener.canClose && closer.canOpen && closer.canClose) {
          closer.blocksLookback = true;
        }
        opener.open.push('<' + tag + '>');
        closer.close.push('</' + tag + '>');
        opener.len -= use;
        closer.len -= use;
        if (opener.len === 0) opener.active = false;
        if (closer.len === 0) {
          closer.active = false; found = true;
          // delimiters between the pair are now inside a formed emphasis
          for (let m = j + 1; m < i; m++) delims[m].blocked = true;
          break;
        }
        // closer still has length: reuse this opener while it has length left
        // (a run of 3+ yields both <strong> and <em>), else look further back
        if (opener.len > 0) continue;
        j--;
        continue;
      }
      j--;
    }
    if (!found && closer.len > 0) {
      // no opener (or closer still unmatched after exhausting openers): move on
    }
    i++;
  }
}

// Render the ops array into `out`, resolving placeholders.
function renderOps(ops, out) {
  // op indices that are alt text of an image: rendered only inside alt=""
  let skipAlt = null;
  for (let k = 0; k < ops.length; k++) {
    const op = ops[k];
    if (typeof op !== 'string' && op.t === OP_LINK && op.img && op.open !== null) {
      if (!skipAlt) skipAlt = new Set();
      for (let x = op.altFrom; x < op.altTo; x++) skipAlt.add(x);
    }
  }
  for (let k = 0; k < ops.length; k++) {
    if (skipAlt && skipAlt.has(k)) continue;
    const op = ops[k];
    if (typeof op === 'string') { out.push(op); continue; }
    if (op.t === OP_AUTOLINK) { out.push(op.html); continue; }
    if (op.t === OP_DELIM) {
      const ch = String.fromCharCode(op.ch);
      for (const t of op.close) out.push(t);
      if (op.len > 0) out.push(ch.repeat(op.len));
      for (let x = op.open.length - 1; x >= 0; x--) out.push(op.open[x]);
    } else {
      // link / image placeholder
      if (op.open !== null) {
        if (op.img) {
          out.push('<img src="' + op.href + '" alt="' + altOf(ops, op.altFrom, op.altTo) + '"' + (op.title ? ' title="' + op.title + '"' : '') + '>');
        } else {
          out.push(op.open);
        }
      } else {
        out.push(op.img ? '![' : '[');
      }
    }
  }
  // link closers were pushed as '</a>' strings already; nothing more to do
}

// Plain-text rendering of ops[from..to) for alt text / labels: strings verbatim,
// delimiters as their literal chars, links as their own plain text.
// Plain-text rendering of a link label (for alt=""): a formed link contributes
// its content text, a formed image contributes its alt text, an unformed bracket
// is literal, and a delimiter contributes only the characters left over after
// emphasis processing (a fully used delimiter contributes nothing).
function altOf(ops, from, to) {
  if (from < 0) return '';
  const parts = [];
  let k = from;
  while (k < to && k < ops.length) {
    const op = ops[k];
    if (typeof op === 'string') {
      if (op !== '</a>') parts.push(op);
      k++;
    } else if (op.t === OP_AUTOLINK) {
      parts.push(op.text);
      k++;
    } else if (op.t === OP_DELIM) {
      if (op.len > 0) parts.push(String.fromCharCode(op.ch).repeat(op.len));
      k++;
    } else if (op.open === null) {
      parts.push(op.img ? '![' : '[');
      k++;
    } else if (op.img) {
      parts.push(altOf(ops, op.altFrom, op.altTo));
      k = Math.max(k + 1, op.altTo); // skip its content ops (already in the alt)
    } else {
      k++; // a formed link: its content ops follow in the range
    }
  }
  return escAttrText(parts.join(''));
}

function escAttrText(s) {
  const out = [];
  escRange(s, 0, s.length, out);
  return out.join('');
}

// ---------------------------------------------------------------- links
// Skip inline whitespace (spaces, tabs, newlines) without crossing a blank line.
// Returns the new position, or -1 if a blank line is crossed or the end is reached.
function skipInlineWS(str, i, b) {
  let nl = false;
  while (i < b) {
    const c = str.charCodeAt(i);
    if (c === 32 || c === 9) i++;
    else if (c === 10) {
      if (nl) return -1;
      nl = true; i++;
    } else break;
  }
  return i < b ? i : -1;
}

// Parse a link destination starting at str[i] (after '(' or after ']:').
// Returns {dest, end} or null. `end` is the index just past the destination.
function parseDest(str, i, b) {
  if (i >= b) return null;
  if (str.charCodeAt(i) === 60) { // <...>
    let j = i + 1, dest = '';
    while (j < b) {
      const c = str.charCodeAt(j);
      if (c === 62) return { dest, end: j + 1 };
      if (c === 60 || c === 10) return null;
      if (c === 92 && j + 1 < b && isAsciiPunct(str.charCodeAt(j + 1))) { dest += str[j + 1]; j += 2; }
      else { dest += str[j]; j++; }
    }
    return null;
  }
  let j = i, depth = 0, dest = '';
  while (j < b) {
    const c = str.charCodeAt(j);
    if (c === 32 || c === 9 || c === 10 || c < 32) break;
    if (c === 92 && j + 1 < b && isAsciiPunct(str.charCodeAt(j + 1))) { dest += str[j + 1]; j += 2; continue; }
    if (c === 40) { depth++; dest += '('; j++; continue; }
    if (c === 41) {
      if (depth === 0) break;
      depth--; dest += ')'; j++; continue;
    }
    dest += str[j]; j++;
  }
  if (j === i) return null;
  return { dest, end: j };
}

// Parse a link title starting at str[i] ('"' or '\'' or '('). Returns {title, end} or null.
function parseTitle(str, i, b) {
  const q = str.charCodeAt(i);
  if (q !== 34 && q !== 39 && q !== 40) return null;
  let j = i + 1, title = '';
  if (q === 40) {
    let depth = 1;
    while (j < b) {
      const c = str.charCodeAt(j);
      if (c === 92 && j + 1 < b && isAsciiPunct(str.charCodeAt(j + 1))) { title += str[j + 1]; j += 2; continue; }
      if (c === 40) { depth++; title += '('; j++; continue; }
      if (c === 41) {
        depth--;
        if (depth === 0) return { title, end: j + 1 };
        title += ')'; j++; continue;
      }
      if (c === 10 && j + 1 < b && str.charCodeAt(j + 1) === 10) return null;
      title += str[j]; j++;
    }
    return null;
  }
  while (j < b) {
    const c = str.charCodeAt(j);
    if (c === q) return { title, end: j + 1 };
    if (c === 10 && j + 1 < b && str.charCodeAt(j + 1) === 10) return null;
    if (c === 92 && j + 1 < b && isAsciiPunct(str.charCodeAt(j + 1))) { title += str[j + 1]; j += 2; continue; }
    title += str[j]; j++;
  }
  return null;
}

// Normalise a link label: trim, collapse internal whitespace to one space, case-fold.
// Labels match on their RAW text (backslash escapes kept: 'foo\!' != 'foo!');
// case folding is full Unicode folding, so sharp-s (U+00DF / U+1E9E) folds to 'ss'.
function normaliseLabel(s) {
  let out = '', ws = true;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (isUnicodeSpace(c)) { if (!ws) { out += ' '; ws = true; } }
    else if (c === 0x00DF || c === 0x1E9E) { out += 'ss'; ws = false; }
    else { out += s[i].toLowerCase(); ws = false; }
  }
  if (out.charCodeAt(out.length - 1) === 32) out = out.slice(0, -1);
  return out;
}

// Raw link-text label: backslash escapes resolved, entities left as-is.
function labelFromRaw(str, a, b) {
  let s = '';
  for (let i = a; i < b; i++) {
    const c = str.charCodeAt(i);
    if (c === 92 && i + 1 < b && isAsciiPunct(str.charCodeAt(i + 1))) { s += str[i + 1]; i++; }
    else s += str[i];
  }
  return normaliseLabel(s);
}

// True when the link text [from, to) contains a code span whose content itself
// contains a backtick: marked then does not form the link at all (the code
// span still renders, but the '[...](...)' stays literal).
function linkTextHasBacktickSpan(str, from, to) {
  let j = from;
  while (j < to) {
    if (str.charCodeAt(j) !== 96) { j++; continue; }
    let L = 0;
    while (j + L < to && str.charCodeAt(j + L) === 96) L++;
    let q = j + L, close = -1;
    for (;;) {
      q = str.indexOf('`', q);
      if (q < 0 || q >= to) break;
      let r = 0;
      while (q + r < to && str.charCodeAt(q + r) === 96) r++;
      if (r === L) { close = q; break; }
      q += r;
    }
    if (close > 0) {
      // a code span whose content is space-padded on both ends (one space
      // stripped each side) does not block the link; only an unpadded span
      // with a backtick inside does
      const content = str.slice(j + L, close);
      const padded = content.length >= 2 && content.charCodeAt(0) === 32 && content.charCodeAt(content.length - 1) === 32 && /\S/.test(content);
      if (!padded && str.indexOf('`', j + L) < close) return true;
      j = close + L;
    } else j += L;
  }
  return false;
}

// Try to form a link/image when ']' is hit at str[i]. Returns position after the
// link syntax, or i+1 with a literal ']' pushed when no link forms.
function scanCloseBracket(str, i, b, ops, openers, delims) {
  let oi = -1;
  for (let k = openers.length - 1; k >= 0; k--) {
    if (openers[k].active) { oi = k; break; }
  }
  if (oi < 0) { ops.push(']'); return i + 1; }
  const opener = openers[oi];
  // The nearest opener is popped by this ']' whether or not a link forms (so a
  // later ']' uses an outer opener, e.g. [[foo]](bar) -> <a href="bar">[foo]</a>).
  opener.active = false;
  const textStart = opener.textStart, textEnd = i;
  let href = null, title = '', end = -1;
  // inline link: ]( ... ) — the '(' must follow ']' immediately (no space)
  if (i + 1 < b && str.charCodeAt(i + 1) === 40) {
    let k = skipInlineWS(str, i + 2, b);
    if (k > 0 && str.charCodeAt(k) === 41) { href = ''; end = k + 1; } // empty ()
    else if (k > 0) {
      const d = parseDest(str, k, b);
      if (d) {
        k = skipInlineWS(str, d.end, b);
        if (k > 0 && str.charCodeAt(k) === 41) { href = d.dest; end = k + 1; }
        else if (k > 0) {
          const t = parseTitle(str, k, b);
          if (t) {
            k = skipInlineWS(str, t.end, b);
            if (k > 0 && str.charCodeAt(k) === 41) { href = d.dest; title = t.title; end = k + 1; }
          }
        }
      }
    }
  }
  // full reference link: ][label] — when ']' is followed by '[', ONLY the
  // full/collapsed reference is tried; a parsed label that is not defined does NOT
  // fall through to the shortcut (e.g. [foo][bar] with only [foo] defined stays
  // literal). An unparseable label does fall through to the shortcut.
  if (href === null && i + 1 < b && str.charCodeAt(i + 1) === 91) {
    const lbl = parseBracketLabel(str, i + 1, b);
    if (lbl) {
      const key = lbl.label === '' ? normaliseLabel(str.slice(textStart, textEnd)) : normaliseLabel(lbl.label);
      const ref = REFS.get(key);
      if (ref) { href = ref.href; title = ref.title; end = lbl.end; }
      else { ops.push(']'); return i + 1; }
    }
  }
  // shortcut reference link: ] alone
  if (href === null) {
    const key = normaliseLabel(str.slice(textStart, textEnd));
    const ref = key === '' ? undefined : REFS.get(key);
    if (ref) { href = ref.href; title = ref.title; end = i + 1; }
  }
  if (href === null) { ops.push(']'); return i + 1; }
  // a code span with a backtick inside the link text blocks an inline link
  // without a title entirely (reference links and titled inline links still
  // form)
  if (title === '' && i + 1 < b && str.charCodeAt(i + 1) === 40 && linkTextHasBacktickSpan(str, textStart, textEnd)) { ops.push(']'); return i + 1; }
  // a LINK's text must not itself contain a formed link; an IMAGE's alt text may
  // (the inner link renders as plain text inside alt="")
  if (!opener.ph.img) {
    for (let k = opener.phOpIdx + 1; k < ops.length; k++) {
      const op = ops[k];
      if (typeof op !== 'string' && op.t === OP_LINK && op.open !== null && !op.img) {
        ops.push(']'); return i + 1;
      }
    }
  }
  // autolinks inside a link's text stay plain text (never a nested <a>)
  if (!opener.ph.img) {
    for (let k = opener.phOpIdx + 1; k < ops.length; k++) {
      const op = ops[k];
      if (typeof op !== 'string' && op.t === OP_AUTOLINK) ops[k] = op.text;
    }
  }
  // scope delimiters inside this link/image to it, so they cannot pair with
  // delimiters outside it (an inner link keeps its own scope)
  const lid = ++LINK_SEQ;
  for (const d of delims) {
    if (d.linkId === 0 && d.pos >= textStart && d.pos < textEnd) d.linkId = lid;
  }
  // form the link / image
  const ph = opener.ph;
  if (ph.img) {
    ph.open = 'img';
    ph.href = cleanUrl(href);
    ph.title = title ? escAttrEnt(title) : '';
    ph.altFrom = opener.phOpIdx + 1;
    ph.altTo = ops.length;
  } else {
    ph.open = '<a href="' + cleanUrl(href) + '"' + (title ? ' title="' + escAttrEnt(title) + '"' : '') + '>';
    ops.push('</a>');
  }
  return end;
}

// Parse a bracketed label starting at str[i] === '['. Returns {label, end} (end just
// past the closing ']') or null. Label content is raw (escapes kept).
function parseBracketLabel(str, i, b) {
  let depth = 1, j = i + 1;
  while (j < b) {
    const c = str.charCodeAt(j);
    if (c === 92 && j + 1 < b) { j += 2; continue; }
    if (c === 91) depth++;
    else if (c === 93) {
      depth--;
      if (depth === 0) return { label: str.slice(i + 1, j), end: j + 1 };
    }
    j++;
  }
  return null;
}

// ---------------------------------------------------------------- '<' handling
function scanLt(str, i, b, ops) {
  // autolink <scheme:...> or <email>
  const gt = str.indexOf('>', i + 1);
  if (gt > 0 && gt < b) {
    const inner = str.slice(i + 1, gt);
    if (inner.length > 0 && inner.indexOf(' ') < 0 && inner.indexOf('\t') < 0 && inner.indexOf('<') < 0 && inner.indexOf('\n') < 0) {
      const colon = inner.indexOf(':');
      if (colon > 1) {
        const scheme = inner.slice(0, colon);
        if (/^[A-Za-z][A-Za-z0-9+.-]{1,31}$/.test(scheme)) {
          const href = autolinkHref(inner);
          ops.push('<a href="' + href + '">' + escTextOf(inner) + '</a>');
          return gt + 1;
        }
      }
      if (isEmailInner(inner)) {
        ops.push('<a href="mailto:' + autolinkHref(inner) + '">' + escTextOf(inner) + '</a>');
        return gt + 1;
      }
    }
  }
  // raw HTML
  const tagEnd = scanHtmlTag(str, i, b);
  if (tagEnd > 0) { ops.push(str.slice(i, tagEnd)); return tagEnd; }
  ops.push('&lt;');
  return i + 1;
}

function isEmailInner(s) {
  const at = s.indexOf('@');
  if (at <= 0) return false;
  const local = s.slice(0, at), domain = s.slice(at + 1);
  if (!/^[A-Za-z0-9.!#$%&'*+/=?^_`{|}~-]+$/.test(local)) return false;
  if (!/^[A-Za-z0-9-]+(\.[A-Za-z0-9-]+)+$/.test(domain)) return false;
  return true;
}

// Scan a raw HTML tag / comment / PI / declaration / CDATA starting at str[i] === '<'.
// Returns the index just past it, or -1.
function scanHtmlTag(str, i, b) {
  if (str.startsWith('<!--', i)) {
    // '<!-->' and '<!--->' are complete comments on their own
    if (str.charCodeAt(i + 4) === 62) return i + 5;
    if (str.charCodeAt(i + 4) === 45 && str.charCodeAt(i + 5) === 62) return i + 6;
    const e = str.indexOf('-->', i + 4);
    return e >= 0 && e < b ? e + 3 : -1;
  }
  if (str.startsWith('<?', i)) {
    const e = str.indexOf('?>', i + 2);
    return e >= 0 && e < b ? e + 2 : -1;
  }
  if (str.startsWith('<![CDATA[', i)) {
    const e = str.indexOf(']]>', i + 9);
    return e >= 0 && e < b ? e + 3 : -1;
  }
  if (str.startsWith('<!', i)) {
    if (i + 2 < b && isAlpha(str.charCodeAt(i + 2))) {
      const e = str.indexOf('>', i + 2);
      return e >= 0 && e < b ? e + 1 : -1;
    }
    return -1;
  }
  let j = i + 1, closing = false;
  if (j < b && str.charCodeAt(j) === 47) { closing = true; j++; }
  if (j >= b || !isAlpha(str.charCodeAt(j))) return -1;
  while (j < b && (isAlnum(str.charCodeAt(j)) || str.charCodeAt(j) === 45)) j++;
  if (closing) {
    while (j < b && (str.charCodeAt(j) === 32 || str.charCodeAt(j) === 9)) j++;
    if (j < b && str.charCodeAt(j) === 62) return j + 1;
    return -1;
  }
  // attributes: an attribute must be preceded by whitespace (a name or a
  // quoted value directly followed by another name is not a tag)
  let wsSeen = false;
  for (;;) {
    while (j < b && (str.charCodeAt(j) === 32 || str.charCodeAt(j) === 9 || str.charCodeAt(j) === 10)) { j++; wsSeen = true; }
    if (j >= b) return -1;
    const c = str.charCodeAt(j);
    if (c === 62) return j + 1;
    if (c === 47) {
      if (j + 1 < b && str.charCodeAt(j + 1) === 62) return j + 2;
      return -1;
    }
    if (!wsSeen) return -1;
    // attribute name
    if (!(isAlpha(c) || c === 95 || c === 58)) return -1;
    j++;
    while (j < b) {
      const d = str.charCodeAt(j);
      if (isAlnum(d) || d === 95 || d === 58 || d === 46 || d === 45) j++;
      else break;
    }
    wsSeen = false;
    while (j < b && (str.charCodeAt(j) === 32 || str.charCodeAt(j) === 9)) { j++; wsSeen = true; }
    if (j < b && str.charCodeAt(j) === 61) {
      j++;
      while (j < b && (str.charCodeAt(j) === 32 || str.charCodeAt(j) === 9)) j++;
      if (j >= b) return -1;
      const q = str.charCodeAt(j);
      if (q === 34 || q === 39) {
        j++;
        while (j < b && str.charCodeAt(j) !== q) j++;
        if (j >= b) return -1;
        j++;
      } else {
        if (j < b && (str.charCodeAt(j) === 34 || str.charCodeAt(j) === 39 || str.charCodeAt(j) === 61 || str.charCodeAt(j) === 60 || str.charCodeAt(j) === 62 || str.charCodeAt(j) === 96)) return -1;
        while (j < b) {
          const d = str.charCodeAt(j);
          if (d === 32 || d === 9 || d === 10 || d === 34 || d === 39 || d === 61 || d === 60 || d === 62 || d === 96) break;
          j++;
        }
      }
    }
  }
}

// ---------------------------------------------------------------- extended autolinks (GFM)
const TRAIL_PUNCT = '?!,.:;*_~\'"';
function trimAutolinkEnd(str, a, e) {
  // an unmatched '(' (no ')' after it) ends the link before the '('
  let lastClose = -1;
  for (let k = e - 1; k >= a; k--) if (str.charCodeAt(k) === 41) { lastClose = k; break; }
  // an unmatched '(' has no ')' after it inside the URL; scan from the URL
  // start (not from 0, which would catch a '(' from earlier text)
  for (let k = Math.max(lastClose + 1, a); k < e; k++) if (str.charCodeAt(k) === 40) { e = k; break; }
  // drop trailing punctuation, unbalanced ')' and entity-like ';'
  for (;;) {
    if (e <= a) break;
    const c = str.charCodeAt(e - 1);
    if (c === 41) { // )
      let open = 0, close = 0;
      for (let k = a; k < e; k++) {
        if (str.charCodeAt(k) === 40) open++;
        else if (str.charCodeAt(k) === 41) close++;
      }
      if (close > open) { e--; continue; }
      break;
    }
    if (c === 59) { // ; — drop the whole entity-looking &xxx; (the URL ends
      // before the '&'); otherwise it is ordinary trailing punctuation
      let k = e - 2;
      while (k >= a && isAlnum(str.charCodeAt(k))) k--;
      if (k >= a && str.charCodeAt(k) === 38) { e = k; continue; }
    }
    if (TRAIL_PUNCT.indexOf(str[e - 1]) >= 0) { e--; continue; }
    break;
  }
  return e;
}

// Validate an email domain: labels of [A-Za-z0-9_-]+ joined by '.', at least one
// dot (so foo@bar.b, foo@123.456, foo@bar_baz.qux and foo@-.baz all link, while
// foo@bar, foo@.bar.baz and foo@bar..baz do not).
function validEmailDomain(str, a, e) {
  if (e - a < 3) return false;
  let labels = 0, start = a, hasDot = false;
  for (let k = a; k <= e; k++) {
    if (k === e || str.charCodeAt(k) === 46) {
      if (k - start === 0) return false;
      // a label must end with a letter or digit (a.b- and a.b_ do not link)
      const lc = str.charCodeAt(k - 1);
      if (lc === 45 || lc === 95) return false;
      labels++;
      if (k < e) hasDot = true;
      start = k + 1;
    } else if (!(isAlnum(str.charCodeAt(k)) || str.charCodeAt(k) === 45 || str.charCodeAt(k) === 95)) return false;
  }
  return hasDot && labels >= 2;
}

// 'www.' autolink starting at str[k]. Returns end index or -1.
function matchWww(str, k, b, inLink) {
  let e = k;
  while (e < b) {
    const c = str.charCodeAt(e);
    if (c === 32 || c === 9 || c === 10 || c === 60 || c < 32 || (inLink && (c === 91 || c === 93))) break;
    e++;
  }
  e = trimAutolinkEnd(str, k, e);
  if (e - k < 5) return null;
  // host is up to the first / ? # (or end); it must be non-empty and start with a
  // letter, digit, '-', '_' or non-ASCII char (www.x, www.-x.com, www.a..b all link;
  // www., www./x and www..x do not)
  let dEnd = k + 4;
  while (dEnd < e) {
    const c = str.charCodeAt(dEnd);
    if (c === 47 || c === 63 || c === 35) break;
    dEnd++;
  }
  if (dEnd <= k + 4) return null;
  const hc = str.charCodeAt(k + 4);
  if (!(isAlnum(hc) || hc === 45 || hc === 95 || hc >= 128)) return null;
  return { start: k, end: e };
}

// scheme:// autolink whose '://' is at str[k]. Returns end index or -1.
// (The link starts at the scheme, before k.)
function matchScheme(str, k, b, inLink) {
  let s = k;
  while (s > 0) {
    const c = str.charCodeAt(s - 1);
    if (isAlnum(c) || c === 43 || c === 45 || c === 46) s--;
    else break;
  }
  if (k - s < 2 || k - s > 32) return null;
  if (!isAlpha(str.charCodeAt(s))) return null;
  let e = k + 3;
  while (e < b) {
    const c = str.charCodeAt(e);
    if (c === 32 || c === 9 || c === 10 || c === 60 || c < 32 || (inLink && (c === 91 || c === 93))) break;
    e++;
  }
  e = trimAutolinkEnd(str, s, e);
  if (e - (k + 3) < 1) return null;
  // host is up to the first / ? #; it must be non-empty and start with a letter,
  // digit, '-', '_' or non-ASCII char (http://foo, http://-foo/, http://foo_bar/
  // link; http://, http:///x, http://.foo/x, http://:8080/x do not)
  let hEnd = k + 3;
  while (hEnd < e) {
    const c = str.charCodeAt(hEnd);
    if (c === 47 || c === 63 || c === 35) break;
    hEnd++;
  }
  if (hEnd <= k + 3) return null;
  const hc = str.charCodeAt(k + 3);
  if (!(isAlnum(hc) || hc === 45 || hc === 95 || hc >= 128)) return null;
  return { start: s, end: e };
}

// A valid scheme (2-32 chars, first a letter) ending with ':' just before
// index s; returns the scheme start, or -1.
function schemePrefixStart(str, s) {
  if (s < 2 || str.charCodeAt(s - 1) !== 58) return -1;
  let t = s - 1;
  while (t > 0) {
    const c = str.charCodeAt(t - 1);
    if (isAlnum(c) || c === 43 || c === 45 || c === 46) t--;
    else break;
  }
  const len = (s - 1) - t;
  if (len < 2 || len > 32) return -1;
  if (!isAlpha(str.charCodeAt(t))) return -1;
  return t;
}

// email autolink whose '@' is at str[k]. Returns {start, end} or null. The local
// part is [A-Za-z0-9._+-]+ (leading/trailing dots ok; '_', '+' and '-' included,
// while ', !, #, %, /, =, ?, ', ", *, ~ and : break it), the domain is scanned
// forward and must pass validEmailDomain (trailing dots trimmed). A lowercase
// 'mailto:' immediately before the local part is part of the link.
function matchEmail(str, k, b, delims) {
  let e = k + 1;
  while (e < b) {
    const c = str.charCodeAt(e);
    if (isAlnum(c) || c === 45 || c === 46 || c === 95) e++;
    else break;
  }
  while (e > k + 1 && str.charCodeAt(e - 1) === 46) e--;
  if (!validEmailDomain(str, k + 1, e)) {
    // a trailing '_' may be an emphasis closer, not domain text: trim it
    // (and any further '_') only when an unmatched '_' opener precedes
    if (delims && e > k + 1 && str.charCodeAt(e - 1) === 95) {
      let hasOpener = false;
      for (let d = 0; d < delims.length; d++) {
        const od = delims[d];
        if (od.ch === 95 && od.canOpen && od.pos < k) { hasOpener = true; break; }
      }
      if (hasOpener) {
        let e2 = e;
        while (e2 > k + 1 && str.charCodeAt(e2 - 1) === 95) e2--;
        if (validEmailDomain(str, k + 1, e2)) e = e2;
        else return null;
      } else return null;
    } else return null;
  }
  let s = k;
  while (s > 0) {
    const c = str.charCodeAt(s - 1);
    if (isAlnum(c) || c === 46 || c === 43 || c === 95 || c === 45) s--;
    else break;
  }
  if (s === k) return null;
  if (s > 0 && str.charCodeAt(s - 1) === 92) return null; // local part escaped
  if (s >= 7 && str.slice(s - 7, s) === 'mailto:') s -= 7;
  return { start: s, end: e };
}

// ================= block parser =================

// Is a line view blank (only spaces/tabs)?
function isBlank(ln) {
  for (let k = ln.s; k < ln.e; k++) {
    const c = SRC.charCodeAt(k);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

// The text of a line view (pad spaces + source slice).
function viewText(ln) {
  const p = ln.pad || 0;
  return p > 0 ? ' '.repeat(p) + SRC.slice(ln.s, ln.e) : SRC.slice(ln.s, ln.e);
}

// ATX heading: {level, a, b} (content range in SRC) or null.
function parseAtx(ln, off) {
  let k = off, n = 0;
  while (k < ln.e && SRC.charCodeAt(k) === 35) { k++; n++; }
  if (n === 0 || n > 6) return null;
  let hadSpace = false;
  if (k < ln.e) {
    const c = SRC.charCodeAt(k);
    if (c !== 32 && c !== 9) return null;
    hadSpace = true;
    k++;
  }
  let a = k;
  while (a < ln.e && (SRC.charCodeAt(a) === 32 || SRC.charCodeAt(a) === 9)) a++;
  let b = ln.e;
  while (b > a && (SRC.charCodeAt(b - 1) === 32 || SRC.charCodeAt(b - 1) === 9)) b--;
  // strip a closing '#' run: preceded by space/tab, or the whole text when a
  // space followed the opening run (# # -> empty, # foo # -> foo, # foo# -> foo#)
  let r = b;
  while (r > a && SRC.charCodeAt(r - 1) === 35) r--;
  if (r < b) {
    if ((r > a && (SRC.charCodeAt(r - 1) === 32 || SRC.charCodeAt(r - 1) === 9)) ||
        (r === a && hadSpace)) {
      b = r;
      while (b > a && (SRC.charCodeAt(b - 1) === 32 || SRC.charCodeAt(b - 1) === 9)) b--;
    }
  }
  return { level: n, a, b };
}

// Thematic break: 3+ of the same char (*, -, _) with optional spaces/tabs between.
function isThematicBreak(ln, off) {
  const ch = SRC.charCodeAt(off);
  if (ch !== 42 && ch !== 45 && ch !== 95) return false;
  let n = 0;
  for (let k = off; k < ln.e; k++) {
    const c = SRC.charCodeAt(k);
    if (c === ch) n++;
    else if (c !== 32 && c !== 9) return false;
  }
  return n >= 3;
}

// Setext underline level (1 for '=', 2 for '-') or 0. The run must be contiguous
// (no spaces between the chars); trailing spaces are allowed.
function setextLevel(ln, off) {
  const ch = SRC.charCodeAt(off);
  if (ch !== 61 && ch !== 45) return 0;
  let k = off;
  while (k < ln.e && SRC.charCodeAt(k) === ch) k++;
  while (k < ln.e && (SRC.charCodeAt(k) === 32 || SRC.charCodeAt(k) === 9)) k++;
  if (k !== ln.e) return 0;
  return ch === 61 ? 1 : 2;
}

// Fenced code opening: {ch, len, infoStart} or null. A backtick fence's info
// string may not contain backticks.
function fenceOpen(ln, off) {
  const ch = SRC.charCodeAt(off);
  if (ch !== 96 && ch !== 126) return null;
  let k = off, n = 0;
  while (k < ln.e && SRC.charCodeAt(k) === ch) { k++; n++; }
  if (n < 3) return null;
  if (ch === 96) {
    for (let p = k; p < ln.e; p++) if (SRC.charCodeAt(p) === 96) return null;
  }
  return { ch, len: n, infoStart: k };
}

// Fenced code closing: same char, length >= open length, only spaces after.
function fenceClose(ln, off, ch, len) {
  let k = off, n = 0;
  while (k < ln.e && SRC.charCodeAt(k) === ch) { k++; n++; }
  if (n < len) return false;
  while (k < ln.e && (SRC.charCodeAt(k) === 32 || SRC.charCodeAt(k) === 9)) k++;
  return k === ln.e;
}

// Block-level tag names (CommonMark 0.31.2) for HTML block type 6.
const BLOCK_TAGS = new Set(('address article aside base basefont blockquote body caption center col colgroup dd details dialog dir div dl dt fieldset figcaption figure footer form frame frameset h1 h2 h3 h4 h5 h6 head header hr html iframe legend li link main menu nav noframes ol optgroup option p param section summary table tbody td tfoot th thead title tr track ul').split(' '));

// HTML block start: {type, close} or null. Types 1-5 end at a line containing
// `close`; types 6-7 end at a blank line. Type 7 cannot interrupt a paragraph.
function htmlBlockType(ln, off) {
  if (SRC.charCodeAt(off) !== 60) return null; // '<'
  const rest = SRC.slice(off, ln.e);
  if (rest.startsWith('<!--')) return { type: 2, close: '-->' };
  if (rest.startsWith('<?')) return { type: 3, close: '?>' };
  if (rest.startsWith('<!') && rest.length > 2 && isAlpha(rest.charCodeAt(2))) return { type: 4, close: '>' };
  if (rest.startsWith('<![CDATA[')) return { type: 5, close: ']]>' };
  const m1 = /^<(script|pre|style|textarea)(?=[\s>\/]|$)/i.exec(rest);
  if (m1) return { type: 1, close: '</' + m1[1].toLowerCase() + '>' };
  const m6 = /^<\/?([A-Za-z][A-Za-z0-9-]*)(?=[\s>\/]|$)/.exec(rest);
  if (m6 && BLOCK_TAGS.has(m6[1].toLowerCase())) return { type: 6, close: null };
  // type 7: a complete open tag (any attributes) or a closing tag (no
  // attributes), only whitespace after it
  const t = rest.trim();
  if (t.startsWith('</')) {
    if (/^<\/[A-Za-z][A-Za-z0-9-]*\s*>$/.test(t)) return { type: 7, close: null };
  } else if (/^<[A-Za-z][A-Za-z0-9-]*(?:\s+[A-Za-z_:][A-Za-z0-9_.:-]*(?:\s*=\s*(?:"[^"]*"|'[^']*'|[^\s"'=<>`]+))?)*\s*\/?>$/.test(t)) {
    return { type: 7, close: null };
  }
  return null;
}

// List marker: {bullet, ordered, num, delim, markerLen, markerEnd} or null.
// Ordered markers are 1-9 digits followed by '.' or ')'.
// A list marker must be followed by a space, tab or end of line ('+++' and
// '--' are paragraphs, not lists; '*foo*' does not interrupt a paragraph).
function listMarker(ln, off) {
  const c = SRC.charCodeAt(off);
  if (c === 45 || c === 43 || c === 42) {
    if (off + 1 < ln.e) {
      const d = SRC.charCodeAt(off + 1);
      if (d !== 32 && d !== 9) return null;
    }
    return { bullet: true, ordered: false, ch: c, markerLen: 1, markerEnd: off + 1 };
  }
  if (c >= 48 && c <= 57) {
    let k = off, n = 0;
    while (k < ln.e && SRC.charCodeAt(k) >= 48 && SRC.charCodeAt(k) <= 57 && n < 10) { k++; n++; }
    if (n === 0 || n > 9) return null;
    if (k < ln.e && (SRC.charCodeAt(k) === 46 || SRC.charCodeAt(k) === 41)) {
      if (k + 1 < ln.e) {
        const d = SRC.charCodeAt(k + 1);
        if (d !== 32 && d !== 9) return null;
      }
      return { bullet: false, ordered: true, num: parseInt(SRC.slice(off, k), 10), delim: SRC.charCodeAt(k), markerLen: k - off + 1, markerEnd: k + 1 };
    }
  }
  return null;
}

// The content column W for a list item and its content view, RELATIVE to the
// marker line's lineStartCol (absolute columns do not compare across views
// that were stripped through different container prefixes).
// markerLen + wsWidth (tabs expanded), or markerCol + markerLen + 1 when the
// whitespace run is >= 5 columns wide; an empty item always gets markerCol +
// markerLen + 1. (Verified: '- foo' W=2, '-    foo' W=5, '-     foo' W=2,
// '-\tfoo' W=4, '-\t\tfoo' W=2.)
function listItemContent(ln, marker, markerCol) {
  let col = markerCol + marker.markerLen, off = marker.markerEnd;
  let wsWidth = 0;
  while (off < ln.e) {
    const c = SRC.charCodeAt(off);
    if (c === 32) { col++; wsWidth++; off++; }
    else if (c === 9) { const nc = col + 4 - (col & 3); wsWidth += nc - col; col = nc; off++; }
    else break;
  }
  const base = lineStartCol(ln);
  if (off >= ln.e) {
    return { W: markerCol + marker.markerLen + 1 - base, empty: true, content: null };
  }
  const Wabs = wsWidth >= 5 ? markerCol + marker.markerLen + 1 : markerCol + marker.markerLen + wsWidth;
  return { W: Wabs - base, empty: false, content: cutToCol(ln, Wabs) };
}

// Does this line start a block that interrupts a paragraph? (ATX, fence, HTML
// types 1-6, blockquote, thematic break, or a list that can interrupt.) A '-'/ '='
// run is a setext underline, not an interruption; indented code cannot interrupt.
function startsInterruptingBlock(ln, inListItem) {
  const { off, col } = firstNonSpace(ln);
  if (off >= ln.e) return false;
  const indent = col - lineStartCol(ln);
  if (indent >= 4) return false;
  const c = SRC.charCodeAt(off);
  if (c === 35 && parseAtx(ln, off)) return true;
  if ((c === 96 || c === 126) && fenceOpen(ln, off)) return true;
  if (c === 60) {
    const h = htmlBlockType(ln, off);
    if (h && h.type >= 1 && h.type <= 6) return true;
  }
  if (c === 62) return true;
  if (c === 42 || c === 45 || c === 95) {
    if (setextLevel(ln, off) > 0) return false;
    if (isThematicBreak(ln, off)) return true;
  }
  const m = listMarker(ln, off);
  if (m) {
    // an empty item cannot interrupt a paragraph
    let k = m.markerEnd;
    while (k < ln.e && (SRC.charCodeAt(k) === 32 || SRC.charCodeAt(k) === 9)) k++;
    if (k >= ln.e) return false;
    if (m.bullet) return true;
    if (m.ordered && (m.num === 1 || inListItem)) return true;
    return false;
  }
  return false;
}

// Strip a blockquote marker '>' (indent <= 3) plus one optional space/tab.
// A tab after '>' leaves its remainder as pad (pad = tabEnd - (gtCol + 2)).
function stripQuoteMarker(ln) {
  const { off, col } = firstNonSpace(ln);
  if (col - lineStartCol(ln) > 3) return null;
  if (off >= ln.e || SRC.charCodeAt(off) !== 62) return null;
  const gtCol = col;
  const base = lineStartCol(ln);
  let s = off + 1, c = gtCol + 1, pad = 0;
  if (s < ln.e) {
    const ch = SRC.charCodeAt(s);
    if (ch === 32) {
      s++; c++;
      // a tab right after '> ' is the first content char; expand it to
      // spaces (to the next multiple of 4, relative to the view's own
      // line start, so a quote inside a list item expands correctly)
      if (s < ln.e && SRC.charCodeAt(s) === 9) {
        const rc = c - base;
        const tabEnd = rc + 4 - (rc & 3);
        pad = tabEnd - rc;
        s++; c = base + tabEnd;
      }
    }
    else if (ch === 9) {
      const rc = c - base;
      const tabEnd = rc + 4 - (rc & 3);
      pad = tabEnd - (gtCol - base + 2);
      s++; c = base + tabEnd;
    }
  }
  const v = { s, e: ln.e, pad, col: c, nl: ln.nl };
  // a '>'-prefixed line whose remaining content is only spaces is a paragraph
  // line with space content, not a blank line (e.g. '>  ' -> ' ')
  if (pad > 0 || s < ln.e) {
    let allWs = true;
    for (let k = s; k < ln.e; k++) {
      const ch = SRC.charCodeAt(k);
      if (ch !== 32 && ch !== 9) { allWs = false; break; }
    }
    if (allWs) v.notBlank = true;
  }
  return v;
}

// Update (inPara, fence) tracking for a content line already stripped/dedented.
// inPara = the line is a paragraph line; fence = an open fence at this level.
function updateParaFence(ln, inPara, fence) {
  if (isBlank(ln)) return { inPara: false, fence };
  const { off, col } = firstNonSpace(ln);
  const indent = col - lineStartCol(ln);
  if (indent <= 3) {
    const c = SRC.charCodeAt(off);
    if (c === 96 || c === 126) {
      if (fence && fenceClose(ln, off, fence.ch, fence.len)) return { inPara: false, fence: null };
      if (!fence) {
        const f = fenceOpen(ln, off);
        if (f) return { inPara: false, fence: f };
      } else {
        return { inPara: false, fence }; // fence content line
      }
    }
  }
  const np = !startsInterruptingBlock(ln) && (inPara || indent < 4);
  return { inPara: np, fence };
}

// Resolve backslash escapes of ASCII punctuation in a string.
function unescapePunct(s) {
  if (s.indexOf('\\') < 0) return s;
  let out = '';
  for (let i = 0; i < s.length; i++) {
    if (s.charCodeAt(i) === 92 && i + 1 < s.length && isAsciiPunct(s.charCodeAt(i + 1))) { out += s[i + 1]; i++; }
    else out += s[i];
  }
  return out;
}

// Parse a link title starting at s[r] ('"' / "'" / '('). Returns {title, end}
// (end = just past the closing delimiter) or null. Titles never span lines.
function parseTitleAt(s, r) {
  const c = s.charCodeAt(r);
  const close = c === 40 ? 41 : c;
  let e2 = r + 1, ok = false;
  while (e2 < s.length) {
    const d = s.charCodeAt(e2);
    if (d === 92 && e2 + 1 < s.length && isAsciiPunct(s.charCodeAt(e2 + 1))) { e2 += 2; continue; }
    if (close === 41 && d === 40) return null; // unescaped '(' inside a (...) title
    if (d === close) { ok = true; break; }
    e2++;
  }
  if (!ok) return null;
  return { title: s.slice(r + 1, e2), end: e2 + 1 };
}

// Try to parse a link reference definition starting at lines[i]. The label,
// destination and title may each be on the following line, but no blank line may
// appear inside. Returns {linesUsed, label, href, title} or null.
function tryRefDef(lines, i) {
  let s = '';
  const starts = [];
  for (let k = i; k < lines.length && starts.length < 20; k++) {
    if (isBlank(lines[k])) break;
    starts.push(s.length);
    if (s.length > 0) s += '\n';
    s += viewText(lines[k]);
  }
  if (starts.length === 0) return null;
  let p = 0;
  while (p < s.length && s.charCodeAt(p) === 32) p++;
  if (p > 3 || s.charCodeAt(p) !== 91) return null; // '['
  let q = p + 1, labelEnd = -1;
  while (q < s.length) {
    const c = s.charCodeAt(q);
    if (c === 92 && q + 1 < s.length) { q += 2; continue; }
    if (c === 91) return null;
    if (c === 93) { labelEnd = q; break; }
    q++;
  }
  if (labelEnd < 0) return null;
  const rawLabel = s.slice(p + 1, labelEnd);
  if (rawLabel.length === 0 || rawLabel.length > 999) return null;
  if (rawLabel.trim().length === 0) return null;
  let r = labelEnd + 1;
  if (r >= s.length || s.charCodeAt(r) !== 58) return null; // ':'
  r++;
  while (r < s.length) {
    const c = s.charCodeAt(r);
    if (c === 32 || c === 9 || c === 10) r++;
    else break;
  }
  if (r >= s.length) return null;
  let href = '';
  if (s.charCodeAt(r) === 60) { // '<...>'
    let e2 = r + 1;
    while (e2 < s.length) {
      const c = s.charCodeAt(e2);
      if (c === 10 || c === 60) return null;
      if (c === 62) break;
      e2++;
    }
    if (e2 >= s.length || s.charCodeAt(e2) !== 62) return null;
    href = s.slice(r + 1, e2);
    r = e2 + 1;
  } else {
    let e2 = r;
    while (e2 < s.length) {
      const c = s.charCodeAt(e2);
      if (c === 32 || c === 9 || c === 10 || c < 32) break;
      e2++;
    }
    if (e2 === r) return null;
    href = s.slice(r, e2);
    r = e2;
  }
  // optional title: same line, or the next line (after the dest's line ends).
  // A title needs whitespace before it; a bad title on a later line is dropped
  // and the definition keeps only label + destination; a bad title on the
  // destination's own line invalidates the definition.
  const rDestEnd = r;
  while (r < s.length && (s.charCodeAt(r) === 32 || s.charCodeAt(r) === 9)) r++;
  let title = '';
  let tStart = -1, crossedNl = false;
  if (r < s.length && s.charCodeAt(r) === 10) {
    crossedNl = true;
    let qq = r + 1;
    while (qq < s.length && (s.charCodeAt(qq) === 32 || s.charCodeAt(qq) === 9)) qq++;
    if (qq < s.length && (s.charCodeAt(qq) === 34 || s.charCodeAt(qq) === 39 || s.charCodeAt(qq) === 40)) tStart = qq;
  } else if (r < s.length && (s.charCodeAt(r) === 34 || s.charCodeAt(r) === 39 || s.charCodeAt(r) === 40)) {
    tStart = r;
  } else if (r < s.length && s.charCodeAt(r) !== 10) {
    return null; // junk after the destination on its line
  }
  if (tStart >= 0) {
    if (tStart === rDestEnd) return null; // a title needs whitespace before it
    const t = parseTitleAt(s, tStart);
    let titleOk = false;
    if (t) {
      let rr = t.end;
      while (rr < s.length && (s.charCodeAt(rr) === 32 || s.charCodeAt(rr) === 9)) rr++;
      if (rr >= s.length || s.charCodeAt(rr) === 10) { title = t.title; r = t.end; titleOk = true; }
    }
    if (!titleOk) {
      if (crossedNl) r = rDestEnd; // title on a later line: keep label + dest only
      else return null; // title on the dest's line and bad: no definition
    }
  }
  while (r < s.length && (s.charCodeAt(r) === 32 || s.charCodeAt(r) === 9)) r++;
  if (r < s.length && s.charCodeAt(r) !== 10) return null;
  let endOff = r;
  if (endOff > 0 && endOff < s.length && s.charCodeAt(endOff) === 10) endOff--;
  let linesUsed = 1;
  for (let k = 1; k < starts.length; k++) if (starts[k] <= endOff) linesUsed = k + 1;
  const label = normaliseLabel(rawLabel);
  if (!label) return null;
  return { linesUsed, label, href: unescapePunct(href), title: unescapePunct(title) };
}

// Split a table row's text into cells: split on unescaped '|' outside code
// spans; leading/trailing '|' create no cells; cells are trimmed. 'f\|oo' stays
// one cell 'f|oo'; a '|' inside backticks does not split.
function splitTableRow(text) {
  let a = 0;
  while (a < text.length && (text.charCodeAt(a) === 32 || text.charCodeAt(a) === 9)) a++;
  let b = text.length;
  while (b > a && (text.charCodeAt(b - 1) === 32 || text.charCodeAt(b - 1) === 9)) b--;
  let s = text.slice(a, b);
  if (s.charCodeAt(0) === 124) s = s.slice(1);
  if (s.length > 0 && s.charCodeAt(s.length - 1) === 124) s = s.slice(0, -1);
  const cells = [];
  let cur = '', inCode = 0;
  for (let k = 0; k < s.length; k++) {
    const c = s.charCodeAt(k);
    if (c === 92 && k + 1 < s.length && s.charCodeAt(k + 1) === 124) { cur += '|'; k++; continue; }
    if (c === 96) {
      let n = 0;
      while (k + n < s.length && s.charCodeAt(k + n) === 96) n++;
      if (inCode === 0) {
        // a backtick run only opens a code span when a matching run of the
        // same length follows; an unmatched run is literal text and does not
        // suppress '|' splitting
        let hasClose = false;
        for (let q = k + n; q < s.length; q++) {
          if (s.charCodeAt(q) !== 96) continue;
          let m = 0;
          while (q + m < s.length && s.charCodeAt(q + m) === 96) m++;
          if (m === n) { hasClose = true; break; }
          q += m - 1;
        }
        if (hasClose) inCode = n;
      } else if (n === inCode) inCode = 0;
      cur += s.slice(k, k + n);
      k += n - 1;
      continue;
    }
    if (c === 124 && inCode === 0) { cells.push(cur.trim()); cur = ''; continue; }
    cur += s[k];
  }
  cells.push(cur.trim());
  return cells;
}

// Parse a table delimiter row: returns the alignment array ('left'/'right'/
// 'center'/'') or null. A pure '-' run is a setext underline, not a delimiter.
function parseTableDelimiter(ln, off) {
  const text = SRC.slice(off, ln.e);
  if (text.indexOf('|') < 0 && text.indexOf(':') < 0) return null;
  let s = text.trim();
  if (s.charCodeAt(0) === 124) s = s.slice(1);
  if (s.length > 0 && s.charCodeAt(s.length - 1) === 124) s = s.slice(0, -1);
  if (s.length === 0) return null;
  const parts = s.split('|');
  const aligns = [];
  for (const part of parts) {
    const t = part.trim();
    if (!/^:?-+:?$/.test(t)) return null;
    if (t.charCodeAt(0) === 58 && t.charCodeAt(t.length - 1) === 58) aligns.push('center');
    else if (t.charCodeAt(t.length - 1) === 58) aligns.push('right');
    else if (t.charCodeAt(0) === 58) aligns.push('left');
    else aligns.push('');
  }
  return aligns;
}

// Emit the inline content of paragraph lines (verbatim lines joined by '\n').
function emitInlineLines(pLines, out) {
  let text = '';
  for (let k = 0; k < pLines.length; k++) {
    if (k > 0) text += '\n';
    text += viewText(pLines[k]);
  }
  inlineTo(text, 0, text.length, out);
}

// Emit a table starting at the delimiter row. headerLn is the header line.
// Returns the index of the first line after the table.
function emitTable(lines, table, headerLn, out, prefix) {
  const aligns = table.delimCells;
  const headerCells = table.headerCells;
  out.push('<table>\n<thead>\n<tr>\n');
  for (let k = 0; k < headerCells.length; k++) {
    out.push('<th' + (aligns[k] ? ' align="' + aligns[k] + '"' : '') + '>');
    if (k === 0 && prefix) out.push(prefix);
    inlineTo(headerCells[k], 0, headerCells[k].length, out);
    out.push('</th>\n');
  }
  out.push('</tr>\n</thead>\n');
  const rows = [];
  let j = table.delimIdx + 1;
  while (j < lines.length) {
    const ln = lines[j];
    // a line of only spaces (or empty) ends the table, but a line containing
    // a tab is an (empty-cell) table row
    let tableBlank = true;
    for (let k = ln.s; k < ln.e; k++) {
      if (SRC.charCodeAt(k) !== 32) { tableBlank = false; break; }
    }
    if (tableBlank) break;
    if (startsInterruptingBlock(ln)) break;
    rows.push(ln);
    j++;
  }
  if (rows.length > 0) {
    out.push('<tbody>');
    for (const rowLn of rows) {
      const cells = splitTableRow(viewText(rowLn));
      out.push('<tr>\n');
      for (let k = 0; k < headerCells.length; k++) {
        const cell = k < cells.length ? cells[k] : '';
        out.push('<td' + (aligns[k] ? ' align="' + aligns[k] + '"' : '') + '>');
        inlineTo(cell, 0, cell.length, out);
        out.push('</td>\n');
      }
      out.push('</tr>\n');
    }
    out.push('</tbody>');
  }
  out.push('</table>\n');
  return j;
}

// ---- individual block types (each returns the index of the next line) ----

function parseIndentedCode(lines, i, out) {
  const content = [];
  let j = i;
  while (j < lines.length) {
    const ln = lines[j];
    if (isBlank(ln)) {
      let k = j + 1;
      while (k < lines.length && isBlank(lines[k])) k++;
      if (k < lines.length) {
        const f = firstNonSpace(lines[k]);
        if (f.col - lineStartCol(lines[k]) >= 4) {
          for (let b = j; b < k; b++) content.push(viewText(removeIndent(lines[b], 4)));
          j = k;
          continue;
        }
      }
      break;
    }
    const f = firstNonSpace(ln);
    if (f.col - lineStartCol(ln) < 4) break;
    content.push(viewText(removeIndent(ln, 4)));
    j++;
  }
  out.push('<pre><code>');
  for (const t of content) {
    const tmp = [];
    escRange(t, 0, t.length, tmp);
    out.push(tmp.join(''));
    out.push('\n');
  }
  out.push('</code></pre>\n');
  return j;
}

function parseFencedCode(lines, i, f, out) {
  const ln = lines[i];
  let p = f.infoStart;
  while (p < ln.e && (SRC.charCodeAt(p) === 32 || SRC.charCodeAt(p) === 9)) p++;
  const w0 = p;
  while (p < ln.e && SRC.charCodeAt(p) !== 32 && SRC.charCodeAt(p) !== 9) p++;
  const lang = unescapePunct(SRC.slice(w0, p));
  out.push('<pre><code' + (lang ? ' class="language-' + escAttrEnt(lang) + '"' : '') + '>');
  // content lines are dedented by the opening fence's indent (up to their own)
  // for backtick fences only: a tilde fence never dedents its content
  const fInd = f.ch === 96 ? firstNonSpace(ln).col - lineStartCol(ln) : 0;
  let j = i + 1;
  const contentLines = [];
  while (j < lines.length) {
    const cl = lines[j];
    const f2 = firstNonSpace(cl);
    if (f2.col - lineStartCol(cl) <= 3 && fenceClose(cl, f2.off, f.ch, f.len)) { j++; break; }
    contentLines.push(cl);
    j++;
  }
  // one trailing EMPTY line before the closing fence is dropped (a line with
  // only spaces is kept)
  if (contentLines.length > 0 && viewText(contentLines[contentLines.length - 1]).length === 0) {
    contentLines.pop();
  }
  for (const cl of contentLines) {
    const t = viewText(removeIndentFenced(cl, fInd));
    const tmp = [];
    escRange(t, 0, t.length, tmp);
    out.push(tmp.join(''));
    out.push('\n');
  }
  out.push('</code></pre>\n');
  return j;
}

function parseHtmlBlock(lines, i, h, out) {
  const close = h.close ? h.close.toLowerCase() : null;
  const blockLines = [];
  let j = i;
  while (j < lines.length) {
    const ln = lines[j];
    blockLines.push(ln);
    j++;
    if (close) {
      if (viewText(ln).toLowerCase().indexOf(close) >= 0) break;
    } else if (j < lines.length && isBlank(lines[j])) {
      break;
    }
  }
  for (let k = 0; k < blockLines.length; k++) {
    const ln = blockLines[k];
    out.push(viewText(ln));
    if (k + 1 < blockLines.length) { out.push('\n'); continue; }
    // last line: types 1-5 (close-tag) get a trailing newline when the line
    // was newline-terminated and the following line is not TRULY empty (a
    // whitespace-only line still counts: only a zero-length line suppresses
    // it); types 6-7 (blank-line) only when the block runs to the very end
    // of the document
    if (close) {
      const nx = j < lines.length ? lines[j] : null;
      const trulyEmpty = nx !== null && nx.e === nx.s && (nx.pad || 0) === 0;
      if (ln.nl && (nx === null || !trulyEmpty)) out.push('\n');
    } else if (ln.nl && ln.e + 1 === SRC.length) out.push('\n');
  }
  return j;
}

// Gather a blockquote's content lines (stripping '>' markers, applying the
// lazy-line rules) and the index just past it. Shared by the renderer and by
// the reference-definition pre-scan, so a def inside a quote applies document-wide.
function gatherBlockquote(lines, i) {
  const content = [];
  let j = i;
  let inPara = false;
  let fence = null;
  let lastWasLazy = false;
  let canLazy = false;
  while (j < lines.length) {
    const ln = lines[j];
    const stripped = stripQuoteMarker(ln);
    if (stripped) {
      content.push(stripped);
      const st = updateParaFence(stripped, inPara, fence);
      inPara = st.inPara; fence = st.fence;
      canLazy = contentCanLazy(stripped);
      lastWasLazy = false;
      j++;
      continue;
    }
    if (isBlank(ln)) break;
    const lf = firstNonSpace(ln);
    // a thematic break ends the quote; it is never a lazy continuation.
    // A lazy line continues an open paragraph at any depth (canLazy), and is
    // dedented by 4 columns when its indent is >= 4.
    if (canLazy && !fence && !startsInterruptingBlock(ln) && !isThematicBreak(ln, lf.off)) {
      let base = ln;
      if (lf.col - lineStartCol(ln) >= 4) base = removeIndent(ln, 4);
      const bf = firstNonSpace(base);
      // a lazy '='-run is not a setext underline; one following another lazy
      // line is demoted with 4 spaces (marked's observable output)
      let v;
      if (setextLevel(base, bf.off) === 1) {
        const pad = (base.pad || 0) + (lastWasLazy ? 4 : 0);
        v = { s: base.s, e: base.e, pad, col: base.col, nl: base.nl, lazy: true };
      } else {
        v = { s: base.s, e: base.e, pad: base.pad || 0, col: base.col, nl: base.nl, lazy: true };
      }
      content.push(v);
      inPara = true;
      lastWasLazy = true;
      j++;
      continue;
    }
    break;
  }
  return { content, endIdx: j };
}

function parseBlockquote(lines, i, out) {
  const g = gatherBlockquote(lines, i);
  out.push('<blockquote>\n');
  parseBlocksInto(g.content, out, false, '', false);
  out.push('</blockquote>\n');
  return g.endIdx;
}

// Whether a blockquote content line can hold an open paragraph (so a later
// lazy line may continue it): a paragraph, blockquote or list line. Closed
// blocks (heading, fence, HTML, thematic break, setext underline, indented
// code) cannot.
function contentCanLazy(v) {
  if (isBlank(v)) return false;
  const f = firstNonSpace(v);
  if (f.col - lineStartCol(v) >= 4) return false;
  const c = f.off < v.e ? SRC.charCodeAt(f.off) : 10;
  if (c === 35 && parseAtx(v, f.off)) return false;
  if ((c === 96 || c === 126) && fenceOpen(v, f.off)) return false;
  if (c === 60 && htmlBlockType(v, f.off)) return false;
  if (isThematicBreak(v, f.off)) return false;
  if (setextLevel(v, f.off) > 0) return false;
  return true;
}

// A task-list marker at the start of an item's content view: '[ ]', '[x]' or
// '[X]' followed by whitespace. Returns {prefix, rest} or null. The marker's
// following whitespace run is consumed, so the rest never starts indented.
function matchTask(cv) {
  const t = viewText(cv);
  if (t.length < 4) return null;
  if (t.charCodeAt(0) !== 91) return null;
  const c1 = t.charCodeAt(1);
  if (c1 !== 32 && c1 !== 120 && c1 !== 88) return null;
  if (t.charCodeAt(2) !== 93) return null;
  if (t.charCodeAt(3) !== 32 && t.charCodeAt(3) !== 9) return null;
  let k = 3;
  while (k < t.length && (t.charCodeAt(k) === 32 || t.charCodeAt(k) === 9)) k++;
  let col = lineStartCol(cv);
  for (let p = 0; p < k; p++) {
    if (t.charCodeAt(p) === 9) col += 4 - (col & 3);
    else col++;
  }
  const rest = cutToCol(cv, col);
  const checked = c1 === 120 || c1 === 88;
  const prefix = checked
    ? '<input checked="" disabled="" type="checkbox"> '
    : '<input disabled="" type="checkbox"> ';
  return { prefix, rest };
}

// Gather one list item starting at lines[i] (marker info given). Returns
// {item: {content, taskPrefix, blankAfter}, endIdx}. content lines are views
// dedented by W (or verbatim lazy lines); trailing blanks are trimmed and
// reported via blankAfter.
function gatherListItem(lines, i, marker, markerCol) {
  const ln = lines[i];
  const lic = listItemContent(ln, marker, markerCol);
  const W = lic.W;
  const content = [];
  let taskPrefix = '';
  let inPara = false;
  let fence = null;
  let fenceHasContent = false;
  let canLazy = false;
  if (!lic.empty) {
    let cv = lic.content;
    const t = matchTask(cv);
    if (t) { taskPrefix = t.prefix; cv = t.rest; }
    content.push(cv);
    const st = updateParaFence(cv, false, null);
    inPara = st.inPara; fence = st.fence;
    canLazy = contentCanLazy(cv);
  }
  let j = i + 1;
  let afterBlank = false;
  while (j < lines.length) {
    const l2 = lines[j];
    // a blank line after an empty item closes the item
    if (isBlank(l2)) {
      if (content.length === 0) break;
      // if the next non-blank line is not part of this item, leave the blank
      // line(s) for the outer parser (they separate blocks / mark looseness)
      let nk = j + 1;
      while (nk < lines.length && isBlank(lines[nk])) nk++;
      if (nk >= lines.length) break;
      const nf = firstNonSpace(lines[nk]);
      if (nf.col - lineStartCol(lines[nk]) < W) break;
      content.push(l2); afterBlank = true; j++; continue;
    }
    const f = firstNonSpace(l2);
    const col = f.col - lineStartCol(l2);
    const m = listMarker(l2, f.off);
    // a marker at col < W is a new item / new list, unless it is indented >= 4
    if (m && col < W && col <= 3) break;
    // a thematic break at col < W ends the item (it is not a lazy line, and a
    // '-' run there is not a setext underline for the item's paragraph)
    if (col < W && (isThematicBreak(l2, f.off) || setextLevel(l2, f.off) === 2)) break;
    if (col >= W) {
      const dv = cutToCol(l2, lineStartCol(l2) + W);
      content.push(dv);
      const hadFence = fence;
      const st = updateParaFence(dv, inPara, fence);
      inPara = st.inPara; fence = st.fence;
      if (st.fence && hadFence) fenceHasContent = true;
      if (!st.fence) fenceHasContent = false;
      canLazy = contentCanLazy(dv);
      afterBlank = false;
      j++;
      continue;
    }
    // inside a fenced code block that already has content, a content line is
    // part of the item even at col < W (the fence captures it); but when the
    // first line after the opening fence is at col < W, the item ends and
    // the code block is empty
    if (fence && fenceHasContent) {
      content.push(l2);
      const st = updateParaFence(l2, inPara, fence);
      inPara = st.inPara; fence = st.fence;
      if (!st.fence) fenceHasContent = false;
      canLazy = contentCanLazy(l2);
      afterBlank = false;
      j++;
      continue;
    }
    // a lazy line continues the item's paragraph (at any depth, via canLazy),
    // but not across a blank line; it is dedented by 4 when its indent is >= 4
    if (canLazy && !afterBlank && !fence && !startsInterruptingBlock(l2) && !isThematicBreak(l2, f.off)) {
      let base = l2;
      if (f.col - lineStartCol(l2) >= 4) base = removeIndent(l2, 4);
      content.push({ s: base.s, e: base.e, pad: base.pad || 0, col: base.col, nl: base.nl, lazy: true });
      inPara = true;
      afterBlank = false;
      j++;
      continue;
    }
    break;
  }
  let blankAfter = false;
  while (content.length > 0 && isBlank(content[content.length - 1])) {
    content.pop();
    blankAfter = true;
  }
  return { item: { content, taskPrefix, blankAfter }, endIdx: j };
}

function parseList(lines, i, out) {
  const firstLn = lines[i];
  const f0 = firstNonSpace(firstLn);
  const m0 = listMarker(firstLn, f0.off);
  const bullet = m0.bullet;
  const bch = m0.ch;
  const delim = m0.delim;
  const startNum = m0.num;
  const items = [];
  let j = i;
  while (j < lines.length) {
    const ln = lines[j];
    if (isBlank(ln)) break;
    const f = firstNonSpace(ln);
    const m = listMarker(ln, f.off);
    if (!m || m.bullet !== bullet || (bullet && m.ch !== bch) || (!bullet && m.delim !== delim)) break;
    const res = gatherListItem(lines, j, m, f.col);
    items.push(res.item);
    j = res.endIdx;
    // look past blanks for the next item; consume the blanks only when one
    // follows, so a blank before a non-item block stays visible to the outer
    // parser (it separates blocks and marks the enclosing list loose)
    let k = j;
    while (k < lines.length && isBlank(lines[k])) k++;
    if (k >= lines.length) { j = k; break; }
    const ln2 = lines[k];
    const f2 = firstNonSpace(ln2);
    if (isThematicBreak(ln2, f2.off)) break; // a thematic break ends the list
    // a marker indented >= 4 is not a new item (it is indented code / lazy)
    if (f2.col - lineStartCol(ln2) > 3) break;
    const m2 = listMarker(ln2, f2.off);
    if (!m2 || m2.bullet !== bullet || (bullet && m2.ch !== bch) || (!bullet && m2.delim !== delim)) break;
    if (k > j) items[items.length - 1].blankAfter = true;
    j = k;
  }
  // Loose iff a blank line sits between two items, or any item's content has a
  // blank line between two of its blocks. Parse each item once (paragraphs
  // wrapped) to learn the latter; re-parse with unwrapped paragraphs only when
  // the list turns out tight.
  let loose = false;
  for (let x = 0; x + 1 < items.length; x++) if (items[x].blankAfter) loose = true;
  const rendered = [];
  for (const it of items) {
    const tmp = [];
    if (parseBlocksInto(it.content, tmp, false, it.taskPrefix || '', true)) loose = true;
    rendered.push(tmp);
  }
  if (bullet) out.push('<ul>\n');
  else out.push(startNum === 1 ? '<ol>\n' : '<ol start="' + startNum + '">\n');
  for (let x = 0; x < items.length; x++) {
    out.push('<li>');
    if (loose) {
      for (const chunk of rendered[x]) out.push(chunk);
    } else {
      const tmp = [];
      parseBlocksInto(items[x].content, tmp, true, items[x].taskPrefix || '', true);
      for (const chunk of tmp) out.push(chunk);
    }
    out.push('</li>\n');
  }
  out.push(bullet ? '</ul>\n' : '</ol>\n');
  return j;
}

// Parse a paragraph starting at lines[i] (ref defs, setext heading, table or a
// plain paragraph). Returns {end, usedPrefix}.
function parseParagraph(lines, i, out, unwrapParas, prefix, inListItem) {
  const n = lines.length;
  const pLines = [];
  let j = i;
  let setext = 0;
  let table = null;
  let usedPrefix = false;
  while (j < n) {
    const ln = lines[j];
    // a space-only '>'-stripped line continues a paragraph but never starts one
    if (isBlank(ln) && !ln.notBlank) break;
    if (pLines.length === 0) {
      const rd = tryRefDef(lines, j);
      if (rd) {
        if (!REFS.has(rd.label)) REFS.set(rd.label, { href: rd.href, title: rd.title });
        j += rd.linesUsed;
        continue;
      }
    }
    const f = firstNonSpace(ln);
    const indent = f.col - lineStartCol(ln);
    if (pLines.length > 0 && indent <= 3 && !ln.lazy) {
      const sl = setextLevel(ln, f.off);
      if (sl > 0) { setext = sl; j++; break; }
    }
    if (pLines.length > 0 && !ln.lazy) {
      const delimCells = parseTableDelimiter(ln, f.off);
      if (delimCells) {
        const headerCells = splitTableRow(viewText(pLines[pLines.length - 1]));
        if (headerCells.length === delimCells.length) {
          table = { delimIdx: j, headerCells, delimCells };
          break;
        }
      }
    }
    if (!ln.lazy && startsInterruptingBlock(ln, inListItem)) break;
    pLines.push(ln);
    j++;
  }
  if (pLines.length === 0 && !table) return { end: j, usedPrefix: false };
  if (setext > 0) {
    out.push('<h' + setext + '>');
    // a setext heading's content has its leading/trailing whitespace stripped
    // (unlike a paragraph, whose lines are verbatim)
    let text = '';
    for (let k = 0; k < pLines.length; k++) {
      if (k > 0) text += '\n';
      text += viewText(pLines[k]);
    }
    let a = 0, b = text.length;
    while (a < b && (text.charCodeAt(a) === 32 || text.charCodeAt(a) === 9)) a++;
    while (b > a && (text.charCodeAt(b - 1) === 32 || text.charCodeAt(b - 1) === 9)) b--;
    inlineTo(text, a, b, out);
    out.push('</h' + setext + '>\n');
    return { end: j, usedPrefix: false };
  }
  if (table) {
    if (pLines.length > 1) {
      const head = pLines.slice(0, pLines.length - 1);
      if (unwrapParas) {
        if (prefix) { out.push(prefix); usedPrefix = true; prefix = ''; }
        emitInlineLines(head, out);
      } else {
        out.push('<p>');
        if (prefix) { out.push(prefix); usedPrefix = true; prefix = ''; }
        emitInlineLines(head, out);
        out.push('</p>\n');
      }
    }
    const endIdx = emitTable(lines, table, pLines[pLines.length - 1], out, prefix);
    if (prefix) usedPrefix = true;
    return { end: endIdx, usedPrefix };
  }
  if (unwrapParas) {
    if (prefix) { out.push(prefix); usedPrefix = true; prefix = ''; }
    emitInlineLines(pLines, out);
  } else {
    out.push('<p>');
    if (prefix) { out.push(prefix); usedPrefix = true; prefix = ''; }
    emitInlineLines(pLines, out);
    out.push('</p>\n');
  }
  return { end: j, usedPrefix };
}


// ---- ref-def pre-scan (forward references) ----
// Skip a fenced code block starting at lines[i] (fence info given).
function skipFencedCode(lines, i, f) {
  let j = i + 1;
  while (j < lines.length) {
    const cl = lines[j];
    const f2 = firstNonSpace(cl);
    if (f2.col - lineStartCol(cl) <= 3 && fenceClose(cl, f2.off, f.ch, f.len)) { j++; break; }
    j++;
  }
  return j;
}

// Skip an indented code block starting at lines[i].
function skipIndentedCode(lines, i) {
  let j = i;
  while (j < lines.length) {
    const ln = lines[j];
    if (isBlank(ln)) {
      let k = j + 1;
      while (k < lines.length && isBlank(lines[k])) k++;
      if (k < lines.length) {
        const f = firstNonSpace(lines[k]);
        if (f.col - lineStartCol(lines[k]) >= 4) { j = k; continue; }
      }
      break;
    }
    const f = firstNonSpace(ln);
    if (f.col - lineStartCol(ln) < 4) break;
    j++;
  }
  return j;
}

// Skip an HTML block starting at lines[i] (type info given).
function skipHtmlBlock(lines, i, h) {
  let j = i;
  const close = h.close ? h.close.toLowerCase() : null;
  while (j < lines.length) {
    const ln = lines[j];
    const t = viewText(ln);
    j++;
    if (close) {
      if (t.toLowerCase().indexOf(close) >= 0) break;
    } else if (j < lines.length && isBlank(lines[j])) {
      break;
    }
  }
  return j;
}

// Skip a blockquote starting at lines[i].
function skipBlockquote(lines, i) {
  let j = i;
  let inPara = false, fence = null, canLazy = false;
  while (j < lines.length) {
    const ln = lines[j];
    const stripped = stripQuoteMarker(ln);
    if (stripped) {
      const st = updateParaFence(stripped, inPara, fence);
      inPara = st.inPara; fence = st.fence;
      canLazy = contentCanLazy(stripped);
      j++;
      continue;
    }
    if (isBlank(ln)) break;
    const lf = firstNonSpace(ln);
    if (canLazy && !fence && !startsInterruptingBlock(ln) && !isThematicBreak(ln, lf.off)) { inPara = true; j++; continue; }
    break;
  }
  return j;
}

// Skip a list starting at lines[i].
function skipList(lines, i) {
  const firstLn = lines[i];
  const f0 = firstNonSpace(firstLn);
  const m0 = listMarker(firstLn, f0.off);
  if (!m0) return i + 1;
  const bullet = m0.bullet, bch = m0.ch, delim = m0.delim;
  let j = i;
  while (j < lines.length) {
    const ln = lines[j];
    if (isBlank(ln)) break;
    const f = firstNonSpace(ln);
    const m = listMarker(ln, f.off);
    if (!m || m.bullet !== bullet || (!bullet && m.delim !== delim)) break;
    const res = gatherListItem(lines, j, m, f.col);
    j = res.endIdx;
    let k = j;
    while (k < lines.length && isBlank(lines[k])) k++;
    if (k >= lines.length) { j = k; break; }
    const ln2b = lines[k];
    const f2b = firstNonSpace(ln2b);
    if (isThematicBreak(ln2b, f2b.off)) break;
    if (f2b.col - lineStartCol(ln2b) > 3) break;
    const m2b = listMarker(ln2b, f2b.off);
    if (!m2b || m2b.bullet !== bullet || (bullet && m2b.ch !== bch) || (!bullet && m2b.delim !== delim)) break;
    j = k;
    if (j >= lines.length) break;
    const ln2 = lines[j];
    if (isBlank(ln2)) break;
    const f2 = firstNonSpace(ln2);
    if (isThematicBreak(ln2, f2.off)) break;
    if (f2.col - lineStartCol(ln2) > 3) break;
    const m2 = listMarker(ln2, f2.off);
    if (!m2 || m2.bullet !== bullet || (bullet && m2.ch !== bch) || (!bullet && m2.delim !== delim)) break;
  }
  return j;
}

// Skip a paragraph starting at lines[i] (its first line is not a ref def).
function skipParagraph(lines, i) {
  let j = i;
  while (j < lines.length) {
    const ln = lines[j];
    if (isBlank(ln)) break;
    if (j > i) {
      if (startsInterruptingBlock(ln)) break;
      const f = firstNonSpace(ln);
      if (f.col - lineStartCol(ln) <= 3 && setextLevel(ln, f.off) > 0) { j++; break; }
    }
    j++;
  }
  return j;
}

// Collect link reference definitions at this level into REFS before any inline
// rendering, so a definition after its first use still applies (CommonMark
// forward references, e.g. [foo] before '[foo]: /url'). Only definitions at
// paragraph starts count; code, HTML, blockquote and list content is skipped
// here — nested levels collect their own definitions when they are rendered.
function collectRefDefs(lines) {
  let i = 0;
  const n = lines.length;
  while (i < n) {
    const ln = lines[i];
    if (isBlank(ln)) { i++; continue; }
    const f = firstNonSpace(ln);
    const indent = f.col - lineStartCol(ln);
    const c = f.off < ln.e ? SRC.charCodeAt(f.off) : 10;
    if (indent >= 4) { i = skipIndentedCode(lines, i); continue; }
    if (c === 96 || c === 126) {
      const fo = fenceOpen(ln, f.off);
      if (fo) { i = skipFencedCode(lines, i, fo); continue; }
    }
    if (c === 60) {
      const h = htmlBlockType(ln, f.off);
      if (h) { i = skipHtmlBlock(lines, i, h); continue; }
    }
    if (c === 62) {
      const g = gatherBlockquote(lines, i);
      collectRefDefs(g.content);
      i = g.endIdx;
      continue;
    }
    if (c === 35 && parseAtx(ln, f.off)) { i++; continue; }
    if ((c === 42 || c === 45 || c === 95) && isThematicBreak(ln, f.off)) { i++; continue; }
    const lm = listMarker(ln, f.off);
    if (lm) {
      // recurse into each item's content so a def inside a list applies
      let j = i;
      const bullet0 = lm.bullet, ch0 = lm.ch, delim0 = lm.delim;
      while (j < n) {
        const ln2 = lines[j];
        if (isBlank(ln2)) break;
        const f2 = firstNonSpace(ln2);
        const m2 = listMarker(ln2, f2.off);
        if (!m2 || m2.bullet !== bullet0 || (bullet0 && m2.ch !== ch0) || (!bullet0 && m2.delim !== delim0)) break;
        const res = gatherListItem(lines, j, m2, f2.col);
        collectRefDefs(res.item.content);
        j = res.endIdx;
        let k = j;
        while (k < n && isBlank(lines[k])) k++;
        if (k >= n) { j = k; break; }
        const ln3 = lines[k];
        const f3 = firstNonSpace(ln3);
        if (isThematicBreak(ln3, f3.off)) break;
        if (f3.col - lineStartCol(ln3) > 3) break;
        const m3 = listMarker(ln3, f3.off);
        if (!m3 || m3.bullet !== bullet0 || (bullet0 && m3.ch !== ch0) || (!bullet0 && m3.delim !== delim0)) break;
        j = k;
      }
      i = j;
      continue;
    }
    const rd = tryRefDef(lines, i);
    if (rd) {
      if (!REFS.has(rd.label)) REFS.set(rd.label, { href: rd.href, title: rd.title });
      i += rd.linesUsed;
      continue;
    }
    i = skipParagraph(lines, i);
  }
}

// The main block parser. lines = array of line views, out = output chunk array.
// unwrapParas: render paragraphs without <p> tags (tight list items).
// firstPrefix: HTML to prepend to the first paragraph's content (task checkbox).
// Returns true when a blank line separates two blocks in this content.
function parseBlocksInto(lines, out, unwrapParas, firstPrefix, inListItem) {
  collectRefDefs(lines);
  let prefix = firstPrefix || '';
  let i = 0;
  const n = lines.length;
  let alreadyEmitted = false;
  let pendingBlank = false;
  let blankBetween = false;
  const noteEmitted = () => {
    if (pendingBlank && alreadyEmitted) blankBetween = true;
    alreadyEmitted = true;
    pendingBlank = false;
  };
  while (i < n) {
    const ln = lines[i];
    if (isBlank(ln)) { pendingBlank = true; i++; continue; }
    const f = firstNonSpace(ln);
    const indent = f.col - lineStartCol(ln);
    const c = f.off < ln.e ? SRC.charCodeAt(f.off) : 10;
    if (indent >= 4) {
      if (prefix) { out.push(prefix); prefix = ''; }
      i = parseIndentedCode(lines, i, out);
      noteEmitted();
      continue;
    }
    if (c === 35) {
      const atx = parseAtx(ln, f.off);
      if (atx) {
        if (prefix) { out.push(prefix); prefix = ''; }
        out.push('<h' + atx.level + '>');
        inlineTo(SRC, atx.a, atx.b, out);
        out.push('</h' + atx.level + '>\n');
        i++;
        noteEmitted();
        continue;
      }
    }
    if (c === 96 || c === 126) {
      const fo = fenceOpen(ln, f.off);
      if (fo) {
        if (prefix) { out.push(prefix); prefix = ''; }
        i = parseFencedCode(lines, i, fo, out);
        noteEmitted();
        continue;
      }
    }
    if ((c === 42 || c === 45 || c === 95) && isThematicBreak(ln, f.off)) {
      if (prefix) { out.push(prefix); prefix = ''; }
      out.push('<hr>\n');
      i++;
      noteEmitted();
      continue;
    }
    if (c === 60) {
      const h = htmlBlockType(ln, f.off);
      if (h) {
        if (prefix) { out.push(prefix); prefix = ''; }
        i = parseHtmlBlock(lines, i, h, out);
        noteEmitted();
        continue;
      }
    }
    if (c === 62) {
      if (prefix) { out.push(prefix); prefix = ''; }
      i = parseBlockquote(lines, i, out);
      noteEmitted();
      continue;
    }
    const m = listMarker(ln, f.off);
    if (m) {
      if (prefix) { out.push(prefix); prefix = ''; }
      i = parseList(lines, i, out);
      noteEmitted();
      continue;
    }
    const pr = parseParagraph(lines, i, out, unwrapParas, prefix, inListItem);
    if (pr.usedPrefix) prefix = '';
    i = pr.end;
    noteEmitted();
  }
  return blankBetween;
}
