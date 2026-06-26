#!/usr/bin/env python3
"""Normalize .remember/*.md log files to be markdownlint-clean.

The `remember` plugin (Claude Code-specific) emits machine logs whose form
— long-line H2 entries (`## HH:MM | ...`, `## YYYY-MM-DD`), occasional
stray code fences, duplicate H1s, unwrapped prose — does not satisfy
markdownlint's prose rules (line length, heading punctuation/length, single
H1). Since `.remember/` is scanned by the repository-wide markdownlint run,
this normalizer rewrites each file as a single H1 title (from the filename)
followed by:

* marker entries (timestamps, dates, `Week of`) demoted to wrapped
  paragraphs, re-detected by their leading marker on later passes;
* short, punctuation-free non-marker headings kept as H2 section labels;
* list items and prose wrapped to 80 columns.

Logical blocks are grouped by markers and headings rather than by blank
lines, so the pass repairs files whose paragraph breaks were lost to
over-wrapping and is idempotent. These logs hold no real code, so bare
```/~~~ fence lines are dropped rather than entered, which makes content
loss impossible. Empty buffer files are left untouched. All text is
preserved verbatim; only layout changes.

Invoked by `scripts/hooks/clean-remember.sh` (a Claude Code `Stop` hook).
"""
import os
import re
import sys
import textwrap

WIDTH = 80
MARKER = re.compile(r'^(\d{1,2}:\d{2}\b|\d{4}-\d{2}-\d{2}\b|Week of\b)')
FENCE = re.compile(r'^\s*(```+|~~~+)')
HEADING = re.compile(r'^(#{1,6})\s+(.*)$')
LIST = re.compile(r'^\s*[-*]\s+')
PUNCT = '.,;:!?'


def wrap_block(text):
    text = text.rstrip()
    if not text:
        return []
    m = LIST.match(text)
    if m:
        bullet, rest = m.group(0), text[m.end():]
        return textwrap.wrap(rest, width=WIDTH, initial_indent=bullet,
                             subsequent_indent=' ' * len(bullet),
                             break_long_words=False, break_on_hyphens=False) or [text]
    return textwrap.wrap(text, width=WIDTH, break_long_words=False,
                         break_on_hyphens=False) or [text]


def normalize(path):
    with open(path, encoding='utf-8') as f:
        raw = f.read()
    if not raw.strip():
        return  # leave empty buffer files (now.md, remember.md) untouched

    base = os.path.basename(path)[:-3]
    blocks = []   # list of ('para'|'list'|'head', text)
    cur = None    # open (kind, text) accumulating continuation lines

    def flush():
        nonlocal cur
        if cur is not None:
            blocks.append(cur)
            cur = None

    def closed(kind, text):
        flush()
        blocks.append((kind, text))  # block that accepts no continuations

    def is_title(t):
        return not blocks and cur is None and t.strip().lower() == base.lower()

    for ln in raw.split('\n'):
        s = ln.strip()
        if not s or FENCE.match(s):
            continue
        h = HEADING.match(s)
        if h:
            s = h.group(2).strip()  # heading text, level dropped
        if is_title(s):
            continue
        if LIST.match(s):
            flush()
            cur = ('list', s)
        elif MARKER.match(s):
            if ' | ' in s:
                flush()
                cur = ('para', s)          # inline timestamped entry
            else:
                closed('para', s)          # bare date / week label
        elif h:
            if len(s) <= WIDTH - 3 and s[-1] not in PUNCT:
                closed('head', s)          # short section label kept as H2
            else:
                closed('para', s)
        elif cur is None:
            cur = ('para', s)
        else:
            cur = (cur[0], cur[1] + ' ' + s)
    flush()

    out = ['# ' + base]
    prev = None
    for kind, text in blocks:
        if kind == 'head':
            out += ['', '## ' + text]
        else:
            if not (kind == 'list' and prev == 'list'):
                out.append('')
            out += wrap_block(text)
        prev = kind
    new = '\n'.join(out).rstrip('\n') + '\n'
    if new != raw:
        with open(path, 'w', encoding='utf-8') as f:
            f.write(new)


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else '.remember'
    if os.path.isdir(root):
        for name in sorted(os.listdir(root)):
            if name.endswith('.md'):
                normalize(os.path.join(root, name))


if __name__ == '__main__':
    main()
