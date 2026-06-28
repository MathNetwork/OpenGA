#!/usr/bin/env python3
"""
tex2mdx — extract the *mathematical content* of LaTeX source into MDX.

A generic, content-free converter. It keeps the math — sections, theorem-like
environments (theorem/lemma/proposition/corollary/definition/proof/…), and
displayed & inline formulas — and drops LaTeX scaffolding: preamble, packages,
figures/tables, labels, index entries, cross-reference and citation macros, and
comments. Point it at your own .tex files; it ships no content of its own.

Custom macros (e.g. `\def\Ar{\mathbb{R}}`) are NOT expanded into the output.
Instead every math macro definition found in the source (preamble, .sty, .cls,
or chapter bodies) is collected into a `katex-macros.json` next to the docs; the
renderer feeds that table to KaTeX's `macros` option, so the MDX keeps `\Ar` as
written and KaTeX resolves it. Layout/figure-only macros are dropped.

Usage:
  python3 tools/tex2mdx.py INPUT.tex -o OUT.mdx
  python3 tools/tex2mdx.py SRC_DIR  -o DEST_DIR      # batch every *.tex
  python3 tools/tex2mdx.py SRC_DIR  -o DEST_DIR --root booktemplate.tex
        # use the root file's \include/\input order to number the outputs
  # writes <DEST_DIR>/../katex-macros.json  (override with --macros-out)

Best-effort: LaTeX → Markdown is never lossless. Review the output; refine the
rules below for a given source as needed.
"""
import argparse
import json
import os
import re
from pathlib import Path

# theorem-like env name -> display label
THEOREM_ENVS = {
    'theorem': 'Theorem', 'thm': 'Theorem',
    'lemma': 'Lemma', 'lem': 'Lemma',
    'proposition': 'Proposition', 'prop': 'Proposition',
    'corollary': 'Corollary', 'cor': 'Corollary',
    'definition': 'Definition', 'defn': 'Definition', 'defi': 'Definition',
    'claim': 'Claim', 'remark': 'Remark', 'rem': 'Remark',
    'example': 'Example', 'conjecture': 'Conjecture', 'proof': 'Proof',
}

# environments to drop entirely (non-mathematical scaffolding)
DROP_ENVS = ['figure', 'figure*', 'table', 'table*', 'wrapfigure',
             'thebibliography', 'titlepage', 'abstract']

DISPLAY_MATH_ENVS = ['align', 'align*', 'gather', 'gather*',
                     'multline', 'multline*', 'eqnarray', 'eqnarray*',
                     'aligned', 'split']

# old TeX font switches: {\bf x} / {\it x} / ... -> markdown
FONT_SWITCHES = {
    'bf': '**', 'bfseries': '**',
    'it': '*', 'itshape': '*', 'em': '*', 'sl': '*', 'slshape': '*',
    'tt': '`', 'ttfamily': '`',
    'sc': '', 'scshape': '', 'sf': '', 'sffamily': '', 'rm': '', 'rmfamily': '',
}

# a macro whose *body* mentions any of these is layout/figure glue, not math:
# we drop it from the KaTeX macro table (KaTeX can't render it anyway).
LAYOUT_TOKENS = re.compile(
    r'\\(?:marginpar|hbox|vbox|vtop|rlap|llap|smash|kern|raise|lower|moveleft'
    r'|moveright|special|epsf|includegraphics|psfig|relabel|newif|setbox|box'
    r'|vskip|hskip|centerline|halign|valign|parbox|makebox|framebox|rule'
    r'|hfill|vfill|hrule|vrule|noalign|multicolumn|footnote|marginnote)\b'
)


def _balanced(s: str, i: int):
    """Given s[i] == '{', return (inner_text, index_after_closing_brace)."""
    assert s[i] == '{'
    depth, j = 0, i
    while j < len(s):
        c = s[j]
        if c == '\\':            # skip escaped char
            j += 2
            continue
        if c == '{':
            depth += 1
        elif c == '}':
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
        j += 1
    return s[i + 1:], len(s)      # unbalanced: take the rest


def _read_group(s: str, i: int):
    """Read a `{...}` or single-token argument starting at s[i]; skip spaces."""
    while i < len(s) and s[i] in ' \t\n':
        i += 1
    if i < len(s) and s[i] == '{':
        return _balanced(s, i)
    m = re.match(r'\\[A-Za-z]+|.', s[i:])   # a control word or single char
    return (m.group(0), i + m.end()) if m else ('', i)


def collect_macros(texts):
    """Scan LaTeX source(s) for macro definitions -> {r'\\name': body} for KaTeX.

    Handles \\newcommand/\\renewcommand/\\providecommand (with [n] args),
    \\DeclareMathOperator[*], and simple \\def\\name{...} (undelimited #1 params).
    Drops definitions whose body is layout/figure glue.
    """
    macros = {}
    for text in texts:
        text = strip_comments(text)
        # \newcommand{\name}[n][default]{body} | \newcommand\name{body}
        for m in re.finditer(r'\\(?:new|renew|provide)command\*?\s*', text):
            i = m.end()
            if i < len(text) and text[i] == '{':
                name, i = _balanced(text, i)
            else:
                mm = re.match(r'\\[A-Za-z]+', text[i:])
                if not mm:
                    continue
                name, i = mm.group(0), i + mm.end()
            name = name.strip()
            # optional [nargs] and [default] — skip past them
            while i < len(text) and re.match(r'\s*\[', text[i:]):
                i = text.index('[', i)
                i = text.index(']', i) + 1
            while i < len(text) and text[i] in ' \t\n':
                i += 1
            if i >= len(text) or text[i] != '{':
                continue
            body, _ = _balanced(text, i)
            if re.match(r'\\[A-Za-z]+$', name):
                macros[name] = body.strip()
        # \DeclareMathOperator{\name}{text}  ( * -> \operatorname* )
        for m in re.finditer(r'\\DeclareMathOperator(\*?)\s*', text):
            star, i = m.group(1), m.end()
            if i >= len(text) or text[i] != '{':
                continue
            name, i = _balanced(text, i)
            while i < len(text) and text[i] in ' \t\n':
                i += 1
            if i >= len(text) or text[i] != '{':
                continue
            op, _ = _balanced(text, i)
            macros[name.strip()] = f'\\operatorname{star}{{{op.strip()}}}'
        # \def\name{body}  or  \def\name#1#2{body}  (undelimited params only)
        for m in re.finditer(r'\\def\s*(\\[A-Za-z]+|\\.)\s*((?:#\d)*)\s*', text):
            name, params, i = m.group(1), m.group(2), m.end()
            if i >= len(text) or text[i] != '{':
                continue            # delimited/odd param text -> skip
            body, _ = _balanced(text, i)
            if re.match(r'\\[A-Za-z]+$', name):
                macros.setdefault(name, body.strip())  # newcommand wins over \def
    # drop layout glue and self-referential/empty bodies
    return {k: v for k, v in macros.items()
            if v and not LAYOUT_TOKENS.search(v) and v != k}


def convert_font_switches(s: str) -> str:
    """{\\bf x} -> **x**, {\\it x} -> *x*, etc. Balanced over the group, so the
    content may itself contain braces (e.g. inline math `$x_{k}$`) and nested
    switches."""
    names = '|'.join(sorted(FONT_SWITCHES, key=len, reverse=True))
    pat = re.compile(r'\{\\(' + names + r')\b[ \t\n]*')
    out, i = [], 0
    while True:
        m = pat.search(s, i)
        if not m:
            out.append(s[i:])
            break
        out.append(s[i:m.start()])
        kind = m.group(1)
        inner, end = _balanced(s, m.start())          # m.start() is the '{'
        content = convert_font_switches(inner[len('\\' + kind):].strip())
        mark = FONT_SWITCHES[kind]
        out.append(f'{mark}{content}{mark}' if content else '')
        i = end
    return ''.join(out)


def strip_comments(s: str) -> str:
    return re.sub(r'(?<!\\)%.*', '', s)


def keep_document_body(s: str) -> str:
    m = re.search(r'\\begin\{document\}(.*)\\end\{document\}', s, re.S)
    return m.group(1) if m else s  # chapter fragments have no document env


def drop_environments(s: str, names) -> str:
    for n in names:
        s = re.sub(rf'\\begin\{{{re.escape(n)}\}}.*?\\end\{{{re.escape(n)}\}}', '', s, flags=re.S)
    return s


def convert_sections(s: str) -> str:
    s = re.sub(r'\\chapter\*?\{([^}]*)\}', r'\n# \1\n', s)
    s = re.sub(r'\\section\*?\{([^}]*)\}', r'\n## \1\n', s)
    s = re.sub(r'\\subsection\*?\{([^}]*)\}', r'\n### \1\n', s)
    s = re.sub(r'\\subsubsection\*?\{([^}]*)\}', r'\n#### \1\n', s)
    return s


def convert_theoremlike(s: str) -> str:
    for env, label in THEOREM_ENVS.items():
        pat = re.compile(rf'\\begin\{{{env}\*?\}}\s*(?:\[([^\]]*)\])?(.*?)\\end\{{{env}\*?\}}', re.S)

        def repl(m, label=label):
            opt = (m.group(1) or '').strip()
            body = m.group(2).strip()
            head = f'**{label}' + (f' ({opt})' if opt else '') + '.**'
            return f'\n\n{head} {body}\n\n'

        s = pat.sub(repl, s)
    return s


def convert_math(s: str) -> str:
    # \[ ... \]  ->  $$ ... $$
    s = re.sub(r'\\\[(.*?)\\\]', lambda m: f'\n$$\n{m.group(1).strip()}\n$$\n', s, flags=re.S)
    # equation -> $$ ... $$
    s = re.sub(r'\\begin\{equation\*?\}(.*?)\\end\{equation\*?\}',
               lambda m: f'\n$$\n{m.group(1).strip()}\n$$\n', s, flags=re.S)
    # align/gather/... -> $$ \begin{aligned} ... \end{aligned} $$ (KaTeX-friendly)
    for env in DISPLAY_MATH_ENVS:
        s = re.sub(rf'\\begin\{{{re.escape(env)}\}}(.*?)\\end\{{{re.escape(env)}\}}',
                   lambda m: f'\n$$\n\\begin{{aligned}}\n{m.group(1).strip()}\n\\end{{aligned}}\n$$\n',
                   s, flags=re.S)
    # bare TeX display math `$$ ... $$` (incl. ones glued to surrounding text):
    # isolate each onto its own block so remark-math parses it and the dollar
    # pairing of the surrounding prose never breaks. Runs last so it also
    # re-normalizes the `$$` we just emitted above.
    s = re.sub(r'\$\$(.+?)\$\$', lambda m: f'\n\n$$\n{m.group(1).strip()}\n$$\n\n', s, flags=re.S)
    return s


def convert_lists(s: str) -> str:
    """\\begin{enumerate|itemize|description} ... \\item ... -> markdown lists.

    Resolves innermost lists first (so nesting unwinds); each \\item becomes a
    line item. An optional `\\item[label]` keeps the label in bold.
    """
    inner = re.compile(
        r'\\begin\{(enumerate|itemize|description)\}'
        r'((?:(?!\\begin\{(?:enumerate|itemize|description)\}).)*?)'
        r'\\end\{\1\}', re.S)

    def repl(m):
        kind, body = m.group(1), m.group(2)
        marker = '1.' if kind == 'enumerate' else '-'
        items = re.split(r'\\item\b', body)[1:]   # text before first \item dropped
        lines = []
        for it in items:
            it = it.strip()
            mo = re.match(r'\[([^\]]*)\]', it)
            if mo:
                label, rest = mo.group(1).strip(), it[mo.end():].strip()
                lines.append(f'- **{label}** {rest}'.rstrip())
            else:
                lines.append(f'{marker} {it}'.rstrip())
        return '\n\n' + '\n'.join(lines) + '\n\n'

    prev = None
    while prev != s:
        prev = s
        s = inner.sub(repl, s)
    return s


def convert_inline(s: str) -> str:
    s = re.sub(r'\\(?:emph|textit|textsl)\{([^}]*)\}', r'*\1*', s)
    s = re.sub(r'\\textbf\{([^}]*)\}', r'**\1**', s)
    s = re.sub(r'\\texttt\{([^}]*)\}', r'`\1`', s)
    s = re.sub(r'\\textsc\{([^}]*)\}', r'\1', s)
    return s


def drop_macros(s: str) -> str:
    s = re.sub(r'\\label\{[^}]*\}', '', s)
    s = re.sub(r'\\index\{[^}]*\}', '', s)
    s = re.sub(r'\\(?:eqref|ref|pageref|autoref|cref|Cref)\{[^}]*\}', '', s)
    s = re.sub(r'\\cite[tp]?\*?(?:\[[^\]]*\])?\{[^}]*\}', '', s)
    s = re.sub(r'\\(?:maketitle|tableofcontents|newpage|clearpage|bigskip|medskip|smallskip|noindent|par)\b', '', s)
    return s


def strip_definitions(s: str) -> str:
    """Remove macro definitions sitting in the body (chapter fragments have no
    preamble to strip). Balanced over the definition body."""
    out, i = [], 0
    pat = re.compile(r'\\(?:(?:new|renew|provide)command\*?|def|DeclareMathOperator\*?)')
    while True:
        m = pat.search(s, i)
        if not m:
            out.append(s[i:])
            break
        out.append(s[i:m.start()])
        j = m.end()
        # skip name, optional [..] args, then the {body}
        while j < len(s) and s[j] in ' \t\n':
            j += 1
        if j < len(s) and s[j] == '{':            # {\name}
            _, j = _balanced(s, j)
        else:
            mm = re.match(r'\\[A-Za-z]+|\\.|#\d', s[j:])
            j = j + mm.end() if mm else j
        while j < len(s) and re.match(r'\s*(?:\[|#\d|\\[A-Za-z]+)', s[j:]):
            if s[j:].lstrip().startswith('['):
                j = s.index('[', j); j = s.index(']', j) + 1
            else:
                mm = re.match(r'\s*(?:#\d|\\[A-Za-z]+)', s[j:]); j += mm.end()
        while j < len(s) and s[j] in ' \t\n':
            j += 1
        if j < len(s) and s[j] == '{':
            _, j = _balanced(s, j)
        i = j
    return ''.join(out)


def tidy(s: str) -> str:
    s = re.sub(r'[ \t]+\n', '\n', s)
    s = re.sub(r'\n{3,}', '\n\n', s)
    return s.strip() + '\n'


def convert(tex: str) -> str:
    s = strip_comments(tex)
    s = keep_document_body(s)
    s = drop_environments(s, DROP_ENVS)
    s = convert_sections(s)
    s = strip_definitions(s)     # remove any \newcommand/\def in the body
    s = convert_lists(s)         # list envs before math/theorem so \item is gone
    s = convert_math(s)          # math envs before theorem bodies/inline
    s = convert_theoremlike(s)
    s = convert_inline(s)
    s = convert_font_switches(s)  # {\bf ..} -> **..** (outside math)
    s = drop_macros(s)
    return tidy(s)


def chapter_order(root: Path):
    text = strip_comments(root.read_text(encoding='utf-8', errors='replace'))
    names = []
    for m in re.finditer(r'\\(?:include|input)\{([^}]+)\}', text):
        n = m.group(1).strip()
        names.append(n[:-4] if n.endswith('.tex') else n)
    return names


def main():
    ap = argparse.ArgumentParser(description='Extract math content from LaTeX into MDX.')
    ap.add_argument('input', help='a .tex file or a directory of .tex files')
    ap.add_argument('-o', '--out', required=True, help='output .mdx file or directory')
    ap.add_argument('--root', help='root .tex whose \\include order numbers the outputs')
    ap.add_argument('--macros-out', help='where to write the KaTeX macro table '
                    '(default: <out-dir>/../katex-macros.json)')
    args = ap.parse_args()

    inp = Path(os.path.expanduser(args.input))
    out = Path(os.path.expanduser(args.out))

    def write_macros(texts, default_dir: Path):
        macros = collect_macros(texts)
        mpath = Path(os.path.expanduser(args.macros_out)) if args.macros_out \
            else default_dir / 'katex-macros.json'
        mpath.parent.mkdir(parents=True, exist_ok=True)
        mpath.write_text(json.dumps(macros, ensure_ascii=False, indent=2,
                                    sort_keys=True) + '\n', encoding='utf-8')
        print(f'wrote {mpath}  ({len(macros)} macros)')

    if inp.is_file():
        out.parent.mkdir(parents=True, exist_ok=True)
        text = inp.read_text(encoding='utf-8', errors='replace')
        out.write_text(convert(text), encoding='utf-8')
        print(f'wrote {out}')
        write_macros([text], out.parent)
        return

    out.mkdir(parents=True, exist_ok=True)
    # macros can live anywhere in the source tree (preamble, .sty, .cls, chapters)
    src_texts = [p.read_text(encoding='utf-8', errors='replace')
                 for p in sorted(inp.rglob('*.tex')) + sorted(inp.rglob('*.sty'))
                 + sorted(inp.rglob('*.cls'))]
    write_macros(src_texts, out.parent)
    order = []
    if args.root:
        root = inp / args.root
        if root.exists():
            order = chapter_order(root)
    if not order:
        skip = {(args.root or '').replace('.tex', ''), 'epsf', 'booktemplate'}
        order = sorted(p.stem for p in inp.glob('*.tex') if p.stem not in skip)

    n = 0
    for i, name in enumerate(order, 1):
        src = inp / f'{name}.tex'
        if not src.exists():
            print(f'skip (missing): {name}.tex')
            continue
        mdx = convert(src.read_text(encoding='utf-8', errors='replace'))
        dst = out / f'{i:02d}-{name}.mdx'
        dst.write_text(mdx, encoding='utf-8')
        n += 1
        print(f'wrote {dst.name}  ({len(mdx)} chars)')
    print(f'\ndone: {n} files -> {out}')


if __name__ == '__main__':
    main()
