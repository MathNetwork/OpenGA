#!/usr/bin/env python3
"""
tex2mdx — extract the *mathematical content* of LaTeX source into MDX.

A generic, content-free converter. It keeps the math — sections, theorem-like
environments (theorem/lemma/proposition/corollary/definition/proof/…), and
displayed & inline formulas — and drops LaTeX scaffolding: preamble, packages,
figures/tables, labels, index entries, cross-reference and citation macros, and
comments. Point it at your own .tex files; it ships no content of its own.

Usage:
  python3 tools/tex2mdx.py INPUT.tex -o OUT.mdx
  python3 tools/tex2mdx.py SRC_DIR  -o DEST_DIR      # batch every *.tex
  python3 tools/tex2mdx.py SRC_DIR  -o DEST_DIR --root booktemplate.tex
        # use the root file's \include/\input order to number the outputs

Best-effort: LaTeX → Markdown is never lossless. Review the output; refine the
rules below for a given source as needed.
"""
import argparse
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


def tidy(s: str) -> str:
    s = re.sub(r'[ \t]+\n', '\n', s)
    s = re.sub(r'\n{3,}', '\n\n', s)
    return s.strip() + '\n'


def convert(tex: str) -> str:
    s = strip_comments(tex)
    s = keep_document_body(s)
    s = drop_environments(s, DROP_ENVS)
    s = convert_sections(s)
    s = convert_math(s)          # math envs before theorem bodies/inline
    s = convert_theoremlike(s)
    s = convert_inline(s)
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
    args = ap.parse_args()

    inp = Path(os.path.expanduser(args.input))
    out = Path(os.path.expanduser(args.out))

    if inp.is_file():
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(convert(inp.read_text(encoding='utf-8', errors='replace')), encoding='utf-8')
        print(f'wrote {out}')
        return

    out.mkdir(parents=True, exist_ok=True)
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
