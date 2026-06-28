#!/usr/bin/env python3
"""Build the Poincare Challenge Astrolabe store from Morgan--Tian TeX.

This is intentionally project-specific.  The generic ``tex2mdx.py`` is good for
first-pass reading docs, but it drops labels and references.  Here the TeX source
is the authority for statement boundaries and labels; the generated MDX is a
structured source format that can be re-extracted deterministically.

Outputs:
  projects/poincare-conjecture/.astrolabe/docs-src/*.mdx
      readable MDX with ``astrolabe:begin/end`` statement markers
  projects/poincare-conjecture/.astrolabe/docs/*.mdx
      reading docs with ``\\entryblock{hash}``
  projects/poincare-conjecture/.astrolabe/atoms/*.md
  projects/poincare-conjecture/.astrolabe/edges/*.md
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import sys
import tarfile
import tempfile
import unicodedata
import urllib.request
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path

from astrolabe_store import AstrolabeStorage, validate_store
from tex2mdx import (
    collect_macros,
    convert_font_switches,
    convert_inline,
    convert_lists,
    strip_comments,
    strip_definitions,
    tidy,
    _balanced,
)


DEFAULT_PROJECT = Path("projects/poincare-conjecture")
DEFAULT_SRC = Path("/tmp/poincare-arxiv-src")
ARXIV_EPRINT = "https://arxiv.org/e-print/math/0607607"

ENV_SORT = {
    "thm": "theorem",
    "cor": "corollary",
    "lem": "lemma",
    "prop": "proposition",
    "claim": "claim",
    "defn": "definition",
    "exam": "example",
    "conj": "conjecture",
    "ex": "exercise",
    "rem": "remark",
    "assumption": "assumption",
    "addendum": "addendum",
}

SORT_LABEL = {
    "theorem": "Theorem",
    "corollary": "Corollary",
    "lemma": "Lemma",
    "proposition": "Proposition",
    "claim": "Claim",
    "definition": "Definition",
    "example": "Example",
    "conjecture": "Conjecture",
    "exercise": "Exercise",
    "remark": "Remark",
    "assumption": "Assumption",
    "addendum": "Addendum",
}

STATEMENT_ENV_RE = re.compile(
    r"\\begin\{(" + "|".join(re.escape(k) for k in ENV_SORT) + r")\}"
    r"(?:\[([^\]]*)\])?(.*?)\\end\{\1\}",
    re.S,
)
PROOF_RE = re.compile(r"\\begin\{proof\}(.*?)\\end\{proof\}", re.S)
PROOF_TOKEN_RE = re.compile(r"\\(begin|end)\{proof\}")
LABEL_RE = re.compile(r"\\label\{([^{}]+)\}")
REF_RE = re.compile(r"\\(?:ref|eqref)\{([^{}]+)\}")
CITE_RE = re.compile(r"\\cite[tp]?\*?(?:\[[^\]]*\])?\s*\{([^{}]+)\}")
DISPLAY_START_RE = re.compile(r"\$\$|\\\[|\\begin\{(?:equation|eqnarray|align|gather|multline)\*?\}")
DISPLAY_BLOCK_ENVS = ["align", "align*", "gather", "gather*", "multline", "multline*", "eqnarray", "eqnarray*"]
TEXT_MACROS = {
    r"\f1": r"\frac",
    r"\g1": r"\Sigma",
    r"\01": r"\Omega",
    r"\c1": r"\gamma",
    r"\o1": r"\omega",
    r"\d1": r"\delta",
    r"\e1": r"\epsilon",
    r"\l1": r"\Lambda",
    r"\m1": r"\Theta",
    r"\t1": r"\theta",
    r"\v1": r"\varphi",
    r"\w1": r"\wedge",
    r"\lemin": r"\le \min",
    r"\betacos": r"\beta\cos",
    r"\cdotexp": r"\cdot \exp",
    r"\setminusint": r"\setminus \operatorname{int}",
    r"\lbrack": "[",
    r"\rbrack": "]",
}
OUTER_FONT_SWITCHES = {
    "bf": "**",
    "bfseries": "**",
    "it": "*",
    "itshape": "*",
    "em": "*",
    "sl": "*",
    "slshape": "*",
    "tt": "`",
    "ttfamily": "`",
    "sc": "",
    "scshape": "",
    "sf": "",
    "sffamily": "",
    "rm": "",
    "rmfamily": "",
}
GENERATED_SENTINEL = "<!-- generated: tools/poincare_tex_extract.py -->"
LEGACY_GENERATED_DOC_NAMES = {
    "01-intro.mdx",
    "02-prelim.mdx",
    "03-flowbasics.mdx",
    "04-maxprin.mdx",
    "05-converge2.mdx",
    "06-newcompar.mdx",
    "07-newcomp2.mdx",
    "08-noncoll.mdx",
    "09-temp2kappa.mdx",
    "10-bddcurvbdddist.mdx",
    "11-singlimit2.mdx",
    "12-stdsoln.mdx",
    "13-surgery.mdx",
    "14-energy1.mdx",
    "15-canonnbhd.mdx",
}
LOCAL_ANAPHORA_RE = re.compile(
    r"(?i)\b(this|previous|preceding|following)\s+"
    r"(theorem|lemma|proposition|corollary|claim|definition|remark)\b"
)
RESOLVABLE_ANAPHORA_RE = re.compile(
    r"(?i)\b(previous|preceding|following)\s+"
    r"(theorem|lemma|proposition|corollary|claim|definition|remark|example)\b"
)
PROSE_DEPENDENCY_SIGNAL_RE = re.compile(
    r"(?i)\b("
    r"follows? (?:immediately |directly )?from|"
    r"by|from|using|applying|apply|combining|together with|"
    r"in view of|as a consequence of|according to|implies?|"
    r"we conclude|we deduce|we obtain|this proves|completes the proof|"
    r"proved above|established above|leads? (?:immediately )?to"
    r")\b"
)
PROSE_DEPENDENCY_NEGATIVE_RE = re.compile(
    r"(?i)\b("
    r"will|shall|later|below|next|in section|following section|"
    r"chapter|appendix|see|cf\.|compare|recall|called|denote|"
    r"is proved in|are proved in|was proved in|were proved in|"
    r"we prove|we shall prove|will prove"
    r")\b"
)
PROSE_NEXT_STATEMENT_SOURCE_RE = re.compile(
    r"(?i)\b("
    r"the following is|"
    r"following\s+(?:theorem|lemma|proposition|corollary|claim|statement|result)|"
    r"leads? (?:immediately )?to (?:the )?following"
    r")\b"
)
THEOREM_LIKE_SORTS = {"theorem", "lemma", "proposition", "corollary", "claim"}
TERM_STOP_WORDS = {
    "appendix",
    "case",
    "central",
    "chapter",
    "condition",
    "conditions",
    "constant",
    "curvature",
    "definition",
    "direction",
    "domain",
    "equation",
    "equivalent",
    "example",
    "exists",
    "family",
    "flow",
    "function",
    "generate",
    "length",
    "lemma",
    "manifold",
    "metric",
    "minimizing",
    "neighborhood",
    "point",
    "preserves",
    "property",
    "proposition",
    "remark",
    "result",
    "section",
    "set",
    "solution",
    "space",
    "strong",
    "structure",
    "system",
    "theorem",
    "time",
    "within",
}
TERM_STOP_PHRASES = {
    "boundary contained",
    "cap in whose core contains",
    "component",
    "converges in the gromov hausdorff sense",
    "surgery operation at time",
}
TERM_BAD_INTERNAL_WORDS = {
    "contains",
    "converges",
    "satisfies",
}
TERM_SINGLE_ALLOWLIST = {
    "convex",
    "geodesic",
    "neck",
    "soliton",
    "worldline",
}
TERM_BAD_BOUNDARY_WORDS = {
    "a",
    "an",
    "and",
    "at",
    "by",
    "for",
    "from",
    "if",
    "in",
    "is",
    "of",
    "on",
    "or",
    "the",
    "to",
    "with",
}
MAX_DEFINITION_TERM_USES_PER_SOURCE = 3
MAX_DEFINITION_TERM_USES_PER_TERM = 30
SECTION_COMMAND_RE = re.compile(r"\\(section|subsection|subsubsection)\*?\s*")
EDGE_LAYER_METADATA = {
    "explicit": {
        "evidence_type": "tex-reference",
        "confidence": 1.0,
        "review_status": "accepted",
        "inference": "explicit",
        "kind": "reference",
        "scope": "statement-or-proof",
    },
    "proof_containment_dependency": {
        "evidence_type": "proof-contained-theorem-like-statement",
        "confidence": 0.85,
        "review_status": "accepted",
        "inference": "inferred",
        "kind": "dependency",
        "scope": "proof-containment",
    },
    "prose_dependency": {
        "evidence_type": "inferential-prose-reference",
        "confidence": 0.8,
        "review_status": "accepted",
        "inference": "inferred",
        "kind": "dependency",
        "scope": "prose",
    },
    "local_anaphora": {
        "evidence_type": "local-anaphora-reference",
        "confidence": 0.72,
        "review_status": "accepted",
        "inference": "inferred",
        "kind": "dependency",
        "scope": "local-context",
    },
    "definition_term": {
        "evidence_type": "same-chapter-definition-term-match",
        "confidence": 0.45,
        "review_status": "candidate",
        "inference": "weak",
        "kind": "definition-use",
        "scope": "same-chapter-term-match",
    },
    "prose_mention": {
        "evidence_type": "prose-mention-nearest-previous-statement",
        "confidence": 0.35,
        "review_status": "candidate",
        "inference": "weak",
        "kind": "mention",
        "scope": "prose",
    },
    "proof_contains": {
        "evidence_type": "proof-containment",
        "confidence": 0.9,
        "review_status": "accepted",
        "inference": "structural",
        "kind": "containment",
        "scope": "proof",
    },
    "section_sequence": {
        "evidence_type": "section-reading-order-adjacency",
        "confidence": 0.25,
        "review_status": "accepted",
        "inference": "navigational",
        "kind": "sequence",
        "scope": "section",
    },
    "chapter_sequence": {
        "evidence_type": "chapter-reading-order-adjacency",
        "confidence": 0.2,
        "review_status": "accepted",
        "inference": "navigational",
        "kind": "sequence",
        "scope": "chapter",
    },
}


@dataclass
class Statement:
    chapter: int
    segment_key: str
    file_stem: str
    index: int
    env: str
    sort: str
    raw_body: str
    start: int
    end: int
    body_start: int
    body_end: int
    opt_title: str = ""
    labels: list[str] = field(default_factory=list)
    hash: str = ""

    @property
    def mtref(self) -> str:
        return f"{self.chapter}.{self.index}"


@dataclass
class ChapterSegment:
    key: str
    order: int
    chapter: int
    file_stem: str
    title_raw: str
    start: int
    end: int


@dataclass
class ProofSpan:
    file_stem: str
    start: int
    body_start: int
    body_end: int
    end: int
    depth: int
    owner_label: str = ""

    @property
    def body_range(self) -> tuple[int, int]:
        return self.body_start, self.body_end


@dataclass(frozen=True)
class DefinitionTerm:
    term: str
    source: str
    raw_start: int
    raw_end: int


def canon(record: dict) -> str:
    return json.dumps(record, sort_keys=True, ensure_ascii=False)


def norm_label(label: str) -> str:
    """Normalize TeX labels split across source lines."""
    return re.sub(r"\s+", " ", label.strip())


def safe_extract_tar(tf: tarfile.TarFile, dest: Path) -> None:
    """Extract an arXiv tarball without allowing path traversal."""
    root = dest.resolve()
    for member in tf.getmembers():
        target = (root / member.name).resolve()
        if target != root and root not in target.parents:
            raise RuntimeError(f"Refusing to extract unsafe tar member: {member.name}")
    tf.extractall(root)


def ensure_source(src: Path) -> Path:
    """Use an existing source dir, or download/extract arXiv e-print to it."""
    if (src / "booktemplate.tex").exists():
        return src
    src.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(suffix=".tar.gz", delete=False) as tmp:
        tmp_path = Path(tmp.name)
    try:
        print(f"downloading {ARXIV_EPRINT} -> {tmp_path}")
        urllib.request.urlretrieve(ARXIV_EPRINT, tmp_path)
        with tarfile.open(tmp_path, "r:*") as tf:
            safe_extract_tar(tf, src)
    finally:
        try:
            tmp_path.unlink()
        except OSError:
            pass
    if not (src / "booktemplate.tex").exists():
        raise FileNotFoundError(f"booktemplate.tex not found in {src}")
    return src


def include_order(src: Path) -> list[str]:
    root = strip_comments((src / "booktemplate.tex").read_text(encoding="utf-8", errors="replace"))
    return [m.group(1).strip().removesuffix(".tex") for m in re.finditer(r"\\include\{([^{}]+)\}", root)]


def source_texts(src: Path, order: list[str]) -> dict[str, str]:
    return {
        stem: strip_comments((src / f"{stem}.tex").read_text(encoding="utf-8", errors="replace"))
        for stem in order
    }


def read_group_at(s: str, i: int) -> tuple[str, int] | None:
    while i < len(s) and s[i].isspace():
        i += 1
    if i >= len(s) or s[i] != "{":
        return None
    return _balanced(s, i)


def remove_balanced_macro(s: str, name: str, keep: str = "") -> str:
    """Remove ``\name{...}`` occurrences with balanced braces."""
    out: list[str] = []
    i = 0
    pat = re.compile(r"\\" + re.escape(name) + r"\s*")
    while True:
        m = pat.search(s, i)
        if not m:
            out.append(s[i:])
            break
        out.append(s[i:m.start()])
        g = read_group_at(s, m.end())
        if not g:
            out.append(m.group(0))
            i = m.end()
            continue
        body, j = g
        out.append(keep.format(body=body) if keep else "")
        i = j
    return "".join(out)


def chapter_commands(text: str) -> list[tuple[int, int, bool, str]]:
    """Return ``(start, title_end, starred, title_raw)`` for each chapter."""
    found: list[tuple[int, int, bool, str]] = []
    for m in re.finditer(r"\\chapter(\*)?\s*", text):
        g = read_group_at(text, m.end())
        if not g:
            continue
        title, j = g
        found.append((m.start(), j, bool(m.group(1)), title))
    return found


def chapter_segments(texts: dict[str, str], order: list[str]) -> list[ChapterSegment]:
    """Split included files by actual TeX chapter boundaries.

    Morgan--Tian has multi-chapter include files (notably ``prelim`` and
    ``surgery``).  The theorem counter is reset by ``\chapter``, so statement
    identities and reader docs have to follow these boundaries, not filenames.
    """
    segments: list[ChapterSegment] = []
    chapter = 0
    order_index = 0
    for stem in order:
        text = texts[stem]
        commands = chapter_commands(text)
        if not commands:
            continue
        for i, (start, _title_end, starred, title_raw) in enumerate(commands):
            if not starred:
                chapter += 1
            number = 0 if starred and not segments else chapter
            end = commands[i + 1][0] if i + 1 < len(commands) else len(text)
            order_index += 1
            segments.append(
                ChapterSegment(
                    key=f"{stem}:{i}",
                    order=order_index,
                    chapter=number,
                    file_stem=stem,
                    title_raw=title_raw,
                    start=start,
                    end=end,
                )
            )
    return segments


def strip_labels(s: str) -> str:
    return LABEL_RE.sub("", s)


def statement_labels(raw_body: str) -> list[str]:
    """Labels before the first display-math block are statement labels.

    Morgan--Tian often labels equations inside theorem environments.  Those
    labels should stay textual references for now, not edges to the enclosing
    statement.
    """
    first_display = DISPLAY_START_RE.search(raw_body)
    limit = first_display.start() if first_display else len(raw_body)
    return [norm_label(m.group(1)) for m in LABEL_RE.finditer(raw_body) if m.start() <= limit]


def collect_aux_label_texts(texts: dict[str, str], segments: list[ChapterSegment]) -> dict[str, str]:
    """Best-effort labels for refs that are not statement atoms.

    These stay textual on purpose.  Equation/figure/section labels are not atoms
    in this pass, but rendering "Equation (2.7)" is much better than leaking
    "Equation (conemetric)".
    """
    out: dict[str, str] = {}
    for seg in segments:
        text = texts[seg.file_stem][seg.start:seg.end]
        eq_no = 0
        for m in re.finditer(
            r"\\begin\{(equation|eqnarray|align|gather|multline)\*?\}(.*?)\\end\{\1\*?\}",
            text,
            re.S,
        ):
            if "*" in m.group(0).split("}", 1)[0]:
                continue
            eq_no += 1
            for lab in LABEL_RE.findall(m.group(2)):
                out.setdefault(norm_label(lab), f"{seg.chapter}.{eq_no}")

        fig_no = 0
        for m in re.finditer(r"\\begin\{figure\*?\}(.*?)\\end\{figure\*?\}", text, re.S):
            fig_no += 1
            for lab in LABEL_RE.findall(m.group(1)):
                out.setdefault(norm_label(lab), f"{seg.chapter}.{fig_no}")

        section_no = 0
        subsection_no = 0
        section_pat = re.compile(r"\\(section|subsection|subsubsection)\*?\s*")
        for m in section_pat.finditer(text):
            g = read_group_at(text, m.end())
            if not g:
                continue
            _title, j = g
            if m.group(1) == "section":
                section_no += 1
                subsection_no = 0
                number = f"{seg.chapter}.{section_no}"
            elif m.group(1) == "subsection":
                subsection_no += 1
                number = f"{seg.chapter}.{section_no}.{subsection_no}"
            else:
                number = f"{seg.chapter}.{section_no}.{subsection_no}"
            trailer = text[j:j + 160]
            for lab in LABEL_RE.findall(trailer):
                out.setdefault(norm_label(lab), number)

        # Chapter labels usually appear immediately after the chapter command.
        chap = chapter_commands(text)
        if chap:
            trailer = text[chap[0][1]:chap[0][1] + 160]
            for lab in LABEL_RE.findall(trailer):
                out.setdefault(norm_label(lab), str(seg.chapter))
    return out


def clean_citations(s: str) -> str:
    def repl(m: re.Match) -> str:
        keys = ", ".join(k.strip() for k in m.group(1).split(",") if k.strip())
        return f"[{keys}]" if keys else ""

    return CITE_RE.sub(repl, s)


def normalize_title(
    s: str,
    label2hash: dict[str, str] | None = None,
    label2text: dict[str, str] | None = None,
) -> str:
    if label2hash is not None:
        s = linkify_refs(s, label2hash, label2text)
    s = strip_labels(clean_citations(s))
    s = convert_text_inline(s)
    # TeX titles frequently wrap refs in \protect{...}; grouping braces are
    # unsafe in MDX text and add no semantics once refs are converted.
    prev = None
    while prev != s:
        prev = s
        s = re.sub(r"\{(\\entryref\{[0-9a-f]+\})\}", r"\1", s)
    s = re.sub(r"\s+", " ", s)
    return s.strip()


def linkify_refs(
    s: str,
    label2hash: dict[str, str],
    label2text: dict[str, str] | None = None,
) -> str:
    # Consume the common "Kind~\ref{label}" form at once so the rendered link
    # says "Theorem 5.4" rather than "Theorem Theorem 5.4".
    kinds = (
        "Theorem|Lemma|Proposition|Corollary|Claim|Definition|Remark|Example|"
        "Conjecture|Exercise|Assumption|Addendum"
    )
    pat = re.compile(rf"\b({kinds})~?\\(?:ref|eqref)\{{([^{{}}]+)\}}")

    def kind_ref(m: re.Match) -> str:
        lab = norm_label(m.group(2))
        h = label2hash.get(lab)
        if h:
            return f"\\entryref{{{h}}}"
        text = label2text.get(lab) if label2text else None
        return f"{m.group(1)} {text or lab}"

    s = pat.sub(kind_ref, s)

    def bare_ref(m: re.Match) -> str:
        lab = norm_label(m.group(1))
        h = label2hash.get(lab)
        if h:
            return f"\\entryref{{{h}}}"
        text = label2text.get(lab) if label2text else None
        return text or lab

    return REF_RE.sub(bare_ref, s)


def replace_section_commands(
    s: str,
    chapter: int,
    label2hash: dict[str, str] | None = None,
    label2text: dict[str, str] | None = None,
) -> str:
    out: list[str] = []
    i = 0
    pat = re.compile(r"\\(chapter|section|subsection|subsubsection)\*?")
    while True:
        m = pat.search(s, i)
        if not m:
            out.append(s[i:])
            break
        g = read_group_at(s, m.end())
        if not g:
            out.append(s[i:m.end()])
            i = m.end()
            continue
        body, j = g
        out.append(s[i:m.start()])
        title = normalize_title(body, label2hash, label2text)
        cmd = m.group(1)
        if cmd == "chapter":
            out.append(f"\n# Chapter {chapter} -- {title}\n")
        elif cmd == "section":
            out.append(f"\n## {title}\n")
        elif cmd == "subsection":
            out.append(f"\n### {title}\n")
        else:
            out.append(f"\n#### {title}\n")
        i = j
    return "".join(out)


def convert_quote_envs(s: str) -> str:
    def repl(m: re.Match) -> str:
        body = m.group(1).strip()
        return "\n\n" + "\n".join("> " + line for line in body.splitlines()) + "\n\n"

    return re.sub(r"\\begin\{quote\}(.*?)\\end\{quote\}", repl, s, flags=re.S)


def convert_proof_markers(s: str) -> str:
    s = re.sub(r"\\begin\{proof\}\s*", "\n\n**Proof.** ", s)
    return re.sub(r"\\end\{proof\}", "\n\n", s)


def cleanup_display_math_body(body: str) -> str:
    """Normalize old TeX text boxes that contain inline math delimiters."""
    def mbox_math_repl(m: re.Match) -> str:
        prefix = m.group(1)
        math = m.group(2)
        suffix = m.group(3)
        out = ""
        if prefix:
            out += rf"\text{{{prefix}}}"
        out += math
        if suffix:
            out += rf"\text{{{suffix}}}"
        return out

    return re.sub(r"\\mbox\{([^{}$]*?)\$([^$]+)\$([^{}$]*?)\}", mbox_math_repl, body)


def convert_math(s: str) -> str:
    """Convert display math without reprocessing generated aligned blocks."""
    s = re.sub(r"\\\[(.*?)\\\]", lambda m: f"\n$$\n{cleanup_display_math_body(m.group(1).strip())}\n$$\n", s, flags=re.S)
    s = re.sub(
        r"\\begin\{equation\*?\}(.*?)\\end\{equation\*?\}",
        lambda m: f"\n$$\n{cleanup_display_math_body(m.group(1).strip())}\n$$\n",
        s,
        flags=re.S,
    )
    for env in DISPLAY_BLOCK_ENVS:
        s = re.sub(
            rf"\\begin\{{{re.escape(env)}\}}(.*?)\\end\{{{re.escape(env)}\}}",
            lambda m: f"\n$$\n\\begin{{aligned}}\n{cleanup_display_math_body(m.group(1).strip())}\n\\end{{aligned}}\n$$\n",
            s,
            flags=re.S,
        )

    def bare_display(m: re.Match) -> str:
        body = cleanup_display_math_body(m.group(1).strip())
        return f"\n\n$$\n{body}\n$$\n\n" if body else "\n\n"

    return re.sub(r"\$\$(.*?)\$\$", bare_display, s, flags=re.S)


def normalize_markdown_math_boundaries(s: str) -> str:
    s = re.sub(r"(\*\*(?:Theorem|Corollary|Lemma|Proposition|Claim|Definition|Example|Conjecture|Exercise|Remark|Assumption|Addendum)\.?\*\*)\s+\$\$", r"\1\n\n$$", s)
    s = re.sub(r"\$\$\s+(\*\*(?:Theorem|Corollary|Lemma|Proposition|Claim|Definition|Example|Conjecture|Exercise|Remark|Assumption|Addendum)\.?\*\*)", r"$$\n\n\1", s)
    return s


def drop_display_environments(s: str) -> str:
    for n in ["figure", "figure*", "table", "table*", "wrapfigure", "titlepage", "abstract"]:
        s = re.sub(rf"\\begin\{{{re.escape(n)}\}}.*?\\end\{{{re.escape(n)}\}}", "", s, flags=re.S)
    return s


def cleanup_latex_scaffolding(s: str) -> str:
    s = remove_balanced_macro(s, "protect", keep="{body}")
    s = remove_balanced_macro(s, "lefteqn", keep="{body}")
    s = re.sub(r"\\protect\s*", "", s)
    s = re.sub(r"\{(\\entryref\{[0-9a-f]+\})\}", r"\1", s)
    s = re.sub(r"\\(?:maketitle|tableofcontents|newpage|clearpage|bigskip|medskip|smallskip|noindent|par)\b", "", s)
    s = re.sub(r"\\(?:pagestyle|thispagestyle|bibliographystyle|bibliography|includeonly)\{[^{}]*\}", "", s)
    s = re.sub(r"\\(?:printindex|makeindex)\b", "", s)
    # Old TeX spacing commands that should not survive in prose.
    s = re.sub(r"\\[,;:!]\s*", " ", s)
    s = s.replace("~", " ")
    return s


def expand_text_macros(s: str) -> str:
    for old, new in TEXT_MACROS.items():
        s = s.replace(old, new)
    s = re.sub(r"\\root\s+([^\\{}\s]+)\s*\\of\s*\{([^{}]+)\}", r"\\sqrt[\1]{\2}", s)
    return s


def convert_legacy_bold_in_math(s: str) -> str:
    """Convert old TeX font switches inside math to KaTeX-safe commands."""
    def repl(m: re.Match) -> str:
        prefix = m.group(1)
        body = m.group(2).strip()
        if not body:
            return prefix
        cmd = r"\mathbf" if prefix in (r"\bf", r"\textbf") else r"\mathit"
        return f"{cmd}{{{body}}}"

    # Braced forms inside math, e.g. ${\bf t}$.
    s = re.sub(r"\{(\\(?:bf|it|rm|textbf|textit))\s+([^{}]+)\}", repl, s)
    # Simple switch forms up to the next obvious math delimiter.
    s = re.sub(r"\\bf\s+([A-Za-z0-9]+)", r"\\mathbf{\1}", s)
    s = re.sub(r"\\it\s+([A-Za-z0-9]+)", r"\\mathit{\1}", s)
    return re.sub(r"\\rm\s+", "", s)


def math_ranges(s: str) -> list[tuple[int, int]]:
    """Return best-effort markdown math ranges so prose transforms can avoid them."""
    ranges: list[tuple[int, int]] = []
    i = 0
    while i < len(s):
        starts = [(s.find(token, i), token) for token in ("$$", "$") if s.find(token, i) != -1]
        starts = [(pos, token) for pos, token in starts if pos >= 0]
        if not starts:
            break
        pos, token = min(starts, key=lambda item: item[0])
        j = s.find(token, pos + len(token))
        if j == -1:
            break
        ranges.append((pos, j + len(token)))
        i = j + len(token)
    return ranges


def position_in_ranges(pos: int, ranges: list[tuple[int, int]]) -> bool:
    return any(start <= pos < end for start, end in ranges)


def convert_outer_font_switch_groups(s: str) -> str:
    """Convert balanced text font groups that may span inline math."""
    names = "|".join(sorted(OUTER_FONT_SWITCHES, key=len, reverse=True))
    pat = re.compile(r"\{\\(" + names + r")\b[ \t\n]*")
    ranges = math_ranges(s)
    out: list[str] = []
    i = 0
    while True:
        m = pat.search(s, i)
        if not m:
            out.append(s[i:])
            break
        if position_in_ranges(m.start(), ranges):
            out.append(s[i:m.end()])
            i = m.end()
            continue
        out.append(s[i:m.start()])
        kind = m.group(1)
        inner, end = _balanced(s, m.start())
        content = convert_outer_font_switch_groups(inner[len("\\" + kind):].strip())
        mark = OUTER_FONT_SWITCHES[kind]
        out.append(f"{mark}{content}{mark}" if mark and content else content)
        i = end
    return "".join(out)


TEX_ACCENT_COMBINING = {
    "'": "\u0301",
    "`": "\u0300",
    "^": "\u0302",
    "\"": "\u0308",
    "~": "\u0303",
    "=": "\u0304",
    ".": "\u0307",
    "u": "\u0306",
    "v": "\u030c",
    "H": "\u030b",
    "r": "\u030a",
    "c": "\u0327",
    "d": "\u0323",
    "b": "\u0331",
    "k": "\u0328",
}
TEX_ACCENT_RE = re.compile(
    r"\\(?P<accent>['`\"^~=.uvHrcdbk])\s*(?:\{(?P<grouped>\\i|\\j|[A-Za-z])\}|(?P<bare>[A-Za-z]))"
)
PROSE_SYMBOL_MACROS = {
    r"\S": "Section",
    r"\P": "Paragraph",
    r"\LaTeX": "LaTeX",
    r"\TeX": "TeX",
}


def tex_accent_repl(m: re.Match) -> str:
    accent = m.group("accent")
    char = m.group("grouped") or m.group("bare") or ""
    if char == r"\i":
        char = "i"
    elif char == r"\j":
        char = "j"
    mark = TEX_ACCENT_COMBINING.get(accent, "")
    return unicodedata.normalize("NFC", char + mark) if mark else char


def cleanup_prose_tex_commands(s: str) -> str:
    """Clean TeX commands that occur in prose, leaving math spans untouched."""
    s = re.sub(r"`([^`'\n]{1,120})'", r"'\1'", s)
    s = s.replace("``", '"').replace("''", '"')
    s = TEX_ACCENT_RE.sub(tex_accent_repl, s)
    for old, new in PROSE_SYMBOL_MACROS.items():
        s = re.sub(re.escape(old) + r"\b", new, s)
    s = re.sub(r"\\(?:quad|qquad)\b", " ", s)
    s = re.sub(r"\\[ ,;:!]\s*", " ", s)
    return re.sub(r"[ \t]{2,}", " ", s)


def move_footnotes_after_following_font_group(s: str) -> str:
    """Keep inline footnotes from splitting an immediately following font group."""
    out: list[str] = []
    i = 0
    pat = re.compile(r"\\footnote\s*")
    font_pat = re.compile(r"\{\\(" + "|".join(sorted(OUTER_FONT_SWITCHES, key=len, reverse=True)) + r")\b")
    while True:
        m = pat.search(s, i)
        if not m:
            out.append(s[i:])
            break
        g = read_group_at(s, m.end())
        if not g:
            out.append(s[i:m.end()])
            i = m.end()
            continue
        footnote_end = g[1]
        j = footnote_end
        while j < len(s) and s[j].isspace():
            j += 1
        if j < len(s) and s[j] == "{" and font_pat.match(s, j):
            _font_inner, font_end = _balanced(s, j)
            out.append(s[i:m.start()])
            out.append(s[j:font_end])
            out.append(s[m.start():footnote_end])
            i = font_end
            continue
        out.append(s[i:footnote_end])
        i = footnote_end
    return "".join(out)


def split_math_spans(s: str) -> list[tuple[bool, str]]:
    """Best-effort split into math and prose spans for markdown-only transforms."""
    spans: list[tuple[bool, str]] = []
    i = 0
    while i < len(s):
        starts = [(s.find(token, i), token) for token in ("$$", "$") if s.find(token, i) != -1]
        starts = [(pos, token) for pos, token in starts if pos >= 0]
        if not starts:
            spans.append((False, s[i:]))
            break
        pos, token = min(starts, key=lambda item: item[0])
        if pos > i:
            spans.append((False, s[i:pos]))
        j = s.find(token, pos + len(token))
        if j == -1:
            spans.append((False, s[pos:]))
            break
        spans.append((True, s[pos:j + len(token)]))
        i = j + len(token)
    return spans


def convert_text_inline(s: str) -> str:
    s = expand_text_macros(s)
    s = convert_outer_font_switch_groups(s)
    out: list[str] = []
    for is_math, part in split_math_spans(s):
        if is_math:
            out.append(convert_legacy_bold_in_math(part))
        else:
            part = convert_inline(part)
            part = convert_font_switches(part)
            part = re.sub(r"\\(?:em|it|rm|bf)\b\s*", "", part)
            part = cleanup_prose_tex_commands(part)
            out.append(part)
    rendered = "".join(out)
    rendered = re.sub(r"\*\*\s*\*\*", " ", rendered)
    return cleanup_latex_scaffolding(rendered)


def convert_fragment(
    raw: str,
    chapter: int,
    label2hash: dict[str, str],
    label2text: dict[str, str] | None = None,
    *,
    statement: bool = False,
) -> str:
    s = strip_comments(raw)
    s = drop_display_environments(s)
    s = strip_definitions(s)
    s = remove_balanced_macro(s, "label")
    s = remove_balanced_macro(s, "index")
    s = move_footnotes_after_following_font_group(s)
    s = remove_balanced_macro(s, "footnote", keep=" ({body})")
    s = linkify_refs(s, label2hash, label2text)
    s = clean_citations(s)
    if not statement:
        s = replace_section_commands(s, chapter, label2hash, label2text)
        s = convert_proof_markers(s)
    s = convert_quote_envs(s)
    s = convert_lists(s)
    s = convert_math(s)
    # tex2mdx can create empty display wrappers around aligned blocks when the
    # source mixed $$ with old eqnarray syntax; remove the harmless wrappers.
    s = re.sub(r"\$\$\s*\$\$\s*(?=\n\\begin\{aligned\})", "", s, flags=re.S)
    s = convert_text_inline(s)
    s = normalize_markdown_math_boundaries(s)
    s = re.sub(r"\n{3,}", "\n\n", s)
    return tidy(s)


def atom_record(st: Statement, label2text: dict[str, str]) -> dict:
    # Keep atom notes hash-local: embedding target hashes via label2hash would
    # create content-address cycles for mutually referencing statements.  The
    # dependency graph stores those links; generated docs-src prose can still
    # render clickable entryrefs where it is not part of an atom hash.
    notes = convert_fragment(st.raw_body, st.chapter, {}, label2text, statement=True)
    rec = {
        "sort": st.sort,
        "source": "tex",
        "src": "morgan-tian",
        "mtref": st.mtref,
        "chapter": st.chapter,
        "tex_file": st.file_stem,
        "generator": "tools/poincare_tex_extract.py",
        "title": normalize_title(st.opt_title, {}, label2text) if st.opt_title else "",
        "labels": st.labels,
        "notes": notes,
    }
    if st.labels:
        rec["label"] = st.labels[0]
    if not rec["title"]:
        rec.pop("title")
    return rec


def parse_statements(
    texts: dict[str, str],
    segments: list[ChapterSegment],
    storage: AstrolabeStorage,
) -> tuple[dict[str, str], dict[str, str], dict[str, list[Statement]]]:
    label2hash: dict[str, str] = {}
    label2text: dict[str, str] = collect_aux_label_texts(texts, segments)
    by_segment: dict[str, list[Statement]] = {}

    for seg in segments:
        text = texts[seg.file_stem]
        items: list[Statement] = []
        for idx, m in enumerate(STATEMENT_ENV_RE.finditer(text, seg.start, seg.end), 1):
            st = Statement(
                chapter=seg.chapter,
                segment_key=seg.key,
                file_stem=seg.file_stem,
                index=idx,
                env=m.group(1),
                sort=ENV_SORT[m.group(1)],
                opt_title=(m.group(2) or "").strip(),
                raw_body=m.group(3),
                start=m.start(),
                end=m.end(),
                body_start=m.start(3),
                body_end=m.end(3),
                labels=statement_labels(m.group(3)),
            )
            items.append(st)
        by_segment[seg.key] = items
    for items in by_segment.values():
        for st in items:
            for lab in st.labels:
                label2text[lab] = st.mtref
    for items in by_segment.values():
        for st in items:
            rec = atom_record(st, label2text)
            st.hash = storage._compute_hash(["__self__"], canon(rec))
            for lab in st.labels:
                label2hash[lab] = st.hash
    return label2hash, label2text, by_segment


def statements_by_file(
    order: list[str],
    by_segment: dict[str, list[Statement]],
) -> dict[str, list[Statement]]:
    out: dict[str, list[Statement]] = {stem: [] for stem in order}
    for items in by_segment.values():
        for st in items:
            out.setdefault(st.file_stem, []).append(st)
    return {stem: sorted(items, key=lambda st: st.start) for stem, items in out.items()}


def all_statements(by_segment: dict[str, list[Statement]]) -> list[Statement]:
    return [st for items in by_segment.values() for st in items]


def statement_inner_label_owners(by_segment: dict[str, list[Statement]]) -> dict[str, Statement]:
    """Map equation/figure/other labels inside statements back to the statement.

    Statement labels are the leading labels already exposed through
    ``label2hash``.  Later labels usually name equations inside the statement;
    references to those labels are useful dependencies on the enclosing
    statement, but they should not become standalone atoms in this pass.
    """
    owners: dict[str, Statement] = {}
    statement_labels_set = {lab for st in all_statements(by_segment) for lab in st.labels}
    for st in all_statements(by_segment):
        for m in LABEL_RE.finditer(st.raw_body):
            lab = norm_label(m.group(1))
            if lab in statement_labels_set:
                continue
            owners.setdefault(lab, st)
    return owners


def proof_owner_hash(
    proof: ProofSpan,
    statements: list[Statement],
    label2hash: dict[str, str],
) -> str | None:
    owner_hash = label2hash.get(proof.owner_label) if proof.owner_label else None
    if owner_hash:
        return owner_hash
    prev = previous_statement(statements, proof.start)
    return prev.hash if prev else None


def proof_owner_label(raw_body: str) -> str:
    """Return a label from leading proof headings such as ``(Of Lemma~\ref{x})``.

    Only the leading heading counts.  Prose like "For a proof of Theorem ..."
    later in a proof body is a reference, not an owner declaration.
    """
    prefix = raw_body[:500].lstrip()
    prefix = re.sub(r"^\{?\\(?:em|it|rm)\b\s*", "", prefix)
    prefix = prefix.lstrip(" \t\r\n({[")
    pat = re.compile(
        r"(?i)^(?:proof\s+)?of\s+"
        r"(?:(?:the|a)\s+)?"
        r"(?:(?:Theorem|Lemma|Proposition|Corollary|Claim|Definition|Remark|"
        r"Example|Conjecture|Exercise|Assumption|Addendum)\s*)?"
        r"~?\s*(?:\\(?:ref|eqref)\{([^{}]+)\}|\\protect\{\\(?:ref|eqref)\{([^{}]+)\}\})"
    )
    m = pat.search(prefix)
    return norm_label(next((g for g in m.groups() if g), "")) if m else ""


def parse_proof_spans(texts: dict[str, str], order: list[str]) -> dict[str, list[ProofSpan]]:
    """Parse proof environments with a stack so nested proofs stay well scoped."""
    spans: dict[str, list[ProofSpan]] = {stem: [] for stem in order}
    for stem in order:
        stack: list[tuple[int, int, int]] = []
        text = texts[stem]
        for m in PROOF_TOKEN_RE.finditer(text):
            if m.group(1) == "begin":
                stack.append((m.start(), m.end(), len(stack) + 1))
                continue
            if not stack:
                continue
            start, body_start, depth = stack.pop()
            body_end = m.start()
            spans[stem].append(
                ProofSpan(
                    file_stem=stem,
                    start=start,
                    body_start=body_start,
                    body_end=body_end,
                    end=m.end(),
                    depth=depth,
                    owner_label=proof_owner_label(text[body_start:body_end]),
                )
            )
        spans[stem].sort(key=lambda p: p.start)
    return spans


def previous_statement(statements: list[Statement], pos: int) -> Statement | None:
    prev = None
    for st in statements:
        if st.start < pos:
            prev = st
        else:
            break
    return prev


def next_statement(statements: list[Statement], pos: int) -> Statement | None:
    for st in statements:
        if st.start > pos:
            return st
    return None


def statement_at(statements: list[Statement], pos: int) -> Statement | None:
    for st in statements:
        if st.start <= pos < st.end:
            return st
        if st.start > pos:
            break
    return None


def proof_at(proofs: list[ProofSpan], pos: int) -> ProofSpan | None:
    matches = [p for p in proofs if p.body_start <= pos < p.body_end]
    return max(matches, key=lambda p: p.body_start) if matches else None


def nearby_statement_by_sort(
    statements: list[Statement],
    pos: int,
    sort: str,
    *,
    direction: str,
) -> Statement | None:
    if direction == "following":
        for st in statements:
            if st.start > pos and st.sort == sort:
                return st
        return None
    for st in reversed(statements):
        if st.start < pos and st.sort == sort:
            return st
    return None


def reference_sentence(text: str, start: int, end: int) -> str:
    """Small context window for deciding whether a prose ref is inferential."""
    _a, _b, sentence = reference_sentence_span(text, start, end)
    return sentence


def reference_sentence_span(text: str, start: int, end: int) -> tuple[int, int, str]:
    """Return ``(start, end, normalized_text)`` for the sentence around a ref."""
    before = [
        text.rfind("\n\n", 0, start),
        text.rfind(". ", 0, start),
        text.rfind("; ", 0, start),
    ]
    a = max(before)
    a = 0 if a < 0 else a + 1
    after = [
        pos for pos in (
            text.find(". ", end),
            text.find("; ", end),
            text.find("\n\n", end),
        )
        if pos != -1
    ]
    b = min(after) if after else min(len(text), end + 320)
    return a, b, " ".join(text[a:b].split())


def refs_in_fragment(fragment: str, label2hash: dict[str, str]) -> list[str]:
    hashes: list[str] = []
    for lab in REF_RE.findall(fragment):
        h = label2hash.get(norm_label(lab))
        if h and h not in hashes:
            hashes.append(h)
    return hashes


def refs_in_fragment_with_spans(
    fragment: str,
    label2hash: dict[str, str],
    *,
    base_offset: int = 0,
) -> list[dict]:
    refs: list[dict] = []
    for m in REF_RE.finditer(fragment):
        lab = norm_label(m.group(1))
        h = label2hash.get(lab)
        if h:
            refs.append({
                "hash": h,
                "label": lab,
                "start": base_offset + m.start(),
                "end": base_offset + m.end(),
            })
    return refs


def prose_dependency_clause_spans(sentence: str) -> list[tuple[int, int, str]]:
    """Split a context window so inferential refs do not cross sentence boundaries."""
    spans: list[tuple[int, int, str]] = []
    start = 0
    for m in re.finditer(r"(?<=[.!?])\s+(?=[A-Z\\])|;\s+", sentence):
        end = m.start()
        if sentence[start:end].strip():
            spans.append((start, end, sentence[start:end]))
        start = m.end()
    if sentence[start:].strip():
        spans.append((start, len(sentence), sentence[start:]))
    return spans


def normalize_match_text(s: str) -> str:
    s = re.sub(r"\$[^$]*\$", " ", s)
    s = re.sub(r"\\[A-Za-z]+", " ", s)
    s = re.sub(r"[^A-Za-z0-9 -]+", " ", s)
    s = re.sub(r"[-]+", " ", s)
    return re.sub(r"\s+", " ", s).strip().lower()


TERM_HIDDEN_MACROS = {
    "cite",
    "citep",
    "citet",
    "eqref",
    "footnote",
    "index",
    "label",
    "pageref",
    "ref",
}


def skip_optional_bracket(s: str, i: int) -> int:
    while i < len(s) and s[i].isspace():
        i += 1
    if i >= len(s) or s[i] != "[":
        return i
    depth = 0
    while i < len(s):
        if s[i] == "\\":
            i += 2
            continue
        if s[i] == "[":
            depth += 1
        elif s[i] == "]":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return len(s)


def skip_macro_arguments(s: str, i: int) -> int:
    i = skip_optional_bracket(s, i)
    while True:
        while i < len(s) and s[i].isspace():
            i += 1
        if i >= len(s) or s[i] != "{":
            return i
        _inner, i = _balanced(s, i)


def normalize_match_text_with_map(raw: str) -> tuple[str, list[int]]:
    """Normalize raw TeX for term matching, including hidden macro arguments."""
    return normalize_visible_match_text_with_map(raw, skip_hidden_macros=False)


def normalize_visible_match_text_with_map(raw: str, *, skip_hidden_macros: bool = True) -> tuple[str, list[int]]:
    """Normalize visible raw TeX and map normalized chars back to raw offsets."""
    chars: list[str] = []
    positions: list[int] = []

    def emit_space(pos: int) -> None:
        if chars and chars[-1] != " ":
            chars.append(" ")
            positions.append(pos)

    i = 0
    while i < len(raw):
        ch = raw[i]
        if ch == "$":
            j = raw.find("$", i + 1)
            emit_space(i)
            i = len(raw) if j == -1 else j + 1
            continue
        if ch == "\\":
            if i + 1 < len(raw) and raw[i + 1].isalpha():
                command_start = i
                i += 1
                command_name_start = i
                while i < len(raw) and raw[i].isalpha():
                    i += 1
                command = raw[command_name_start:i]
                if skip_hidden_macros and command in TERM_HIDDEN_MACROS:
                    emit_space(command_start)
                    i = skip_macro_arguments(raw, i)
                    continue
                if command in {"quad", "qquad"}:
                    emit_space(command_start)
                    continue
                continue
            i += 1
            if i >= len(raw):
                break
            ch = raw[i]
        if ch.isalnum():
            chars.append(ch.lower())
            positions.append(i)
        else:
            emit_space(i)
        i += 1

    while chars and chars[0] == " ":
        chars.pop(0)
        positions.pop(0)
    while chars and chars[-1] == " ":
        chars.pop()
        positions.pop()
    return "".join(chars), positions


def find_term_span_in_raw(raw: str, term: str) -> tuple[int, int] | None:
    normalized, positions = normalize_visible_match_text_with_map(raw)
    if not normalized:
        return None
    m = term_match_pattern(term).search(normalized)
    if not m:
        return None
    return positions[m.start()], positions[m.end() - 1] + 1


def find_specific_term_span_in_raw(raw: str, term: str, covering_terms: list[str]) -> tuple[int, int] | None:
    normalized, positions = normalize_visible_match_text_with_map(raw)
    if not normalized:
        return None
    covered: list[tuple[int, int]] = []
    for covering_term in covering_terms:
        if covering_term == term:
            continue
        for m in term_match_pattern(covering_term).finditer(normalized):
            covered.append((m.start(), m.end()))
    for m in term_match_pattern(term).finditer(normalized):
        if any(start <= m.start() and m.end() <= end for start, end in covered):
            continue
        return positions[m.start()], positions[m.end() - 1] + 1
    return None


def term_span_record(st: Statement, raw_start: int, raw_end: int) -> dict:
    return absolute_statement_span(st, raw_start, raw_end)


def clean_definition_term(raw: str) -> str:
    term = normalize_match_text(raw)
    words = term.split()
    while words and words[0] in {"a", "an", "the"}:
        words.pop(0)
    while words and words[0] in {"dimensional"}:
        words.pop(0)
    while words and words[-1] in TERM_BAD_BOUNDARY_WORDS:
        words.pop()
    term = " ".join(words)
    if not term:
        return ""
    if len(words) > 6 or sum(ch.isalpha() for ch in term) < 4:
        return ""
    if words[0] in TERM_BAD_BOUNDARY_WORDS or words[-1] in TERM_BAD_BOUNDARY_WORDS:
        return ""
    if any(word in TERM_BAD_INTERNAL_WORDS for word in words):
        return ""
    if len(words) == 1 and words[0] not in TERM_SINGLE_ALLOWLIST:
        return ""
    if term in TERM_STOP_WORDS or term in TERM_STOP_PHRASES:
        return ""
    return term


def definition_terms(st: Statement, label2text: dict[str, str]) -> list[DefinitionTerm]:
    if st.sort != "definition":
        return []
    rendered = convert_fragment(st.raw_body, st.chapter, {}, label2text, statement=True)
    candidates: list[tuple[str, str]] = []
    if st.opt_title:
        candidates.append((normalize_title(st.opt_title, {}, label2text), "title"))
    for m in re.finditer(r"\*([^*]{3,180})\*", rendered[:1800]):
        candidates.append((m.group(1), "italic"))
    plain = normalize_match_text(rendered[:1000])
    fallback_patterns = [
        ("called-if", r"\bis called (?:a|an|the)?\s*([a-z][a-z0-9 ]{3,70})\s+if\b"),
        ("said-to-be-if", r"\bis said to be (?:a|an|the)?\s*([a-z][a-z0-9 ]{3,70})\s+if\b"),
        ("we-call", r"\bwe call [a-z0-9 ]{0,80}? (?:a|an|the)?\s*([a-z][a-z0-9 ]{3,70})"),
    ]
    for source, pat in fallback_patterns:
        candidates.extend((m.group(1), source) for m in re.finditer(pat, plain))

    terms: list[DefinitionTerm] = []
    seen: set[str] = set()
    for candidate, source in candidates:
        term = clean_definition_term(candidate)
        if not term or term in seen:
            continue
        span = find_term_span_in_raw(st.raw_body, term)
        if not span:
            continue
        seen.add(term)
        terms.append(DefinitionTerm(term=term, source=source, raw_start=span[0], raw_end=span[1]))
    return sorted(terms, key=lambda t: (len(t.term.split()), len(t.term)), reverse=True)[:4]


def term_match_pattern(term: str) -> re.Pattern:
    return re.compile(r"(?<![a-z0-9])" + re.escape(term) + r"(?![a-z0-9])")


def explicit_prose_dependency_pairs(
    sentence: str,
    label2hash: dict[str, str],
    *,
    file_stem: str,
    sentence_start: int,
) -> tuple[dict[tuple[str, str], set[str]], dict[tuple[str, str], dict]]:
    """Parse explicit prose patterns where both dependent and dependency are refs."""
    edges: dict[tuple[str, str], set[str]] = {}
    details: dict[tuple[str, str], dict] = {}
    patterns = [
        (
            re.compile(r"\b(?:deduce|derive|obtain|conclude|prove)\b(?P<src>.*?)\bfrom\b(?P<dst>.*)", re.I | re.S),
            "prose-deduce-from",
        ),
        (
            re.compile(r"(?P<src>.*?)\bfollows? (?:immediately |directly )?from\b(?P<dst>.*)", re.I | re.S),
            "prose-follows-from",
        ),
        (
            re.compile(
                r"(?P<src>.*?)\b(?:is|are|was|were) "
                r"(?:an? )?(?:immediate |direct )?consequence of\b(?P<dst>.*)",
                re.I | re.S,
            ),
            "prose-consequence-of",
        ),
    ]
    for clause_start, _clause_end, clause in prose_dependency_clause_spans(sentence):
        for pat, via in patterns:
            m = pat.search(clause)
            if not m:
                continue
            source_refs = refs_in_fragment_with_spans(
                m.group("src"),
                label2hash,
                base_offset=sentence_start + clause_start + m.start("src"),
            )
            target_refs = refs_in_fragment_with_spans(
                m.group("dst"),
                label2hash,
                base_offset=sentence_start + clause_start + m.start("dst"),
            )
            for source_ref in source_refs:
                for target_ref in target_refs:
                    src_hash = source_ref["hash"]
                    dst_hash = target_ref["hash"]
                    if src_hash == dst_hash:
                        continue
                    pair = (src_hash, dst_hash)
                    edges.setdefault(pair, set()).add(via)
                    add_edge_detail(details, pair, "proseTriggers", {
                        "via": [via],
                        "label": target_ref["label"],
                        "sourceLabel": source_ref["label"],
                        "sentence": " ".join(sentence.split()),
                        "sentenceSpan": tex_span_record(file_stem, sentence_start, sentence_start + len(sentence)),
                        "sourceRefSpan": tex_span_record(file_stem, source_ref["start"], source_ref["end"]),
                        "refSpan": tex_span_record(file_stem, target_ref["start"], target_ref["end"]),
                        "sourceStrategy": "refs-in-inferential-sentence",
                    })
    return edges, details


def merge_edge_maps(*maps: dict[tuple[str, str], set[str]]) -> dict[tuple[str, str], set[str]]:
    merged: dict[tuple[str, str], set[str]] = {}
    for edge_map in maps:
        for pair, via_set in edge_map.items():
            merged.setdefault(pair, set()).update(via_set)
    return merged


def edge_map_difference(
    edge_map: dict[tuple[str, str], set[str]],
    existing_pairs: set[tuple[str, str]],
) -> dict[tuple[str, str], set[str]]:
    return {pair: set(via_set) for pair, via_set in edge_map.items() if pair not in existing_pairs}


def detail_map_difference(
    details: dict[tuple[str, str], dict],
    edges: dict[tuple[str, str], set[str]],
) -> dict[tuple[str, str], dict]:
    return {pair: details[pair] for pair in edges if pair in details}


def tex_span_record(file_stem: str, start: int, end: int) -> dict:
    return {
        "file": f"{file_stem}.tex",
        "start": start,
        "end": end,
        "coordinateSpace": "comment-stripped-tex",
        "sourceTransform": "tex2mdx.strip_comments",
    }


def proof_span_record(proof: ProofSpan) -> dict:
    return {
        "file": f"{proof.file_stem}.tex",
        "start": proof.start,
        "bodyStart": proof.body_start,
        "bodyEnd": proof.body_end,
        "end": proof.end,
        "depth": proof.depth,
        "ownerLabel": proof.owner_label,
        "coordinateSpace": "comment-stripped-tex",
        "sourceTransform": "tex2mdx.strip_comments",
    }


def add_edge_detail(
    details: dict[tuple[str, str], dict],
    pair: tuple[str, str],
    key: str,
    value: dict,
) -> None:
    bucket = details.setdefault(pair, {}).setdefault(key, [])
    if value not in bucket:
        bucket.append(value)


def absolute_statement_span(st: Statement, raw_start: int, raw_end: int) -> dict:
    return tex_span_record(st.file_stem, st.body_start + raw_start, st.body_start + raw_end)


def statement_location(st: Statement) -> dict:
    """Compact, stable source pointer for reviewing generated graph edges."""
    return {
        "file": f"{st.file_stem}.tex",
        "chapter": st.chapter,
        "mtref": st.mtref,
        "sort": st.sort,
        "label": st.labels[0] if st.labels else "",
        "span": {
            "start": st.start,
            "end": st.end,
            "coordinateSpace": "comment-stripped-tex",
            "sourceTransform": "tex2mdx.strip_comments",
        },
    }


def edge_metadata_factory(
    by_segment: dict[str, list[Statement]],
    *,
    evidence_type: str,
    confidence: float,
    review_status: str,
    inference: str,
    kind: str,
    scope: str,
    evidence_extra_by_pair: dict[tuple[str, str], dict] | None = None,
):
    """Return per-edge metadata without changing the collector edge-map shape."""
    hash2statement = {st.hash: st for st in all_statements(by_segment)}

    def metadata(src_hash: str, dst_hash: str, via_set: set[str]) -> dict:
        src = hash2statement.get(src_hash)
        dst = hash2statement.get(dst_hash)
        evidence: dict = {
            "type": evidence_type,
            "via": sorted(via_set),
        }
        if evidence_extra_by_pair:
            evidence.update(evidence_extra_by_pair.get((src_hash, dst_hash), {}))
        if src:
            evidence["sourceStatement"] = statement_location(src)
        if dst:
            evidence["targetStatement"] = statement_location(dst)
        return {
            "confidence": confidence,
            "reviewStatus": review_status,
            "inference": inference,
            "kind": kind,
            "scope": scope,
            "evidence": evidence,
        }

    return metadata


def slice_without_ranges(text: str, start: int, end: int, ranges: list[tuple[int, int]]) -> str:
    out: list[str] = []
    cursor = start
    for a, b in sorted(ranges):
        a = max(a, start)
        b = min(b, end)
        if b <= cursor or a >= end:
            continue
        if a > cursor:
            out.append(text[cursor:a])
        cursor = max(cursor, b)
    if cursor < end:
        out.append(text[cursor:end])
    return "".join(out)


def proof_dependency_body(
    text: str,
    proof: ProofSpan,
    statements: list[Statement],
    proof_spans: list[ProofSpan],
) -> str:
    """Proof text with nested statements/proofs removed to avoid double counting."""
    ignored: list[tuple[int, int]] = [
        (st.start, st.end)
        for st in statements
        if proof.body_start <= st.start and st.end <= proof.body_end
    ]
    ignored.extend(
        (child.start, child.end)
        for child in proof_spans
        if proof.start < child.start and child.end <= proof.body_end
    )
    return slice_without_ranges(text, proof.body_start, proof.body_end, ignored)


def write_macros(src: Path, project: Path) -> None:
    ast = project / ".astrolabe"
    texts = [
        p.read_text(encoding="utf-8", errors="replace")
        for p in sorted(src.glob("*.tex")) + sorted(src.glob("*.sty")) + sorted(src.glob("*.cls"))
    ]
    macros = collect_macros(texts)
    (ast / "katex-macros.json").write_text(
        json.dumps(macros, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def purge_old(storage: AstrolabeStorage) -> None:
    def rec(h: str) -> dict:
        try:
            return json.loads(storage.data[h]["record"])
        except Exception:
            return {}

    old_atoms = {
        h for h, e in storage.data.items()
        if len(e["ref"]) == 1 and rec(h).get("src") == "morgan-tian"
    }
    old_edges = {
        h for h, e in storage.data.items()
        if len(e["ref"]) > 1
        and rec(h).get("src") == "morgan-tian"
        and rec(h).get("source") == "tex"
        and (rec(h).get("rel") == "references" or rec(h).get("generator") == "tools/poincare_tex_extract.py")
    }
    foreign_edges = {
        h for h, e in storage.data.items()
        if len(e["ref"]) > 1 and h not in old_edges and any(r in old_atoms for r in e["ref"])
    }
    if foreign_edges:
        sample = ", ".join(sorted(foreign_edges)[:5])
        raise RuntimeError(
            "Refusing to purge Morgan--Tian atoms because non-generated edges "
            f"still reference them: {sample}"
        )
    for h in old_atoms | old_edges:
        storage.data.pop(h, None)


def register_atoms(
    storage: AstrolabeStorage,
    by_segment: dict[str, list[Statement]],
    label2text: dict[str, str],
) -> None:
    for items in by_segment.values():
        for st in items:
            rec = atom_record(st, label2text)
            storage.data[st.hash] = {"ref": [st.hash], "record": canon(rec)}


def collect_dependency_edges(
    texts: dict[str, str],
    order: list[str],
    by_segment: dict[str, list[Statement]],
    label2hash: dict[str, str],
    aux_label2statement: dict[str, Statement] | None = None,
) -> tuple[dict[tuple[str, str], set[str]], dict[tuple[str, str], dict]]:
    edges: dict[tuple[str, str], set[str]] = {}
    details: dict[tuple[str, str], dict] = {}
    aux_label2statement = aux_label2statement or {}
    stmt_by_start = statements_by_file(order, by_segment)
    proof_by_file = parse_proof_spans(texts, order)

    for stem in order:
        text = texts[stem]
        statements = stmt_by_start[stem]
        proofs = proof_by_file[stem]

        for st in statements:
            for m in REF_RE.finditer(st.raw_body):
                lab = norm_label(m.group(1))
                h = label2hash.get(lab)
                via = "statement"
                if not h and lab in aux_label2statement:
                    h = aux_label2statement[lab].hash
                    via = "statement-aux-label-proxy"
                if h and h != st.hash:
                    pair = (st.hash, h)
                    edges.setdefault(pair, set()).add(via)
                    add_edge_detail(details, pair, "refTriggers", {
                        "via": via,
                        "label": lab,
                        "context": "statement",
                        "sourceSpan": absolute_statement_span(st, m.start(), m.end()),
                    })

        # Proof references are dependencies of the proved statement.  Prefer an
        # explicit "Proof of Lemma \ref{...}" heading; otherwise use the nearest
        # preceding statement, matching ordinary TeX theorem/proof layout.
        for proof in proofs:
            owner_hash = proof_owner_hash(proof, statements, label2hash)
            if owner_hash is None:
                continue
            ignored: list[tuple[int, int]] = [
                (st.start, st.end)
                for st in statements
                if proof.body_start <= st.start and st.end <= proof.body_end
            ]
            ignored.extend(
                (child.start, child.end)
                for child in proofs
                if proof.start < child.start and child.end <= proof.body_end
            )
            for m in REF_RE.finditer(text, proof.body_start, proof.body_end):
                if any(a <= m.start() < b for a, b in ignored):
                    continue
                lab = norm_label(m.group(1))
                h = label2hash.get(lab)
                via = "proof"
                if not h and lab in aux_label2statement:
                    h = aux_label2statement[lab].hash
                    via = "proof-aux-label-proxy"
                if h and h != owner_hash:
                    pair = (owner_hash, h)
                    edges.setdefault(pair, set()).add(via)
                    add_edge_detail(details, pair, "refTriggers", {
                        "via": via,
                        "label": lab,
                        "context": "proof",
                        "sourceSpan": tex_span_record(stem, m.start(), m.end()),
                        "proofSpan": proof_span_record(proof),
                    })
    return edges, details


def collect_proof_containment_dependency_edges(
    structural_edges: dict[tuple[str, str], set[str]],
    structural_details: dict[tuple[str, str], dict],
    by_segment: dict[str, list[Statement]],
) -> tuple[dict[tuple[str, str], set[str]], dict[tuple[str, str], dict]]:
    """Semantic dependencies from a theorem to theorem-like statements in its proof."""
    edges: dict[tuple[str, str], set[str]] = {}
    details: dict[tuple[str, str], dict] = {}
    hash2statement = {st.hash: st for st in all_statements(by_segment)}
    for pair in structural_edges:
        _src_hash, dst_hash = pair
        target = hash2statement.get(dst_hash)
        if target and target.sort in THEOREM_LIKE_SORTS:
            edges.setdefault(pair, set()).add("proof-contained-statement")
            if pair in structural_details:
                details[pair] = {
                    "proofSpan": structural_details[pair].get("proofSpan"),
                    "containmentReason": "target theorem-like statement occurs inside source proof",
                }
    return edges, details


def collect_local_anaphora_edges(
    texts: dict[str, str],
    order: list[str],
    by_segment: dict[str, list[Statement]],
    label2hash: dict[str, str],
) -> tuple[dict[tuple[str, str], set[str]], dict[tuple[str, str], dict]]:
    """Resolve local references such as "previous lemma" in proofs/statements."""
    edges: dict[tuple[str, str], set[str]] = {}
    details: dict[tuple[str, str], dict] = {}
    stmt_by_start = statements_by_file(order, by_segment)
    proof_by_file = parse_proof_spans(texts, order)

    for stem in order:
        text = texts[stem]
        statements = stmt_by_start[stem]
        proofs = proof_by_file[stem]
        for m in RESOLVABLE_ANAPHORA_RE.finditer(text):
            direction = m.group(1).lower()
            sort = m.group(2).lower()
            current = statement_at(statements, m.start())
            via = "local-anaphora-statement"
            if current:
                owner_hash = current.hash
                trigger_context = "statement"
                trigger_detail: dict = {}
            else:
                proof = proof_at(proofs, m.start())
                if not proof:
                    continue
                owner_hash = proof_owner_hash(proof, statements, label2hash)
                via = "local-anaphora-proof"
                trigger_context = "proof"
                trigger_detail = {"proofSpan": proof_span_record(proof)}
            if not owner_hash:
                continue
            target = nearby_statement_by_sort(
                statements,
                m.start(),
                sort,
                direction="following" if direction == "following" else "previous",
            )
            if target and target.hash != owner_hash:
                pair = (owner_hash, target.hash)
                edges.setdefault(pair, set()).add(via)
                trigger = {
                    "via": via,
                    "phrase": m.group(0),
                    "direction": direction,
                    "sort": sort,
                    "context": trigger_context,
                    "sourceSpan": tex_span_record(stem, m.start(), m.end()),
                }
                trigger.update(trigger_detail)
                add_edge_detail(details, pair, "anaphoraTriggers", trigger)
    return edges, details


def collect_definition_term_edges(
    by_segment: dict[str, list[Statement]],
    label2text: dict[str, str],
    existing_pairs: set[tuple[str, str]],
) -> tuple[dict[tuple[str, str], set[str]], dict[tuple[str, str], dict]]:
    """Low-confidence same-chapter edges from later term use to definitions."""
    statements = all_statements(by_segment)
    position = {st.hash: i for i, st in enumerate(statements)}
    degree: Counter[str] = Counter()
    for src_hash, dst_hash in existing_pairs:
        degree[src_hash] += 1
        degree[dst_hash] += 1

    definitions = [
        (st, definition_terms(st, label2text))
        for st in statements
        if st.sort == "definition"
    ]
    definitions = [(st, terms) for st, terms in definitions if terms]
    term_owners_by_chapter: dict[tuple[int, str], set[str]] = defaultdict(set)
    for definition, terms in definitions:
        for term in terms:
            term_owners_by_chapter[(definition.chapter, term.term)].add(definition.hash)
    ambiguous_terms = {
        key for key, owners in term_owners_by_chapter.items() if len(owners) > 1
    }
    terms_by_chapter: dict[int, set[str]] = defaultdict(set)
    for definition, terms in definitions:
        for term in terms:
            terms_by_chapter[definition.chapter].add(term.term)
    covering_terms_by_chapter: dict[tuple[int, str], list[str]] = {}
    for chapter, terms in terms_by_chapter.items():
        for term in terms:
            covering_terms_by_chapter[(chapter, term)] = sorted(
                (
                    other for other in terms
                    if other != term and term_match_pattern(term).search(other)
                ),
                key=lambda value: (len(value.split()), len(value)),
                reverse=True,
            )

    edges: dict[tuple[str, str], set[str]] = {}
    evidence_details: dict[tuple[str, str], dict] = {}
    uses_by_source: Counter[str] = Counter()
    uses_by_term: Counter[tuple[str, str]] = Counter()
    for definition, terms in definitions:
        for source in statements:
            if source.hash == definition.hash:
                continue
            if source.chapter != definition.chapter:
                continue
            if position[source.hash] <= position[definition.hash]:
                continue
            if degree[source.hash] > 0 and degree[definition.hash] > 0:
                continue
            if uses_by_source[source.hash] >= MAX_DEFINITION_TERM_USES_PER_SOURCE:
                continue
            for term in terms:
                if (definition.chapter, term.term) in ambiguous_terms:
                    continue
                term_key = (definition.hash, term.term)
                if uses_by_term[term_key] >= MAX_DEFINITION_TERM_USES_PER_TERM:
                    continue
                covering_terms = covering_terms_by_chapter[(definition.chapter, term.term)]
                source_span = find_specific_term_span_in_raw(source.raw_body, term.term, covering_terms)
                if not source_span:
                    continue
                pair = (source.hash, definition.hash)
                if pair in existing_pairs or pair in edges:
                    break
                source_degree = degree[source.hash]
                target_degree = degree[definition.hash]
                edges.setdefault(pair, set()).add(f"definition-term:{term.term}")
                evidence_details[pair] = {
                    "term": term.term,
                    "termSource": term.source,
                    "selectionReason": "semantic-connectivity-backfill",
                    "endpointSemanticDegreeBeforeTermBackfill": {
                        "source": source_degree,
                        "target": target_degree,
                    },
                    "termAmbiguity": "unique-in-chapter",
                    "termSpecificity": (
                        "not-covered-by-longer-defined-term"
                        if covering_terms else "no-longer-defined-term"
                    ),
                    "sourceMatchSpan": term_span_record(source, source_span[0], source_span[1]),
                    "targetTermSpan": term_span_record(definition, term.raw_start, term.raw_end),
                }
                degree[source.hash] += 1
                degree[definition.hash] += 1
                uses_by_source[source.hash] += 1
                uses_by_term[term_key] += 1
                break
    return edges, evidence_details


def collect_structural_edges(
    texts: dict[str, str],
    order: list[str],
    by_segment: dict[str, list[Statement]],
    label2hash: dict[str, str],
) -> tuple[dict[tuple[str, str], set[str]], dict[tuple[str, str], dict]]:
    """Structural containment edges from proof owners to nested statements."""
    edges: dict[tuple[str, str], set[str]] = {}
    details: dict[tuple[str, str], dict] = {}
    stmt_by_start = statements_by_file(order, by_segment)
    proof_by_file = parse_proof_spans(texts, order)
    for stem in order:
        statements = stmt_by_start[stem]
        proofs = proof_by_file[stem]
        for st in statements:
            containers = [
                proof
                for proof in proofs
                if proof.body_start <= st.start and st.end <= proof.body_end
            ]
            if not containers:
                continue
            proof = max(containers, key=lambda p: p.body_start)
            owner_hash = proof_owner_hash(proof, statements, label2hash)
            if owner_hash and owner_hash != st.hash:
                pair = (owner_hash, st.hash)
                edges.setdefault(pair, set()).add("proof-contains")
                details[pair] = {
                    "proofSpan": proof_span_record(proof),
                    "containmentDepth": proof.depth,
                    "targetContainedSpan": tex_span_record(st.file_stem, st.start, st.end),
                }
    return edges, details


def collect_section_sequence_edges(
    texts: dict[str, str],
    order: list[str],
    segments: list[ChapterSegment],
    by_segment: dict[str, list[Statement]],
) -> dict[tuple[str, str], set[str]]:
    """Reading-order structural edges between adjacent statements in each section."""
    edges: dict[tuple[str, str], set[str]] = {}
    stmt_by_start = statements_by_file(order, by_segment)
    for seg in segments:
        text = texts[seg.file_stem]
        cuts: list[int] = [seg.start]
        pos = seg.start
        while True:
            m = SECTION_COMMAND_RE.search(text, pos, seg.end)
            if not m:
                break
            cuts.append(m.start())
            g = read_group_at(text, m.end())
            pos = g[1] if g else m.end()
        cuts = sorted(set(cuts))
        for i, start in enumerate(cuts):
            end = cuts[i + 1] if i + 1 < len(cuts) else seg.end
            local = [
                st for st in stmt_by_start[seg.file_stem]
                if st.segment_key == seg.key and start <= st.start < end
            ]
            for prev, nxt in zip(local, local[1:]):
                if prev.hash != nxt.hash:
                    edges.setdefault((prev.hash, nxt.hash), set()).add("section-sequence")
    return edges


def collect_chapter_sequence_edges(
    by_segment: dict[str, list[Statement]],
) -> dict[tuple[str, str], set[str]]:
    """Reading-order structural edges between adjacent statements in a chapter."""
    edges: dict[tuple[str, str], set[str]] = {}
    for statements in by_segment.values():
        local = sorted(statements, key=lambda st: st.start)
        for prev, nxt in zip(local, local[1:]):
            if prev.hash != nxt.hash:
                edges.setdefault((prev.hash, nxt.hash), set()).add("chapter-sequence")
    return edges


def collect_prose_dependency_edges(
    texts: dict[str, str],
    order: list[str],
    segments: list[ChapterSegment],
    by_segment: dict[str, list[Statement]],
    label2hash: dict[str, str],
) -> tuple[dict[tuple[str, str], set[str]], dict[tuple[str, str], dict]]:
    """Conservative semantic dependencies from inferential prose references."""
    edges: dict[tuple[str, str], set[str]] = {}
    details: dict[tuple[str, str], dict] = {}
    stmt_by_start = statements_by_file(order, by_segment)
    proof_by_file = parse_proof_spans(texts, order)
    segments_by_file: dict[str, list[ChapterSegment]] = defaultdict(list)
    for seg in segments:
        segments_by_file[seg.file_stem].append(seg)

    for stem in order:
        text = texts[stem]
        statements = stmt_by_start[stem]
        ignored = [(st.start, st.end) for st in statements]
        ignored.extend((p.start, p.end) for p in proof_by_file[stem])
        ignored.sort()
        processed_sentences: set[tuple[int, int]] = set()

        for m in REF_RE.finditer(text):
            lab = norm_label(m.group(1))
            dst_hash = label2hash.get(lab)
            if not dst_hash:
                continue
            if any(a <= m.start() < b for a, b in ignored):
                continue
            line_start = text.rfind("\n", 0, m.start()) + 1
            line_end = text.find("\n", m.end())
            line = text[line_start:line_end if line_end != -1 else len(text)]
            if re.search(r"\\(?:chapter|section|subsection|subsubsection)\*?\s*\{", line):
                continue

            sent_start, sent_end, sentence = reference_sentence_span(text, m.start(), m.end())
            sentence_key = (sent_start, sent_end)
            if sentence_key in processed_sentences:
                continue
            processed_sentences.add(sentence_key)

            raw_sentence = text[sent_start:sent_end]
            explicit_pairs, explicit_details = explicit_prose_dependency_pairs(
                raw_sentence,
                label2hash,
                file_stem=stem,
                sentence_start=sent_start,
            )
            edges = merge_edge_maps(edges, explicit_pairs)
            for pair, detail in explicit_details.items():
                for trigger in detail.get("proseTriggers", []):
                    add_edge_detail(details, pair, "proseTriggers", trigger)

            if not PROSE_NEXT_STATEMENT_SOURCE_RE.search(sentence):
                continue
            if not PROSE_DEPENDENCY_SIGNAL_RE.search(sentence):
                continue
            if PROSE_DEPENDENCY_NEGATIVE_RE.search(sentence):
                continue

            seg = next((s for s in segments_by_file[stem] if s.start <= m.start() < s.end), None)
            if not seg:
                continue
            local_statements = [st for st in statements if st.segment_key == seg.key]
            owner = next_statement(local_statements, m.end())
            if not owner or owner.start - m.end() > 1400:
                continue
            for ref_hash in refs_in_fragment(sentence, label2hash):
                if owner.hash != ref_hash:
                    pair = (owner.hash, ref_hash)
                    edges.setdefault(pair, set()).add("prose-dependency-following")
                    add_edge_detail(details, pair, "proseTriggers", {
                        "via": ["prose-dependency-following"],
                        "label": lab,
                        "sentence": sentence,
                        "sentenceSpan": tex_span_record(stem, sent_start, sent_end),
                        "refSpan": tex_span_record(stem, m.start(), m.end()),
                        "sourceStrategy": "following-statement-after-inferential-prose",
                    })
    return edges, details


def collect_prose_mention_edges(
    texts: dict[str, str],
    order: list[str],
    segments: list[ChapterSegment],
    by_segment: dict[str, list[Statement]],
    label2hash: dict[str, str],
) -> tuple[dict[tuple[str, str], set[str]], dict[tuple[str, str], dict]]:
    """Weak prose mention edges attached to the nearest prior statement.

    These are intentionally not semantic dependencies.  They make roadmap and
    expository references discoverable in optional graph layers without changing
    the default dependency graph.
    """
    edges: dict[tuple[str, str], set[str]] = {}
    details: dict[tuple[str, str], dict] = {}
    stmt_by_start = statements_by_file(order, by_segment)
    proof_by_file = parse_proof_spans(texts, order)
    segments_by_file: dict[str, list[ChapterSegment]] = defaultdict(list)
    for seg in segments:
        segments_by_file[seg.file_stem].append(seg)

    for stem in order:
        text = texts[stem]
        statements = stmt_by_start[stem]
        ignored = [(st.start, st.end) for st in statements]
        ignored.extend((p.start, p.end) for p in proof_by_file[stem])
        ignored.sort()

        for m in REF_RE.finditer(text):
            lab = norm_label(m.group(1))
            dst_hash = label2hash.get(lab)
            if not dst_hash:
                continue
            if any(a <= m.start() < b for a, b in ignored):
                continue
            line_start = text.rfind("\n", 0, m.start()) + 1
            line_end = text.find("\n", m.end())
            line = text[line_start:line_end if line_end != -1 else len(text)]
            if re.search(r"\\(?:chapter|section|subsection|subsubsection)\*?\s*\{", line):
                continue

            seg = next((s for s in segments_by_file[stem] if s.start <= m.start() < s.end), None)
            if not seg:
                continue
            local_statements = [st for st in statements if st.segment_key == seg.key]
            owner = previous_statement(local_statements, m.start())
            if owner and owner.hash != dst_hash:
                pair = (owner.hash, dst_hash)
                edges.setdefault(pair, set()).add("prose")
                sent_start, sent_end, sentence = reference_sentence_span(text, m.start(), m.end())
                add_edge_detail(details, pair, "mentionTriggers", {
                    "via": "prose",
                    "label": lab,
                    "sentence": sentence,
                    "sentenceSpan": tex_span_record(stem, sent_start, sent_end),
                    "refSpan": tex_span_record(stem, m.start(), m.end()),
                    "sourceStrategy": "nearest-previous-statement",
                })
    return edges, details


def register_edges(
    storage: AstrolabeStorage,
    edges: dict[tuple[str, str], set[str]],
    *,
    rel: str = "references",
    edge_class: str = "semantic",
    notes: str = "Morgan--Tian cross-reference.",
    extra: dict | None = None,
    per_edge_extra=None,
) -> None:
    for (src_hash, dst_hash), via_set in sorted(edges.items()):
        via = sorted(via_set)
        rec = {
            "sort": "(morgan-tian, morgan-tian)",
            "source": "tex",
            "src": "morgan-tian",
            "rel": rel,
            "edgeClass": edge_class,
            "generator": "tools/poincare_tex_extract.py",
            "via": via,
            "notes": notes,
        }
        if extra:
            rec.update(extra)
        if per_edge_extra:
            rec.update(per_edge_extra(src_hash, dst_hash, via_set))
        record = canon(rec)
        hid = storage._compute_hash([src_hash, dst_hash], record)
        storage.data.setdefault(hid, {"ref": [src_hash, dst_hash], "record": record})


def validate_generated_span(span: object, context: str) -> None:
    if not isinstance(span, dict):
        raise ValueError(f"{context}: missing span")
    if not isinstance(span.get("start"), int) or not isinstance(span.get("end"), int):
        raise ValueError(f"{context}: span start/end must be integers")
    if span["start"] >= span["end"]:
        raise ValueError(f"{context}: span start must be before end")
    if span.get("coordinateSpace") != "comment-stripped-tex":
        raise ValueError(f"{context}: span coordinateSpace must be comment-stripped-tex")
    if span.get("sourceTransform") != "tex2mdx.strip_comments":
        raise ValueError(f"{context}: span sourceTransform must be tex2mdx.strip_comments")


def validate_generated_edge_metadata(data: dict) -> None:
    required = {
        "confidence",
        "edgeClass",
        "evidence",
        "generator",
        "inference",
        "kind",
        "rel",
        "reviewStatus",
        "scope",
        "source",
        "src",
        "via",
    }
    definition_term_required = {
        "endpointSemanticDegreeBeforeTermBackfill",
        "selectionReason",
        "sourceMatchSpan",
        "targetTermSpan",
        "term",
        "termAmbiguity",
        "termSpecificity",
        "termSource",
    }

    def validate_trigger_list(evidence: dict, key: str, span_keys: tuple[str, ...], context: str) -> None:
        triggers = evidence.get(key)
        if not isinstance(triggers, list) or not triggers:
            raise ValueError(f"{context}: missing evidence.{key}")
        for idx, trigger in enumerate(triggers):
            if not isinstance(trigger, dict):
                raise ValueError(f"{context}: evidence.{key}[{idx}] must be a mapping")
            for span_key in span_keys:
                if span_key not in trigger:
                    raise ValueError(f"{context}: missing evidence.{key}[{idx}].{span_key}")
                validate_generated_span(trigger[span_key], f"{context} evidence.{key}[{idx}].{span_key}")

    for h, entry in data.items():
        ref = entry["ref"]
        if len(ref) <= 1:
            continue
        rec = json.loads(entry["record"])
        if rec.get("generator") != "tools/poincare_tex_extract.py":
            continue
        missing = sorted(required - set(rec))
        if missing:
            raise ValueError(f"Generated edge {h}: missing metadata fields {missing}")
        evidence = rec.get("evidence")
        if not isinstance(evidence, dict):
            raise ValueError(f"Generated edge {h}: evidence must be a mapping")
        if evidence.get("via") != rec.get("via"):
            raise ValueError(f"Generated edge {h}: evidence.via and record via differ")
        for side in ("sourceStatement", "targetStatement"):
            statement = evidence.get(side)
            if not isinstance(statement, dict):
                raise ValueError(f"Generated edge {h}: missing evidence.{side}")
            validate_generated_span(statement.get("span"), f"Generated edge {h} evidence.{side}")
        if rec.get("kind") == "definition-use":
            missing_detail = sorted(definition_term_required - set(evidence))
            if missing_detail:
                raise ValueError(
                    f"Generated definition-use edge {h}: missing evidence fields {missing_detail}"
                )
            validate_generated_span(evidence.get("sourceMatchSpan"), f"Generated edge {h} sourceMatchSpan")
            validate_generated_span(evidence.get("targetTermSpan"), f"Generated edge {h} targetTermSpan")
        elif rec.get("kind") == "reference":
            validate_trigger_list(evidence, "refTriggers", ("sourceSpan",), f"Generated edge {h}")
        elif rec.get("kind") == "mention":
            validate_trigger_list(evidence, "mentionTriggers", ("sentenceSpan", "refSpan"), f"Generated edge {h}")
        elif rec.get("kind") == "containment":
            validate_generated_span(evidence.get("proofSpan"), f"Generated edge {h} proofSpan")
            validate_generated_span(evidence.get("targetContainedSpan"), f"Generated edge {h} targetContainedSpan")
        elif rec.get("kind") == "dependency":
            evidence_type = evidence.get("type")
            if evidence_type == "proof-contained-theorem-like-statement":
                validate_generated_span(evidence.get("proofSpan"), f"Generated edge {h} proofSpan")
            elif evidence_type == "local-anaphora-reference":
                validate_trigger_list(evidence, "anaphoraTriggers", ("sourceSpan",), f"Generated edge {h}")
            elif evidence_type == "inferential-prose-reference":
                validate_trigger_list(evidence, "proseTriggers", ("sentenceSpan", "refSpan"), f"Generated edge {h}")


RAW_REF_RESIDUE_RE = re.compile(r"\\(?:label|ref|eqref|cite)\{")
FONT_SWITCH_RESIDUE_RE = re.compile(r"\{\\(?:em|it|sl|bf|rm|tt|sc)\b|\\(?:em|it|sl|bf|rm|tt|sc)\b")
FRAGMENTED_FONT_MATH_RE = re.compile(r"\*[A-Za-z][^*\n]{0,80}\*\$")
TRAILING_FONT_BRACE_RE = re.compile(
    r"\b[A-Za-z][A-Za-z -]{2,80}\}\s+(?:if|is|are|consists|centered|from|in|of)\b"
)
PROSE_TEX_COMMAND_RESIDUE_RE = re.compile(r"\\(?!entryref\{|entryblock\{)[A-Za-z]+\*?\b")


def validate_generated_text_quality(data: dict, project: Path) -> None:
    """Fail fast on TeX residues that break generated MDX/atom readability."""
    texts: list[tuple[str, str]] = []
    for h, entry in data.items():
        if len(entry["ref"]) != 1:
            continue
        rec = json.loads(entry["record"])
        if rec.get("generator") == "tools/poincare_tex_extract.py":
            texts.append((f"atom {h}", rec.get("notes", "")))

    ast = project / ".astrolabe"
    for directory in ("docs-src", "docs"):
        for path in sorted((ast / directory).glob("*.mdx")):
            text = path.read_text(encoding="utf-8")
            if GENERATED_SENTINEL in text:
                texts.append((str(path.relative_to(project)), text))

    for context, text in texts:
        if RAW_REF_RESIDUE_RE.search(text):
            raise ValueError(f"{context}: raw TeX ref/label/cite residue")
        if FRAGMENTED_FONT_MATH_RE.search(text):
            raise ValueError(f"{context}: fragmented font switch around inline math")
        for is_math, part in split_math_spans(text):
            if is_math:
                if part.startswith("$$") and "$" in part[2:-2]:
                    raise ValueError(f"{context}: nested inline dollar in display math")
                continue
            if FONT_SWITCH_RESIDUE_RE.search(part):
                raise ValueError(f"{context}: raw TeX font switch residue")
            if TRAILING_FONT_BRACE_RE.search(part):
                raise ValueError(f"{context}: trailing TeX font group brace residue")
            if PROSE_TEX_COMMAND_RESIDUE_RE.search(part):
                raise ValueError(f"{context}: raw prose TeX command residue")


def isolated_count(hashes: list[str], edges: set[tuple[str, str]]) -> int:
    degree: Counter[str] = Counter()
    for src_hash, dst_hash in edges:
        degree[src_hash] += 1
        degree[dst_hash] += 1
    return sum(1 for h in hashes if degree[h] == 0)


def component_sizes(hashes: list[str], edges: set[tuple[str, str]]) -> list[int]:
    adj: dict[str, set[str]] = defaultdict(set)
    for src_hash, dst_hash in edges:
        adj[src_hash].add(dst_hash)
        adj[dst_hash].add(src_hash)
    seen: set[str] = set()
    sizes: list[int] = []
    for h in hashes:
        if h in seen:
            continue
        stack = [h]
        seen.add(h)
        n = 0
        while stack:
            cur = stack.pop()
            n += 1
            for nxt in adj[cur]:
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
        sizes.append(n)
    return sorted(sizes, reverse=True)


def graph_audit(
    texts: dict[str, str],
    order: list[str],
    by_segment: dict[str, list[Statement]],
    label2hash: dict[str, str],
    label2text: dict[str, str],
    edges: dict[tuple[str, str], set[str]],
    mention_edges: dict[tuple[str, str], set[str]] | None = None,
    structural_edges: dict[tuple[str, str], set[str]] | None = None,
    semantic_edge_layers: dict[str, dict[tuple[str, str], set[str]]] | None = None,
    structural_edge_layers: dict[str, dict[tuple[str, str], set[str]]] | None = None,
) -> dict:
    statements = all_statements(by_segment)
    stmt_hashes = [st.hash for st in statements]
    stmt_hash_set = set(stmt_hashes)
    hash2stmt = {st.hash: st for st in statements}
    stmt_by_start = statements_by_file(order, by_segment)
    proof_by_file = parse_proof_spans(texts, order)
    edge_pairs = set(edges)
    mention_pairs = set(mention_edges or {})
    structural_pairs = set(structural_edges or {})
    semantic_layer_pairs = {
        name: set(layer_edges)
        for name, layer_edges in (semantic_edge_layers or {"semantic": edges}).items()
    }
    structural_layer_pairs = {
        name: set(layer_edges)
        for name, layer_edges in (structural_edge_layers or {"structural": structural_edges or {}}).items()
    }
    explicit_pairs = semantic_layer_pairs.get("explicit", set())
    proof_contains_pairs = structural_layer_pairs.get("proof_contains", structural_pairs)
    section_sequence_pairs = structural_layer_pairs.get("section_sequence", set())
    chapter_sequence_pairs = structural_layer_pairs.get("chapter_sequence", set())
    all_edge_pairs = edge_pairs | mention_pairs | structural_pairs

    degree: Counter[str] = Counter()
    in_degree: Counter[str] = Counter()
    out_degree: Counter[str] = Counter()
    for src_hash, dst_hash in edge_pairs:
        out_degree[src_hash] += 1
        in_degree[dst_hash] += 1
        degree[src_hash] += 1
        degree[dst_hash] += 1

    isolated = [st for st in statements if degree[st.hash] == 0]
    labelled = [st for st in statements if st.labels]
    unlabelled = [st for st in statements if not st.labels]

    via_counts: Counter[str] = Counter()
    via_target_sorts: dict[str, Counter[str]] = defaultdict(Counter)
    for via_set in edges.values():
        via_counts.update(via_set)
    for (_src_hash, dst_hash), via_set in edges.items():
        dst = hash2stmt.get(dst_hash)
        if not dst:
            continue
        for via in via_set:
            via_target_sorts[via][dst.sort] += 1

    semantic_layer_stats: dict[str, dict[str, int]] = {}
    cumulative_pairs: set[tuple[str, str]] = set()
    for name, pairs in semantic_layer_pairs.items():
        cumulative_pairs |= pairs
        semantic_layer_stats[name] = {
            "edges": len(pairs),
            "new_vs_explicit": len(pairs - explicit_pairs) if explicit_pairs else 0,
            "overlap_explicit": len(pairs & explicit_pairs) if explicit_pairs else 0,
            "isolated_cumulative": isolated_count(stmt_hashes, cumulative_pairs),
        }
    structural_layer_stats = {
        name: {
            "edges": len(pairs),
            "new_vs_semantic": len(pairs - edge_pairs),
        }
        for name, pairs in structural_layer_pairs.items()
    }

    statement_label_set = set(label2hash)
    aux_label_set = set(label2text) - statement_label_set
    aux_label_owners = statement_inner_label_owners(by_segment)
    aux_proxy_pairs = {
        pair for pair, via_set in edges.items()
        if any("aux-label-proxy" in via for via in via_set)
    }
    ref_context: Counter[str] = Counter()
    unresolved: Counter[str] = Counter()
    prose_statement_refs: Counter[str] = Counter()
    prose_pairs: set[tuple[str, str]] = set()
    local_anaphora: Counter[str] = Counter()
    nested_statement_hashes: set[str] = set()

    explicit_owner_mismatches: list[dict[str, str]] = []
    proof_spans = [p for spans in proof_by_file.values() for p in spans]
    for proof in proof_spans:
        if not proof.owner_label:
            continue
        owner_hash = label2hash.get(proof.owner_label)
        prev = previous_statement(stmt_by_start[proof.file_stem], proof.start)
        if owner_hash and prev and owner_hash != prev.hash:
            owner = hash2stmt.get(owner_hash)
            explicit_owner_mismatches.append({
                "file": proof.file_stem,
                "owner_label": proof.owner_label,
                "owner": owner.mtref if owner else owner_hash,
                "nearest_previous": prev.mtref,
            })

    for stem in order:
        text = texts[stem]
        statements_in_file = stmt_by_start[stem]
        proofs = proof_by_file[stem]
        for st in statements_in_file:
            if any(p.body_start <= st.start and st.end <= p.body_end for p in proofs):
                nested_statement_hashes.add(st.hash)
        for m in LOCAL_ANAPHORA_RE.finditer(text):
            local_anaphora[f"{m.group(1).lower()} {m.group(2).lower()}"] += 1
        for m in REF_RE.finditer(text):
            pos = m.start()
            lab = norm_label(m.group(1))
            target = "statement" if lab in statement_label_set else "aux" if lab in aux_label_set else "unresolved"
            context = "prose"
            for st in statements_in_file:
                if st.start <= pos < st.end:
                    context = "statement"
                    break
                if st.start > pos:
                    break
            if context == "prose":
                proof = next((p for p in reversed(proofs) if p.body_start <= pos < p.body_end), None)
                if proof:
                    context = "proof"
            ref_context[f"{context}:{target}"] += 1
            if target == "unresolved":
                unresolved[lab] += 1
            if context == "prose" and target == "statement":
                prose_statement_refs[lab] += 1
                prev = previous_statement(statements_in_file, pos)
                dst_hash = label2hash[lab]
                if prev and prev.hash != dst_hash:
                    prose_pairs.add((prev.hash, dst_hash))

    combined_with_prose = edge_pairs | prose_pairs
    combined_with_mentions = edge_pairs | mention_pairs
    sizes = component_sizes(stmt_hashes, edge_pairs)
    all_sizes = component_sizes(stmt_hashes, all_edge_pairs)
    top_connected = sorted(
        statements,
        key=lambda st: degree[st.hash],
        reverse=True,
    )[:10]

    return {
        "statements": len(statements),
        "edges": len(edge_pairs),
        "semantic_edges": len(edge_pairs),
        "prose_mention_edges": len(mention_pairs),
        "structural_edges": len(structural_pairs),
        "semantic_edge_layers": semantic_layer_stats,
        "structural_edge_layers": structural_layer_stats,
        "edge_layer_metadata": EDGE_LAYER_METADATA,
        "all_statement_edges": len(all_edge_pairs),
        "semantic_plus_mentions_edges": len(combined_with_mentions),
        "isolated": len(isolated),
        "isolated_with_explicit_semantic": isolated_count(stmt_hashes, explicit_pairs) if explicit_pairs else len(isolated),
        "isolated_with_mentions": isolated_count(stmt_hashes, combined_with_mentions),
        "isolated_with_all_edge_classes": isolated_count(stmt_hashes, all_edge_pairs),
        "isolated_percent": round(len(isolated) / len(statements), 4) if statements else 0,
        "no_incoming": sum(1 for h in stmt_hashes if in_degree[h] == 0),
        "no_outgoing": sum(1 for h in stmt_hashes if out_degree[h] == 0),
        "sorts": dict(sorted(Counter(st.sort for st in statements).items())),
        "isolated_by_sort": dict(sorted(Counter(st.sort for st in isolated).items())),
        "isolated_by_chapter": dict(sorted(Counter(str(st.chapter) for st in isolated).items(), key=lambda kv: int(kv[0]))),
        "labelled": len(labelled),
        "unlabelled": len(unlabelled),
        "isolated_labelled": sum(1 for st in labelled if degree[st.hash] == 0),
        "isolated_unlabelled": sum(1 for st in unlabelled if degree[st.hash] == 0),
        "components": len(sizes),
        "singleton_components": sum(1 for size in sizes if size == 1),
        "largest_components": sizes[:10],
        "components_all_edge_classes": len(all_sizes),
        "singleton_components_all_edge_classes": sum(1 for size in all_sizes if size == 1),
        "largest_components_all_edge_classes": all_sizes[:10],
        "via_counts": dict(sorted(via_counts.items())),
        "via_target_sorts": {
            via: dict(sorted(counts.items()))
            for via, counts in sorted(via_target_sorts.items())
        },
        "proof_spans": len(proof_spans),
        "proof_max_depth": max((p.depth for p in proof_spans), default=0),
        "explicit_proof_owners": sum(1 for p in proof_spans if p.owner_label),
        "explicit_owner_mismatches": explicit_owner_mismatches[:20],
        "explicit_owner_mismatch_count": len(explicit_owner_mismatches),
        "nested_statement_count": len(nested_statement_hashes),
        "nested_statement_isolated_semantic": sum(1 for h in nested_statement_hashes if degree[h] == 0),
        "nested_contains_edges": len(proof_contains_pairs),
        "section_sequence_edges": len(section_sequence_pairs),
        "chapter_sequence_edges": len(chapter_sequence_pairs),
        "inner_label_owner_count": len(aux_label_owners),
        "aux_label_proxy_edges": len(aux_proxy_pairs),
        "ref_context": dict(sorted(ref_context.items())),
        "unresolved_refs": dict(unresolved.most_common(20)),
        "prose_statement_refs": sum(prose_statement_refs.values()),
        "top_prose_statement_refs": dict(prose_statement_refs.most_common(20)),
        "simulated_prose_new_pairs": len(prose_pairs - edge_pairs),
        "simulated_isolated_with_prose": isolated_count(stmt_hashes, combined_with_prose),
        "local_anaphora_hits": sum(local_anaphora.values()),
        "local_anaphora": dict(local_anaphora.most_common(20)),
        "top_connected": [
            {
                "degree": degree[st.hash],
                "sort": st.sort,
                "mtref": st.mtref,
                "label": st.labels[0] if st.labels else "",
                "title": normalize_title(st.opt_title, {}, label2text) if st.opt_title else "",
            }
            for st in top_connected
            if st.hash in stmt_hash_set
        ],
    }


def slugify_title(
    title_raw: str,
    fallback: str,
    label2hash: dict[str, str] | None = None,
    label2text: dict[str, str] | None = None,
) -> str:
    title = normalize_title(title_raw, label2hash, label2text)
    title = re.sub(r"\\entryref\{[0-9a-f]+\}", "", title)
    title = re.sub(r"\\(?:ref|eqref)\{[^{}]*\}", "", title)
    title = re.sub(r"\\([A-Za-z]+)", r"\1", title)
    title = re.sub(r"[$\\{}]", " ", title)
    slug = re.sub(r"[^A-Za-z0-9]+", "-", title).strip("-").lower()
    return slug[:72].strip("-") or fallback


def is_generated_doc(path: Path) -> bool:
    try:
        sample = path.read_text(encoding="utf-8", errors="replace")[:4096]
    except OSError:
        return False
    return GENERATED_SENTINEL in sample


def is_legacy_generated_doc(path: Path) -> bool:
    """Legacy first-pass Poincare docs predate the generator sentinel."""
    return path.name in LEGACY_GENERATED_DOC_NAMES


def marker_attr(value: str) -> str:
    return (
        value.replace("&", "&amp;")
        .replace('"', "&quot;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace("--", "- -")
    )


def generate_docs(
    texts: dict[str, str],
    project: Path,
    segments: list[ChapterSegment],
    by_segment: dict[str, list[Statement]],
    label2hash: dict[str, str],
    label2text: dict[str, str],
) -> None:
    ast = project / ".astrolabe"
    docs_src_dir = ast / "docs-src"
    docs_dir = ast / "docs"
    docs_src_dir.mkdir(parents=True, exist_ok=True)
    docs_dir.mkdir(parents=True, exist_ok=True)

    # Preserve the project index; all numbered chapter docs are regenerated.
    for d in (docs_src_dir, docs_dir):
        for p in d.glob("[0-9][0-9]-*.mdx"):
            if p.name != "00-index.mdx":
                if not is_generated_doc(p) and not is_legacy_generated_doc(p):
                    raise RuntimeError(f"Refusing to overwrite non-generated doc: {p}")
                p.unlink()

    for seg in segments:
        text = texts[seg.file_stem]
        items = by_segment[seg.key]
        src_out: list[str] = [GENERATED_SENTINEL + "\n\n"]
        doc_out: list[str] = [GENERATED_SENTINEL + "\n\n"]
        last = seg.start

        for st in items:
            before = convert_fragment(text[last:st.start], seg.chapter, label2hash, label2text)
            src_out.append(before)
            doc_out.append(before)

            label_attr = st.labels[0] if st.labels else ""
            title_attr = normalize_title(st.opt_title, label2hash, label2text) if st.opt_title else ""
            attrs = [
                f'kind="{st.sort}"',
                'src="morgan-tian"',
                f'mtref="{st.mtref}"',
            ]
            if label_attr:
                attrs.append(f'label="{marker_attr(label_attr)}"')
            if title_attr:
                attrs.append(f'title="{marker_attr(title_attr)}"')
            body = convert_fragment(st.raw_body, seg.chapter, label2hash, label2text, statement=True)
            head_sep = "\n\n" if body.lstrip().startswith("$$") else " "
            src_out.append(
                "\n"
                f"<!-- astrolabe:begin {' '.join(attrs)} -->\n"
                f"**{SORT_LABEL[st.sort]}.**{head_sep}{body}"
                "<!-- astrolabe:end -->\n\n"
            )
            doc_out.append(f"\n\\entryblock{{{st.hash}}}\n\n")
            last = st.end

        tail = convert_fragment(text[last:seg.end], seg.chapter, label2hash, label2text)
        src_out.append(tail)
        doc_out.append(tail)

        filename = f"{seg.order:02d}-{slugify_title(seg.title_raw, seg.file_stem, label2hash, label2text)}.mdx"
        docs_src_dir.joinpath(filename).write_text(tidy("".join(src_out)), encoding="utf-8")
        docs_dir.joinpath(filename).write_text(tidy("".join(doc_out)), encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("src", nargs="?", default=str(DEFAULT_SRC), help="Morgan--Tian arXiv source directory")
    ap.add_argument("--project", default=str(DEFAULT_PROJECT), help="project directory")
    ap.add_argument("--report", action="store_true", help="print a graph extraction audit")
    ap.add_argument("--report-json", default="", help="write the graph extraction audit to this JSON file")
    args = ap.parse_args()

    src = ensure_source(Path(os.path.expanduser(args.src)).resolve())
    project = Path(args.project).resolve()
    storage = AstrolabeStorage(str(project))
    order = include_order(src)
    texts = source_texts(src, order)
    segments = chapter_segments(texts, order)

    purge_old(storage)
    label2hash, label2text, by_segment = parse_statements(texts, segments, storage)
    register_atoms(storage, by_segment, label2text)
    aux_label2statement = statement_inner_label_owners(by_segment)
    explicit_edges, explicit_details = collect_dependency_edges(texts, order, by_segment, label2hash, aux_label2statement)
    proof_structural_edges, proof_structural_details = collect_structural_edges(texts, order, by_segment, label2hash)
    proof_dependency_candidates, proof_dependency_details = collect_proof_containment_dependency_edges(
        proof_structural_edges,
        proof_structural_details,
        by_segment,
    )
    proof_dependency_edges = edge_map_difference(proof_dependency_candidates, set(explicit_edges))
    proof_dependency_details = detail_map_difference(proof_dependency_details, proof_dependency_edges)
    semantic_so_far = merge_edge_maps(explicit_edges, proof_dependency_edges)
    prose_dependency_candidates, prose_dependency_details = collect_prose_dependency_edges(texts, order, segments, by_segment, label2hash)
    prose_dependency_edges = edge_map_difference(prose_dependency_candidates, set(semantic_so_far))
    prose_dependency_details = detail_map_difference(prose_dependency_details, prose_dependency_edges)
    semantic_so_far = merge_edge_maps(semantic_so_far, prose_dependency_edges)
    anaphora_candidates, anaphora_details = collect_local_anaphora_edges(texts, order, by_segment, label2hash)
    anaphora_edges = edge_map_difference(anaphora_candidates, set(semantic_so_far))
    anaphora_details = detail_map_difference(anaphora_details, anaphora_edges)
    edges = merge_edge_maps(semantic_so_far, anaphora_edges)
    definition_term_candidates, definition_term_details = collect_definition_term_edges(by_segment, label2text, set(edges))
    definition_term_edges = edge_map_difference(definition_term_candidates, set(edges))
    definition_term_details = {
        pair: detail for pair, detail in definition_term_details.items()
        if pair in definition_term_edges
    }
    edges = merge_edge_maps(edges, definition_term_edges)
    prose_edges, prose_details = collect_prose_mention_edges(texts, order, segments, by_segment, label2hash)
    section_sequence_edges = collect_section_sequence_edges(texts, order, segments, by_segment)
    chapter_sequence_edges = edge_map_difference(
        collect_chapter_sequence_edges(by_segment),
        set(section_sequence_edges),
    )
    structural_edges = merge_edge_maps(proof_structural_edges, section_sequence_edges, chapter_sequence_edges)

    def edge_meta(layer: str):
        return edge_metadata_factory(by_segment, **EDGE_LAYER_METADATA[layer])

    explicit_meta = edge_metadata_factory(
        by_segment,
        **EDGE_LAYER_METADATA["explicit"],
        evidence_extra_by_pair=explicit_details,
    )
    proof_dependency_meta = edge_metadata_factory(
        by_segment,
        **EDGE_LAYER_METADATA["proof_containment_dependency"],
        evidence_extra_by_pair=proof_dependency_details,
    )
    prose_dependency_meta = edge_metadata_factory(
        by_segment,
        **EDGE_LAYER_METADATA["prose_dependency"],
        evidence_extra_by_pair=prose_dependency_details,
    )
    anaphora_meta = edge_metadata_factory(
        by_segment,
        **EDGE_LAYER_METADATA["local_anaphora"],
        evidence_extra_by_pair=anaphora_details,
    )
    definition_term_meta = edge_metadata_factory(
        by_segment,
        **EDGE_LAYER_METADATA["definition_term"],
        evidence_extra_by_pair=definition_term_details,
    )
    prose_mention_meta = edge_metadata_factory(
        by_segment,
        **EDGE_LAYER_METADATA["prose_mention"],
        evidence_extra_by_pair=prose_details,
    )
    proof_structural_meta = edge_metadata_factory(
        by_segment,
        **EDGE_LAYER_METADATA["proof_contains"],
        evidence_extra_by_pair=proof_structural_details,
    )
    section_sequence_meta = edge_meta("section_sequence")
    chapter_sequence_meta = edge_meta("chapter_sequence")
    register_edges(storage, explicit_edges, per_edge_extra=explicit_meta)
    register_edges(
        storage,
        proof_dependency_edges,
        rel="depends",
        edge_class="semantic",
        notes="Morgan--Tian proof-contained statement dependency.",
        per_edge_extra=proof_dependency_meta,
    )
    register_edges(
        storage,
        prose_dependency_edges,
        rel="depends",
        edge_class="semantic",
        notes="Morgan--Tian high-confidence prose dependency.",
        per_edge_extra=prose_dependency_meta,
    )
    register_edges(
        storage,
        anaphora_edges,
        rel="depends",
        edge_class="semantic",
        notes="Morgan--Tian local anaphora dependency.",
        per_edge_extra=anaphora_meta,
    )
    register_edges(
        storage,
        definition_term_edges,
        rel="uses",
        edge_class="semantic",
        notes=(
            "Morgan--Tian same-chapter definition term match. "
            "This is a low-confidence candidate edge for review."
        ),
        per_edge_extra=definition_term_meta,
    )
    register_edges(
        storage,
        prose_edges,
        rel="mentions",
        edge_class="prose",
        notes="Morgan--Tian prose mention. The source is the nearest preceding statement in the same chapter segment.",
        per_edge_extra=prose_mention_meta,
    )
    register_edges(
        storage,
        proof_structural_edges,
        rel="contains",
        edge_class="structural",
        notes="Morgan--Tian proof containment. The source is the statement whose proof contains the target statement.",
        per_edge_extra=proof_structural_meta,
    )
    register_edges(
        storage,
        section_sequence_edges,
        rel="in-section",
        edge_class="structural",
        notes="Morgan--Tian reading-order adjacency within a section.",
        per_edge_extra=section_sequence_meta,
    )
    register_edges(
        storage,
        chapter_sequence_edges,
        rel="in-chapter",
        edge_class="structural",
        notes="Morgan--Tian reading-order adjacency across sections in a chapter.",
        per_edge_extra=chapter_sequence_meta,
    )
    generate_docs(texts, project, segments, by_segment, label2hash, label2text)
    write_macros(src, project)
    audit = graph_audit(
        texts,
        order,
        by_segment,
        label2hash,
        label2text,
        edges,
        prose_edges,
        structural_edges,
        semantic_edge_layers={
            "explicit": explicit_edges,
            "proof_containment_dependency": proof_dependency_edges,
            "prose_dependency": prose_dependency_edges,
            "local_anaphora": anaphora_edges,
            "definition_term": definition_term_edges,
        },
        structural_edge_layers={
            "proof_contains": proof_structural_edges,
            "section_sequence": section_sequence_edges,
            "chapter_sequence": chapter_sequence_edges,
        },
    )

    validate_store(storage.data)
    validate_generated_edge_metadata(storage.data)
    validate_generated_text_quality(storage.data, project)
    storage._save()
    n_atoms = sum(1 for e in storage.data.values() if len(e["ref"]) == 1)
    n_edges = sum(1 for e in storage.data.values() if len(e["ref"]) > 1)
    n_statements = sum(len(v) for v in by_segment.values())
    print(f"registered {n_statements} Morgan--Tian statements")
    print(f"store: {n_atoms} atoms, {n_edges} edges")
    print(f"docs: {len(segments)} chapter docs in {project / '.astrolabe'}")
    if args.report:
        print(json.dumps(audit, ensure_ascii=False, indent=2, sort_keys=True))
    if args.report_json:
        Path(args.report_json).write_text(
            json.dumps(audit, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )


if __name__ == "__main__":
    main()
