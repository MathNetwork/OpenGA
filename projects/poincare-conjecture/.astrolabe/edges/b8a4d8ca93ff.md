---
confidence: 0.45
edgeClass: semantic
evidence:
  endpointSemanticDegreeBeforeTermBackfill:
    source: 0
    target: 1
  selectionReason: semantic-connectivity-backfill
  sourceMatchSpan:
    coordinateSpace: comment-stripped-tex
    end: 12300
    file: newcomp2.tex
    sourceTransform: tex2mdx.strip_comments
    start: 12270
  sourceStatement:
    chapter: 7
    file: newcomp2.tex
    label: weaksense
    mtref: '7.8'
    sort: proposition
    span:
      coordinateSpace: comment-stripped-tex
      end: 12878
      sourceTransform: tex2mdx.strip_comments
      start: 12168
  targetStatement:
    chapter: 7
    file: newcomp2.tex
    label: ''
    mtref: '7.1'
    sort: definition
    span:
      coordinateSpace: comment-stripped-tex
      end: 1366
      sourceTransform: tex2mdx.strip_comments
      start: 781
  targetTermSpan:
    coordinateSpace: comment-stripped-tex
    end: 900
    file: newcomp2.tex
    sourceTransform: tex2mdx.strip_comments
    start: 871
  term: complete of bounded curvature
  termAmbiguity: unique-in-chapter
  termSource: italic
  termSpecificity: no-longer-defined-term
  type: same-chapter-definition-term-match
  via:
  - definition-term:complete of bounded curvature
generator: tools/poincare_tex_extract.py
inference: weak
kind: definition-use
ref:
- 1ef3a78b1911
- 2336b554a054
rel: uses
reviewStatus: candidate
scope: same-chapter-term-match
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- definition-term:complete of bounded curvature
---
Morgan--Tian same-chapter definition term match. This is a low-confidence candidate edge for review.