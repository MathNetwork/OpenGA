---
confidence: 0.45
edgeClass: semantic
evidence:
  endpointSemanticDegreeBeforeTermBackfill:
    source: 0
    target: 7
  selectionReason: semantic-connectivity-backfill
  sourceMatchSpan:
    coordinateSpace: comment-stripped-tex
    end: 113065
    file: newcompar.tex
    sourceTransform: tex2mdx.strip_comments
    start: 113057
  sourceStatement:
    chapter: 6
    file: newcompar.tex
    label: ''
    mtref: '6.76'
    sort: example
    span:
      coordinateSpace: comment-stripped-tex
      end: 113156
      sourceTransform: tex2mdx.strip_comments
      start: 112685
  targetStatement:
    chapter: 6
    file: newcompar.tex
    label: ''
    mtref: '6.7'
    sort: definition
    span:
      coordinateSpace: comment-stripped-tex
      end: 10481
      sourceTransform: tex2mdx.strip_comments
      start: 10161
  targetTermSpan:
    coordinateSpace: comment-stripped-tex
    end: 10318
    file: newcompar.tex
    sourceTransform: tex2mdx.strip_comments
    start: 10310
  term: geodesic
  termAmbiguity: unique-in-chapter
  termSource: italic
  termSpecificity: not-covered-by-longer-defined-term
  type: same-chapter-definition-term-match
  via:
  - definition-term:geodesic
generator: tools/poincare_tex_extract.py
inference: weak
kind: definition-use
ref:
- a6ea3cf8fb92
- d23dc29f2aae
rel: uses
reviewStatus: candidate
scope: same-chapter-term-match
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- definition-term:geodesic
---
Morgan--Tian same-chapter definition term match. This is a low-confidence candidate edge for review.