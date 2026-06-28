---
confidence: 0.45
edgeClass: semantic
evidence:
  endpointSemanticDegreeBeforeTermBackfill:
    source: 2
    target: 0
  selectionReason: semantic-connectivity-backfill
  sourceMatchSpan:
    coordinateSpace: comment-stripped-tex
    end: 8153
    file: maxprin.tex
    sourceTransform: tex2mdx.strip_comments
    start: 8147
  sourceStatement:
    chapter: 4
    file: maxprin.tex
    label: MP
    mtref: '4.7'
    sort: theorem
    span:
      coordinateSpace: comment-stripped-tex
      end: 8808
      sourceTransform: tex2mdx.strip_comments
      start: 7939
  targetStatement:
    chapter: 4
    file: maxprin.tex
    label: ''
    mtref: '4.6'
    sort: definition
    span:
      coordinateSpace: comment-stripped-tex
      end: 7829
      sourceTransform: tex2mdx.strip_comments
      start: 7225
  targetTermSpan:
    coordinateSpace: comment-stripped-tex
    end: 7397
    file: maxprin.tex
    sourceTransform: tex2mdx.strip_comments
    start: 7391
  term: convex
  termAmbiguity: unique-in-chapter
  termSource: italic
  termSpecificity: no-longer-defined-term
  type: same-chapter-definition-term-match
  via:
  - definition-term:convex
generator: tools/poincare_tex_extract.py
inference: weak
kind: definition-use
ref:
- c954e95b5d89
- f3441849c78b
rel: uses
reviewStatus: candidate
scope: same-chapter-term-match
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- definition-term:convex
---
Morgan--Tian same-chapter definition term match. This is a low-confidence candidate edge for review.