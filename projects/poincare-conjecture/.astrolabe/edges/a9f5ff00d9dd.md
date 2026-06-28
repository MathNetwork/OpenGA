---
confidence: 0.45
edgeClass: semantic
evidence:
  endpointSemanticDegreeBeforeTermBackfill:
    source: 0
    target: 4
  selectionReason: semantic-connectivity-backfill
  sourceMatchSpan:
    coordinateSpace: comment-stripped-tex
    end: 47208
    file: surgery.tex
    sourceTransform: tex2mdx.strip_comments
    start: 47198
  sourceStatement:
    chapter: 14
    file: surgery.tex
    label: ''
    mtref: '14.9'
    sort: remark
    span:
      coordinateSpace: comment-stripped-tex
      end: 47267
      sourceTransform: tex2mdx.strip_comments
      start: 47116
  targetStatement:
    chapter: 14
    file: surgery.tex
    label: ''
    mtref: '14.1'
    sort: definition
    span:
      coordinateSpace: comment-stripped-tex
      end: 28555
      sourceTransform: tex2mdx.strip_comments
      start: 27727
  targetTermSpan:
    coordinateSpace: comment-stripped-tex
    end: 28309
    file: surgery.tex
    sourceTransform: tex2mdx.strip_comments
    start: 28299
  term: final time
  termAmbiguity: unique-in-chapter
  termSource: italic
  termSpecificity: no-longer-defined-term
  type: same-chapter-definition-term-match
  via:
  - definition-term:final time
generator: tools/poincare_tex_extract.py
inference: weak
kind: definition-use
ref:
- 21f9e3c12b4c
- 41da6871e864
rel: uses
reviewStatus: candidate
scope: same-chapter-term-match
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- definition-term:final time
---
Morgan--Tian same-chapter definition term match. This is a low-confidence candidate edge for review.