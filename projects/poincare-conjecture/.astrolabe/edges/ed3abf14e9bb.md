---
confidence: 0.45
edgeClass: semantic
evidence:
  endpointSemanticDegreeBeforeTermBackfill:
    source: 4
    target: 0
  selectionReason: semantic-connectivity-backfill
  sourceMatchSpan:
    coordinateSpace: comment-stripped-tex
    end: 2701
    file: bddcurvbdddist.tex
    sourceTransform: tex2mdx.strip_comments
    start: 2678
  sourceStatement:
    chapter: 10
    file: bddcurvbdddist.tex
    label: bcbd
    mtref: '10.2'
    sort: theorem
    span:
      coordinateSpace: comment-stripped-tex
      end: 2942
      sourceTransform: tex2mdx.strip_comments
      start: 2168
  targetStatement:
    chapter: 10
    file: bddcurvbdddist.tex
    label: pinchdef
    mtref: '10.1'
    sort: definition
    span:
      coordinateSpace: comment-stripped-tex
      end: 1390
      sourceTransform: tex2mdx.strip_comments
      start: 647
  targetTermSpan:
    coordinateSpace: comment-stripped-tex
    end: 1119
    file: bddcurvbdddist.tex
    sourceTransform: tex2mdx.strip_comments
    start: 1096
  term: pinched toward positive
  termAmbiguity: unique-in-chapter
  termSource: italic
  termSpecificity: no-longer-defined-term
  type: same-chapter-definition-term-match
  via:
  - definition-term:pinched toward positive
generator: tools/poincare_tex_extract.py
inference: weak
kind: definition-use
ref:
- ecd62fc2ea2b
- 7464980c4085
rel: uses
reviewStatus: candidate
scope: same-chapter-term-match
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- definition-term:pinched toward positive
---
Morgan--Tian same-chapter definition term match. This is a low-confidence candidate edge for review.