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
    end: 4190
    file: flowbasics.tex
    sourceTransform: tex2mdx.strip_comments
    start: 4180
  sourceStatement:
    chapter: 3
    file: flowbasics.tex
    label: ''
    mtref: '3.3'
    sort: example
    span:
      coordinateSpace: comment-stripped-tex
      end: 4618
      sourceTransform: tex2mdx.strip_comments
      start: 4083
  targetStatement:
    chapter: 3
    file: flowbasics.tex
    label: ''
    mtref: '3.1'
    sort: definition
    span:
      coordinateSpace: comment-stripped-tex
      end: 943
      sourceTransform: tex2mdx.strip_comments
      start: 265
  targetTermSpan:
    coordinateSpace: comment-stripped-tex
    end: 297
    file: flowbasics.tex
    sourceTransform: tex2mdx.strip_comments
    start: 287
  term: ricci flow
  termAmbiguity: unique-in-chapter
  termSource: italic
  termSpecificity: not-covered-by-longer-defined-term
  type: same-chapter-definition-term-match
  via:
  - definition-term:ricci flow
generator: tools/poincare_tex_extract.py
inference: weak
kind: definition-use
ref:
- 43be10053c44
- 7e9caf7ba4da
rel: uses
reviewStatus: candidate
scope: same-chapter-term-match
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- definition-term:ricci flow
---
Morgan--Tian same-chapter definition term match. This is a low-confidence candidate edge for review.