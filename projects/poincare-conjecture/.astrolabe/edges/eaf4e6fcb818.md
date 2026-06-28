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
    end: 31349
    file: newcomp2.tex
    sourceTransform: tex2mdx.strip_comments
    start: 31336
  sourceStatement:
    chapter: 7
    file: newcomp2.tex
    label: ''
    mtref: '7.17'
    sort: claim
    span:
      coordinateSpace: comment-stripped-tex
      end: 31480
      sourceTransform: tex2mdx.strip_comments
      start: 31161
  targetStatement:
    chapter: 7
    file: newcomp2.tex
    label: ''
    mtref: '7.7'
    sort: definition
    span:
      coordinateSpace: comment-stripped-tex
      end: 12044
      sourceTransform: tex2mdx.strip_comments
      start: 11683
  targetTermSpan:
    coordinateSpace: comment-stripped-tex
    end: 11799
    file: newcomp2.tex
    sourceTransform: tex2mdx.strip_comments
    start: 11786
  term: upper barrier
  termAmbiguity: unique-in-chapter
  termSource: italic
  termSpecificity: no-longer-defined-term
  type: same-chapter-definition-term-match
  via:
  - definition-term:upper barrier
generator: tools/poincare_tex_extract.py
inference: weak
kind: definition-use
ref:
- b58a798d5eea
- d50ccf232266
rel: uses
reviewStatus: candidate
scope: same-chapter-term-match
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- definition-term:upper barrier
---
Morgan--Tian same-chapter definition term match. This is a low-confidence candidate edge for review.