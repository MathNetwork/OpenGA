---
confidence: 0.45
edgeClass: semantic
evidence:
  endpointSemanticDegreeBeforeTermBackfill:
    source: 3
    target: 0
  selectionReason: semantic-connectivity-backfill
  sourceMatchSpan:
    coordinateSpace: comment-stripped-tex
    end: 13715
    file: maxprin.tex
    sourceTransform: tex2mdx.strip_comments
    start: 13686
  sourceStatement:
    chapter: 4
    file: maxprin.tex
    label: kappa0r0t0
    mtref: '4.11'
    sort: proposition
    span:
      coordinateSpace: comment-stripped-tex
      end: 13944
      sourceTransform: tex2mdx.strip_comments
      start: 13445
  targetStatement:
    chapter: 4
    file: maxprin.tex
    label: norminitcond
    mtref: '4.10'
    sort: definition
    span:
      coordinateSpace: comment-stripped-tex
      end: 13043
      sourceTransform: tex2mdx.strip_comments
      start: 12395
  targetTermSpan:
    coordinateSpace: comment-stripped-tex
    end: 12509
    file: maxprin.tex
    sourceTransform: tex2mdx.strip_comments
    start: 12480
  term: normalized initial conditions
  termAmbiguity: unique-in-chapter
  termSource: italic
  termSpecificity: no-longer-defined-term
  type: same-chapter-definition-term-match
  via:
  - definition-term:normalized initial conditions
generator: tools/poincare_tex_extract.py
inference: weak
kind: definition-use
ref:
- c1330c5a8be3
- 12a9b4e99e24
rel: uses
reviewStatus: candidate
scope: same-chapter-term-match
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- definition-term:normalized initial conditions
---
Morgan--Tian same-chapter definition term match. This is a low-confidence candidate edge for review.