---
confidence: 0.45
edgeClass: semantic
evidence:
  endpointSemanticDegreeBeforeTermBackfill:
    source: 1
    target: 0
  selectionReason: semantic-connectivity-backfill
  sourceMatchSpan:
    coordinateSpace: comment-stripped-tex
    end: 125504
    file: newcompar.tex
    sourceTransform: tex2mdx.strip_comments
    start: 125490
  sourceStatement:
    chapter: 6
    file: newcompar.tex
    label: finiteredvol
    mtref: '6.82'
    sort: corollary
    span:
      coordinateSpace: comment-stripped-tex
      end: 125562
      sourceTransform: tex2mdx.strip_comments
      start: 125396
  targetStatement:
    chapter: 6
    file: newcompar.tex
    label: redvol
    mtref: '6.70'
    sort: definition
    span:
      coordinateSpace: comment-stripped-tex
      end: 107162
      sourceTransform: tex2mdx.strip_comments
      start: 106757
  targetTermSpan:
    coordinateSpace: comment-stripped-tex
    end: 106898
    file: newcompar.tex
    sourceTransform: tex2mdx.strip_comments
    start: 106884
  term: reduced volume
  termAmbiguity: unique-in-chapter
  termSource: italic
  termSpecificity: no-longer-defined-term
  type: same-chapter-definition-term-match
  via:
  - definition-term:reduced volume
generator: tools/poincare_tex_extract.py
inference: weak
kind: definition-use
ref:
- e49b6b45c4d0
- 6f08d8fab637
rel: uses
reviewStatus: candidate
scope: same-chapter-term-match
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- definition-term:reduced volume
---
Morgan--Tian same-chapter definition term match. This is a low-confidence candidate edge for review.