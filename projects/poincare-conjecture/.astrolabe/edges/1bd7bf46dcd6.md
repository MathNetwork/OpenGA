---
confidence: 0.35
edgeClass: prose
evidence:
  mentionTriggers:
  - label: surgerydist
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 3689
      file: energy1.tex
      sourceTransform: tex2mdx.strip_comments
      start: 3672
    sentence: In fact, using the distance-decreasing property for surgery in Proposition~\ref{surgerydist}
      we see that, even in a Ricci flow with surgery, the same forward difference
      quotient estimate holds for as long as $\pi_2$ continues to be non-trivial,
      i.e., is not killed by the surgery
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 3877
      file: energy1.tex
      sourceTransform: tex2mdx.strip_comments
      start: 3596
    sourceStrategy: nearest-previous-statement
    via: prose
  - label: surgerydist
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 5429
      file: energy1.tex
      sourceTransform: tex2mdx.strip_comments
      start: 5412
    sentence: Under Ricci flow, the forward difference quotient of this invariant
      satisfies an inequality and the distance-decreasing property of surgery (Proposition~\ref{surgerydist})
      says that the inequality remains valid for Ricci flow with surgery
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 5497
      file: energy1.tex
      sourceTransform: tex2mdx.strip_comments
      start: 5258
    sourceStrategy: nearest-previous-statement
    via: prose
  - label: surgerydist
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 6158
      file: energy1.tex
      sourceTransform: tex2mdx.strip_comments
      start: 6141
    sentence: As before, the distance-decreasing property of surgery (Proposition~\ref{surgerydist})
      implies that this inequality is valid for Ricci flows with surgery
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 6226
      file: energy1.tex
      sourceTransform: tex2mdx.strip_comments
      start: 6072
    sourceStrategy: nearest-previous-statement
    via: prose
  sourceStatement:
    chapter: 18
    file: energy1.tex
    label: extinct
    mtref: '18.1'
    sort: theorem
    span:
      coordinateSpace: comment-stripped-tex
      end: 1107
      sourceTransform: tex2mdx.strip_comments
      start: 511
  targetStatement:
    chapter: 15
    file: surgery.tex
    label: surgerydist
    mtref: '15.12'
    sort: proposition
    span:
      coordinateSpace: comment-stripped-tex
      end: 97780
      sourceTransform: tex2mdx.strip_comments
      start: 96249
  type: prose-mention-nearest-previous-statement
  via:
  - prose
generator: tools/poincare_tex_extract.py
inference: weak
kind: mention
ref:
- 4b8a44aa316f
- 9021a4eca03f
rel: mentions
reviewStatus: candidate
scope: prose
sort: (morgan-tian, morgan-tian)
source: tex
src: morgan-tian
via:
- prose
---
Morgan--Tian prose mention. The source is the nearest preceding statement in the same chapter segment.