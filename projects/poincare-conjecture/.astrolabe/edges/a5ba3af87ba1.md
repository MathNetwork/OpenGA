---
confidence: 0.35
edgeClass: prose
evidence:
  mentionTriggers:
  - label: surgery
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 12858
      file: intro.tex
      sourceTransform: tex2mdx.strip_comments
      start: 12845
    sentence: 'We immediately deduce Theorem~\ref{Theorem1} from Theorems~\ref{surgery}
      and~\ref{finiteext} as follows: Let $M$ be a $3$-manifold satisfying the hypothesis
      of Theorem~\ref{Theorem1}. Then there is a finite sequence $M=M_0,M_1,\ldots,M_k=\emptyset$
      such that for each $i,\ 1\le i\le k$, $M_i$ is obtained from $M_{i-1}$ by a
      connected sum decomposition or $M_i$ is obtained from $M_{i-1}$ by removing
      a component diffeomorphic to one of $S^2\times S^1$, $\Ar P^3\#\Ar P^3$, a non-orientable
      $2$-sphere bundle over $S^1$, or a $3$-dimensional spherical space-form. Clearly,
      it follows by downward induction on $i$ that each connected component of $M_i$
      is diffeomorphic to a connected sum of $3$-dimensional spherical space-forms,
      copies of $S^2\times S^1$, and copies of the non-orientable $2$-sphere bundle
      over $S^1$'
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 13608
      file: intro.tex
      sourceTransform: tex2mdx.strip_comments
      start: 12785
    sourceStrategy: nearest-previous-statement
    via: prose
  sourceStatement:
    chapter: 0
    file: intro.tex
    label: finiteext
    mtref: '0.4'
    sort: theorem
    span:
      coordinateSpace: comment-stripped-tex
      end: 12644
      sourceTransform: tex2mdx.strip_comments
      start: 11822
  targetStatement:
    chapter: 0
    file: intro.tex
    label: surgery
    mtref: '0.3'
    sort: theorem
    span:
      coordinateSpace: comment-stripped-tex
      end: 11419
      sourceTransform: tex2mdx.strip_comments
      start: 10567
  type: prose-mention-nearest-previous-statement
  via:
  - prose
generator: tools/poincare_tex_extract.py
inference: weak
kind: mention
ref:
- 127db1dc9315
- 847af3ecd4a8
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