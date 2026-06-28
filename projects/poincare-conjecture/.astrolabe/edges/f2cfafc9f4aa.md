---
confidence: 0.35
edgeClass: prose
evidence:
  mentionTriggers:
  - label: asympt
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 63853
      file: stdsoln.tex
      sourceTransform: tex2mdx.strip_comments
      start: 63841
    sentence: then it follows from Claim~\ref{asympt} that $G(\tilde{\rho}_{i-1},{\bf
      x},t)$ is bounded on $\mathbb{R}^{n+2} \times [0,T]$
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 63938
      file: stdsoln.tex
      sourceTransform: tex2mdx.strip_comments
      start: 63813
    sourceStrategy: nearest-previous-statement
    via: prose
  - label: asympt
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 64038
      file: stdsoln.tex
      sourceTransform: tex2mdx.strip_comments
      start: 64026
    sentence: '\[ |G(\tilde{\rho}_{i-1},x,t)| \leq C_*(C_1,\tilde{h} ), \] and also
      because of Claim~\ref{asympt} both $|\nabla B|$ and $|\nabla \tilde h|$ are
      bounded on all of $\Ar^{n+2}\times [0,T]$, it follows that $F(x, \tilde{\rho}_{i-1},\nabla\tilde{\rho}_{i-1},t)$
      is bounded: \begin{align*} & |F(x, \tilde{\rho}_{i-1},\nabla\tilde{\rho}_{i-1},t)|
      \\ \leq & \left[(n-1)\sup |\nabla \tilde{h}| + \sup |\nabla B| \right]C_2+C_2^2+
      C_*(C_1,\tilde{h} ) = C_3 \end{align*} Hence $\tilde{\rho}_i$ exists.'
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 64432
      file: stdsoln.tex
      sourceTransform: tex2mdx.strip_comments
      start: 63939
    sourceStrategy: nearest-previous-statement
    via: prose
  - label: asympt
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 70596
      file: stdsoln.tex
      sourceTransform: tex2mdx.strip_comments
      start: 70584
    sentence: It follows from (\ref{rho_i est}) and Claim~\ref{asympt} that there
      is a constant $C_8$ independent of $i$ such that
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 70656
      file: stdsoln.tex
      sourceTransform: tex2mdx.strip_comments
      start: 70539
    sourceStrategy: nearest-previous-statement
    via: prose
  - label: asympt
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 72629
      file: stdsoln.tex
      sourceTransform: tex2mdx.strip_comments
      start: 72617
    sentence: From (\ref{rhoHolder}) and Claim~\ref{asympt} we know that $\nabla [
      (n-1)\tilde{h} -B+ \tilde{\rho}_\infty ]$ has $C^{\alpha,\alpha/2}$-H\"older-norm
      bounded (this means $\alpha$-H\"older norm in space and the $\alpha/2$-H\"older
      norm in time)
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 72828
      file: stdsoln.tex
      sourceTransform: tex2mdx.strip_comments
      start: 72583
    sourceStrategy: nearest-previous-statement
    via: prose
  sourceStatement:
    chapter: 12
    file: stdsoln.tex
    label: ''
    mtref: '12.24'
    sort: proposition
    span:
      coordinateSpace: comment-stripped-tex
      end: 62221
      sourceTransform: tex2mdx.strip_comments
      start: 61942
  targetStatement:
    chapter: 12
    file: stdsoln.tex
    label: asympt
    mtref: '12.23'
    sort: claim
    span:
      coordinateSpace: comment-stripped-tex
      end: 61284
      sourceTransform: tex2mdx.strip_comments
      start: 60562
  type: prose-mention-nearest-previous-statement
  via:
  - prose
generator: tools/poincare_tex_extract.py
inference: weak
kind: mention
ref:
- 43ea5e1d04cf
- ac4ac4fb06f8
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