---
confidence: 0.35
edgeClass: prose
evidence:
  mentionTriggers:
  - label: divRic
    refSpan:
      coordinateSpace: comment-stripped-tex
      end: 83370
      file: temp2kappa.tex
      sourceTransform: tex2mdx.strip_comments
      start: 83358
    sentence: Taking the trace of the gradient shrinking soliton equation yields $$R+\triangle
      f-\frac{n}{2}=0,$$ and consequently that $$ dR+d(\triangle f)=0.$$ Using Lemma~\ref{lapformula}
      we rewrite this equation as \begin{equation}\label{Rfeqn} dR+\triangle(df)-{\rm
      Ric}(\nabla f,\cdot)=0.\end{equation} On the other hand, taking the divergence
      of the gradient shrinking soliton equation and using the fact that $\nabla^*
      g=0$ gives $$\nabla^*{\rm Ric}+\nabla^*{\rm Hess}(f)=0.$$ Of course, $$\nabla^*{\rm
      Hess}(f)=\nabla^*(\nabla\nabla f)=(\nabla^*\nabla)\nabla f=\triangle (df),$$
      so that $$\triangle(df)=-\nabla^*{\rm Ric}.$$ Plugging this into Equation~\ref{Rfeqn}
      gives $$dR-\nabla^*{\rm Ric}-{\rm Ric}(\nabla f,\cdot)=0.$$ Now invoking Lemma~\ref{divRic}
      we have \begin{equation}\label{dR} dR=2{\rm Ric}(\nabla f,\cdot).\end{equation}
    sentenceSpan:
      coordinateSpace: comment-stripped-tex
      end: 83451
      file: temp2kappa.tex
      sourceTransform: tex2mdx.strip_comments
      start: 82616
    sourceStrategy: nearest-previous-statement
    via: prose
  sourceStatement:
    chapter: 9
    file: temp2kappa.tex
    label: noncompsol
    mtref: '9.46'
    sort: proposition
    span:
      coordinateSpace: comment-stripped-tex
      end: 82429
      sourceTransform: tex2mdx.strip_comments
      start: 82233
  targetStatement:
    chapter: 1
    file: prelim.tex
    label: divRic
    mtref: '1.9'
    sort: lemma
    span:
      coordinateSpace: comment-stripped-tex
      end: 12596
      sourceTransform: tex2mdx.strip_comments
      start: 12512
  type: prose-mention-nearest-previous-statement
  via:
  - prose
generator: tools/poincare_tex_extract.py
inference: weak
kind: mention
ref:
- 03957890f08f
- 9c83686198e8
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