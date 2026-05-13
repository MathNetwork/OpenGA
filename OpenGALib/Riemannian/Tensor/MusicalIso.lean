import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import OpenGALib.Riemannian.Tensor.SmoothOrthoFrame

/-!
# Smoothness of the musical isomorphism

For a smooth Riemannian metric $g$ on the tangent bundle of a smooth manifold
$M$, the musical isomorphism $\sharp_g : T^*M \to TM$ at each point $x$ sends a
covector $\varphi \in T_x^*M$ to the unique tangent vector $V$ with
$g_x(V, W) = \varphi(W)$ for all $W$. This is `g.metricRiesz x φ` in OpenGALib.

This file establishes smoothness of the section
$$x \mapsto \sharp_g\,\varphi(x), \qquad \varphi \in \Gamma^\infty(T^*M),$$
via the chart-local representation
$$\sharp_g\,\varphi(x) = \sum_{i,j} G^{ij}(x)\,\varphi_j(x)\,e_i(x),$$
where:

* $e_i(x) = \mathrm{chartBasisVecFiber}\,\alpha\,i\,x$ is the chart-basis
  frame at $\alpha$ (`SmoothOrthoFrame.lean`).
* $G_{ij}(x) = g_x(e_i(x), e_j(x))$ is the chart Gram matrix.
* $G^{ij}(x)$ is its entrywise matrix inverse.
* $\varphi_j(x) = \varphi(x)(e_j(x))$ is the $j$-th chart-frame coefficient of
  $\varphi$.

The Gram matrix is symmetric positive-definite on the trivialization base set,
so its determinant is strictly positive and its entrywise inverse is smooth via
the cofactor / adjugate formula.

## Main definitions

* `chartGramMatrix g α x` : the Gram matrix at $x$ of `chartBasisVecFiber α · x`
  under `g.inner x`.
* `chartInvGramMatrix g α x` : the matrix inverse of `chartGramMatrix g α x`.

## Main results

* `chartGramMatrix_isHermitian` — symmetry.
* `chartGramMatrix_posDef` — positive-definiteness on the trivialization base
  set.
* `chartGramMatrix_det_pos` — strictly positive determinant on the base set.
* `chartGramMatrix_entry_contMDiffOn`, `chartGramMatrix_det_contMDiffOn`,
  `chartGramMatrix_adjugate_entry_contMDiffOn`,
  `chartInvGramMatrix_entry_contMDiffOn` — smoothness of the Gram-matrix
  entries, determinant, adjugate, and entrywise inverse on the base set.
* `metricRiesz_section_smoothAt` — smoothness of the musical section
  `y ↦ g.metricRiesz y (φ y)` given a smooth covector section `φ` (planned).

**Ground truth**: do Carmo §3 ex. 8 (Riesz duality on a Riemannian manifold);
Lee 2018 §13 (musical isomorphisms); external `differential-geometry` library
`Integral/Measure/ChartDensity.lean` + `Geometry/Gradient.lean` (the
chart-Gram-matrix machinery ported here).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace Riemannian
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Stage 1: the chart Gram matrix -/

/-- The Gram matrix of the chart-basis family `chartBasisVecFiber α · x` at
$x$ under the inner product `g.inner x`. -/
def chartGramMatrix (g : RiemannianMetric I M) (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    g.inner x
      (chartBasisVecFiber (I := I) α i x)
      (chartBasisVecFiber (I := I) α j x)

@[simp] lemma chartGramMatrix_apply
    (g : RiemannianMetric I M) (α : M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) g α x i j =
      g.inner x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) := rfl

/-- The Gram matrix is Hermitian (symmetric for real entries). -/
lemma chartGramMatrix_isHermitian
    (g : RiemannianMetric I M) (α : M) (x : M) :
    (chartGramMatrix (I := I) g α x).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  show star (chartGramMatrix (I := I) g α x j i)
    = chartGramMatrix (I := I) g α x i j
  rw [chartGramMatrix_apply, chartGramMatrix_apply, star_trivial]
  exact g.symm x
    (chartBasisVecFiber (I := I) α j x)
    (chartBasisVecFiber (I := I) α i x)

/-! ## Stage 2: positive-definiteness on the base set -/

/-- The Gram-matrix quadratic form equals the metric-inner-product squared norm
of the corresponding linear combination of chart-basis vectors. Tangent-space
analog of `Matrix.star_dotProduct_gram_mulVec`. -/
lemma chartGramMatrix_dotProduct_mulVec
    (g : RiemannianMetric I M) (α : M) (x : M)
    (c : Fin (Module.finrank ℝ E) → ℝ) :
    star c ⬝ᵥ (chartGramMatrix (I := I) g α x) *ᵥ c =
      g.inner x
        (∑ i, c i • chartBasisVecFiber (I := I) α i x)
        (∑ j, c j • chartBasisVecFiber (I := I) α j x) := by
  have hexpand :
      g.inner x
          (∑ i, c i • chartBasisVecFiber (I := I) α i x)
          (∑ j, c j • chartBasisVecFiber (I := I) α j x)
        = ∑ i, ∑ j, (c i * c j) *
            g.inner x
              (chartBasisVecFiber (I := I) α i x)
              (chartBasisVecFiber (I := I) α j x) := by
    have hL :
        g.inner x (∑ i, c i • chartBasisVecFiber (I := I) α i x)
          = ∑ i, c i • g.inner x (chartBasisVecFiber (I := I) α i x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
    rw [hL, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ContinuousLinearMap.smul_apply]
    have hR :
        g.inner x (chartBasisVecFiber (I := I) α i x)
            (∑ j, c j • chartBasisVecFiber (I := I) α j x)
          = ∑ j, c j *
              g.inner x
                (chartBasisVecFiber (I := I) α i x)
                (chartBasisVecFiber (I := I) α j x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [map_smul, smul_eq_mul]
    rw [hR, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hexpand]
  simp only [dotProduct, Matrix.mulVec, chartGramMatrix_apply, Pi.star_apply,
    star_trivial]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

/-- The Gram matrix of the chart-basis family is positive-definite on the
trivialization base set. -/
lemma chartGramMatrix_posDef
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (chartGramMatrix (I := I) g α x).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (chartGramMatrix_isHermitian (I := I) g α x) ?_
  intro c hc
  set w : TangentSpace I x :=
    ∑ i, c i • chartBasisVecFiber (I := I) α i x with hw_def
  have heq := chartGramMatrix_dotProduct_mulVec (I := I) g α x c
  rw [heq]
  have hwnz : w ≠ 0 := by
    intro hw0
    have hli := chartBasisFamily_linearIndependent (I := I) α hx
    rw [Fintype.linearIndependent_iff] at hli
    have : c = 0 := funext (hli c hw0)
    exact hc this
  exact g.pos x w hwnz

/-- The determinant of the Gram matrix is strictly positive on the
trivialization base set. -/
lemma chartGramMatrix_det_pos
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    0 < (chartGramMatrix (I := I) g α x).det :=
  (chartGramMatrix_posDef (I := I) g α hx).det_pos

/-! ## Stage 3: smoothness of Gram-matrix entries -/

/-- Each Gram-matrix entry is smooth on the trivialization base set: the inner
product evaluated at two smooth chart-basis sections is smooth via
`ContMDiffOn.clm_bundle_apply₂` applied to `g.contMDiff` and two copies of
`chartBasisVec`. -/
lemma chartGramMatrix_entry_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => chartGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        b (g.inner b))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    g.contMDiff.contMDiffOn
  have hv := chartBasisVec_contMDiffOn (I := I) α i
  have hw := chartBasisVec_contMDiffOn (I := I) α j
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            g.inner m
              (chartBasisVecFiber (I := I) α i m)
              (chartBasisVecFiber (I := I) α j m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hg hv hw
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

/-- The determinant of the Gram matrix is smooth on the trivialization base
set. Proof: expand `Matrix.det` into a finite sum over permutations of finite
products of entries, then chain `contMDiffOn_finset_sum` +
`contMDiffOn_finset_prod` with the entry smoothness. -/
lemma chartGramMatrix_det_contMDiffOn
    (g : RiemannianMetric I M) (α : M) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => (chartGramMatrix (I := I) g α x).det)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp :
      (fun x : M => (chartGramMatrix (I := I) g α x).det)
        = (fun x : M =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ i, chartGramMatrix (I := I) g α x (σ i) i) := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul
    (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finset_prod (fun i _ => ?_)
  exact chartGramMatrix_entry_contMDiffOn (I := I) g α (σ i) i

/-! ## Stage 4: smoothness of the adjugate entries -/

/-- Each adjugate entry of the Gram matrix is smooth on the trivialization base
set. The adjugate entry is the determinant of an updated submatrix (`updateRow`
of the Gram matrix with `Pi.single i 1`), hence a polynomial expression in the
(smooth) Gram-matrix entries. -/
lemma chartGramMatrix_adjugate_entry_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => (chartGramMatrix (I := I) g α x).adjugate i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp :
      (fun x : M => (chartGramMatrix (I := I) g α x).adjugate i j) =
        (fun x : M => ((chartGramMatrix (I := I) g α x).updateRow j
          (Pi.single i (1 : ℝ))).det) := by
    funext x
    exact Matrix.adjugate_apply _ _ _
  rw [hexp]
  have hexp2 :
      (fun x : M => ((chartGramMatrix (I := I) g α x).updateRow j
          (Pi.single i (1 : ℝ))).det) =
        (fun x : M => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ k, (chartGramMatrix (I := I) g α x).updateRow j
                (Pi.single i (1 : ℝ)) (σ k) k) := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp2]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul
    (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finset_prod (fun k _ => ?_)
  by_cases hσk : σ k = j
  · have heq :
        (fun x : M => (chartGramMatrix (I := I) g α x).updateRow j
            (Pi.single i (1 : ℝ)) (σ k) k) =
          (fun _ : M => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ)
            i (1 : ℝ)) k) := by
      funext x
      rw [hσk, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · have heq :
        (fun x : M => (chartGramMatrix (I := I) g α x).updateRow j
            (Pi.single i (1 : ℝ)) (σ k) k) =
          (fun x : M => chartGramMatrix (I := I) g α x (σ k) k) := by
      funext x
      rw [Matrix.updateRow_ne hσk]
    rw [heq]
    exact chartGramMatrix_entry_contMDiffOn (I := I) g α (σ k) k

/-! ## Stage 5: the inverse Gram matrix and its smoothness -/

/-- The inverse Gram matrix at `(α, x)`. On the chart base set this is the
matrix inverse of the (positive-definite) Gram matrix; off the base set it
is a default value. -/
def chartInvGramMatrix (g : RiemannianMetric I M) (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (chartGramMatrix (I := I) g α x)⁻¹

/-- On the chart base set, the inverse Gram matrix is a one-sided inverse. -/
lemma chartInvGramMatrix_mul_chartGramMatrix
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartInvGramMatrix (I := I) g α x * chartGramMatrix (I := I) g α x = 1 := by
  have hpos := chartGramMatrix_posDef (I := I) g α hx
  have hdet_unit : IsUnit (chartGramMatrix (I := I) g α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  unfold chartInvGramMatrix
  exact Matrix.nonsing_inv_mul _ hdet_unit

/-- Symmetric form: Gram · inverse Gram = 1 on the base set. -/
lemma chartGramMatrix_mul_chartInvGramMatrix
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartGramMatrix (I := I) g α x * chartInvGramMatrix (I := I) g α x = 1 := by
  have hpos := chartGramMatrix_posDef (I := I) g α hx
  have hdet_unit : IsUnit (chartGramMatrix (I := I) g α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  unfold chartInvGramMatrix
  exact Matrix.mul_nonsing_inv _ hdet_unit

/-- Each entry of the inverse Gram matrix is smooth on the chart base set. -/
lemma chartInvGramMatrix_entry_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hcongr : ∀ x ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      chartInvGramMatrix (I := I) g α x i j =
        ((chartGramMatrix (I := I) g α x).det)⁻¹ *
          (chartGramMatrix (I := I) g α x).adjugate i j := by
    intro x hx
    have hdet_pos := chartGramMatrix_det_pos (I := I) g α hx
    have hdet_ne : (chartGramMatrix (I := I) g α x).det ≠ 0 :=
      ne_of_gt hdet_pos
    unfold chartInvGramMatrix
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) g α x).det •
            (chartGramMatrix (I := I) g α x).adjugate) i j =
      ((chartGramMatrix (I := I) g α x).det)⁻¹ *
          (chartGramMatrix (I := I) g α x).adjugate i j
    rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    exact Ring.inverse_eq_inv _
  refine ContMDiffOn.congr ?_ hcongr
  refine ContMDiffOn.mul ?_ ?_
  · have hdet_smooth :
        ContMDiffOn I 𝓘(ℝ) ∞
          (fun x : M => (chartGramMatrix (I := I) g α x).det)
          (trivializationAt E (TangentSpace I) α).baseSet :=
      chartGramMatrix_det_contMDiffOn (I := I) g α
    intro x hx
    have hdet_pos := chartGramMatrix_det_pos (I := I) g α hx
    have hdet_ne : (chartGramMatrix (I := I) g α x).det ≠ 0 :=
      ne_of_gt hdet_pos
    have hsmooth_inv : ContDiffAt ℝ ∞ (fun y : ℝ => y⁻¹)
        (chartGramMatrix (I := I) g α x).det := contDiffAt_inv _ hdet_ne
    have h_at := hdet_smooth x hx
    exact hsmooth_inv.contMDiffAt.comp_contMDiffWithinAt x h_at
  · exact chartGramMatrix_adjugate_entry_contMDiffOn (I := I) g α i j

/-! ## Stage 6: chart-coordinate expression of the Riesz dual

At any base-set point $x$, the Riesz dual of a covector $\varphi$ admits the
explicit chart-frame expression
$$\sharp_g\,\varphi(x) = \sum_i \Bigl(\sum_j G^{ij}(x)\,\varphi(e_j(x))\Bigr)\,
    e_i(x),$$
derived by `g.metricRiesz_unique` against the bilinear-form action on the
chart frame.

This is the algebraic heart of the smoothness argument: every quantity on
the right-hand side is smooth on the base set (Gram-matrix inverse entries
via Stage 5, chart-basis vectors via `SmoothOrthoFrame`, and the covector
section by hypothesis), so the LHS is smooth too. -/

private lemma metricRiesz_chart_form_inner_e
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (φ : TangentSpace I x →L[ℝ] ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    g.inner x
        (∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
                φ (chartBasisVecFiber (I := I) α j x)) •
            chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α k x)
      = φ (chartBasisVecFiber (I := I) α k x) := by
  -- Expand g.inner over the outer sum in the first argument.
  rw [show g.inner x
        (∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
                φ (chartBasisVecFiber (I := I) α j x)) •
            chartBasisVecFiber (I := I) α i x)
        = ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
                φ (chartBasisVecFiber (I := I) α j x)) •
            g.inner x (chartBasisVecFiber (I := I) α i x) from ?_]
  · -- Now goal: ∑ i, (∑ j, G⁻¹_{ij} φ(e_j)) • g.inner x e_i (e_k) = φ(e_k)
    rw [ContinuousLinearMap.sum_apply]
    -- Goal: ∑ i, ((∑ j, G⁻¹_{ij} φ(e_j)) • g.inner x e_i) (e_k) = φ(e_k)
    have hsmul : ∀ i,
        ((∑ j, chartInvGramMatrix (I := I) g α x i j *
            φ (chartBasisVecFiber (I := I) α j x)) •
              g.inner x (chartBasisVecFiber (I := I) α i x))
            (chartBasisVecFiber (I := I) α k x) =
          (∑ j, chartInvGramMatrix (I := I) g α x i j *
              φ (chartBasisVecFiber (I := I) α j x)) *
            chartGramMatrix (I := I) g α x i k := by
      intro i
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rfl
    rw [Finset.sum_congr rfl (fun i _ => hsmul i)]
    -- Goal: ∑ i, (∑ j, G⁻¹_{ij} φ(e_j)) * G_{ik} = φ(e_k)
    have hdistrib : ∀ i,
        (∑ j, chartInvGramMatrix (I := I) g α x i j *
            φ (chartBasisVecFiber (I := I) α j x)) *
          chartGramMatrix (I := I) g α x i k
            = ∑ j, chartInvGramMatrix (I := I) g α x i j *
                φ (chartBasisVecFiber (I := I) α j x) *
              chartGramMatrix (I := I) g α x i k := by
      intro i
      rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun i _ => hdistrib i)]
    -- Goal: ∑ i, ∑ j, G⁻¹_{ij} φ(e_j) G_{ik} = φ(e_k)
    rw [Finset.sum_comm]
    -- Goal: ∑ j, ∑ i, G⁻¹_{ij} φ(e_j) G_{ik} = φ(e_k)
    have hfact : ∀ j,
        (∑ i, chartInvGramMatrix (I := I) g α x i j *
            φ (chartBasisVecFiber (I := I) α j x) *
          chartGramMatrix (I := I) g α x i k)
          = (∑ i, chartGramMatrix (I := I) g α x i k *
              chartInvGramMatrix (I := I) g α x i j) *
            φ (chartBasisVecFiber (I := I) α j x) := by
      intro j
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [Finset.sum_congr rfl (fun j _ => hfact j)]
    -- Goal: ∑ j, (∑ i, G_{ik} G⁻¹_{ij}) φ(e_j) = φ(e_k)
    -- Use symmetry: G_{ik} = G_{ki}, then (G * G⁻¹)_{kj} = δ_{kj}.
    have hsym : ∀ i j,
        chartGramMatrix (I := I) g α x i k *
          chartInvGramMatrix (I := I) g α x i j
          = chartGramMatrix (I := I) g α x k i *
            chartInvGramMatrix (I := I) g α x i j := by
      intro i j
      have := (chartGramMatrix_isHermitian (I := I) g α x).apply k i
      simp only [star_trivial] at this
      rw [this]
    have hkj : ∀ j,
        (∑ i, chartGramMatrix (I := I) g α x i k *
            chartInvGramMatrix (I := I) g α x i j)
          = (1 : Matrix (Fin (Module.finrank ℝ E))
              (Fin (Module.finrank ℝ E)) ℝ) k j := by
      intro j
      have hsum : (∑ i, chartGramMatrix (I := I) g α x i k *
          chartInvGramMatrix (I := I) g α x i j)
          = ∑ i, chartGramMatrix (I := I) g α x k i *
              chartInvGramMatrix (I := I) g α x i j :=
        Finset.sum_congr rfl (fun i _ => hsym i j)
      rw [hsum]
      have hmul := chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hx
      have hprod_eq :
          (chartGramMatrix (I := I) g α x *
              chartInvGramMatrix (I := I) g α x) k j
            = (1 : Matrix (Fin (Module.finrank ℝ E))
                (Fin (Module.finrank ℝ E)) ℝ) k j := by
        rw [hmul]
      rw [← hprod_eq]
      rfl
    rw [Finset.sum_congr rfl (fun j _ => by rw [hkj j])]
    -- Goal: ∑ j, (1 : Matrix _ _ ℝ) k j * φ(e_j) = φ(e_k)
    rw [Finset.sum_eq_single k]
    · simp [Matrix.one_apply_eq]
    · intro j _ hjk
      have : (1 : Matrix (Fin (Module.finrank ℝ E))
                (Fin (Module.finrank ℝ E)) ℝ) k j = 0 :=
        Matrix.one_apply_ne (Ne.symm hjk)
      rw [this, zero_mul]
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  · -- side goal: g.inner x ∑ᵢ cᵢ • vᵢ = ∑ᵢ cᵢ • g.inner x vᵢ
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_smul]

/-- **Chart-coordinate form of the Riesz dual** at a base-set point $x$. -/
private theorem metricRiesz_chart_form
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (φ : TangentSpace I x →L[ℝ] ℝ) :
    g.metricRiesz x φ =
      ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
              φ (chartBasisVecFiber (I := I) α j x)) •
        chartBasisVecFiber (I := I) α i x := by
  symm
  apply g.metricRiesz_unique
  intro W
  -- Reduce to equality on the chart basis via Module.Basis.ext.
  have hLM_eq :
      (g.inner x
          (∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
                  φ (chartBasisVecFiber (I := I) α j x)) •
              chartBasisVecFiber (I := I) α i x) :
          TangentSpace I x →ₗ[ℝ] ℝ)
        = (φ : TangentSpace I x →ₗ[ℝ] ℝ) := by
    apply (chartBasisFamily (I := I) α hx).ext
    intro k
    rw [chartBasisFamily_apply (I := I) α hx k]
    exact metricRiesz_chart_form_inner_e (I := I) g α hx φ k
  have := congrArg (fun (L : TangentSpace I x →ₗ[ℝ] ℝ) => L W) hLM_eq
  show g.metricInner x _ W = φ W
  exact this

/-! ## Stage 7: chart-local smoothness and the musical-iso section primitive -/

/-- **Chart-local smoothness** of the Riesz-section in chart-frame form.
Given a covector field $\Phi$ whose action on each chart-basis vector
$\Phi(y)(e_j(y))$ is smooth on the trivialization base set, the
chart-local linear combination
$$y \mapsto \sum_i \Bigl(\sum_j G^{ij}(y)\,\Phi(y)(e_j(y))\Bigr)\,e_i(y)$$
is smooth as a tangent-bundle section on the base set.

Mechanism: reduce to scalar smoothness via
`Trivialization.contMDiffOn_section_baseSet_iff`; on the base set, the
trivialization is fiber-linear, so the trivialized fiber of the sum is
$\sum_i c_i(y) \cdot (\mathrm{Module.finBasis}\,\mathbb R\,E)_i$, a finite
sum of smooth scalars times constant model-space vectors. -/
lemma metricRiesz_chartLocal_total_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    {Φ : (y : M) → TangentSpace I y →L[ℝ] ℝ}
    (hΦ : ∀ j : Fin (Module.finrank ℝ E),
        ContMDiffOn I 𝓘(ℝ) ∞
          (fun y => Φ y (chartBasisVecFiber (I := I) α j y))
          (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y
        (∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
                Φ y (chartBasisVecFiber (I := I) α j y)) •
          chartBasisVecFiber (I := I) α i y))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  set triv := trivializationAt E (TangentSpace I) α with htriv_def
  set s := triv.baseSet
  -- Step 1: smoothness of each scalar coefficient.
  have hcoef : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun y => ∑ j, chartInvGramMatrix (I := I) g α y i j *
            Φ y (chartBasisVecFiber (I := I) α j y)) s := by
    intro i
    refine contMDiffOn_finset_sum (fun j _ => ?_)
    exact (chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j).mul (hΦ j)
  -- Step 2: reduce bundle-section smoothness to scalar smoothness via
  -- `Trivialization.contMDiffOn_section_baseSet_iff`. We pick the
  -- trivialization at α (same as in the chart-Gram-matrix machinery).
  rw [triv.contMDiffOn_section_baseSet_iff (IB := I) (n := ∞)]
  -- Goal: ContMDiffOn I 𝓘(ℝ, E) ∞
  --   (fun y => (triv ⟨y, ∑ i, c_i(y) • e_i(y)⟩).2) s
  -- Use fiber-linearity of triv on s to push triv inside the sum +
  -- through scalar multiplication, ending with constant model-basis
  -- vectors.
  have hsnd_eq : ∀ y ∈ s,
      (triv ⟨y,
          ∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
                Φ y (chartBasisVecFiber (I := I) α j y)) •
            chartBasisVecFiber (I := I) α i y⟩).2
        = ∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
            Φ y (chartBasisVecFiber (I := I) α j y)) •
          (Module.finBasis ℝ E i : E) := by
    intro y hy
    -- Pointwise equation: `(triv ⟨y, v⟩).2 = continuousLinearEquivAt R y hy v`
    -- for any fiber element v. Comes from `apply_eq_prod_continuousLinearEquivAt`
    -- by taking snd.
    have hsnd_apply : ∀ v : TangentSpace I y,
        (triv ⟨y, v⟩).2 = triv.continuousLinearEquivAt ℝ y hy v := by
      intro v
      have h := triv.apply_eq_prod_continuousLinearEquivAt ℝ y hy v
      exact congrArg Prod.snd h
    rw [hsnd_apply]
    -- Apply linearity (`map_sum`, `map_smul`) and the chart-basis evaluation.
    rw [map_sum (triv.continuousLinearEquivAt ℝ y hy)]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [(triv.continuousLinearEquivAt ℝ y hy).map_smul]
    congr 1
    rw [← hsnd_apply (chartBasisVecFiber (I := I) α i y)]
    exact trivializationAt_chartBasisVec_snd (I := I) α i hy
  have hRHS_smooth :
      ContMDiffOn I 𝓘(ℝ, E) ∞
        (fun y => ∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
            Φ y (chartBasisVecFiber (I := I) α j y)) •
          (Module.finBasis ℝ E i : E)) s := by
    refine contMDiffOn_finset_sum (fun i _ => ?_)
    exact (hcoef i).smul (contMDiffOn_const (c := (Module.finBasis ℝ E i : E)))
  exact hRHS_smooth.congr (fun y hy => hsnd_eq y hy)

/-- **Smoothness of the musical isomorphism section** at a base-set point.
Given a covector field $\Phi$ whose action on each chart-basis vector is
smooth on the trivialization base set at $\alpha$, the Riesz section
$y \mapsto \sharp_g\,\Phi(y)$ is smooth at any point of the base set.

This is the framework primitive consumed by gradient and Koszul-covariant-
derivative smoothness. -/
theorem metricRiesz_section_contMDiffAt
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {Φ : (y : M) → TangentSpace I y →L[ℝ] ℝ}
    (hΦ : ∀ j : Fin (Module.finrank ℝ E),
        ContMDiffOn I 𝓘(ℝ) ∞
          (fun y => Φ y (chartBasisVecFiber (I := I) α j y))
          (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (g.metricRiesz y (Φ y))) x := by
  have hChartLocal :=
    metricRiesz_chartLocal_total_contMDiffOn (I := I) g α (Φ := Φ) hΦ
  -- Replace chart-local form with metricRiesz via Task 7.
  have hcongr : ∀ y ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      (∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
              Φ y (chartBasisVecFiber (I := I) α j y)) •
            chartBasisVecFiber (I := I) α i y) = g.metricRiesz y (Φ y) := by
    intro y hy
    exact (metricRiesz_chart_form (I := I) g α hy (Φ y)).symm
  have hMR :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => TotalSpace.mk' E y (g.metricRiesz y (Φ y)))
        (trivializationAt E (TangentSpace I) α).baseSet := by
    refine hChartLocal.congr ?_
    intro y hy
    have h := hcongr y hy
    show TotalSpace.mk' E y _ = TotalSpace.mk' E y _
    rw [h]
  -- Base set is open: `(chartAt H α).source` open ⟹ baseSet open.
  have hopen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  exact (hMR x hx).contMDiffAt (hopen.mem_nhds hx)

/-- **Per-point variant** of `metricRiesz_section_contMDiffAt`: replaces the
global `ContMDiffOn baseSet` hypothesis on the covector-section action with
`ContMDiffWithinAt baseSet x` per chart-basis index. Easier to discharge
when the covector field $\Phi$ involves locally-defined data (e.g.,
`koszulFunctional`-style expressions whose smoothness is proved via
bump-function extensions near the target point). -/
theorem metricRiesz_section_contMDiffAt_of_within
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {Φ : (y : M) → TangentSpace I y →L[ℝ] ℝ}
    (hΦ : ∀ j : Fin (Module.finrank ℝ E),
        ContMDiffWithinAt I 𝓘(ℝ) ∞
          (fun y => Φ y (chartBasisVecFiber (I := I) α j y))
          (trivializationAt E (TangentSpace I) α).baseSet x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (g.metricRiesz y (Φ y))) x := by
  classical
  set triv := trivializationAt E (TangentSpace I) α with htriv_def
  set s := triv.baseSet
  have hopen : IsOpen s := triv.open_baseSet
  have hs_nhds : s ∈ nhds x := hopen.mem_nhds hx
  -- Step 1: per-point smoothness of each scalar coefficient.
  have hcoef_at : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ) ∞
        (fun y => ∑ j, chartInvGramMatrix (I := I) g α y i j *
            Φ y (chartBasisVecFiber (I := I) α j y)) x := by
    intro i
    have hsum :
        ContMDiffWithinAt I 𝓘(ℝ) ∞
          (fun y => ∑ j, chartInvGramMatrix (I := I) g α y i j *
              Φ y (chartBasisVecFiber (I := I) α j y)) s x := by
      refine contMDiffWithinAt_finset_sum (fun j _ => ?_)
      exact ((chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j) x hx).mul (hΦ j)
    exact hsum.contMDiffAt hs_nhds
  -- Step 2: per-point smoothness of the bundle-section sum at x.
  -- Reduce to scalar smoothness of the trivialized fiber via the equation
  -- `(triv ⟨y, sum⟩).2 = ∑ i, c_i(y) • (Module.finBasis ℝ E i : E)` on s.
  have hsnd_eq : ∀ y ∈ s,
      (triv ⟨y,
          ∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
                Φ y (chartBasisVecFiber (I := I) α j y)) •
            chartBasisVecFiber (I := I) α i y⟩).2
        = ∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
            Φ y (chartBasisVecFiber (I := I) α j y)) •
          (Module.finBasis ℝ E i : E) := by
    intro y hy
    have hsnd_apply : ∀ v : TangentSpace I y,
        (triv ⟨y, v⟩).2 = triv.continuousLinearEquivAt ℝ y hy v := by
      intro v
      exact congrArg Prod.snd (triv.apply_eq_prod_continuousLinearEquivAt ℝ y hy v)
    rw [hsnd_apply]
    rw [map_sum (triv.continuousLinearEquivAt ℝ y hy)]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [(triv.continuousLinearEquivAt ℝ y hy).map_smul]
    congr 1
    rw [← hsnd_apply (chartBasisVecFiber (I := I) α i y)]
    exact trivializationAt_chartBasisVec_snd (I := I) α i hy
  -- Smoothness of the chart-form section at x via `contMDiffAt_section_iff`.
  have hChartLocal_at :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => TotalSpace.mk' E y
          (∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
                  Φ y (chartBasisVecFiber (I := I) α j y)) •
              chartBasisVecFiber (I := I) α i y)) x := by
    rw [triv.contMDiffAt_section_iff (IB := I) (n := ∞) hx]
    have hRHS_at :
        ContMDiffAt I 𝓘(ℝ, E) ∞
          (fun y => ∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
              Φ y (chartBasisVecFiber (I := I) α j y)) •
            (Module.finBasis ℝ E i : E)) x := by
      refine contMDiffAt_finset_sum (fun i _ => ?_)
      exact (hcoef_at i).smul (contMDiffAt_const (c := (Module.finBasis ℝ E i : E)))
    refine hRHS_at.congr_of_eventuallyEq ?_
    filter_upwards [hs_nhds] with y hy
    exact hsnd_eq y hy
  -- Step 3: replace chart-form with metricRiesz on a nbhd of x.
  refine hChartLocal_at.congr_of_eventuallyEq ?_
  filter_upwards [hs_nhds] with y hy
  show TotalSpace.mk' E y _ = TotalSpace.mk' E y _
  rw [(metricRiesz_chart_form (I := I) g α hy (Φ y)).symm]

/-! ## Stage 8: chart-pullback machinery for the gradient consumer

To turn the abstract primitive `metricRiesz_section_contMDiffAt` into smoothness
of `manifoldGradient`, we need to verify the chart-basis evaluation hypothesis
for `Φ := mfderiv I 𝓘(ℝ, ℝ) f`. The proof uses the chart-pullback identity
$\mathrm{d}f(e_j(x)) = \partial_j (f \circ \varphi^{-1})(\varphi(x))$ on the
chart base set (with `[I.Boundaryless]` so the chart target equals its interior). -/

section ScalarChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The pullback of `f : M → ℝ` through the inverse extended chart at `α`,
viewed as a scalar function on `E`. -/
private def scalarOnE (α : M) (f : M → ℝ) : E → ℝ :=
  fun y => f ((extChartAt I α).symm y)

/-- The directional derivative of `u : E → ℝ` at `y` along the `i`-th
model-basis vector. -/
private def partialDerivE (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) (y : E) : ℝ :=
  fderiv ℝ u y ((Module.finBasis ℝ E) i)

/-- The chart-pullback `scalarOnE α f` of a smooth function `f` is $C^\infty$
on the extended-chart target. -/
private lemma scalarOnE_contDiffOn (α : M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContDiffOn ℝ ∞ (scalarOnE (I := I) α f) (extChartAt I α).target := by
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hf_on : ContMDiffOn I 𝓘(ℝ) ∞ f Set.univ := hf.contMDiffOn
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f ∘ (extChartAt I α).symm)
      (extChartAt I α).target :=
    hf_on.comp hsymm (fun _ _ => Set.mem_univ _)
  exact hcomp.contDiffOn

/-- The partial derivative of the chart-pullback is $C^\infty$ on the interior
of the extended-chart target. -/
private lemma partialDerivE_scalarOnE_contDiffOn_interior
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (partialDerivE (E := E) i (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) := by
  have hbase : ContDiffOn ℝ ∞
      (scalarOnE (I := I) α f) (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hbase_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (interior (extChartAt I α).target) := hbase.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) :=
    hbase_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hconst : ContDiffOn ℝ ∞ (fun _ : E => (Module.finBasis ℝ E) i)
      (interior (extChartAt I α).target) := contDiffOn_const
  exact hfderiv.clm_apply hconst

/-- The partial derivative of the chart-pullback, composed with the extended
chart, is `ContMDiffOn` on the chart base set under `[I.Boundaryless]` (where
the chart target is open and hence equals its interior). -/
private lemma partialDerivE_scalarOnE_comp_extChartAt_contMDiffOn
    [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        partialDerivE (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have htgt_open : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  have htgt_int : interior (extChartAt I α).target = (extChartAt I α).target :=
    htgt_open.interior_eq
  have hpartial : ContDiffOn ℝ ∞
      (partialDerivE (E := E) i (scalarOnE (I := I) α f))
      (extChartAt I α).target := by
    rw [← htgt_int]
    exact partialDerivE_scalarOnE_contDiffOn_interior (I := I) α hf i
  have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (partialDerivE (E := E) i (scalarOnE (I := I) α f))
      (extChartAt I α).target := hpartial.contMDiffOn
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt
  have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet
      = (chartAt H α).source :=
    TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α
  rw [hbase_eq]
  refine hpartialM.comp hchart ?_
  intro x hx
  -- `extChartAt I α x ∈ target` for `x ∈ chartSource`.
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hx
  exact (extChartAt I α).map_source hxsrc

/-- **Chart-basis evaluation of `mfderiv`**: under `[I.Boundaryless]`, the
directional derivative of a smooth scalar `f` along the `i`-th chart-basis
vector equals the `i`-th partial derivative of the chart pullback, evaluated
at the chart image of the base point.

For $x \in (\mathrm{chartAt}\,H\,\alpha).\mathrm{source}$:
$$\mathrm{d}f_x(e_i^\alpha(x)) = \partial_i (f \circ \varphi_\alpha^{-1})(\varphi_\alpha(x)).$$ -/
private lemma mfderiv_chartBasisVecFiber_eq_partialDerivE
    [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M}
    (hx : x ∈ (chartAt H α).source) (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ) f x (chartBasisVecFiber (I := I) α i x)
      = partialDerivE (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  set φ := extChartAt I α
  have hxsrc : x ∈ φ.source := by
    rw [extChartAt_source]; exact hx
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]; exact hx
  have hf_mdiff : MDifferentiableAt I 𝓘(ℝ) f x :=
    hf.mdifferentiableAt (by simp)
  -- Set up: `f = scalarOnE α f ∘ φ` near `x` on `φ.source`.
  have hcomp_eq : ∀ᶠ y in nhds x, f y = (scalarOnE (I := I) α f) (φ y) := by
    have hsrc_nhd : φ.source ∈ nhds x :=
      (isOpen_extChartAt_source (I := I) α).mem_nhds hxsrc
    filter_upwards [hsrc_nhd] with y hy
    change f y = f (φ.symm (φ y))
    rw [φ.left_inv hy]
  have hcong : f =ᶠ[nhds x] (scalarOnE (I := I) α f) ∘ φ := hcomp_eq
  have hmfderiv_cong : mfderiv I 𝓘(ℝ) f x =
      mfderiv I 𝓘(ℝ) ((scalarOnE (I := I) α f) ∘ φ) x :=
    Filter.EventuallyEq.mfderiv_eq hcong
  rw [hmfderiv_cong]
  -- Differentiability of `scalarOnE α f` at `φ x`. We go through
  -- `scalarOnE α f = f ∘ φ.symm` definitionally, plus `φ.symm` smooth at `φ x`.
  have htgt_open : IsOpen φ.target := isOpen_extChartAt_target (I := I) α
  have hxtgt : φ x ∈ φ.target := φ.map_source hxsrc
  have hphi_mdiff : MDifferentiableAt I 𝓘(ℝ, E) φ x :=
    mdifferentiableAt_extChartAt (I := I) hx
  have hphi_symm_mdiff : MDifferentiableAt 𝓘(ℝ, E) I φ.symm (φ x) := by
    have hcontMDiffOn : ContMDiffOn 𝓘(ℝ, E) I ∞ φ.symm φ.target :=
      contMDiffOn_extChartAt_symm (I := I) α
    have hcont_at : ContMDiffAt 𝓘(ℝ, E) I ∞ φ.symm (φ x) :=
      (hcontMDiffOn (φ x) hxtgt).contMDiffAt (htgt_open.mem_nhds hxtgt)
    exact hcont_at.mdifferentiableAt (by simp)
  have hsymm_at_x : φ.symm (φ x) = x := φ.left_inv hxsrc
  have hf_at_symm : MDifferentiableAt I 𝓘(ℝ) f (φ.symm (φ x)) := by
    rw [hsymm_at_x]; exact hf_mdiff
  have hf_comp_symm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (f ∘ φ.symm) (φ x) :=
    hf_at_symm.comp (φ x) hphi_symm_mdiff
  have hscalar_eq : (scalarOnE (I := I) α f) = f ∘ φ.symm := by
    funext y; rfl
  have hg_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x) := by
    rw [hscalar_eq]; exact hf_comp_symm
  -- Apply chain rule for the composition `(scalarOnE α f) ∘ φ`.
  have hchain :
      mfderiv I 𝓘(ℝ) ((scalarOnE (I := I) α f) ∘ φ) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x)).comp
          (mfderiv I 𝓘(ℝ, E) φ x) :=
    mfderiv_comp x hg_mdiff hphi_mdiff
  rw [hchain]
  -- `mfderiv (E → ℝ) (scalarOnE α f) = fderiv ℝ (scalarOnE α f)` (model space).
  rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x)
      = fderiv ℝ (scalarOnE (I := I) α f) (φ x) from
        mfderiv_eq_fderiv (𝕜 := ℝ) (f := scalarOnE (I := I) α f)]
  -- Identify `mfderiv φ x (chartBasisVecFiber α i x) = Module.finBasis ℝ E i`
  -- via the tangent-bundle trivialization at α applied to chartBasisVec.
  have hmfderiv_chartBasis :
      mfderiv I 𝓘(ℝ, E) φ x (chartBasisVecFiber (I := I) α i x)
        = (Module.finBasis ℝ E) i := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hx]
    set T : Bundle.Trivialization E
        (Bundle.TotalSpace.proj : Bundle.TotalSpace E (TangentSpace I : M → Type _)
          → M) := trivializationAt E (TangentSpace I) α
    -- chartBasisVecFiber α i x = T.symm x (basis i) = (T.symmL ℝ x) (basis i).
    have heq : chartBasisVecFiber (I := I) α i x =
        (T.symmL ℝ x) ((Module.finBasis ℝ E) i) := by
      show T.symm x ((Module.finBasis ℝ E) i) = (T.symmL ℝ x) ((Module.finBasis ℝ E) i)
      rfl
    rw [heq]
    exact T.continuousLinearMapAt_symmL (R := ℝ) hbase ((Module.finBasis ℝ E) i)
  -- Conclude via `mfderiv (scalarOnE α f)(φ x) = fderiv` + identification of
  -- composition value with the partial derivative.
  show (fderiv ℝ (scalarOnE (I := I) α f) (φ x))
        ((mfderiv I 𝓘(ℝ, E) φ x) (chartBasisVecFiber (I := I) α i x)) =
    partialDerivE (E := E) i (scalarOnE (I := I) α f) (φ x)
  rw [hmfderiv_chartBasis]
  rfl

/-- Smoothness of the directional derivative `y ↦ mfderiv f y (V y)` on the
trivialization base set at $\alpha$, for a smooth scalar function $f$ and a
smooth tangent-bundle section $V$, under `[I.Boundaryless]`.

Chart-pullback decomposition: on the base set,
$$\mathrm{d}f_y(V(y)) = \mathrm{d}(f\circ\varphi_\alpha^{-1})_{\varphi_\alpha(y)}
    \bigl(V^{\mathrm{chart}}(y)\bigr),$$
where $V^{\mathrm{chart}}(y) := \mathrm{triv}_\alpha\langle y, V(y)\rangle_2 \in E$
is the chart-frame coordinate of $V(y)$. The RHS is smooth in $y$ on the base
set because (i) $f\circ\varphi_\alpha^{-1}$ is $C^\infty$ on the chart target
(`scalarOnE_contDiffOn`), (ii) `fderiv` of a $C^\infty$ function on an open set
is $C^\infty$, (iii) `extChartAt I α` is smooth on its source, and (iv)
$V^{\mathrm{chart}}$ is smooth on the base set by
`Trivialization.contMDiffOn_section_baseSet_iff`. -/
lemma mfderiv_apply_section_contMDiffOn
    [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {V : (y : M) → TangentSpace I y}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (TotalSpace.mk' E y (V y) :
        TotalSpace E (TangentSpace I : M → Type _)))) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun y => mfderiv I 𝓘(ℝ) f y (V y))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  set triv := trivializationAt E (TangentSpace I) α with htriv_def
  set s := triv.baseSet
  -- `V` evaluated in chart coords at α: smooth on `s`.
  have hVchart_total :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun y => (TotalSpace.mk' E y (V y) :
          TotalSpace E (TangentSpace I : M → Type _))) s :=
    hV.contMDiffOn
  have hVchart_snd :
      ContMDiffOn I 𝓘(ℝ, E) ∞
        (fun y => (triv ⟨y, V y⟩).2) s :=
    (triv.contMDiffOn_section_baseSet_iff (IB := I) (n := ∞)).mp hVchart_total
  -- `fderiv (scalarOnE α f)` smooth on the (open under Boundaryless) chart target.
  have htgt_open : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  have hsmooth : ContDiffOn ℝ ∞
      (scalarOnE (I := I) α f) (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hfderiv_smooth : ContDiffOn ℝ ∞
      (fderiv ℝ (scalarOnE (I := I) α f)) (extChartAt I α).target :=
    hsmooth.fderiv_of_isOpen htgt_open (by rw [ENat.coe_top_add_one])
  have hfderivM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] ℝ) ∞
      (fderiv ℝ (scalarOnE (I := I) α f)) (extChartAt I α).target :=
    hfderiv_smooth.contMDiffOn
  -- Compose with `extChartAt I α` (smooth on its source = `s`).
  have hbase_eq : s = (chartAt H α).source :=
    TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E) s := by
    rw [hbase_eq]; exact contMDiffOn_extChartAt
  have hfderivComp :
      ContMDiffOn I 𝓘(ℝ, E →L[ℝ] ℝ) ∞
        (fun y => fderiv ℝ (scalarOnE (I := I) α f) (extChartAt I α y)) s := by
    refine hfderivM.comp hchart ?_
    intro y hy
    have hysrc : y ∈ (extChartAt I α).source := by
      rw [extChartAt_source, ← hbase_eq]; exact hy
    exact (extChartAt I α).map_source hysrc
  -- Combine via `ContMDiffOn.clm_apply`.
  have happly :
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun y => fderiv ℝ (scalarOnE (I := I) α f) (extChartAt I α y)
          ((triv ⟨y, V y⟩).2)) s := hfderivComp.clm_apply hVchart_snd
  refine happly.congr ?_
  intro y hy
  -- Identify the RHS with mfderiv via the chain rule (analog of
  -- `mfderiv_chartBasisVecFiber_eq_partialDerivE`).
  have hy_chart : y ∈ (chartAt H α).source := by rw [← hbase_eq]; exact hy
  -- mfderiv f y (V y) = fderiv (scalarOnE α f) (extChartAt α y) (mfderiv (extChartAt α) y (V y)).
  set φ := extChartAt I α
  have hysrc : y ∈ φ.source := by
    rw [extChartAt_source]; exact hy_chart
  have hf_mdiff : MDifferentiableAt I 𝓘(ℝ) f y := hf.mdifferentiableAt (by simp)
  have hcomp_eq : ∀ᶠ z in nhds y, f z = (scalarOnE (I := I) α f) (φ z) := by
    have hsrc_nhd : φ.source ∈ nhds y :=
      (isOpen_extChartAt_source (I := I) α).mem_nhds hysrc
    filter_upwards [hsrc_nhd] with z hz
    change f z = f (φ.symm (φ z))
    rw [φ.left_inv hz]
  have hcong : f =ᶠ[nhds y] (scalarOnE (I := I) α f) ∘ φ := hcomp_eq
  have hmfderiv_cong : mfderiv I 𝓘(ℝ) f y =
      mfderiv I 𝓘(ℝ) ((scalarOnE (I := I) α f) ∘ φ) y :=
    Filter.EventuallyEq.mfderiv_eq hcong
  have hytgt : φ y ∈ φ.target := φ.map_source hysrc
  have hphi_mdiff : MDifferentiableAt I 𝓘(ℝ, E) φ y :=
    mdifferentiableAt_extChartAt (I := I) hy_chart
  have hphi_symm_mdiff : MDifferentiableAt 𝓘(ℝ, E) I φ.symm (φ y) := by
    have hcontMDiffOn : ContMDiffOn 𝓘(ℝ, E) I ∞ φ.symm φ.target :=
      contMDiffOn_extChartAt_symm (I := I) α
    have hcont_at : ContMDiffAt 𝓘(ℝ, E) I ∞ φ.symm (φ y) :=
      (hcontMDiffOn (φ y) hytgt).contMDiffAt (htgt_open.mem_nhds hytgt)
    exact hcont_at.mdifferentiableAt (by simp)
  have hsymm_at_y : φ.symm (φ y) = y := φ.left_inv hysrc
  have hf_at_symm : MDifferentiableAt I 𝓘(ℝ) f (φ.symm (φ y)) := by
    rw [hsymm_at_y]; exact hf_mdiff
  have hf_comp_symm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (f ∘ φ.symm) (φ y) :=
    hf_at_symm.comp (φ y) hphi_symm_mdiff
  have hscalar_eq : (scalarOnE (I := I) α f) = f ∘ φ.symm := by funext z; rfl
  have hg_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ y) := by
    rw [hscalar_eq]; exact hf_comp_symm
  have hchain :
      mfderiv I 𝓘(ℝ) ((scalarOnE (I := I) α f) ∘ φ) y =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ y)).comp
          (mfderiv I 𝓘(ℝ, E) φ y) :=
    mfderiv_comp y hg_mdiff hphi_mdiff
  rw [hmfderiv_cong, hchain]
  rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ y)
      = fderiv ℝ (scalarOnE (I := I) α f) (φ y) from
        mfderiv_eq_fderiv (𝕜 := ℝ) (f := scalarOnE (I := I) α f)]
  -- Identify the action of `mfderiv (extChartAt I α) y` on `V y` with
  -- `triv.continuousLinearMapAt ℝ y (V y) = (triv ⟨y, V y⟩).2`.
  have hcLMAt :
      (triv.continuousLinearMapAt ℝ y) (V y) = (triv ⟨y, V y⟩).2 := by
    have hLEq := Bundle.Trivialization.coe_continuousLinearEquivAt_eq
      (R := ℝ) (e := triv) hy
    have h1 : (triv.continuousLinearEquivAt ℝ y hy) (V y) = (triv ⟨y, V y⟩).2 :=
      congrArg Prod.snd (triv.apply_eq_prod_continuousLinearEquivAt ℝ y hy (V y))
    have h2 : (triv.continuousLinearEquivAt ℝ y hy : TangentSpace I y → E)
        = triv.continuousLinearMapAt ℝ y := hLEq
    have h3 := congrFun h2 (V y)
    rw [h3] at h1
    exact h1
  have hmfderiv_eq : (mfderiv I 𝓘(ℝ, E) φ y) (V y) = (triv ⟨y, V y⟩).2 := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
        (x₀ := α) (x := y) hy_chart]
    exact hcLMAt
  show (fderiv ℝ (scalarOnE (I := I) α f) (φ y))
        ((mfderiv I 𝓘(ℝ, E) φ y) (V y)) =
      (fderiv ℝ (scalarOnE (I := I) α f) (φ y)) ((triv ⟨y, V y⟩).2)
  rw [hmfderiv_eq]

/-- Global version of `mfderiv_apply_section_contMDiffOn`: under `[I.Boundaryless]`,
the directional derivative of a smooth scalar along a smooth tangent section is
smooth on all of $M$. -/
lemma mfderiv_apply_section_contMDiff
    [I.Boundaryless]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {V : (y : M) → TangentSpace I y}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (TotalSpace.mk' E y (V y) :
        TotalSpace E (TangentSpace I : M → Type _)))) :
    ContMDiff I 𝓘(ℝ) ∞
      (fun y => mfderiv I 𝓘(ℝ) f y (V y)) := by
  intro y
  have hy_base : y ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) y]
    exact mem_chart_source H y
  have hOn := mfderiv_apply_section_contMDiffOn (I := I) y hf hV
  have hopen : IsOpen (trivializationAt E (TangentSpace I) y).baseSet :=
    (trivializationAt E (TangentSpace I) y).open_baseSet
  exact (hOn y hy_base).contMDiffAt (hopen.mem_nhds hy_base)

/-- Smoothness of the directional derivative `y ↦ mfderiv f y (chartBasisVecFiber α j y)`
on the trivialization base set, under `[I.Boundaryless]`. Used to discharge the
covector-section hypothesis of `metricRiesz_section_contMDiffAt` for the
gradient consumer. -/
lemma mfderiv_chartBasisVec_apply_contMDiffOn
    [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun y => mfderiv I 𝓘(ℝ) f y (chartBasisVecFiber (I := I) α j y))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hpartial :=
    partialDerivE_scalarOnE_comp_extChartAt_contMDiffOn (I := I) α hf j
  refine hpartial.congr ?_
  intro y hy
  have hy_chart : y ∈ (chartAt H α).source := by
    rw [← TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
    exact hy
  exact mfderiv_chartBasisVecFiber_eq_partialDerivE (I := I) α hf hy_chart j

end ScalarChart

end Tensor
end Riemannian

end
