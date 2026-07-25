import DifferentialGeometry.Geometry.Boundary.InducedMetric
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Mul


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

def boundaryChartBasisVecFiber (α₀ : BoundaryManifold I M)
    (i : Fin (Module.finrank ℝ hI.boundaryE)) (α : BoundaryManifold I M) :
    TangentSpace hI.boundaryI α :=
  (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symm α
    ((Module.finBasis ℝ hI.boundaryE) i)

def boundaryChartBasisVec (α₀ : BoundaryManifold I M)
    (i : Fin (Module.finrank ℝ hI.boundaryE)) :
    BoundaryManifold I M →
      TotalSpace hI.boundaryE (TangentSpace hI.boundaryI : BoundaryManifold I M → Type _) :=
  fun α => TotalSpace.mk' hI.boundaryE α (boundaryChartBasisVecFiber α₀ i α)

omit [FiniteDimensional ℝ E] in
@[simp] lemma boundaryChartBasisVec_proj
    (α₀ : BoundaryManifold I M) (i : Fin (Module.finrank ℝ hI.boundaryE))
    (α : BoundaryManifold I M) :
    (boundaryChartBasisVec (M := M) α₀ i α).proj = α := rfl

omit [FiniteDimensional ℝ E] in
@[simp] lemma boundaryChartBasisVec_snd
    (α₀ : BoundaryManifold I M) (i : Fin (Module.finrank ℝ hI.boundaryE))
    (α : BoundaryManifold I M) :
    (boundaryChartBasisVec (M := M) α₀ i α).2 =
      boundaryChartBasisVecFiber (M := M) α₀ i α := rfl

omit [FiniteDimensional ℝ E] in
lemma trivializationAt_boundaryChartBasisVec_snd
    (α₀ : BoundaryManifold I M) (i : Fin (Module.finrank ℝ hI.boundaryE))
    {α : BoundaryManifold I M}
    (hα : α ∈ (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet) :
    (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀
        ⟨α, boundaryChartBasisVecFiber (M := M) α₀ i α⟩).2
      = (Module.finBasis ℝ hI.boundaryE) i := by
  have h := (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).apply_mk_symm hα
    ((Module.finBasis ℝ hI.boundaryE) i)
  simpa [boundaryChartBasisVecFiber] using congrArg Prod.snd h

omit [FiniteDimensional ℝ E] in
lemma boundaryChartBasisVec_contMDiffOn
    (α₀ : BoundaryManifold I M) (i : Fin (Module.finrank ℝ hI.boundaryE)) :
    ContMDiffOn hI.boundaryI (hI.boundaryI.prod 𝓘(ℝ, hI.boundaryE)) ∞
      (boundaryChartBasisVec (M := M) α₀ i)
      (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet := by
  have hiff :=
    ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀)).contMDiffOn_section_baseSet_iff
      (IB := hI.boundaryI) (n := ∞)
      (s := fun α => boundaryChartBasisVecFiber (M := M) α₀ i α)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn hI.boundaryI 𝓘(ℝ, hI.boundaryE) ∞
      (fun _ : BoundaryManifold I M => (Module.finBasis ℝ hI.boundaryE) i)
      (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet :=
    contMDiffOn_const
  refine hconst.congr ?_
  intro α hα
  exact (trivializationAt_boundaryChartBasisVec_snd (M := M) α₀ i hα)

def boundaryChartBasisFamily (α₀ : BoundaryManifold I M) {α : BoundaryManifold I M}
    (hα : α ∈ (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet) :
    Module.Basis (Fin (Module.finrank ℝ hI.boundaryE)) ℝ (TangentSpace hI.boundaryI α) :=
  (Module.finBasis ℝ hI.boundaryE).map
    (ContinuousLinearEquiv.toLinearEquiv
      ((trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) α₀).continuousLinearEquivAt ℝ α hα).symm)

omit [FiniteDimensional ℝ E] in
lemma boundaryChartBasisFamily_apply
    (α₀ : BoundaryManifold I M) {α : BoundaryManifold I M}
    (hα : α ∈ (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet)
    (i : Fin (Module.finrank ℝ hI.boundaryE)) :
    boundaryChartBasisFamily (M := M) α₀ hα i =
      boundaryChartBasisVecFiber (M := M) α₀ i α := by
  unfold boundaryChartBasisFamily boundaryChartBasisVecFiber
  rw [Module.Basis.map_apply]
  rfl

omit [FiniteDimensional ℝ E] in
lemma boundaryChartBasisFamily_linearIndependent
    (α₀ : BoundaryManifold I M) {α : BoundaryManifold I M}
    (hα : α ∈ (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet) :
    LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ hI.boundaryE) =>
        boundaryChartBasisVecFiber (M := M) α₀ i α) := by
  have h := (boundaryChartBasisFamily (M := M) α₀ hα).linearIndependent
  have hcongr :
      (boundaryChartBasisFamily (M := M) α₀ hα :
        Fin (Module.finrank ℝ hI.boundaryE) → TangentSpace hI.boundaryI α)
      = fun i => boundaryChartBasisVecFiber (M := M) α₀ i α := by
    funext i
    exact boundaryChartBasisFamily_apply (M := M) α₀ hα i
  rw [← hcongr]
  exact h

def boundaryGramMatrix (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) (α : BoundaryManifold I M) :
    Matrix (Fin (Module.finrank ℝ hI.boundaryE))
      (Fin (Module.finrank ℝ hI.boundaryE)) ℝ :=
  Matrix.of fun i j =>
    inducedMetricInner (M := M) g α
      (boundaryChartBasisVecFiber (M := M) α₀ i α)
      (boundaryChartBasisVecFiber (M := M) α₀ j α)

omit [FiniteDimensional ℝ E] in
@[simp] lemma boundaryGramMatrix_apply
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) (α : BoundaryManifold I M)
    (i j : Fin (Module.finrank ℝ hI.boundaryE)) :
    boundaryGramMatrix (M := M) g α₀ α i j =
      inducedMetricInner (M := M) g α
        (boundaryChartBasisVecFiber (M := M) α₀ i α)
        (boundaryChartBasisVecFiber (M := M) α₀ j α) := rfl

omit [FiniteDimensional ℝ E] in
lemma boundaryGramMatrix_isHermitian
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) (α : BoundaryManifold I M) :
    (boundaryGramMatrix (M := M) g α₀ α).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  show star (boundaryGramMatrix (M := M) g α₀ α j i) =
    boundaryGramMatrix (M := M) g α₀ α i j
  rw [boundaryGramMatrix_apply, boundaryGramMatrix_apply, star_trivial]
  exact inducedMetricInner_symm (M := M) g α
    (boundaryChartBasisVecFiber (M := M) α₀ j α)
    (boundaryChartBasisVecFiber (M := M) α₀ i α)

omit [FiniteDimensional ℝ E] in
lemma boundaryGramMatrix_dotProduct_mulVec
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) (α : BoundaryManifold I M)
    (c : Fin (Module.finrank ℝ hI.boundaryE) → ℝ) :
    star c ⬝ᵥ (boundaryGramMatrix (M := M) g α₀ α) *ᵥ c =
      inducedMetricInner (M := M) g α
        (∑ i, c i • boundaryChartBasisVecFiber (M := M) α₀ i α)
        (∑ j, c j • boundaryChartBasisVecFiber (M := M) α₀ j α) := by
  have hexpand' :
      inducedMetricInner (M := M) g α
          (∑ i, c i • boundaryChartBasisVecFiber (M := M) α₀ i α)
          (∑ j, c j • boundaryChartBasisVecFiber (M := M) α₀ j α)
        = ∑ i, ∑ j, (c i * c j) *
            inducedMetricInner (M := M) g α
              (boundaryChartBasisVecFiber (M := M) α₀ i α)
              (boundaryChartBasisVecFiber (M := M) α₀ j α) := by
    have hL :
        inducedMetricInner (M := M) g α
            (∑ i, c i • boundaryChartBasisVecFiber (M := M) α₀ i α)
          = ∑ i, c i • inducedMetricInner (M := M) g α
              (boundaryChartBasisVecFiber (M := M) α₀ i α) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      exact ContinuousLinearMap.map_smul _ _ _
    rw [hL]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ContinuousLinearMap.smul_apply]
    have hR :
        (inducedMetricInner (M := M) g α
            (boundaryChartBasisVecFiber (M := M) α₀ i α))
            (∑ j, c j • boundaryChartBasisVecFiber (M := M) α₀ j α)
          = ∑ j, c j *
              (inducedMetricInner (M := M) g α
                (boundaryChartBasisVecFiber (M := M) α₀ i α))
                (boundaryChartBasisVecFiber (M := M) α₀ j α) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      change _ = c j * _
      rw [← smul_eq_mul]
      exact ContinuousLinearMap.map_smul _ _ _
    rw [hR, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hexpand']
  simp only [dotProduct, Matrix.mulVec, boundaryGramMatrix_apply, Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

omit [FiniteDimensional ℝ E] in
lemma boundaryGramMatrix_posDef
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) {α : BoundaryManifold I M}
    (hα : α ∈ (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet) :
    (boundaryGramMatrix (M := M) g α₀ α).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (boundaryGramMatrix_isHermitian (M := M) g α₀ α) ?_
  intro c hc
  set w : TangentSpace hI.boundaryI α :=
    ∑ i, c i • boundaryChartBasisVecFiber (M := M) α₀ i α with hw_def
  have heq := boundaryGramMatrix_dotProduct_mulVec (M := M) g α₀ α c
  rw [heq]
  have hwnz : w ≠ 0 := by
    intro hw0
    have hli := boundaryChartBasisFamily_linearIndependent (M := M) α₀ hα
    rw [Fintype.linearIndependent_iff] at hli
    have : c = 0 := funext (hli c hw0)
    exact hc this
  exact inducedMetricInner_pos (M := M) g α w hwnz

omit [FiniteDimensional ℝ E] in
lemma boundaryGramMatrix_det_pos
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) {α : BoundaryManifold I M}
    (hα : α ∈ (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet) :
    0 < (boundaryGramMatrix (M := M) g α₀ α).det :=
  (boundaryGramMatrix_posDef (M := M) g α₀ hα).det_pos

omit [FiniteDimensional ℝ E] in
theorem boundaryGramMatrix_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M)
    (i j : Fin (Module.finrank ℝ hI.boundaryE)) :
    ContMDiffOn hI.boundaryI 𝓘(ℝ) ∞
      (fun α => boundaryGramMatrix (M := M) g α₀ α i j)
      (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet := by
  have hg : ContMDiffOn hI.boundaryI
      (hI.boundaryI.prod 𝓘(ℝ, hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)) ∞
      (fun b : BoundaryManifold I M => TotalSpace.mk' (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
        (E := fun y => TangentSpace hI.boundaryI y →L[ℝ] TangentSpace hI.boundaryI y →L[ℝ] ℝ)
        b (inducedMetricInner (M := M) g b))
      (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet :=
    (inducedMetricInner_contMDiff (M := M) g).contMDiffOn
  have hv := boundaryChartBasisVec_contMDiffOn (M := M) α₀ i
  have hw := boundaryChartBasisVec_contMDiffOn (M := M) α₀ j
  have happ :
      ContMDiffOn hI.boundaryI (hI.boundaryI.prod 𝓘(ℝ, ℝ)) ∞
        (fun α : BoundaryManifold I M => (⟨α,
            inducedMetricInner (M := M) g α
              (boundaryChartBasisVecFiber (M := M) α₀ i α)
              (boundaryChartBasisVecFiber (M := M) α₀ j α)⟩ :
              TotalSpace ℝ (Bundle.Trivial (BoundaryManifold I M) ℝ)))
        (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet :=
    ContMDiffOn.clm_bundle_apply₂
      (F₁ := hI.boundaryE) (F₂ := hI.boundaryE) (F₃ := ℝ)
      (b := id) hg hv hw
  intro α hα
  have hpα := happ α hα
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpα
  exact hpα.2

omit [FiniteDimensional ℝ E] in
lemma boundaryGramMatrix_det_contMDiffOn
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) :
    ContMDiffOn hI.boundaryI 𝓘(ℝ) ∞
      (fun α => (boundaryGramMatrix (M := M) g α₀ α).det)
      (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet := by
  classical
  have hexp :
      (fun α : BoundaryManifold I M => (boundaryGramMatrix (M := M) g α₀ α).det)
        = (fun α : BoundaryManifold I M =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ hI.boundaryE)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ i, boundaryGramMatrix (M := M) g α₀ α (σ i) i) := by
    funext α
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul
    (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finset_prod (fun i _ => ?_)
  exact boundaryGramMatrix_entry_contMDiffOn (M := M) g α₀ (σ i) i

def boundaryInvGramMatrix (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) (α : BoundaryManifold I M) :
    Matrix (Fin (Module.finrank ℝ hI.boundaryE))
      (Fin (Module.finrank ℝ hI.boundaryE)) ℝ :=
  (boundaryGramMatrix (M := M) g α₀ α)⁻¹

omit [FiniteDimensional ℝ E] in
lemma boundaryInvGramMatrix_mul_boundaryGramMatrix
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) {α : BoundaryManifold I M}
    (hα : α ∈ (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet) :
    boundaryInvGramMatrix (M := M) g α₀ α *
      boundaryGramMatrix (M := M) g α₀ α = 1 := by
  have hpos := boundaryGramMatrix_posDef (M := M) g α₀ hα
  have hdet_unit : IsUnit (boundaryGramMatrix (M := M) g α₀ α).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  unfold boundaryInvGramMatrix
  exact Matrix.nonsing_inv_mul _ hdet_unit

omit [FiniteDimensional ℝ E] in
lemma boundaryGramMatrix_mul_boundaryInvGramMatrix
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) {α : BoundaryManifold I M}
    (hα : α ∈ (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet) :
    boundaryGramMatrix (M := M) g α₀ α *
      boundaryInvGramMatrix (M := M) g α₀ α = 1 := by
  have hpos := boundaryGramMatrix_posDef (M := M) g α₀ hα
  have hdet_unit : IsUnit (boundaryGramMatrix (M := M) g α₀ α).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  unfold boundaryInvGramMatrix
  exact Matrix.mul_nonsing_inv _ hdet_unit

omit [FiniteDimensional ℝ E] in
lemma boundaryGramMatrix_adjugate_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M)
    (i j : Fin (Module.finrank ℝ hI.boundaryE)) :
    ContMDiffOn hI.boundaryI 𝓘(ℝ) ∞
      (fun α : BoundaryManifold I M =>
        (boundaryGramMatrix (M := M) g α₀ α).adjugate i j)
      (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet := by
  classical
  have hexp : (fun α : BoundaryManifold I M =>
        (boundaryGramMatrix (M := M) g α₀ α).adjugate i j) =
      (fun α : BoundaryManifold I M =>
        ((boundaryGramMatrix (M := M) g α₀ α).updateRow j
          (Pi.single i (1 : ℝ))).det) := by
    funext α
    exact Matrix.adjugate_apply _ _ _
  rw [hexp]
  have hexp2 : (fun α : BoundaryManifold I M =>
        ((boundaryGramMatrix (M := M) g α₀ α).updateRow j
          (Pi.single i (1 : ℝ))).det) =
      (fun α : BoundaryManifold I M =>
        ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ hI.boundaryE)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ k, (boundaryGramMatrix (M := M) g α₀ α).updateRow j
                (Pi.single i (1 : ℝ)) (σ k) k) := by
    funext α
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp2]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finset_prod (fun k _ => ?_)
  by_cases hσk : σ k = j
  · have heq : (fun α : BoundaryManifold I M =>
        (boundaryGramMatrix (M := M) g α₀ α).updateRow j
          (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun _ : BoundaryManifold I M =>
          (Pi.single (M := fun _ : Fin (Module.finrank ℝ hI.boundaryE) => ℝ) i
            (1 : ℝ)) k) := by
      funext α
      rw [hσk, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · have heq : (fun α : BoundaryManifold I M =>
        (boundaryGramMatrix (M := M) g α₀ α).updateRow j
          (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun α : BoundaryManifold I M =>
          boundaryGramMatrix (M := M) g α₀ α (σ k) k) := by
      funext α
      rw [Matrix.updateRow_ne hσk]
    rw [heq]
    exact boundaryGramMatrix_entry_contMDiffOn (M := M) g α₀ (σ k) k

omit [FiniteDimensional ℝ E] in
theorem boundaryInvGramMatrix_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M)
    (i j : Fin (Module.finrank ℝ hI.boundaryE)) :
    ContMDiffOn hI.boundaryI 𝓘(ℝ) ∞
      (fun α : BoundaryManifold I M =>
        boundaryInvGramMatrix (M := M) g α₀ α i j)
      (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet := by
  classical
  have hcongr : ∀ α ∈ (trivializationAt hI.boundaryE
      (TangentSpace hI.boundaryI) α₀).baseSet,
      boundaryInvGramMatrix (M := M) g α₀ α i j =
        ((boundaryGramMatrix (M := M) g α₀ α).det)⁻¹ *
          (boundaryGramMatrix (M := M) g α₀ α).adjugate i j := by
    intro α hα
    have hdet_pos := boundaryGramMatrix_det_pos (M := M) g α₀ hα
    have hdet_ne : (boundaryGramMatrix (M := M) g α₀ α).det ≠ 0 := ne_of_gt hdet_pos
    unfold boundaryInvGramMatrix
    rw [Matrix.inv_def]
    change (Ring.inverse (boundaryGramMatrix (M := M) g α₀ α).det •
            (boundaryGramMatrix (M := M) g α₀ α).adjugate) i j =
      ((boundaryGramMatrix (M := M) g α₀ α).det)⁻¹ *
          (boundaryGramMatrix (M := M) g α₀ α).adjugate i j
    rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    exact Ring.inverse_eq_inv _
  refine ContMDiffOn.congr ?_ hcongr
  refine ContMDiffOn.mul ?_ ?_
  · have hdet_smooth : ContMDiffOn hI.boundaryI 𝓘(ℝ) ∞
        (fun α : BoundaryManifold I M =>
          (boundaryGramMatrix (M := M) g α₀ α).det)
        (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet :=
      boundaryGramMatrix_det_contMDiffOn (M := M) g α₀
    intro α hα
    have hdet_pos := boundaryGramMatrix_det_pos (M := M) g α₀ hα
    have hdet_ne : (boundaryGramMatrix (M := M) g α₀ α).det ≠ 0 := ne_of_gt hdet_pos
    have hsmooth_inv : ContDiffAt ℝ ∞ (fun y : ℝ => y⁻¹)
        (boundaryGramMatrix (M := M) g α₀ α).det := contDiffAt_inv _ hdet_ne
    have h_at := hdet_smooth α hα
    exact hsmooth_inv.contMDiffAt.comp_contMDiffWithinAt α h_at
  · exact boundaryGramMatrix_adjugate_entry_contMDiffOn (M := M) g α₀ i j

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
