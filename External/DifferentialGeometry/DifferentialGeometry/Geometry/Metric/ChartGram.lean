import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

export DifferentialGeometry (SmoothRiemannianMetric)

@[irreducible] def chartModelBasis (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.map
    (toEuclidean (E := E)).symm.toLinearEquiv

@[simp] lemma chartModelBasis_apply (i : Fin (Module.finrank ℝ E)) :
    chartModelBasis E i =
      (toEuclidean (E := E)).symm (EuclideanSpace.single i (1 : ℝ)) := by
  classical
  with_unfolding_all
    change (toEuclidean (E := E)).symm.toLinearEquiv
        ((EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis i) =
      (toEuclidean (E := E)).symm (EuclideanSpace.single i (1 : ℝ))
  simp [OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply (𝕜 := ℝ) (ι := Fin (Module.finrank ℝ E))]

def chartBasisVecFiber (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    TangentSpace I x :=
  (trivializationAt E (TangentSpace I) x₀).symm x ((chartModelBasis E) i)

def chartBasisVec (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    M → TotalSpace E (TangentSpace I : M → Type _) :=
  fun x => TotalSpace.mk' E x (chartBasisVecFiber (I := I) x₀ i x)

@[simp] lemma chartBasisVec_proj (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    (chartBasisVec (I := I) x₀ i x).proj = x := rfl

@[simp] lemma chartBasisVec_snd (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    (chartBasisVec (I := I) x₀ i x).2 = chartBasisVecFiber (I := I) x₀ i x := rfl

lemma trivializationAt_chartBasisVec_snd
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (trivializationAt E (TangentSpace I) x₀
        ⟨x, chartBasisVecFiber (I := I) x₀ i x⟩).2
      = (chartModelBasis E) i := by
  have h := (trivializationAt E (TangentSpace I) x₀).apply_mk_symm hx
    ((chartModelBasis E) i)
  simpa [chartBasisVecFiber] using congrArg Prod.snd h

lemma chartBasisVec_contMDiffOn
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (chartBasisVec (I := I) x₀ i)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hiff :=
    ((trivializationAt E (TangentSpace I) x₀)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞) (s := fun x => chartBasisVecFiber (I := I) x₀ i x)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun _ : M => (chartModelBasis E) i)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
    contMDiffOn_const
  refine hconst.congr ?_
  intro x hx
  exact (trivializationAt_chartBasisVec_snd (I := I) x₀ i hx)

lemma chartAlphaFrame_section_contMDiffOn
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I I.tangent ∞
      (fun b : M => TotalSpace.mk' E b
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b
          (chartModelBasis E i)))
      (chartAt H α).source := by
  have h_funext :
      (fun b : M => TotalSpace.mk' E b
          ((trivializationAt E (TangentSpace I) α).symmL ℝ b
            (chartModelBasis E i)))
        = chartBasisVec (I := I) α i := by
    funext b
    rfl
  rw [h_funext]
  have h_base := chartBasisVec_contMDiffOn (I := I) α i
  have h_baseSet :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    TangentBundle.trivializationAt_baseSet (I := I) α
  rw [h_baseSet] at h_base
  exact h_base

def chartBasisFamily (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
  (chartModelBasis E).map
    (ContinuousLinearEquiv.toLinearEquiv
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x hx).symm)

lemma chartBasisFamily_apply (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisFamily (I := I) x₀ hx i =
      chartBasisVecFiber (I := I) x₀ i x := by
  unfold chartBasisFamily chartBasisVecFiber
  rw [Module.Basis.map_apply]
  rfl

lemma chartBasisFamily_linearIndependent (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        chartBasisVecFiber (I := I) x₀ i x) := by
  have h := (chartBasisFamily (I := I) x₀ hx).linearIndependent
  have hcongr : (chartBasisFamily (I := I) x₀ hx : Fin (Module.finrank ℝ E) → TangentSpace I x)
      = fun i => chartBasisVecFiber (I := I) x₀ i x := by
    funext i
    exact chartBasisFamily_apply (I := I) x₀ hx i
  rw [← hcongr]
  exact h

def chartGramMatrix (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    g.inner x
      (chartBasisVecFiber (I := I) x₀ i x)
      (chartBasisVecFiber (I := I) x₀ j x)

@[simp] lemma chartGramMatrix_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix g x₀ x i j =
      g.inner x
        (chartBasisVecFiber (I := I) x₀ i x)
        (chartBasisVecFiber (I := I) x₀ j x) := rfl

lemma chartGramMatrix_isHermitian
    (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M) :
    (chartGramMatrix g x₀ x).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  show star (chartGramMatrix g x₀ x j i) = chartGramMatrix g x₀ x i j
  rw [chartGramMatrix_apply, chartGramMatrix_apply, star_trivial]
  exact g.symm x
    (chartBasisVecFiber (I := I) x₀ j x)
    (chartBasisVecFiber (I := I) x₀ i x)

lemma chartGramMatrix_dotProduct_mulVec
    (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M)
    (c : Fin (Module.finrank ℝ E) → ℝ) :
    star c ⬝ᵥ (chartGramMatrix g x₀ x) *ᵥ c =
      g.inner x
        (∑ i, c i • chartBasisVecFiber (I := I) x₀ i x)
        (∑ j, c j • chartBasisVecFiber (I := I) x₀ j x) := by
  have hexpand' :
      g.inner x
          (∑ i, c i • chartBasisVecFiber (I := I) x₀ i x)
          (∑ j, c j • chartBasisVecFiber (I := I) x₀ j x)
        = ∑ i, ∑ j, (c i * c j) *
            g.inner x
              (chartBasisVecFiber (I := I) x₀ i x)
              (chartBasisVecFiber (I := I) x₀ j x) := by
    have hL :
        g.inner x (∑ i, c i • chartBasisVecFiber (I := I) x₀ i x)
          = ∑ i, c i • g.inner x (chartBasisVecFiber (I := I) x₀ i x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
    rw [hL]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ContinuousLinearMap.smul_apply]
    have hR :
        g.inner x (chartBasisVecFiber (I := I) x₀ i x)
            (∑ j, c j • chartBasisVecFiber (I := I) x₀ j x)
          = ∑ j, c j *
              g.inner x
                (chartBasisVecFiber (I := I) x₀ i x)
                (chartBasisVecFiber (I := I) x₀ j x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [map_smul, smul_eq_mul]
    rw [hR, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hexpand']
  simp only [dotProduct, Matrix.mulVec, chartGramMatrix_apply, Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

lemma chartGramMatrix_posDef
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (chartGramMatrix g x₀ x).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (chartGramMatrix_isHermitian (I := I) g x₀ x) ?_
  intro c hc
  set w : TangentSpace I x :=
    ∑ i, c i • chartBasisVecFiber (I := I) x₀ i x with hw_def
  have heq := chartGramMatrix_dotProduct_mulVec (I := I) g x₀ x c
  rw [heq]
  have hwnz : w ≠ 0 := by
    intro hw0
    have hli := chartBasisFamily_linearIndependent (I := I) x₀ hx
    rw [Fintype.linearIndependent_iff] at hli
    have : c = 0 := funext (hli c hw0)
    exact hc this
  exact g.pos x w hwnz

lemma chartGramMatrix_det_pos
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    0 < (chartGramMatrix g x₀ x).det :=
  (chartGramMatrix_posDef (I := I) g x₀ hx).det_pos

lemma chartGramMatrix_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => chartGramMatrix g x₀ x i j)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        b (g.inner b))
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
    g.contMDiff.contMDiffOn
  have hv := chartBasisVec_contMDiffOn (I := I) x₀ i
  have hw := chartBasisVec_contMDiffOn (I := I) x₀ j
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            g.inner m
              (chartBasisVecFiber (I := I) x₀ i m)
              (chartBasisVecFiber (I := I) x₀ j m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) x₀).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hg hv hw
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

private lemma chartGramMatrix_pair_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => chartGramMatrix g x₀ x ij.1 ij.2)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
  chartGramMatrix_entry_contMDiffOn (I := I) g x₀ ij.1 ij.2

lemma chartGramMatrix_det_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => (chartGramMatrix g x₀ x).det)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  classical
  have hexp :
      (fun x : M => (chartGramMatrix g x₀ x).det)
        = (fun x : M =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ i, chartGramMatrix g x₀ x (σ i) i) := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul
    (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finset_prod (fun i _ => ?_)
  exact chartGramMatrix_entry_contMDiffOn (I := I) g x₀ (σ i) i

end Measure
end Integral
end DifferentialGeometry
