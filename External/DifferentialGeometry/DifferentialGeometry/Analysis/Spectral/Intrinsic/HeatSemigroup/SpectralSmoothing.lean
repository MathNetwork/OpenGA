import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Intrinsic
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SmoothingHs
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem tensorHeatSemigroup_intrinsic_tensorL2Coeff_ofCompact
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 ≤ t) (u₀ : TensorL2 r s g)
    (i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        (tensorHeatSemigroup (I := I) (M := M) g r s t u₀) i =
      Real.exp (-(TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          u₀ i := by
  rw [tensorL2Coeff_eq_inner, tensorL2Coeff_eq_inner]
  exact tensorHeatSemigroup_intrinsic_inner_eigenbasis
    (I := I) (M := M) g r s ht u₀ i

private def baseHZero (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u₀ : TensorL2 r s g) :
    tensorHs (I := I) (M := M) g r s 0 :=
  (tensorHsZeroEquivL2 (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)).symm u₀

private lemma baseHZero_coeff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u₀ : TensorL2 r s g) (i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :
    (baseHZero (I := I) (M := M) g r s u₀).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        u₀ i :=
  tensorHsZeroEquivL2_symm_coeff (I := I) (M := M) _ u₀ i

def heatHsWitness (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : ℝ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    tensorHs (I := I) (M := M) g r s σ :=
  tensorHs.heatHsFun (I := I) (M := M) σ ht
    (baseHZero (I := I) (M := M) g r s u₀)

@[simp] theorem heatHsWitness_coeff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : ℝ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g)
    (i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :
    (heatHsWitness (I := I) (M := M) g r s σ ht u₀).coeff i =
      Real.exp (-(TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          u₀ i := by
  unfold heatHsWitness
  rw [tensorHs.heatHsFun_coeff, baseHZero_coeff]

theorem heat_semigroup_into_tensorHs (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {σ : ℝ} (hσ : 0 ≤ σ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        hσ (heatHsWitness (I := I) (M := M) g r s σ ht u₀) =
      tensorHeatSemigroup (I := I) (M := M) g r s t u₀ := by
  set h_compact :=
    tensorResolventL2_isCompactOperator (I := I) (M := M) g r s
    with hcompact_def
  refine (tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) h_compact).repr.injective ?_
  ext i
  have hlhs :
      ((tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_compact).repr
        (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
          h_compact hσ (heatHsWitness (I := I) (M := M) g r s σ ht u₀))) i =
        Real.exp (-(TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          tensorL2Coeff (I := I) (M := M) h_compact u₀ i := by
    have h := tensorHsToL2_tensorL2Coeff
      (I := I) (M := M) (h_compact := h_compact) hσ
      (heatHsWitness (I := I) (M := M) g r s σ ht u₀) i
    rw [heatHsWitness_coeff] at h
    simpa only [tensorL2Coeff] using h
  have hrhs :
      ((tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_compact).repr
        (tensorHeatSemigroup (I := I) (M := M) g r s t u₀)) i =
        Real.exp (-(TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          tensorL2Coeff (I := I) (M := M) h_compact u₀ i := by
    have h := tensorHeatSemigroup_intrinsic_tensorL2Coeff_ofCompact
      (I := I) (M := M) g r s ht.le u₀ i
    simpa only [tensorL2Coeff] using h
  rw [hlhs, hrhs]

theorem heat_semigroup_into_all_tensorHs (g : SmoothRiemannianMetric I M)
    (r s : ℕ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : tensorHs (I := I) (M := M) g r s σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) g r s) hσ v =
          tensorHeatSemigroup (I := I) (M := M) g r s t u₀ :=
  fun σ hσ =>
    ⟨heatHsWitness (I := I) (M := M) g r s σ ht u₀,
      heat_semigroup_into_tensorHs (I := I) (M := M) g r s hσ ht u₀⟩

def SpectralSmoothRealizesAsSmooth (g : SmoothRiemannianMetric I M)
    (r s : ℕ) : Prop :=
  ∀ u : TensorL2 r s g,
    (∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : tensorHs (I := I) (M := M) g r s σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) g r s) hσ v = u) →
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = u

theorem spectral_smooth_realization_reduction
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_gate : SpectralSmoothRealizesAsSmooth (I := I) (M := M) g r s)
    {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    ∃ T : SmoothCcTensor g r s,
      (T : TensorL2 r s g) =
        tensorHeatSemigroup (I := I) (M := M) g r s t u₀ :=
  h_gate _ (fun σ hσ =>
    ⟨heatHsWitness (I := I) (M := M) g r s σ ht u₀,
      heat_semigroup_into_tensorHs (I := I) (M := M) g r s hσ ht u₀⟩)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
