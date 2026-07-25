import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothing




























































noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]




def spectralCoeff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u₀ : TensorL2 r s g) :
    TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
  tensorL2Coeff (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) u₀

@[simp] lemma spectralCoeff_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u₀ : TensorL2 r s g) (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    spectralCoeff (I := I) (M := M) g r s u₀ i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        u₀ i := rfl





theorem heatHsWitness_support_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : ℝ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    Function.support (heatHsWitness (I := I) (M := M) g r s σ ht u₀).coeff =
      Function.support (spectralCoeff (I := I) (M := M) g r s u₀) := by
  apply Set.ext
  intro i
  have hexp : Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  rw [Function.mem_support, Function.mem_support, heatHsWitness_coeff,
    spectralCoeff_apply]
  exact mul_ne_zero_iff_left hexp




theorem heatHsWitness_finite_support_of_finite
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : ℝ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g)
    (hu₀_fs : (Function.support (spectralCoeff (I := I) (M := M) g r s u₀)).Finite) :
    (Function.support (heatHsWitness (I := I) (M := M) g r s σ ht u₀).coeff).Finite := by
  rw [heatHsWitness_support_eq (I := I) (M := M) g r s σ ht u₀]
  exact hu₀_fs







def heatOutputSmoothRepr (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g)
    (hu₀_fs : (Function.support (spectralCoeff (I := I) (M := M) g r s u₀)).Finite) :
    SmoothCcTensor g r s :=
  tensorHsSmoothRepr (I := I) (M := M)
    (heatHsWitness (I := I) (M := M) g r s 0 ht u₀)
    (heatHsWitness_finite_support_of_finite (I := I) (M := M) g r s 0 ht u₀ hu₀_fs)









theorem heatOutputSmoothRepr_toL2 (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g)
    (hu₀_fs : (Function.support (spectralCoeff (I := I) (M := M) g r s u₀)).Finite) :
    (heatOutputSmoothRepr (I := I) (M := M) g r s ht u₀ hu₀_fs :
        TensorL2 r s g) =
      tensorHeatSemigroup (I := I) (M := M) g r s t u₀ := by
  unfold heatOutputSmoothRepr
  rw [tensorHsSmoothRepr_toL2 (I := I) (M := M) (le_refl (0 : ℝ))
    (heatHsWitness (I := I) (M := M) g r s 0 ht u₀)
    (heatHsWitness_finite_support_of_finite (I := I) (M := M) g r s 0 ht u₀ hu₀_fs)]
  exact heat_semigroup_into_tensorHs (I := I) (M := M) g r s (le_refl (0 : ℝ)) ht u₀





theorem heatOutputSmoothRepr_memWtwokTwo (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g)
    (hu₀_fs : (Function.support (spectralCoeff (I := I) (M := M) g r s u₀)).Finite)
    (k : ℕ) :
    MemWtwokTwo (I := I) (M := M) g k
      (heatOutputSmoothRepr (I := I) (M := M) g r s ht u₀ hu₀_fs) :=
  tensorHsSmoothRepr_memWtwokTwo (I := I) (M := M)
    (heatHsWitness (I := I) (M := M) g r s 0 ht u₀)
    (heatHsWitness_finite_support_of_finite (I := I) (M := M) g r s 0 ht u₀ hu₀_fs) k






theorem exists_smooth_heatOutput_representative (g : SmoothRiemannianMetric I M)
    (r s : ℕ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g)
    (hu₀_fs : (Function.support (spectralCoeff (I := I) (M := M) g r s u₀)).Finite) :
    ∃ T : SmoothCcTensor g r s,
      (T : TensorL2 r s g) =
          tensorHeatSemigroup (I := I) (M := M) g r s t u₀ ∧
        ∀ k : ℕ, MemWtwokTwo (I := I) (M := M) g k T :=
  ⟨heatOutputSmoothRepr (I := I) (M := M) g r s ht u₀ hu₀_fs,
    heatOutputSmoothRepr_toL2 (I := I) (M := M) g r s ht u₀ hu₀_fs,
    fun k => heatOutputSmoothRepr_memWtwokTwo (I := I) (M := M) g r s ht u₀ hu₀_fs k⟩











theorem spectralSmooth_realizesAsSmooth_of_finite_support
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (h_mem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : tensorHs (I := I) (M := M) g r s σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) g r s) hσ v = u)
    (hu_fs : ∀ v : tensorHs (I := I) (M := M) g r s 0,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) g r s) (le_refl (0 : ℝ)) v = u →
          (Function.support v.coeff).Finite) :
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = u := by
  obtain ⟨v₀, hv₀⟩ := h_mem 0 (le_refl (0 : ℝ))
  have hv₀_fs : (Function.support v₀.coeff).Finite := hu_fs v₀ hv₀
  refine ⟨tensorHsSmoothRepr (I := I) (M := M) v₀ hv₀_fs, ?_⟩
  rw [tensorHsSmoothRepr_toL2 (I := I) (M := M)
    (le_refl (0 : ℝ)) v₀ hv₀_fs]
  exact hv₀



def heatOutputBilinSymm (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 0 2 g)
    (hu₀_fs : (Function.support (spectralCoeff (I := I) (M := M) g 0 2 u₀)).Finite)
    (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  ccTensorBilinSymm (I := I) g
    (heatOutputSmoothRepr (I := I) (M := M) g 0 2 ht u₀ hu₀_fs) x

















theorem exists_smooth_metric_of_heatOutput_small
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 0 2 g)
    (hu₀_fs : (Function.support (spectralCoeff (I := I) (M := M) g 0 2 u₀)).Finite)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g
      (heatOutputBilinSymm (I := I) g ht u₀ hu₀_fs) δ') :
    ∃ g' : SmoothRiemannianMetric I M,
      ∀ (x : M) (v w : TangentSpace I x),
        g'.inner x v w =
          g.inner x v w + heatOutputBilinSymm (I := I) g ht u₀ hu₀_fs x v w :=
  exists_smooth_metric_of_smooth_tensor_small (I := I) g
    (heatOutputSmoothRepr (I := I) (M := M) g 0 2 ht u₀ hu₀_fs) hδ'_lt hδ'

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
