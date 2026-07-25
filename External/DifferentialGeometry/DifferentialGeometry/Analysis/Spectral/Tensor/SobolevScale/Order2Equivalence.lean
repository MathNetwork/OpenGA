import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.FractionalPower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.L2BanachIso
import DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactSAResolventIntrinsic
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.NablaTensor.IteratedNabla
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral
namespace SobolevScale

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.RicciFlow.HebeyBlock

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorPouSobolevHs_order2_equiv_pouSobolev
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g 2 T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g 2 T).toReal :=
  iterated_nabla_vs_iterated_partial_equivalence_H1
    (I := I) (M := M) g r s 2

def tensorHs_order2_isometryEquiv_tensorL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    tensorHs (I := I) (M := M) g r s 2 ≃ₗᵢ[ℝ] TensorL2 r s g :=
  (tensorHsEquivOfFractionalPower (I := I) (M := M)
      (g := g) (r := r) (s := s) 2 0).trans
    (tensorHsZeroEquivL2 (I := I) (M := M)
      (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.tensorResolventL2_isCompactOperator
        (I := I) (M := M) g r s))

def Order2NormEquivOnSmooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Nspec : SmoothCcTensor g r s → ℝ) (C₁ C₂ : ℝ) : Prop :=
  (∀ T : SmoothCcTensor g r s,
      Nspec T ≤ C₁ * (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal) ∧
    (∀ T : SmoothCcTensor g r s,
      (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal ≤ C₂ * Nspec T)

noncomputable def smoothCcTensorHs2LinearEquiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorHs g r s 2 ≃ₗ[ℝ] SmoothCcTensor g r s where
  toFun := SmoothCcTensorHs.toCcTensor
  invFun := fun T => ⟨T⟩
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl
  map_add' S T := SmoothCcTensorHs.toCcTensor_add S T
  map_smul' c S := SmoothCcTensorHs.toCcTensor_smul c S

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothCcTensorHs2_norm_eq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensorHs g r s 2) :
    ‖S‖ = (tensorPouSobolevHsNorm (I := I) (M := M) g 2 S.toCcTensor).toReal := by
  rcases S with ⟨T⟩
  have h1 := tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g (k := 2) T
  have h2 : ‖((⟨T⟩ : SmoothCcTensorHs g r s 2) :
        TensorPouSobolevHilbert g r s 2)‖ =
      ‖(⟨T⟩ : SmoothCcTensorHs g r s 2)‖ :=
    UniformSpace.Completion.norm_coe (⟨T⟩ : SmoothCcTensorHs g r s 2)
  have h_eq : SmoothCcTensor.toHs (g := g) (r := r) (s := s) 2 T =
      ((⟨T⟩ : SmoothCcTensorHs g r s 2) :
        TensorPouSobolevHilbert g r s 2) := rfl
  rw [h_eq] at h1
  linarith

noncomputable def tensorPouSobolevHilbert_order2_continuousLinearEquiv_of_normEquiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (e₂ : SmoothCcTensor g r s →ₗ[ℝ] F)
    (he₂_dense : DenseRange e₂)
    (Nspec : SmoothCcTensor g r s → ℝ)
    (he₂_norm : ∀ T : SmoothCcTensor g r s, ‖e₂ T‖ = Nspec T)
    (C₁ C₂ : ℝ)
    (h_equiv : Order2NormEquivOnSmooth (I := I) (M := M) g r s Nspec C₁ C₂) :
    TensorPouSobolevHilbert g r s 2 ≃L[ℝ] F :=
  let f : SmoothCcTensorHs g r s 2 ≃ₗ[ℝ] SmoothCcTensor g r s :=
    smoothCcTensorHs2LinearEquiv (I := I) (M := M) g r s
  let e₁ : SmoothCcTensorHs g r s 2 →ₗ[ℝ] TensorPouSobolevHilbert g r s 2 :=
    (UniformSpace.Completion.toComplL :
      SmoothCcTensorHs g r s 2 →L[ℝ]
        UniformSpace.Completion (SmoothCcTensorHs g r s 2)).toLinearMap
  f.extend e₁ e₂
    (by
      change DenseRange (UniformSpace.Completion.toComplL :
        SmoothCcTensorHs g r s 2 →L[ℝ]
          UniformSpace.Completion (SmoothCcTensorHs g r s 2))
      rw [show (UniformSpace.Completion.toComplL :
          SmoothCcTensorHs g r s 2 →
            UniformSpace.Completion (SmoothCcTensorHs g r s 2)) =
          ((↑) : SmoothCcTensorHs g r s 2 →
            UniformSpace.Completion (SmoothCcTensorHs g r s 2)) from
        UniformSpace.Completion.coe_toComplL]
      exact UniformSpace.Completion.denseRange_coe)
    ⟨C₁, by
      intro S
      have hfS : f S = S.toCcTensor := rfl
      have he₂T : ‖e₂ (f S)‖ = Nspec S.toCcTensor := by
        rw [hfS]; exact he₂_norm S.toCcTensor
      have he₁S : ‖e₁ S‖ = ‖S‖ := by
        change ‖((S : SmoothCcTensorHs g r s 2) :
          UniformSpace.Completion (SmoothCcTensorHs g r s 2))‖ = ‖S‖
        exact UniformSpace.Completion.norm_coe S
      rw [he₂T, he₁S]
      have hS_norm : ‖S‖ =
          (tensorPouSobolevHsNorm (I := I) (M := M) g 2 S.toCcTensor).toReal :=
        smoothCcTensorHs2_norm_eq (I := I) (M := M) g S
      rw [hS_norm]
      exact h_equiv.1 S.toCcTensor⟩
    he₂_dense
    ⟨C₂, by
      intro T
      have hfsymmT : f.symm T = ⟨T⟩ := rfl
      have he₁ST : ‖e₁ (f.symm T)‖ = ‖(⟨T⟩ : SmoothCcTensorHs g r s 2)‖ := by
        rw [hfsymmT]
        change ‖((⟨T⟩ : SmoothCcTensorHs g r s 2) :
          UniformSpace.Completion (SmoothCcTensorHs g r s 2))‖ =
          ‖(⟨T⟩ : SmoothCcTensorHs g r s 2)‖
        exact UniformSpace.Completion.norm_coe
          (⟨T⟩ : SmoothCcTensorHs g r s 2)
      have he₂T : ‖e₂ T‖ = Nspec T := he₂_norm T
      rw [he₁ST, he₂T]
      have hT_norm : ‖(⟨T⟩ : SmoothCcTensorHs g r s 2)‖ =
          (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal := by
        have := smoothCcTensorHs2_norm_eq (I := I) (M := M) g
          (⟨T⟩ : SmoothCcTensorHs g r s 2)
        simpa using this
      rw [hT_norm]
      exact h_equiv.2 T⟩

end SobolevScale
end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
