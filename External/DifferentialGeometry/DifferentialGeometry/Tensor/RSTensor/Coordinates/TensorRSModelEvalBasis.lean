import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.ChartGram
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Constructions


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open Bundle Manifold Set Filter Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold Topology ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

noncomputable def eval0SLinear (n : ℕ) :
    Tensor0SModel n ℝ E →ₗ[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) where
  toFun := fun Φ φ => Φ (fun k : Fin n => (chartModelBasis E) (φ k))
  map_add' Φ₁ Φ₂ := by
    funext φ
    simp [ContinuousMultilinearMap.add_apply]
  map_smul' c Φ := by
    funext φ
    simp [ContinuousMultilinearMap.smul_apply]

@[simp] lemma eval0SLinear_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    eval0SLinear (E := E) n Φ φ =
      Φ (fun k : Fin n => (chartModelBasis E) (φ k)) := rfl

private lemma eval0SLinear_injective (n : ℕ) :
    Function.Injective (eval0SLinear (E := E) n) := by
  intro Φ₁ Φ₂ h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear (e := fun _ : Fin n => chartModelBasis E) ?_
  intro v
  exact congr_fun h v

private lemma finrank_tensor0SModel_loc (n : ℕ) :
    Module.finrank ℝ (Tensor0SModel n ℝ E) =
      (Module.finrank ℝ E) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero]
      rw [(continuousMultilinearCurryFin0 ℝ E ℝ).toLinearEquiv.finrank_eq]
      exact Module.finrank_self ℝ
  | succ n ih =>
      rw [(continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => E) ℝ).toLinearEquiv.finrank_eq]
      let φ : (E →L[ℝ] Tensor0SModel n ℝ E) ≃ₗ[ℝ]
          (E →ₗ[ℝ] Tensor0SModel n ℝ E) :=
        { toFun := fun f => f.toLinearMap
          invFun := fun f => LinearMap.toContinuousLinearMap f
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      rw [φ.finrank_eq, Module.finrank_linearMap, ih]
      ring

omit [Module.Finite ℝ E] in
private lemma finrank_basis_pi_loc (n : ℕ) :
    Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) =
      (Module.finrank ℝ E) ^ n := by
  rw [Module.finrank_pi, Fintype.card_pi]
  simp [Fintype.card_fin]

private lemma eval0SLinear_bijective (n : ℕ) :
    Function.Bijective (eval0SLinear (E := E) n) := by
  have h_inj := eval0SLinear_injective (E := E) n
  refine ⟨h_inj, ?_⟩
  have h_eq : Module.finrank ℝ (Tensor0SModel n ℝ E) =
      Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) := by
    rw [finrank_tensor0SModel_loc, finrank_basis_pi_loc]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_eq).mp h_inj

noncomputable def eval0SLinearEquiv (n : ℕ) :
    Tensor0SModel n ℝ E ≃ₗ[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) :=
  LinearEquiv.ofBijective (eval0SLinear (E := E) n)
    (eval0SLinear_bijective (E := E) n)

@[simp] private lemma eval0SLinearEquiv_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    eval0SLinearEquiv (E := E) n Φ φ =
      Φ (fun k : Fin n => (chartModelBasis E) (φ k)) := rfl

noncomputable def eval0SCLE (n : ℕ) :
    Tensor0SModel n ℝ E ≃L[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) :=
  (eval0SLinearEquiv (E := E) n).toContinuousLinearEquiv

@[simp] lemma eval0SCLE_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    eval0SCLE (E := E) n Φ φ =
      Φ (fun k : Fin n => (chartModelBasis E) (φ k)) := rfl

noncomputable def evalAtBasisLinear_TensorRSModel (r s : ℕ) :
    TensorRSModel r s ℝ E →ₗ[ℝ]
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) → ℝ) where
  toFun := fun T p =>
    (T ((eval0SCLE (E := E) r).symm (Pi.single p.1 (1 : ℝ))))
      (fun k : Fin s => (chartModelBasis E) (p.2 k))
  map_add' T₁ T₂ := by
    funext p
    simp [ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply]
  map_smul' c T := by
    funext p
    simp [ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]

@[simp] lemma evalAtBasisLinear_TensorRSModel_apply (r s : ℕ)
    (T : TensorRSModel r s ℝ E)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    evalAtBasisLinear_TensorRSModel (E := E) r s T (Idx, Jdx) =
      (T ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))))
        (fun k : Fin s => (chartModelBasis E) (Jdx k)) := rfl

private lemma evalAtBasisLinear_TensorRSModel_injective (r s : ℕ) :
    Function.Injective (evalAtBasisLinear_TensorRSModel (E := E) r s) := by
  intro T₁ T₂ h
  have h_pt :
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
        T₁ ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) =
        T₂ ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) := by
    intro Idx
    apply eval0SLinear_injective (E := E) s
    funext Jdx
    have h_pair := congr_fun h (Idx, Jdx)
    simpa [evalAtBasisLinear_TensorRSModel, eval0SLinear_apply] using h_pair
  let bPi : Module.Basis (Fin r → Fin (Module.finrank ℝ E)) ℝ
      ((Fin r → Fin (Module.finrank ℝ E)) → ℝ) :=
    Pi.basisFun ℝ (Fin r → Fin (Module.finrank ℝ E))
  let bTen : Module.Basis (Fin r → Fin (Module.finrank ℝ E)) ℝ
      (Tensor0SModel r ℝ E) :=
    bPi.map (eval0SLinearEquiv (E := E) r).symm
  have h_basis :
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
        bTen Idx =
        (eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)) := by
    intro Idx
    have : bPi Idx = Pi.single Idx (1 : ℝ) := by
      simp [bPi, Pi.basisFun_apply]
    simp [bTen, Module.Basis.map_apply, this, eval0SCLE]
  have h_linear :
      (T₁ : Tensor0SModel r ℝ E →ₗ[ℝ] Tensor0SModel s ℝ E) =
      (T₂ : Tensor0SModel r ℝ E →ₗ[ℝ] Tensor0SModel s ℝ E) := by
    refine Module.Basis.ext bTen ?_
    intro Idx
    rw [h_basis Idx]
    exact h_pt Idx
  exact ContinuousLinearMap.coe_injective h_linear

private lemma finrank_tensorRSModel_loc (r s : ℕ) :
    Module.finrank ℝ (TensorRSModel r s ℝ E) =
      (Module.finrank ℝ E) ^ (r + s) := by
  haveI : FiniteDimensional ℝ (Tensor0SModel r ℝ E) :=
    continuousMultilinearMap_finiteDimensional r
  haveI : FiniteDimensional ℝ (Tensor0SModel s ℝ E) :=
    continuousMultilinearMap_finiteDimensional s
  haveI : Module.Free ℝ (Tensor0SModel s ℝ E) := inferInstance
  have e : (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) ≃ₗ[ℝ]
      (Tensor0SModel r ℝ E →ₗ[ℝ] Tensor0SModel s ℝ E) :=
    LinearMap.toContinuousLinearMap.symm
  change Module.finrank ℝ (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) =
      (Module.finrank ℝ E) ^ (r + s)
  rw [e.finrank_eq, Module.finrank_linearMap,
    finrank_tensor0SModel_loc (E := E) r,
    finrank_tensor0SModel_loc (E := E) s, ← pow_add]

omit [Module.Finite ℝ E] in
private lemma finrank_basis_pair_pi_loc (r s : ℕ) :
    Module.finrank ℝ
      (((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))) → ℝ) =
      (Module.finrank ℝ E) ^ (r + s) := by
  rw [Module.finrank_pi, Fintype.card_prod, Fintype.card_pi, Fintype.card_pi]
  simp [Fintype.card_fin, pow_add]

private lemma evalAtBasisLinear_TensorRSModel_bijective (r s : ℕ) :
    Function.Bijective (evalAtBasisLinear_TensorRSModel (E := E) r s) := by
  haveI : FiniteDimensional ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_finiteDimensional r s
  have h_inj := evalAtBasisLinear_TensorRSModel_injective (E := E) r s
  refine ⟨h_inj, ?_⟩
  have h_eq : Module.finrank ℝ (TensorRSModel r s ℝ E) =
      Module.finrank ℝ
        (((Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E))) → ℝ) := by
    rw [finrank_tensorRSModel_loc, finrank_basis_pair_pi_loc]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_eq).mp h_inj

noncomputable def evalAtBasisCLE_TensorRSModel (r s : ℕ) :
    TensorRSModel r s ℝ E ≃L[ℝ]
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) → ℝ) :=
  haveI : FiniteDimensional ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_finiteDimensional r s
  (LinearEquiv.ofBijective (evalAtBasisLinear_TensorRSModel (E := E) r s)
    (evalAtBasisLinear_TensorRSModel_bijective (E := E) r s)).toContinuousLinearEquiv

@[simp] lemma evalAtBasisCLE_TensorRSModel_apply (r s : ℕ)
    (T : TensorRSModel r s ℝ E)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    evalAtBasisCLE_TensorRSModel (E := E) r s T (Idx, Jdx) =
      (T ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))))
        (fun k : Fin s => (chartModelBasis E) (Jdx k)) := rfl

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
theorem contMDiffOn_into_tensorRSModel_of_eval_basis
    {r s : ℕ}
    {f : M → (ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →L[ℝ]
              ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)}
    {U : Set M} :
    ContMDiffOn I
      𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) ∞ f U ↔
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun b : M =>
            evalAtBasisCLE_TensorRSModel (E := E) r s (f b) (Idx, Jdx)) U := by
  constructor
  · intro hf Idx Jdx
    have hCLE :
        ContMDiff
          𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →L[ℝ]
                ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
          𝓘(ℝ, (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)) → ℝ) ∞
          (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →L[ℝ]
                    ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ =>
            evalAtBasisCLE_TensorRSModel (E := E) r s T) :=
      (evalAtBasisCLE_TensorRSModel (E := E) r s).toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffOn I 𝓘(ℝ, (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)) → ℝ) ∞
          (fun b : M => evalAtBasisCLE_TensorRSModel (E := E) r s (f b)) U :=
      hCLE.comp_contMDiffOn hf
    have hpi := (contMDiffOn_pi_space).1 hcomp
    exact hpi (Idx, Jdx)
  · intro h
    have hpi : ContMDiffOn I
        𝓘(ℝ, (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)) → ℝ) ∞
        (fun b : M => evalAtBasisCLE_TensorRSModel (E := E) r s (f b)) U := by
      rw [contMDiffOn_pi_space]
      intro p
      exact h p.1 p.2
    have hsymm_smooth :
        ContMDiff 𝓘(ℝ, (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)) → ℝ)
          𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →L[ℝ]
                ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) ∞
          (fun g : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)) → ℝ =>
            (evalAtBasisCLE_TensorRSModel (E := E) r s).symm g) :=
      ((evalAtBasisCLE_TensorRSModel (E := E) r s).symm.toContinuousLinearMap).contMDiff
    have hcomp := hsymm_smooth.comp_contMDiffOn hpi
    refine hcomp.congr ?_
    intro b _
    exact ((evalAtBasisCLE_TensorRSModel (E := E) r s).symm_apply_apply (f b)).symm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
