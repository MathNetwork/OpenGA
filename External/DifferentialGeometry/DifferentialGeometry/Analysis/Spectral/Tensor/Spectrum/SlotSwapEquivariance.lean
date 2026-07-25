import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SlotSwapPairingCalculus
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable (g : SmoothRiemannianMetric I M)

private lemma cons_cons_comp_decomposeFin_double {α : Type*} {s : ℕ}
    (tau : Equiv.Perm (Fin s)) (a b : α) (v : Fin s → α) :
    (fun k : Fin (s + 2) =>
        (Fin.cons a (Fin.cons b v) : Fin (s + 2) → α)
          ((Equiv.Perm.decomposeFin.symm
            (0, Equiv.Perm.decomposeFin.symm (0, tau))) k)) =
      Fin.cons a (Fin.cons b (fun j => v (tau j))) := by
  funext k
  refine Fin.cases ?_ (fun k' => ?_) k
  · rw [Equiv.Perm.decomposeFin_symm_apply_zero]
    rfl
  · rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self]
    simp only [Equiv.refl_apply, Fin.cons_succ]
    refine Fin.cases ?_ (fun k'' => ?_) k'
    · rw [Equiv.Perm.decomposeFin_symm_apply_zero]
      rfl
    · rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self]
      simp only [Equiv.refl_apply, Fin.cons_succ]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_add (s : ℕ) (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S + S') x =
      unitModel (I := I) (M := M) g s S x + unitModel (I := I) (M := M) g s S' x := by
  classical
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma domDomCongrSection_add {s : ℕ} (σ : Equiv.Perm (Fin s))
    (A B : SmoothCcTensor g 0 s) :
    domDomCongrSection (I := I) g σ (A + B) =
      domDomCongrSection (I := I) g σ A + domDomCongrSection (I := I) g σ B := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  rw [domDomCongrSection_unitModel (I := I) g σ (A + B) x,
    unitModel_add (I := I) (M := M) g s A B x,
    unitModel_add (I := I) (M := M) g s
      (domDomCongrSection (I := I) g σ A) (domDomCongrSection (I := I) g σ B) x,
    domDomCongrSection_unitModel (I := I) g σ A x,
    domDomCongrSection_unitModel (I := I) g σ B x]
  refine ContinuousMultilinearMap.ext (fun w => ?_)
  rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma domDomCongrSection_swap_swap (T : SmoothCcTensor g 0 2) :
    domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T) = T := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  rw [domDomCongrSection_unitModel (I := I) g (Equiv.swap (0 : Fin 2) 1)
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T) x,
    domDomCongrSection_unitModel (I := I) g (Equiv.swap (0 : Fin 2) 1) T x]
  refine ContinuousMultilinearMap.ext (fun w => ?_)
  rw [ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  rw [Equiv.swap_apply_self]

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_domDomCongrSection {s : ℕ} (σ : Equiv.Perm (Fin s))
    (U : SmoothCcTensor g 0 s) :
    ‖domDomCongrSection (I := I) g σ U‖ = ‖U‖ := by
  classical
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          ((domDomCongrSection (I := I) g σ U).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 0 s x (U.toSection x) := by
    intro x
    have h := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g σ U 0 x
    simpa only [iteratedCovGrad_zero] using h
  have hsq : ‖domDomCongrSection (I := I) g σ U‖ ^ 2 = ‖U‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M), SmoothCcTensor.norm_def (I := I) (M := M),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g 0 s
        (domDomCongrSection (I := I) g σ U),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g 0 s U]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have h1 : (0 : ℝ) ≤ ‖domDomCongrSection (I := I) g σ U‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖U‖ := norm_nonneg _
  rw [← Real.sqrt_sq h1, ← Real.sqrt_sq h2, hsq]

omit [NeZero (Module.finrank ℝ E)] in
theorem inner_domDomCongrSection_swap (A B : SmoothCcTensor g 0 2) :
    ⟪domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) A, B⟫_ℝ =
      ⟪A, domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) B⟫_ℝ := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  have hsum : domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) A + B =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (A + domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) B) := by
    rw [domDomCongrSection_add (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1) A
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) B),
      domDomCongrSection_swap_swap (I := I) (M := M) g B]
  rw [hsum,
    norm_domDomCongrSection (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1)
      (A + domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) B),
    norm_domDomCongrSection (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1) A,
    norm_domDomCongrSection (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1) B]

omit [NeZero (Module.finrank ℝ E)] in
private lemma inner_toL2_domDomCongrSection_swap (A B : SmoothCcTensor g 0 2) :
    ⟪SmoothCcTensor.toL2
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) A),
      SmoothCcTensor.toL2 B⟫_ℝ =
    ⟪SmoothCcTensor.toL2 A,
      SmoothCcTensor.toL2
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) B)⟫_ℝ := by
  rw [SmoothCcTensor.inner_toL2, SmoothCcTensor.inner_toL2]
  exact inner_domDomCongrSection_swap (I := I) (M := M) g A B

theorem rawTensorConnLapSmooth_domDomCongrSection {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (U : SmoothCcTensor g 0 s) :
    rawTensorConnLapSmooth (I := I) g 0 s (domDomCongrSection (I := I) g σ U) =
      domDomCongrSection (I := I) g σ
        (rawTensorConnLapSmooth (I := I) g 0 s U) := by
  classical
  set σ1 : Equiv.Perm (Fin (s + 1)) := Equiv.Perm.decomposeFin.symm (0, σ) with hσ1
  set σ2 : Equiv.Perm (Fin (s + 2)) := Equiv.Perm.decomposeFin.symm (0, σ1) with hσ2
  have h0 : ∀ y : M, unitModel (I := I) (M := M) g s
      (domDomCongrSection (I := I) g σ U) y =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s U y) :=
    fun y => domDomCongrSection_unitModel (I := I) g σ U y
  have h1 : ∀ y : M, unitModel (I := I) (M := M) g (s + 1)
      (covGrad (I := I) (M := M) g 0 s (domDomCongrSection (I := I) g σ U)) y =
      ContinuousMultilinearMap.domDomCongr σ1
        (unitModel (I := I) (M := M) g (s + 1)
          (covGrad (I := I) (M := M) g 0 s U) y) :=
    fun y => unitModel_covGrad_of_unitModel_domDomCongr (I := I) (M := M) g s σ
      U (domDomCongrSection (I := I) g σ U) h0 y
  have h2 : ∀ y : M, unitModel (I := I) (M := M) g (s + 2)
      (covGrad (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s (domDomCongrSection (I := I) g σ U))) y =
      ContinuousMultilinearMap.domDomCongr σ2
        (unitModel (I := I) (M := M) g (s + 2)
          (covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s U)) y) :=
    fun y => unitModel_covGrad_of_unitModel_domDomCongr (I := I) (M := M) g (s + 1) σ1
      (covGrad (I := I) (M := M) g 0 s U)
      (covGrad (I := I) (M := M) g 0 s (domDomCongrSection (I := I) g σ U)) h1 y
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [unitModel_rawConnLap_eq_frame_sum_gen (I := I) g s
    (domDomCongrSection (I := I) g σ U) x v]
  rw [domDomCongrSection_unitModel (I := I) g σ
    (rawTensorConnLapSmooth (I := I) g 0 s U) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [unitModel_rawConnLap_eq_frame_sum_gen (I := I) g s U x (fun k => v (σ k))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h2x := congrArg
    (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 2) => E) ℝ =>
      T (Fin.cons ((smoothOrthoFrame (I := I) g x i x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g x i x : TangentSpace I x) : E)
          (fun j => (v j : E))))) (h2 x)
  simp only [ContinuousMultilinearMap.domDomCongr_apply] at h2x
  rw [cons_cons_comp_decomposeFin_double σ
    ((smoothOrthoFrame (I := I) g x i x : TangentSpace I x) : E)
    ((smoothOrthoFrame (I := I) g x i x : TangentSpace I x) : E)
    (fun j => (v j : E))] at h2x
  exact h2x

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lambda_eq_of_fst_eq
    {i j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2}
    (h : i.1 = j.1) :
    TensorEigenIdx.lambda (I := I) (M := M) i =
      TensorEigenIdx.lambda (I := I) (M := M) j :=
  congrArg (fun μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g 0 2 =>
    tensorLaplacianEigenvalueOf μ.val) h

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma fst_eq_of_lambda_eq
    {i j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2}
    (h : TensorEigenIdx.lambda (I := I) (M := M) i =
      TensorEigenIdx.lambda (I := I) (M := M) j) :
    i.1 = j.1 := by
  have ha : i.1.val ≠ 0 := TensorNonzeroResolventEigenvalue.val_ne_zero i.1
  have hb : j.1.val ≠ 0 := TensorNonzeroResolventEigenvalue.val_ne_zero j.1
  have h' : (1 - i.1.val) / i.1.val = (1 - j.1.val) / j.1.val := h
  rw [div_eq_div_iff ha hb] at h'
  refine TensorNonzeroResolventEigenvalue.ext i.1 j.1 ?_
  linear_combination -h'

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorSobolevWeight_eq_of_fst_eq
    {i j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2}
    (h : i.1 = j.1) (σ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i σ =
      tensorSobolevWeight (I := I) (M := M) j σ := by
  unfold tensorSobolevWeight
  rw [lambda_eq_of_fst_eq (I := I) (M := M) g h]

omit [BoundarylessManifold I M] in
private lemma eigenbasis_eq_toL2_eigenSmooth
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
        (hCompact (I := I) (M := M) g) i =
      SmoothCcTensor.toL2 (eigenSmooth (I := I) (M := M) g i) := by
  rw [tensorResolventHilbertEigenbasisSigma_apply (I := I) (M := M)
      (hCompact (I := I) (M := M) g) i,
    SmoothCcTensor.toL2_apply (eigenSmooth (I := I) (M := M) g i)]
  exact (eigenvectorSmooth_toL2 (I := I) (M := M) g 0 2 i).symm

omit [BoundarylessManifold I M] in
private lemma tensorL2_ext_of_coeff_eq {U V : TensorL2 0 2 g}
    (h : ∀ k, tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g) U k =
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g) V k) :
    U = V := by
  apply (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (hCompact (I := I) (M := M) g)).repr.injective
  ext k
  exact h k

theorem toL2_rawConnLapSmooth_eigenSmooth
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 2
        (eigenSmooth (I := I) (M := M) g i)) =
      (- TensorEigenIdx.lambda (I := I) (M := M) i) •
        SmoothCcTensor.toL2 (eigenSmooth (I := I) (M := M) g i) := by
  classical
  refine tensorL2_ext_of_coeff_eq (I := I) (M := M) g (fun k => ?_)
  rw [rawConnLapSmooth_tensorL2Coeff (I := I) (M := M) g
      (eigenSmooth (I := I) (M := M) g i) k,
    tensorL2Coeff_smul (I := I) (M := M) (hCompact (I := I) (M := M) g)
      (- TensorEigenIdx.lambda (I := I) (M := M) i)
      (SmoothCcTensor.toL2 (eigenSmooth (I := I) (M := M) g i)) k,
    SmoothCcTensor.toL2_apply (eigenSmooth (I := I) (M := M) g i),
    tensorL2Coeff_ofCompact_eigenSmooth (I := I) (M := M) g k i]
  by_cases hk : k = i
  · subst hk
    simp
  · simp [hk]

theorem tensorL2Coeff_toL2_swap_eigenSmooth_eq_zero_of_fst_ne
    (i j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2)
    (hij : i.1 ≠ j.1) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
      (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (eigenSmooth (I := I) (M := M) g i))) j = 0 := by
  classical
  have hL : tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
      (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 2
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
          (eigenSmooth (I := I) (M := M) g i)))) j =
      (- TensorEigenIdx.lambda (I := I) (M := M) j) *
        tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
            (eigenSmooth (I := I) (M := M) g i))) j :=
    rawConnLapSmooth_tensorL2Coeff (I := I) (M := M) g
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (eigenSmooth (I := I) (M := M) g i)) j
  have hR : tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
      (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (rawTensorConnLapSmooth (I := I) g 0 2 (eigenSmooth (I := I) (M := M) g i)))) j =
      (- TensorEigenIdx.lambda (I := I) (M := M) i) *
        tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
            (eigenSmooth (I := I) (M := M) g i))) j := by
    rw [tensorL2Coeff_eq_inner, eigenbasis_eq_toL2_eigenSmooth (I := I) (M := M) g j,
      ← inner_toL2_domDomCongrSection_swap (I := I) (M := M) g
        (eigenSmooth (I := I) (M := M) g j)
        (rawTensorConnLapSmooth (I := I) g 0 2 (eigenSmooth (I := I) (M := M) g i)),
      toL2_rawConnLapSmooth_eigenSmooth (I := I) (M := M) g i,
      real_inner_smul_right,
      inner_toL2_domDomCongrSection_swap (I := I) (M := M) g
        (eigenSmooth (I := I) (M := M) g j) (eigenSmooth (I := I) (M := M) g i),
      ← eigenbasis_eq_toL2_eigenSmooth (I := I) (M := M) g j,
      ← tensorL2Coeff_eq_inner]
  rw [rawTensorConnLapSmooth_domDomCongrSection (I := I) (M := M) g
    (Equiv.swap (0 : Fin 2) 1) (eigenSmooth (I := I) (M := M) g i), hR] at hL
  have hlam : TensorEigenIdx.lambda (I := I) (M := M) i ≠
      TensorEigenIdx.lambda (I := I) (M := M) j :=
    fun h => hij (fst_eq_of_lambda_eq (I := I) (M := M) g h)
  have hfac : (TensorEigenIdx.lambda (I := I) (M := M) i -
      TensorEigenIdx.lambda (I := I) (M := M) j) *
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
          (eigenSmooth (I := I) (M := M) g i))) j = 0 := by
    linear_combination -hL
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) hlam
  · exact h

theorem orthonormal_toL2_swap_eigenSmooth :
    Orthonormal ℝ
      (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 =>
        SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
          (eigenSmooth (I := I) (M := M) g i))) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  have hstep : ⟪SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (eigenSmooth (I := I) (M := M) g i)),
      SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (eigenSmooth (I := I) (M := M) g j))⟫_ℝ = (if i = j then (1 : ℝ) else 0) := by
    rw [SmoothCcTensor.inner_toL2,
      inner_domDomCongrSection_swap (I := I) (M := M) g (eigenSmooth (I := I) (M := M) g i)
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
          (eigenSmooth (I := I) (M := M) g j)),
      domDomCongrSection_swap_swap (I := I) (M := M) g (eigenSmooth (I := I) (M := M) g j),
      ← SmoothCcTensor.inner_toL2,
      ← eigenbasis_eq_toL2_eigenSmooth (I := I) (M := M) g i,
      ← eigenbasis_eq_toL2_eigenSmooth (I := I) (M := M) g j]
    have horth := (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
      (hCompact (I := I) (M := M) g)).orthonormal
    rw [orthonormal_iff_ite] at horth
    exact horth i j
  exact hstep

open scoped Classical in

omit [BoundarylessManifold I M] in
private lemma tensorL2Coeff_sum_smul_eigenbasis
    (S : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (k : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (∑ j ∈ S, c j • tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
          (hCompact (I := I) (M := M) g) j) k =
      (if k ∈ S then c k else 0) := by
  classical
  rw [tensorL2Coeff_eq_inner, inner_sum]
  have h_term : ∀ j ∈ S,
      ⟪tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
          (hCompact (I := I) (M := M) g) k,
        c j • tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
          (hCompact (I := I) (M := M) g) j⟫_ℝ =
      (if k = j then c j else 0) := by
    intro j _
    rw [inner_smul_right]
    have horth := (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
      (hCompact (I := I) (M := M) g)).orthonormal
    rw [orthonormal_iff_ite] at horth
    rw [horth k j]
    by_cases h : k = j <;> simp [h]
  rw [Finset.sum_congr rfl h_term]
  by_cases hkS : k ∈ S
  · rw [Finset.sum_eq_single k]
    · simp [hkS]
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm)]
    · intro h
      exact absurd hkS h
  · rw [if_neg hkS, Finset.sum_eq_zero]
    intro j hj
    rw [if_neg (fun h => hkS (by rw [h]; exact hj))]

omit [BoundarylessManifold I M] in
private lemma eq_sum_of_tensorL2Coeff_support
    (S : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (U : TensorL2 0 2 g)
    (hU : ∀ k ∉ S,
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g) U k = 0) :
    U = ∑ j ∈ S, tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g) U j •
      tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
        (hCompact (I := I) (M := M) g) j := by
  classical
  refine tensorL2_ext_of_coeff_eq (I := I) (M := M) g (fun k => ?_)
  rw [tensorL2Coeff_sum_smul_eigenbasis (I := I) (M := M) g S
    (fun j => tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g) U j) k]
  by_cases hkS : k ∈ S
  · rw [if_pos hkS]
  · rw [if_neg hkS, hU k hkS]

private lemma tensorL2Coeff_toL2_domDomCongrSection_swap (X : SmoothCcTensor g 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X)) i =
      ⟪SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
          (eigenSmooth (I := I) (M := M) g i)),
        SmoothCcTensor.toL2 X⟫_ℝ := by
  rw [tensorL2Coeff_eq_inner, eigenbasis_eq_toL2_eigenSmooth (I := I) (M := M) g i,
    ← inner_toL2_domDomCongrSection_swap (I := I) (M := M) g
      (eigenSmooth (I := I) (M := M) g i) X]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] in
private lemma toL2_symmS_eq (X : SmoothCcTensor g 0 2) :
    SmoothCcTensor.toL2 (ccTensor02Symm (I := I) (M := M) g X) =
      (1 / 2 : ℝ) • (SmoothCcTensor.toL2 X +
        SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X)) := by
  simp only [ccTensor02Symm]
  rw [map_smul, map_add]

theorem tensorL2Coeff_toL2_symmS_eq_zero_of_notMem
    (S : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (hS : ∀ i j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
      i.1 = j.1 → (i ∈ S ↔ j ∈ S))
    (X : SmoothCcTensor g 0 2)
    (hX : ∀ k ∉ S, tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
      (SmoothCcTensor.toL2 X) k = 0)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2)
    (hi : i ∉ S) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
      (SmoothCcTensor.toL2 (ccTensor02Symm (I := I) (M := M) g X)) i = 0 := by
  classical
  have hswap : tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
      (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X)) i =
      0 := by
    rw [tensorL2Coeff_toL2_domDomCongrSection_swap (I := I) (M := M) g X i]
    conv_lhs => rw [eq_sum_of_tensorL2Coeff_support (I := I) (M := M) g S
      (SmoothCcTensor.toL2 X) hX]
    rw [inner_sum]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    have hij : i.1 ≠ j.1 := fun h => hi ((hS i j h).mpr hj)
    rw [real_inner_smul_right, real_inner_comm, ← tensorL2Coeff_eq_inner,
      tensorL2Coeff_toL2_swap_eigenSmooth_eq_zero_of_fst_ne (I := I) (M := M) g i j hij,
      mul_zero]
  rw [toL2_symmS_eq (I := I) (M := M) g X, tensorL2Coeff_smul, tensorL2Coeff_add,
    hX i hi, hswap]
  ring


theorem sum_tensorSobolevWeight_mul_sq_tensorL2Coeff_toL2_symmS_le
    (σ : ℝ)
    (S : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (_hS : ∀ i j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
      i.1 = j.1 → (i ∈ S ↔ j ∈ S))
    (X : SmoothCcTensor g 0 2)
    (hX : ∀ k ∉ S, tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
      (SmoothCcTensor.toL2 X) k = 0) :
    ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
        (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 (ccTensor02Symm (I := I) (M := M) g X)) i) ^ 2 ≤
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
        (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 X) i) ^ 2 := by
  classical
  have hd : ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 (ccTensor02Symm (I := I) (M := M) g X)) i =
      (1 / 2 : ℝ) *
        (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 X) i +
          tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1) X)) i) := by
    intro i
    rw [toL2_symmS_eq (I := I) (M := M) g X, tensorL2Coeff_smul, tensorL2Coeff_add]
  have hXexp := eq_sum_of_tensorL2Coeff_support (I := I) (M := M) g S
    (SmoothCcTensor.toL2 X) hX
  have hM : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
      (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
          (Equiv.swap (0 : Fin 2) 1) X)) i) ^ 2 ≤
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
        (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 X) i) ^ 2 := by
    have hperblock : ∀ μ ∈ S.image Sigma.fst,
        ∑ i ∈ S.filter (fun i => i.1 = μ),
          tensorSobolevWeight (I := I) (M := M) i σ *
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
                (Equiv.swap (0 : Fin 2) 1) X)) i) ^ 2 ≤
        ∑ i ∈ S.filter (fun i => i.1 = μ),
          tensorSobolevWeight (I := I) (M := M) i σ *
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 X) i) ^ 2 := by
      intro μ hμ
      obtain ⟨i₀, hi₀S, hi₀⟩ := Finset.mem_image.mp hμ
      have hwconst : ∀ i ∈ S.filter
          (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 =>
            i.1 = μ),
          tensorSobolevWeight (I := I) (M := M) i σ =
            tensorSobolevWeight (I := I) (M := M) i₀ σ := by
        intro i hi
        exact tensorSobolevWeight_eq_of_fst_eq (I := I) (M := M) g
          (((Finset.mem_filter.mp hi).2).trans hi₀.symm) σ
      have hm_eq : ∀ i ∈ S.filter
          (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 =>
            i.1 = μ),
          tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1) X)) i =
          ⟪SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
              (eigenSmooth (I := I) (M := M) g i)),
            ∑ j ∈ S.filter
              (fun j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g 0 2 => j.1 = μ),
              tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                  (SmoothCcTensor.toL2 X) j •
                tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
                  (hCompact (I := I) (M := M) g) j⟫_ℝ := by
        intro i hi
        have hifst : i.1 = μ := (Finset.mem_filter.mp hi).2
        rw [tensorL2Coeff_toL2_domDomCongrSection_swap (I := I) (M := M) g X i]
        conv_lhs => rw [hXexp]
        rw [inner_sum, inner_sum]
        refine (Finset.sum_subset (Finset.filter_subset _ _) (fun j hjS hjB => ?_)).symm
        have hjne : ¬ j.1 = μ := fun h => hjB (Finset.mem_filter.mpr ⟨hjS, h⟩)
        have hij : i.1 ≠ j.1 := by
          rw [hifst]
          exact fun h => hjne h.symm
        rw [real_inner_smul_right, real_inner_comm, ← tensorL2Coeff_eq_inner,
          tensorL2Coeff_toL2_swap_eigenSmooth_eq_zero_of_fst_ne (I := I) (M := M) g i j hij,
          mul_zero]
      have hnorm : ‖∑ j ∈ S.filter
            (fun j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g 0 2 => j.1 = μ),
            tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                (SmoothCcTensor.toL2 X) j •
              tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
                (hCompact (I := I) (M := M) g) j‖ ^ 2 =
          ∑ j ∈ S.filter
            (fun j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g 0 2 => j.1 = μ),
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 X) j) ^ 2 := by
        rw [← real_inner_self_eq_norm_sq]
        calc ⟪∑ j ∈ S.filter
              (fun j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g 0 2 => j.1 = μ),
              tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                  (SmoothCcTensor.toL2 X) j •
                tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
                  (hCompact (I := I) (M := M) g) j,
            ∑ j ∈ S.filter
              (fun j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g 0 2 => j.1 = μ),
              tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                  (SmoothCcTensor.toL2 X) j •
                tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
                  (hCompact (I := I) (M := M) g) j⟫_ℝ
            = ∑ j ∈ S.filter
              (fun j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g 0 2 => j.1 = μ),
              (starRingEnd ℝ) (tensorL2Coeff (I := I) (M := M)
                  (hCompact (I := I) (M := M) g) (SmoothCcTensor.toL2 X) j) *
                tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                  (SmoothCcTensor.toL2 X) j :=
              Orthonormal.inner_sum
                ((tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
                  (hCompact (I := I) (M := M) g)).orthonormal) _ _ _
          _ = ∑ j ∈ S.filter
              (fun j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g 0 2 => j.1 = μ),
              (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                (SmoothCcTensor.toL2 X) j) ^ 2 :=
              Finset.sum_congr rfl (fun j _ => by
                simp only [conj_trivial]
                ring)
      have hblock : ∑ i ∈ S.filter
            (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g 0 2 => i.1 = μ),
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
                (Equiv.swap (0 : Fin 2) 1) X)) i) ^ 2 ≤
          ∑ j ∈ S.filter
            (fun j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g 0 2 => j.1 = μ),
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 X) j) ^ 2 := by
        calc ∑ i ∈ S.filter
              (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g 0 2 => i.1 = μ),
              (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 2) 1) X)) i) ^ 2
            = ∑ i ∈ S.filter
              (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g 0 2 => i.1 = μ),
              ‖⟪SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
                  (eigenSmooth (I := I) (M := M) g i)),
                ∑ j ∈ S.filter
                  (fun j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                    (I := I) (M := M) g 0 2 => j.1 = μ),
                  tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                      (SmoothCcTensor.toL2 X) j •
                    tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
                      (hCompact (I := I) (M := M) g) j⟫_ℝ‖ ^ 2 :=
              Finset.sum_congr rfl (fun i hi => by
                rw [hm_eq i hi, Real.norm_eq_abs, sq_abs])
          _ ≤ ‖∑ j ∈ S.filter
              (fun j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g 0 2 => j.1 = μ),
              tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                  (SmoothCcTensor.toL2 X) j •
                tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
                  (hCompact (I := I) (M := M) g) j‖ ^ 2 :=
              Orthonormal.sum_inner_products_le
                (∑ j ∈ S.filter
                  (fun j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                    (I := I) (M := M) g 0 2 => j.1 = μ),
                  tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                      (SmoothCcTensor.toL2 X) j •
                    tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
                      (hCompact (I := I) (M := M) g) j)
                (orthonormal_toL2_swap_eigenSmooth (I := I) (M := M) g)
          _ = ∑ j ∈ S.filter
              (fun j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g 0 2 => j.1 = μ),
              (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                (SmoothCcTensor.toL2 X) j) ^ 2 := hnorm
      calc ∑ i ∈ S.filter (fun i => i.1 = μ),
            tensorSobolevWeight (I := I) (M := M) i σ *
              (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 2) 1) X)) i) ^ 2
          = ∑ i ∈ S.filter (fun i => i.1 = μ),
            tensorSobolevWeight (I := I) (M := M) i₀ σ *
              (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 2) 1) X)) i) ^ 2 :=
            Finset.sum_congr rfl (fun i hi => by rw [hwconst i hi])
        _ = tensorSobolevWeight (I := I) (M := M) i₀ σ *
            ∑ i ∈ S.filter (fun i => i.1 = μ),
              (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 2) 1) X)) i) ^ 2 :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ tensorSobolevWeight (I := I) (M := M) i₀ σ *
            ∑ j ∈ S.filter (fun j => j.1 = μ),
              (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                (SmoothCcTensor.toL2 X) j) ^ 2 :=
            mul_le_mul_of_nonneg_left hblock
              (tensorSobolevWeight_nonneg (I := I) (M := M) i₀ σ)
        _ = ∑ j ∈ S.filter (fun j => j.1 = μ),
            tensorSobolevWeight (I := I) (M := M) i₀ σ *
              (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                (SmoothCcTensor.toL2 X) j) ^ 2 :=
            Finset.mul_sum _ _ _
        _ = ∑ j ∈ S.filter (fun j => j.1 = μ),
            tensorSobolevWeight (I := I) (M := M) j σ *
              (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                (SmoothCcTensor.toL2 X) j) ^ 2 :=
            Finset.sum_congr rfl (fun j hj => by rw [hwconst j hj])
    have hmemS : ∀ i ∈ S, i.1 ∈ S.image Sigma.fst :=
      fun i hi => Finset.mem_image_of_mem Sigma.fst hi
    calc ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1) X)) i) ^ 2
        = ∑ i ∈ S.filter (fun i => i.1 ∈ S.image Sigma.fst),
          tensorSobolevWeight (I := I) (M := M) i σ *
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
                (Equiv.swap (0 : Fin 2) 1) X)) i) ^ 2 := by
          rw [Finset.filter_true_of_mem hmemS]
      _ = ∑ μ ∈ S.image Sigma.fst, ∑ i ∈ S.filter (fun i => i.1 = μ),
          tensorSobolevWeight (I := I) (M := M) i σ *
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
                (Equiv.swap (0 : Fin 2) 1) X)) i) ^ 2 :=
          (Finset.sum_fiberwise_eq_sum_filter S (S.image Sigma.fst) Sigma.fst _).symm
      _ ≤ ∑ μ ∈ S.image Sigma.fst, ∑ i ∈ S.filter (fun i => i.1 = μ),
          tensorSobolevWeight (I := I) (M := M) i σ *
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 X) i) ^ 2 :=
          Finset.sum_le_sum hperblock
      _ = ∑ i ∈ S.filter (fun i => i.1 ∈ S.image Sigma.fst),
          tensorSobolevWeight (I := I) (M := M) i σ *
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 X) i) ^ 2 :=
          Finset.sum_fiberwise_eq_sum_filter S (S.image Sigma.fst) Sigma.fst _
      _ = ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 X) i) ^ 2 := by
          rw [Finset.filter_true_of_mem hmemS]
  have hpt : ∀ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
      (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 (ccTensor02Symm (I := I) (M := M) g X)) i) ^ 2 ≤
      tensorSobolevWeight (I := I) (M := M) i σ *
        ((1 / 2 : ℝ) * (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 X) i) ^ 2 +
          (1 / 2 : ℝ) * (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1) X)) i) ^ 2) := by
    intro i _
    refine mul_le_mul_of_nonneg_left ?_ (tensorSobolevWeight_nonneg (I := I) (M := M) i σ)
    rw [hd i]
    nlinarith [sq_nonneg (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 X) i -
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
          (Equiv.swap (0 : Fin 2) 1) X)) i)]
  calc ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
        (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 (ccTensor02Symm (I := I) (M := M) g X)) i) ^ 2
      ≤ ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
        ((1 / 2 : ℝ) * (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 X) i) ^ 2 +
          (1 / 2 : ℝ) * (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1) X)) i) ^ 2) := Finset.sum_le_sum hpt
    _ = (1 / 2 : ℝ) * (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 X) i) ^ 2) +
        (1 / 2 : ℝ) * (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1) X)) i) ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
    _ ≤ (1 / 2 : ℝ) * (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 X) i) ^ 2) +
        (1 / 2 : ℝ) * (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 X) i) ^ 2) := by
        have h2 := mul_le_mul_of_nonneg_left hM (by norm_num : (0 : ℝ) ≤ 1 / 2)
        linarith
    _ = ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
        (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 X) i) ^ 2 := by ring

private lemma block_tensorL2Coeff_sq_swap_le (X : SmoothCcTensor g 0 2)
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g 0 2) :
    ∑ k : Fin (Module.finrank ℝ (tensorResolventEigenspace (I := I) (M := M) g 0 2 μ.val)),
        (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X))
          ⟨μ, k⟩) ^ 2 ≤
      ∑ l : Fin (Module.finrank ℝ (tensorResolventEigenspace (I := I) (M := M) g 0 2 μ.val)),
        (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 X) ⟨μ, l⟩) ^ 2 := by
  classical
  have hinj : Function.Injective
      (fun l : Fin (Module.finrank ℝ (tensorResolventEigenspace (I := I) (M := M) g 0 2 μ.val)) =>
        (⟨μ, l⟩ :
          Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2)) := by
    intro a c h; simpa using h
  set F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :=
    Finset.univ.map
      ⟨fun l : Fin (Module.finrank ℝ (tensorResolventEigenspace (I := I) (M := M) g 0 2 μ.val)) =>
        (⟨μ, l⟩ :
          Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2), hinj⟩
    with hF
  set Y : TensorL2 0 2 g :=
    ∑ j ∈ F, tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 X) j •
      (tensorResolventHilbertEigenbasisSigma (I := I) (M := M) (hCompact (I := I) (M := M) g)) j
    with hY
  have hsorth : Orthonormal ℝ
      (fun k : Fin (Module.finrank ℝ (tensorResolventEigenspace (I := I) (M := M) g 0 2 μ.val)) =>
        SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
          (eigenSmooth (I := I) (M := M) g ⟨μ, k⟩))) :=
    (orthonormal_toL2_swap_eigenSmooth (I := I) (M := M) g).comp
      (fun l : Fin (Module.finrank ℝ (tensorResolventEigenspace (I := I) (M := M) g 0 2 μ.val)) =>
        (⟨μ, l⟩ :
          Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2)) hinj
  have hstep1 : ∀ k : Fin (Module.finrank ℝ (tensorResolventEigenspace (I := I) (M := M) g 0 2 μ.val)),
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X))
          ⟨μ, k⟩ =
        ⟪SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
            (eigenSmooth (I := I) (M := M) g ⟨μ, k⟩)), Y⟫_ℝ := by
    intro k
    rw [tensorL2Coeff_toL2_domDomCongrSection_swap (I := I) (M := M) g X ⟨μ, k⟩]
    set sk : TensorL2 0 2 g :=
      SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (eigenSmooth (I := I) (M := M) g ⟨μ, k⟩)) with hsk
    have hHS : HasSum
        (fun j => tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 X) j •
          (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (hCompact (I := I) (M := M) g)) j)
        (SmoothCcTensor.toL2 X) :=
      (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
        (hCompact (I := I) (M := M) g)).hasSum_repr (SmoothCcTensor.toL2 X)
    have hmap := hHS.mapL (innerSL ℝ sk)
    simp only [innerSL_apply_apply, real_inner_smul_right] at hmap
    have hzero : ∀ j ∉ F,
        tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 X) j *
          ⟪sk, (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (hCompact (I := I) (M := M) g)) j⟫_ℝ = 0 := by
      intro j hj
      have hjfst : ¬ (⟨μ, k⟩ :
          Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2).1 = j.1 := by
        intro heq
        obtain ⟨ν, w⟩ := j
        have heq' : μ = ν := heq
        subst heq'
        exact hj (by rw [hF, Finset.mem_map]; exact ⟨w, Finset.mem_univ w, rfl⟩)
      have hbj : ⟪sk, (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
          (hCompact (I := I) (M := M) g)) j⟫_ℝ = 0 := by
        rw [real_inner_comm, hsk, ← tensorL2Coeff_eq_inner (I := I) (M := M)
          (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
            (eigenSmooth (I := I) (M := M) g ⟨μ, k⟩))) j]
        exact tensorL2Coeff_toL2_swap_eigenSmooth_eq_zero_of_fst_ne (I := I) (M := M) g ⟨μ, k⟩ j hjfst
      rw [hbj, mul_zero]
    have hlhs : ⟪sk, SmoothCcTensor.toL2 X⟫_ℝ =
        ∑ j ∈ F, tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 X) j *
          ⟪sk, (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (hCompact (I := I) (M := M) g)) j⟫_ℝ := by
      rw [← hmap.tsum_eq]; exact tsum_eq_sum hzero
    have hrhs : ⟪sk, Y⟫_ℝ =
        ∑ j ∈ F, tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 X) j *
          ⟪sk, (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (hCompact (I := I) (M := M) g)) j⟫_ℝ := by
      rw [hY, inner_sum]
      exact Finset.sum_congr rfl (fun j _ => real_inner_smul_right _ _ _)
    rw [hlhs, hrhs]
  have hbessel : ∑ k : Fin (Module.finrank ℝ (tensorResolventEigenspace (I := I) (M := M) g 0 2 μ.val)),
      ‖⟪SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
          (eigenSmooth (I := I) (M := M) g ⟨μ, k⟩)), Y⟫_ℝ‖ ^ 2 ≤ ‖Y‖ ^ 2 :=
    Orthonormal.sum_inner_products_le Y hsorth
  have hYnorm : ‖Y‖ ^ 2 =
      ∑ j ∈ F, (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 X) j) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hY,
      Orthonormal.inner_sum (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
          (hCompact (I := I) (M := M) g)).orthonormal
        (fun j => tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 X) j)
        (fun j => tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 X) j) F]
    exact Finset.sum_congr rfl (fun j _ => by simp only [conj_trivial]; ring)
  calc ∑ k : Fin (Module.finrank ℝ (tensorResolventEigenspace (I := I) (M := M) g 0 2 μ.val)),
          (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X))
            ⟨μ, k⟩) ^ 2
      = ∑ k : Fin (Module.finrank ℝ (tensorResolventEigenspace (I := I) (M := M) g 0 2 μ.val)),
          (⟪SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
              (eigenSmooth (I := I) (M := M) g ⟨μ, k⟩)), Y⟫_ℝ) ^ 2 :=
        Finset.sum_congr rfl (fun k _ => by rw [hstep1 k])
    _ = ∑ k : Fin (Module.finrank ℝ (tensorResolventEigenspace (I := I) (M := M) g 0 2 μ.val)),
          ‖⟪SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
              (eigenSmooth (I := I) (M := M) g ⟨μ, k⟩)), Y⟫_ℝ‖ ^ 2 :=
        Finset.sum_congr rfl (fun k _ => by rw [Real.norm_eq_abs, sq_abs])
    _ ≤ ‖Y‖ ^ 2 := hbessel
    _ = ∑ j ∈ F, (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 X) j) ^ 2 := hYnorm
    _ = ∑ l : Fin (Module.finrank ℝ (tensorResolventEigenspace (I := I) (M := M) g 0 2 μ.val)),
          (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 X) ⟨μ, l⟩) ^ 2 := by
        rw [hF]; exact Finset.sum_map _ _ _

private lemma tsum_weighted_symmS_le (X : SmoothCcTensor g 0 2) (σ : ℝ) :
    ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
        (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 (ccTensor02Symm (I := I) (M := M) g X)) i) ^ 2 ≤
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
        (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 X) i) ^ 2 := by
  classical
  have hsummX : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
      (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 X) i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g σ X).weighted_summable
  have hsummSwap : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
      (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X)) i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g σ
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X)).weighted_summable
  have hsummSymm : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
      (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 (ccTensor02Symm (I := I) (M := M) g X)) i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g σ (ccTensor02Symm (I := I) (M := M) g X)).weighted_summable
  have hswapLe : ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
        (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X))
          i) ^ 2 ≤
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
        (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 X) i) ^ 2 := by
    rw [hsummSwap.tsum_sigma, hsummX.tsum_sigma]
    refine Summable.tsum_le_tsum (fun μ => ?_) hsummSwap.sigma hsummX.sigma
    rw [tsum_eq_sum (s := (Finset.univ :
          Finset (Fin (Module.finrank ℝ (tensorResolventEigenspace (I := I) (M := M) g 0 2 μ.val)))))
        (fun c hc => absurd (Finset.mem_univ c) hc),
      tsum_eq_sum (s := (Finset.univ :
          Finset (Fin (Module.finrank ℝ (tensorResolventEigenspace (I := I) (M := M) g 0 2 μ.val)))))
        (fun c hc => absurd (Finset.mem_univ c) hc)]
    rcases isEmpty_or_nonempty
        (Fin (Module.finrank ℝ (tensorResolventEigenspace (I := I) (M := M) g 0 2 μ.val)))
      with hemp | hne
    · haveI := hemp; simp
    · obtain ⟨c₀⟩ := hne
      have hwc : ∀ c : Fin (Module.finrank ℝ (tensorResolventEigenspace (I := I) (M := M) g 0 2 μ.val)),
          tensorSobolevWeight (I := I) (M := M)
            (⟨μ, c⟩ : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) σ =
          tensorSobolevWeight (I := I) (M := M)
            (⟨μ, c₀⟩ : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) σ :=
        fun c => tensorSobolevWeight_eq_of_fst_eq (I := I) (M := M) g rfl σ
      calc ∑ c, tensorSobolevWeight (I := I) (M := M)
              (⟨μ, c⟩ : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) σ *
              (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X))
                ⟨μ, c⟩) ^ 2
          = tensorSobolevWeight (I := I) (M := M)
              (⟨μ, c₀⟩ : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) σ *
              ∑ c, (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X))
                ⟨μ, c⟩) ^ 2 := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun c _ => by rw [hwc c])
        _ ≤ tensorSobolevWeight (I := I) (M := M)
              (⟨μ, c₀⟩ : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) σ *
              ∑ c, (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                (SmoothCcTensor.toL2 X) ⟨μ, c⟩) ^ 2 :=
            mul_le_mul_of_nonneg_left (block_tensorL2Coeff_sq_swap_le (I := I) (M := M) g X μ)
              (tensorSobolevWeight_nonneg (I := I) (M := M) _ σ)
        _ = ∑ c, tensorSobolevWeight (I := I) (M := M)
              (⟨μ, c⟩ : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) σ *
              (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
                (SmoothCcTensor.toL2 X) ⟨μ, c⟩) ^ 2 := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun c _ => by rw [hwc c])
  have hcoeff : ∀ i, tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 (ccTensor02Symm (I := I) (M := M) g X)) i =
      (1 / 2 : ℝ) * (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 X) i +
        tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X)) i) := by
    intro i
    rw [toL2_symmS_eq (I := I) (M := M) g X, tensorL2Coeff_smul, tensorL2Coeff_add]
  have hRHSsumm : Summable (fun i => (1 / 2 : ℝ) * (tensorSobolevWeight (I := I) (M := M) i σ *
        (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 X) i) ^ 2) +
      (1 / 2 : ℝ) * (tensorSobolevWeight (I := I) (M := M) i σ *
        (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X)) i) ^ 2)) :=
    (hsummX.mul_left _).add (hsummSwap.mul_left _)
  calc ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 (ccTensor02Symm (I := I) (M := M) g X)) i) ^ 2
      ≤ ∑' i, ((1 / 2 : ℝ) * (tensorSobolevWeight (I := I) (M := M) i σ *
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 X) i) ^ 2) +
          (1 / 2 : ℝ) * (tensorSobolevWeight (I := I) (M := M) i σ *
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X))
              i) ^ 2)) := by
        refine Summable.tsum_le_tsum (fun i => ?_) hsummSymm hRHSsumm
        rw [hcoeff i]
        nlinarith [sq_nonneg (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 X) i -
          tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X)) i),
          tensorSobolevWeight_nonneg (I := I) (M := M) i σ]
    _ = (1 / 2 : ℝ) * (∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 X) i) ^ 2) +
          (1 / 2 : ℝ) * (∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X))
              i) ^ 2) := by
        rw [Summable.tsum_add (hsummX.mul_left _) (hsummSwap.mul_left _), tsum_mul_left,
          tsum_mul_left]
    _ ≤ (1 / 2 : ℝ) * (∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 X) i) ^ 2) +
          (1 / 2 : ℝ) * (∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 X) i) ^ 2) := by
        have hh := mul_le_mul_of_nonneg_left hswapLe (by norm_num : (0 : ℝ) ≤ 1 / 2)
        linarith
    _ = ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 X) i) ^ 2 := by ring

theorem norm_smoothCcToTensorHs_symmS_le (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (X : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ (ccTensor02Symm (I := I) (M := M) g₀ X)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ X‖ := by
  rw [tensorHs.norm_eq_sqrt_tsum
      (smoothCcToTensorHs (I := I) (M := M) g₀ σ (ccTensor02Symm (I := I) (M := M) g₀ X)),
    tensorHs.norm_eq_sqrt_tsum (smoothCcToTensorHs (I := I) (M := M) g₀ σ X)]
  apply Real.sqrt_le_sqrt
  simp only [smoothCcToTensorHs_coeff]
  exact tsum_weighted_symmS_le (I := I) (M := M) g₀ X σ

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
