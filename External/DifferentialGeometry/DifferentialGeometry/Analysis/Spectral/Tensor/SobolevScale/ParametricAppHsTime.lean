import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ParametricAppHs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParametricTimeDeriv
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParametricJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParametricJetIntegral










noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter MeasureTheory Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (jointContMDiff_toModel_continuous_slice)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem appCc_time_deriv
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ dΦ : ℝ → SmoothCcTensor g b c) {S : Set ℝ}
    (hderiv : ∀ t ∈ S, ∀ x : M, ∀ A : Tensor0SSpace b I x,
      ∀ slots : Fin c → E,
        HasDerivAt
          (fun τ => Tensor0SSpace.toModel (((Φ τ).toSection x) A) slots)
          (Tensor0SSpace.toModel (((dΦ t).toSection x) A) slots) t)
    (W : SmoothCcTensor g 0 b) {t : ℝ} (ht : t ∈ S)
    (x : M) (slots : Fin c → E) :
    HasDerivAt
      (fun τ => unitModel (I := I) (M := M) g c
        (operatorFieldApply (I := I) (M := M) g b c (Φ τ) W) x slots)
      (unitModel (I := I) (M := M) g c
        (operatorFieldApply (I := I) (M := M) g b c (dΦ t) W) x slots) t := by
  let A : Tensor0SSpace b I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace b I x from W.toSection x)
      (unitTensor (I := I) (M := M) x)
  have key (Ψ : SmoothCcTensor g b c) :
      unitModel (I := I) (M := M) g c
          (operatorFieldApply (I := I) (M := M) g b c Ψ W) x slots =
        Tensor0SSpace.toModel ((Ψ.toSection x) A) slots := by
    simp only [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply, A]
  rw [show (fun τ => unitModel (I := I) (M := M) g c
      (operatorFieldApply (I := I) (M := M) g b c (Φ τ) W) x slots) =
      (fun τ => Tensor0SSpace.toModel (((Φ τ).toSection x) A) slots) by
        funext τ
        exact key (Φ τ),
    key (dΦ t)]
  exact hderiv t ht x A slots

private def affineSet (S : Set ℝ) (a h : ℝ) : Set ℝ :=
  (fun θ : ℝ => a + h * θ) ⁻¹' S

private theorem affineSet_open {S : Set ℝ} (hS : IsOpen S) (a h : ℝ) :
    IsOpen (affineSet S a h) := by
  exact hS.preimage (by fun_prop)

private theorem affine_uIcc {S : Set ℝ} {a h : ℝ}
    (hseg : Set.uIcc a (a + h) ⊆ S) :
    Set.uIcc (0 : ℝ) 1 ⊆ affineSet S a h := by
  intro θ hθ
  apply hseg
  have hθ' : 0 ≤ θ ∧ θ ≤ 1 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hθ
  rw [Set.mem_uIcc]
  by_cases hh : 0 ≤ h
  · exact Or.inl ⟨by nlinarith, by nlinarith⟩
  · exact Or.inr ⟨by nlinarith, by nlinarith⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in

private theorem joint_affine
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : ℝ → SmoothCcTensor g b c) {S : Set ℝ}
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (a h : ℝ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((Φ (a + h * p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ affineSet S a h) := by
  have harg : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : M × ℝ => (p.1, a + h * p.2))
      ((Set.univ : Set M) ×ˢ affineSet S a h) := by
    exact contMDiffOn_fst.prodMk
      (contMDiffOn_const.add (contMDiffOn_const.mul contMDiffOn_snd))
  exact hjoint.comp harg (fun p hp => ⟨Set.mem_univ p.1, hp.2⟩)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in


private theorem joint_const
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (S : Set ℝ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        (Φ.toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  simpa only using Φ.toSection.contMDiff.comp_contMDiffOn contMDiffOn_fst

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in


private theorem joint_affine_sub
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : ℝ → SmoothCcTensor g b c) {S : Set ℝ}
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (a h : ℝ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        (((Φ (a + h * p.2) - Φ a).toSection p.1)))
      ((Set.univ : Set M) ×ˢ affineSet S a h) := by
  have hsub := joint_rs_sub (I := I) (M := M)
    (fun p : M × ℝ => (Φ (a + h * p.2)).toSection p.1)
    (fun p : M × ℝ => (Φ a).toSection p.1)
    (joint_affine (I := I) (M := M) g b c Φ hjoint a h)
    (joint_const (I := I) (M := M) g b c (Φ a) (affineSet S a h))
  simpa only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
    Pi.sub_apply] using hsub



private noncomputable def coeffRem
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (dΦ : ℝ → SmoothCcTensor g b c) (S : Set ℝ) (hS : IsOpen S)
    (hdjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((dΦ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (a h : ℝ) (hseg : Set.uIcc a (a + h) ⊆ S) :
    SmoothCcTensor g b c :=
  pathIntegralCoeffField (I := I) (M := M) g b c
    (fun θ => dΦ (a + h * θ) - dΦ a) (affineSet S a h)
    (affineSet_open hS a h) (affine_uIcc hseg)
    (joint_affine_sub (I := I) (M := M) g b c dΦ hdjoint a h)



private noncomputable def coeffRem0
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (dΦ : ℝ → SmoothCcTensor g b c) (S : Set ℝ) (hS : IsOpen S)
    (hdjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((dΦ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (a h : ℝ) : SmoothCcTensor g b c := by
  classical
  exact if hseg : Set.uIcc a (a + h) ⊆ S then
    coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint a h hseg
  else 0



private theorem segment_eventually {S : Set ℝ} {a : ℝ}
    (ha : S ∈ 𝓝 a) :
    ∀ᶠ h in 𝓝 (0 : ℝ), Set.uIcc a (a + h) ⊆ S := by
  rcases Metric.mem_nhds_iff.mp ha with ⟨δ, hδ, hδS⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
  intro t ht
  apply hδS
  rw [Metric.mem_ball, dist_comm]
  have hh' : dist a (a + h) < δ := by
    calc
      dist a (a + h) = |a - (a + h)| := Real.dist_eq _ _
      _ = |-h| := by congr 1; ring
      _ = |h| := abs_neg h
      _ = dist h 0 := by rw [Real.dist_eq, sub_zero]
      _ < δ := by simpa only [Metric.mem_ball] using hh
  exact (Real.dist_left_le_of_mem_uIcc ht).trans_lt hh'



private theorem affine_eventually {P : ℝ → Prop} {a : ℝ}
    (hP : ∀ᶠ t in 𝓝 a, P t) :
    ∀ᶠ h in 𝓝 (0 : ℝ), ∀ θ ∈ Set.Icc (0 : ℝ) 1, P (a + h * θ) := by
  rcases Metric.mem_nhds_iff.mp hP with ⟨δ, hδ, hδP⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
  intro θ hθ
  apply hδP
  rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_mul]
  have hh' : |h| < δ := by
    have : dist h 0 < δ := by simpa only [Metric.mem_ball] using hh
    simpa only [Real.dist_eq, sub_zero] using this
  calc
    |h| * |θ| ≤ |h| * 1 := by
      exact mul_le_mul_of_nonneg_left (by
        rw [abs_of_nonneg hθ.1]
        exact hθ.2) (abs_nonneg h)
    _ < δ := by simpa only [mul_one] using hh'



omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem coeff_secant
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ dΦ : ℝ → SmoothCcTensor g b c) {S : Set ℝ} (hS : IsOpen S)
    (hdjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((dΦ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (hderiv : ∀ t ∈ S, ∀ x : M, ∀ A : Tensor0SSpace b I x,
      ∀ slots : Fin c → E,
        HasDerivAt
          (fun τ => Tensor0SSpace.toModel (((Φ τ).toSection x) A) slots)
          (Tensor0SSpace.toModel (((dΦ t).toSection x) A) slots) t)
    (a h : ℝ) (hseg : Set.uIcc a (a + h) ⊆ S) :
    Φ (a + h) - Φ a - h • dΦ a =
      h • coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint a h hseg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply TensorRSSpace.toModel_injective
  apply ContinuousLinearMap.ext
  intro A₀
  apply ContinuousMultilinearMap.ext
  intro slots
  let A : Tensor0SSpace b I x := Tensor0SSpace.ofModel A₀
  have hA : Tensor0SSpace.toModel A = A₀ := by
    simp only [A, Tensor0SSpace.toModel_ofModel]
  have eval_eq (Ψ : SmoothCcTensor g b c) :
      ((TensorRSSpace.toModel (Ψ.toSection x)) A₀) slots =
        Tensor0SSpace.toModel ((Ψ.toSection x) A) slots := by
    rw [← hA, ← toModel_tensorRS_apply (I := I) b c x (Ψ.toSection x) A]
  let f : ℝ → ℝ := fun τ =>
    Tensor0SSpace.toModel (((Φ τ).toSection x) A) slots
  let f' : ℝ → ℝ := fun τ =>
    Tensor0SSpace.toModel (((dΦ τ).toSection x) A) slots
  have hf'cont : ContinuousOn f' S := by
    let Q : TensorRSModel b c ℝ E →L[ℝ] ℝ :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin c => E) ℝ slots).comp
        (ContinuousLinearMap.apply ℝ (Tensor0SModel c ℝ E) A₀)
    have hmodel := jointContMDiff_toModel_continuous_slice
      (I := I) g b c dΦ S hdjoint x
    have hQ := Q.continuous.comp_continuousOn hmodel
    refine hQ.congr (fun τ _ => ?_)
    simp only [Q, f']
    exact eval_eq (dΦ τ)
  have hInt : IntervalIntegrable f' volume a (a + h) :=
    (hf'cont.mono hseg).intervalIntegrable
  have hFTC : (∫ τ in a..a + h, f' τ) = f (a + h) - f a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun τ hτ => by simpa only [f, f'] using hderiv τ (hseg hτ) x A slots)
      hInt
  have hAffInt : IntervalIntegrable (fun θ : ℝ => f' (a + h * θ)) volume 0 1 := by
    have hcont : ContinuousOn (fun θ : ℝ => f' (a + h * θ))
        (Set.Icc (0 : ℝ) 1) :=
      hf'cont.comp (by fun_prop) (fun θ hθ =>
        affine_uIcc hseg (by
          simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hθ))
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hchange : h * (∫ θ in (0 : ℝ)..1, f' (a + h * θ)) =
      f (a + h) - f a := by
    calc
      h * (∫ θ in (0 : ℝ)..1, f' (a + h * θ)) =
          ∫ τ in a..a + h, f' τ := by
        simpa only [smul_eq_mul, mul_zero, mul_one, add_zero] using
          (intervalIntegral.smul_integral_comp_add_mul
            (f := f') (a := (0 : ℝ)) (b := 1) h a)
      _ = f (a + h) - f a := hFTC
  let Ψ : ℝ → SmoothCcTensor g b c :=
    fun θ => dΦ (a + h * θ) - dΦ a
  have hΨjoint := joint_affine_sub (I := I) (M := M)
    g b c dΦ hdjoint a h
  have hΨcont := jointContMDiff_toModel_continuous_slice
    (I := I) g b c Ψ (affineSet S a h) hΨjoint x
  have hΨI : ContinuousOn
      (fun θ => TensorRSSpace.toModel ((Ψ θ).toSection x))
      (Set.Icc (0 : ℝ) 1) :=
    hΨcont.mono (fun θ hθ => affine_uIcc hseg (by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hθ))
  have hΨInt : IntervalIntegrable
      (fun θ => TensorRSSpace.toModel ((Ψ θ).toSection x)) volume 0 1 :=
    hΨI.intervalIntegrable_of_Icc (by norm_num)
  have hΨAppInt : IntervalIntegrable
      (fun θ => (TensorRSSpace.toModel ((Ψ θ).toSection x)) A₀) volume 0 1 :=
    ((ContinuousLinearMap.apply ℝ (Tensor0SModel c ℝ E) A₀).continuous.comp_continuousOn
      hΨI).intervalIntegrable_of_Icc (by norm_num)
  have hRem :
      Tensor0SSpace.toModel
          (((coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint a h hseg).toSection x) A)
          slots =
        ∫ θ in (0 : ℝ)..1, (f' (a + h * θ) - f' a) := by
    rw [toModel_tensorRS_apply (I := I) b c x
      ((coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint a h hseg).toSection x) A]
    rw [hA]
    change
      ((TensorRSSpace.toModel
        ((pathIntegralCoeffField (I := I) (M := M) g b c Ψ
          (affineSet S a h) (affineSet_open hS a h) (affine_uIcc hseg)
          hΨjoint).toSection x)) A₀) slots = _
    rw [pathIntegralCoeffField_toModel]
    rw [ContinuousLinearMap.intervalIntegral_apply hΨInt A₀]
    let L : Tensor0SModel c ℝ E →L[ℝ] ℝ :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin c => E) ℝ slots
    change L (∫ θ in (0 : ℝ)..1,
      (TensorRSSpace.toModel ((Ψ θ).toSection x)) A₀) = _
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm L hΨAppInt]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [Ψ, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
      Pi.sub_apply, TensorRSSpace.toModel_sub, ContinuousLinearMap.sub_apply,
      f']
    rw [L.map_sub]
    change
      (((dΦ (a + h * θ)).toSection x).toModel A₀) slots -
          (((dΦ a).toSection x).toModel A₀) slots = _
    rw [eval_eq (dΦ (a + h * θ)), eval_eq (dΦ a)]
  have hdiffInt :
      (∫ θ in (0 : ℝ)..1, (f' (a + h * θ) - f' a)) =
        (∫ θ in (0 : ℝ)..1, f' (a + h * θ)) - f' a := by
    rw [intervalIntegral.integral_sub hAffInt intervalIntegrable_const,
      intervalIntegral.integral_const]
    norm_num
  have hscalar :
      f (a + h) - f a - h * f' a =
        h * Tensor0SSpace.toModel
          (((coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint a h hseg).toSection x) A)
          slots := by
    rw [hRem, hdiffInt, ← hchange]
    ring
  simpa only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
    Pi.sub_apply, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
    Pi.smul_apply, TensorRSSpace.toModel_sub, TensorRSSpace.toModel_smul,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul, eval_eq, f, f'] using hscalar



omit [NeZero (Module.finrank ℝ E)] in
private theorem coeffRem_jet
    (g : SmoothRiemannianMetric I M) (b c n : ℕ)
    (dΦ : ℝ → SmoothCcTensor g b c) {S : Set ℝ} (hS : IsOpen S)
    (hdjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((dΦ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    {a : ℝ} (ha : a ∈ S) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ h in 𝓝 (0 : ℝ),
      ∀ hseg : Set.uIcc a (a + h) ⊆ S, ∀ i, i ≤ n → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
          ((iteratedCovGrad (I := I) g b c i
            (coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint a h hseg)).toSection x) ≤ η := by
  classical
  let Ξ : ℝ → SmoothCcTensor g b c := fun t => dΦ t - dΦ a
  have hΞjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((Ξ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
    have hsub := joint_rs_sub (I := I) (M := M)
      (fun p : M × ℝ => (dΦ p.2).toSection p.1)
      (fun p : M × ℝ => (dΦ a).toSection p.1)
      hdjoint (joint_const (I := I) (M := M) g b c (dΦ a) S)
    simpa only [Ξ, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
      Pi.sub_apply] using hsub
  have hΞ0 : Ξ a = 0 := by simp only [Ξ, sub_self]
  have hjet := joint_jet_small (I := I) (M := M) g b c n Ξ
    (hS.mem_nhds ha) hΞ0 hΞjoint hη
  have haff := affine_eventually hjet
  filter_upwards [haff] with h hh
  intro hseg i hi x
  let Ψ : ℝ → SmoothCcTensor g b c :=
    fun θ => dΦ (a + h * θ) - dΦ a
  have hΨjoint := joint_affine_sub (I := I) (M := M)
    g b c dΦ hdjoint a h
  have hji := covGrad_iter_joint (I := I) (M := M)
    g b c i Ψ (affineSet S a h) hΨjoint
  have hcont : ContinuousOn
      (fun θ => TensorRSSpace.toModel
        ((iteratedCovGrad (I := I) g b c i (Ψ θ)).toSection x))
      (Set.Icc (0 : ℝ) 1) :=
    (jointContMDiff_toModel_continuous_slice (I := I)
      g b (c + i) (fun θ => iteratedCovGrad (I := I) g b c i (Ψ θ))
      (affineSet S a h) hji x).mono (fun θ hθ =>
        affine_uIcc hseg (by
          simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hθ))
  have hsup : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M)
        g b (c + i) x
        ((iteratedCovGrad (I := I) g b c i (Ψ θ)).toSection x)) ≤
        Real.sqrt η := by
    intro θ hθ
    apply Real.sqrt_le_sqrt
    have hlt : riemannianFiberNormSq (I := I) (M := M)
        g b (c + i) x
        ((iteratedCovGrad (I := I) g b c i (Ψ θ)).toSection x) < η := by
      simpa only [Ψ, Ξ] using (hh θ hθ i hi x)
    exact hlt.le
  have hpath :=
    riemannianFiberNormSq_pathIntegralCoeffField_le_sq
      (I := I) (M := M) g b (c + i)
      (fun θ => iteratedCovGrad (I := I) g b c i (Ψ θ))
      (affineSet S a h) (affineSet_open hS a h) (affine_uIcc hseg)
      hji x (Real.sqrt η) (Real.sqrt_nonneg η) hcont hsup
  have hcomm := icg_path_comm (I := I) (M := M)
    g b c i Ψ (affineSet S a h) (affineSet_open hS a h)
    (affine_uIcc hseg) hΨjoint hji
  have hcoeff :
      coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint a h hseg =
        pathIntegralCoeffField (I := I) (M := M) g b c Ψ
          (affineSet S a h) (affineSet_open hS a h) (affine_uIcc hseg) hΨjoint := rfl
  have hcomm_eval :
      riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
          ((iteratedCovGrad (I := I) g b c i
            (coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint a h hseg)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
          ((pathIntegralCoeffField (I := I) (M := M) g b (c + i)
            (fun θ => iteratedCovGrad (I := I) g b c i (Ψ θ))
            (affineSet S a h) (affineSet_open hS a h) (affine_uIcc hseg) hji).toSection x) := by
    rw [hcoeff]
    exact congrArg
      (fun Q : SmoothCcTensor g b (c + i) =>
        riemannianFiberNormSq (I := I) (M := M) g b (c + i) x (Q.toSection x))
      hcomm
  calc
    riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
        ((iteratedCovGrad (I := I) g b c i
          (coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint a h hseg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
        ((pathIntegralCoeffField (I := I) (M := M) g b (c + i)
          (fun θ => iteratedCovGrad (I := I) g b c i (Ψ θ))
          (affineSet S a h) (affineSet_open hS a h) (affine_uIcc hseg) hji).toSection x) :=
        hcomm_eval
    _ ≤ (Real.sqrt η) ^ 2 := hpath
    _ = η := Real.sq_sqrt hη.le



private theorem coeffRemHs_small
    (g : SmoothRiemannianMetric I M) (b c n : ℕ)
    (dΦ : ℝ → SmoothCcTensor g b c) {S : Set ℝ} (hS : IsOpen S)
    (hdjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((dΦ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    {a : ℝ} (ha : a ∈ S) :
    ∀ ε > 0, ∀ᶠ h in 𝓝 (0 : ℝ),
      ∀ hseg : Set.uIcc a (a + h) ⊆ S,
        ‖appHs g b c n
          (coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint a h hseg)‖ < ε := by
  classical
  obtain ⟨C, hC, happ⟩ := appHs_unif (I := I) (M := M) g b c n
  intro ε hε
  have hbound_cont : ContinuousAt
      (fun q : ℝ => C * Real.sqrt (∑ i ∈ Finset.range (n + 1), q)) 0 := by
    fun_prop
  have hsmall :
      {q : ℝ | C * Real.sqrt (∑ i ∈ Finset.range (n + 1), q) < ε} ∈
        𝓝 (0 : ℝ) := by
    exact hbound_cont.eventually_lt_const (by simpa only [Finset.sum_const_zero,
      Real.sqrt_zero, mul_zero] using hε)
  rcases Metric.mem_nhds_iff.mp hsmall with ⟨δ, hδ, hδsmall⟩
  let η : ℝ := δ / 2
  have hη : 0 < η := half_pos hδ
  have hηsmall : C * Real.sqrt (∑ i ∈ Finset.range (n + 1), η) < ε := by
    apply hδsmall
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hη]
    exact half_lt_self hδ
  have hjet := coeffRem_jet (I := I) (M := M)
    g b c n dΦ hS hdjoint ha hη
  filter_upwards [hjet] with h hh
  intro hseg
  exact (happ _ (fun _ => η) (fun _ _ => hη.le)
    (fun i hi x => hh hseg i hi x)).trans_lt hηsmall



private theorem coeffRem0_apply
    (g : SmoothRiemannianMetric I M) (b c n : ℕ)
    (dΦ : ℝ → SmoothCcTensor g b c) {S : Set ℝ} (hS : IsOpen S)
    (hdjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((dΦ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    {a : ℝ} (ha : a ∈ S)
    (U : tensorHs (I := I) (M := M) g 0 b (n : ℝ)) :
    Tendsto
      (fun h => appHs g b c n
        (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint a h) U)
      (𝓝 (0 : ℝ))
      (𝓝 (0 : tensorHs (I := I) (M := M) g 0 c (n : ℝ))) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / (‖U‖ + 1)
  have hden : 0 < ‖U‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hprod : δ * ‖U‖ < ε := by
    have heq : δ * ‖U‖ = ε * ‖U‖ / (‖U‖ + 1) := by
      simp only [δ]
      ring
    rw [heq, div_lt_iff₀ hden]
    nlinarith [norm_nonneg U]
  have hsmall := coeffRemHs_small (I := I) (M := M)
    g b c n dΦ hS hdjoint ha δ hδ
  have hseg := segment_eventually (hS.mem_nhds ha)
  filter_upwards [hsmall, hseg] with h hh hseg
  have heq :
      coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint a h =
        coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint a h hseg := by
    simp only [coeffRem0, dif_pos hseg]
  have happ :
      ‖appHs g b c n
        (coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint a h hseg) U‖ < ε := by
    refine (ContinuousLinearMap.le_opNorm _ U).trans_lt ?_
    exact (mul_le_mul_of_nonneg_right (hh hseg).le (norm_nonneg U)).trans_lt hprod
  simpa only [heq, Real.dist_eq, sub_zero, abs_norm] using happ



private theorem coeffRem0_move
    (g : SmoothRiemannianMetric I M) (b c n : ℕ)
    (dΦ : ℝ → SmoothCcTensor g b c) {S : Set ℝ} (hS : IsOpen S)
    (hdjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((dΦ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    {a : ℝ} (ha : a ∈ S)
    (U : ℝ → tensorHs (I := I) (M := M) g 0 b (n : ℝ))
    (hU : ContinuousAt U a) :
    Tendsto
      (fun h => appHs g b c n
        (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint a h) (U (a + h)))
      (𝓝 (0 : ℝ))
      (𝓝 (0 : tensorHs (I := I) (M := M) g 0 c (n : ℝ))) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  rw [Metric.tendsto_nhds]
  intro ε hε
  let B : ℝ := ‖U a‖ + 1
  have hB : 0 < B := by
    simp only [B]
    positivity
  let δ : ℝ := ε / B
  have hδ : 0 < δ := div_pos hε hB
  have hsmall := coeffRemHs_small (I := I) (M := M)
    g b c n dΦ hS hdjoint ha δ hδ
  have hseg := segment_eventually (hS.mem_nhds ha)
  have harg : Tendsto (fun h : ℝ => a + h) (𝓝 0) (𝓝 a) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add tendsto_id :
        Tendsto (fun h : ℝ => a + h) (𝓝 0) (𝓝 (a + 0)))
  have hUt : Tendsto (fun h : ℝ => U (a + h)) (𝓝 0) (𝓝 (U a)) :=
    hU.tendsto.comp harg
  have hUb : ∀ᶠ h in 𝓝 (0 : ℝ), ‖U (a + h)‖ < B := by
    exact hUt.norm.eventually_lt_const (by simp only [B]; linarith)
  filter_upwards [hsmall, hseg, hUb] with h hh hseg hUb
  have heq :
      coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint a h =
        coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint a h hseg := by
    simp only [coeffRem0, dif_pos hseg]
  have happ :
      ‖appHs g b c n
        (coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint a h hseg)
        (U (a + h))‖ < ε := by
    calc
      ‖appHs g b c n
          (coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint a h hseg)
          (U (a + h))‖ ≤
          ‖appHs g b c n
            (coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint a h hseg)‖ *
            ‖U (a + h)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ δ * ‖U (a + h)‖ :=
        mul_le_mul_of_nonneg_right (hh hseg).le (norm_nonneg _)
      _ < δ * B := mul_lt_mul_of_pos_left hUb hδ
      _ = ε := by
        simp only [δ]
        field_simp
  simpa only [heq, Real.dist_eq, sub_zero, abs_norm] using happ



theorem exists_appHsDeriv
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : ℝ → SmoothCcTensor g b c) {S : Set ℝ} (hS : IsOpen S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ∃ dΦ : ℝ → SmoothCcTensor g b c,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
          (E := fun x : M => TensorRSSpace b c I x) p.1
          ((dΦ p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ S) ∧
      ∀ n : ℕ, ∀ t ∈ S,
        ∀ U : tensorHs (I := I) (M := M) g 0 b (n : ℝ),
        HasDerivAt
          (fun τ => appHs g b c n (Φ τ) U)
          (appHs g b c n (dΦ t) U) t := by
  classical
  obtain ⟨dΦ, hdjoint, hderiv⟩ :=
    exists_timeDerivCc (I := I) (M := M) g b c Φ hS hjoint
  refine ⟨dΦ, hdjoint, ?_⟩
  intro n t ht U
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hrem := coeffRem0_apply (I := I) (M := M)
    g b c n dΦ hS hdjoint ht U
  have hrem' : Tendsto
      (fun h => appHs g b c n
        (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h) U)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (0 : tensorHs (I := I) (M := M) g 0 c (n : ℝ))) :=
    hrem.mono_left inf_le_left
  have htarget : Tendsto
      (fun h => appHs g b c n (dΦ t) U +
        appHs g b c n
          (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h) U)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (appHs g b c n (dΦ t) U)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hrem'
  have hseg : ∀ᶠ h in 𝓝[≠] (0 : ℝ), Set.uIcc t (t + h) ⊆ S :=
    (segment_eventually (hS.mem_nhds ht)).filter_mono inf_le_left
  have hslope : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      h⁻¹ • (appHs g b c n (Φ (t + h)) U - appHs g b c n (Φ t) U) =
        appHs g b c n (dΦ t) U +
          appHs g b c n
            (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h) U := by
    filter_upwards [hseg, self_mem_nhdsWithin] with h hseg hh
    have hh0 : h ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh
    have hrem_eq :
        coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h =
          coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint t h hseg := by
      simp only [coeffRem0, dif_pos hseg]
    have hsec := coeff_secant (I := I) (M := M)
      g b c Φ dΦ hS hdjoint hderiv t h hseg
    have hact := congrArg
      (fun Q : SmoothCcTensor g b c => appHs g b c n Q U) hsec
    simp only [appHs_sub, appHs_smul] at hact
    rw [← hrem_eq] at hact
    have hdiff :
        appHs g b c n (Φ (t + h)) U - appHs g b c n (Φ t) U =
          h • (appHs g b c n (dΦ t) U +
            appHs g b c n
              (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h) U) := by
      calc
        appHs g b c n (Φ (t + h)) U - appHs g b c n (Φ t) U =
            h • appHs g b c n
                (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h) U +
              h • appHs g b c n (dΦ t) U :=
          (sub_eq_iff_eq_add.mp hact)
        _ = h • (appHs g b c n (dΦ t) U +
            appHs g b c n
              (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h) U) := by
          module
    calc
      h⁻¹ • (appHs g b c n (Φ (t + h)) U - appHs g b c n (Φ t) U) =
          h⁻¹ • (h • (appHs g b c n (dΦ t) U +
            appHs g b c n
              (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h) U)) := by
        rw [hdiff]
      _ = appHs g b c n (dΦ t) U +
          appHs g b c n
            (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h) U :=
        inv_smul_smul₀ hh0 _
  exact htarget.congr' (hslope.mono fun _ hh => hh.symm)




theorem exists_appHsDyn
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : ℝ → SmoothCcTensor g b c) {S : Set ℝ} (hS : IsOpen S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ∃ dΦ : ℝ → SmoothCcTensor g b c,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
          (E := fun x : M => TensorRSSpace b c I x) p.1
          ((dΦ p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ S) ∧
      ∀ n : ℕ, ∀ t ∈ S,
        ∀ (U : ℝ → tensorHs (I := I) (M := M) g 0 b (n : ℝ))
          (U' : tensorHs (I := I) (M := M) g 0 b (n : ℝ)),
          HasDerivAt U U' t →
          HasDerivAt
            (fun τ => appHs g b c n (Φ τ) (U τ))
            (appHs g b c n (dΦ t) (U t) + appHs g b c n (Φ t) U') t := by
  classical
  obtain ⟨dΦ, hdjoint, hderiv⟩ :=
    exists_timeDerivCc (I := I) (M := M) g b c Φ hS hjoint
  refine ⟨dΦ, hdjoint, ?_⟩
  intro n t ht U U' hU
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hinput : Tendsto
      (fun h : ℝ => h⁻¹ • (U (t + h) - U t))
      (𝓝[≠] (0 : ℝ)) (𝓝 U') :=
    hU.tendsto_slope_zero
  have hfixed : Tendsto
      (fun h : ℝ => appHs g b c n (Φ t) (h⁻¹ • (U (t + h) - U t)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (appHs g b c n (Φ t) U')) :=
    ((appHs g b c n (Φ t)).continuous.tendsto U').comp hinput
  have harg : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 t) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add tendsto_id :
        Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 (t + 0)))
  have hUt : Tendsto (fun h : ℝ => U (t + h)) (𝓝 0) (𝓝 (U t)) :=
    hU.continuousAt.tendsto.comp harg
  have hcoeff : Tendsto
      (fun h : ℝ => appHs g b c n (dΦ t) (U (t + h)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (appHs g b c n (dΦ t) (U t))) :=
    (((appHs g b c n (dΦ t)).continuous.tendsto (U t)).comp hUt).mono_left inf_le_left
  have hrem := coeffRem0_move (I := I) (M := M)
    g b c n dΦ hS hdjoint ht U hU.continuousAt
  have hrem' : Tendsto
      (fun h : ℝ => appHs g b c n
        (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h) (U (t + h)))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (0 : tensorHs (I := I) (M := M) g 0 c (n : ℝ))) :=
    hrem.mono_left inf_le_left
  have htarget : Tendsto
      (fun h : ℝ =>
        appHs g b c n (dΦ t) (U (t + h)) +
          appHs g b c n (Φ t) (h⁻¹ • (U (t + h) - U t)) +
          appHs g b c n
            (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
            (U (t + h)))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (appHs g b c n (dΦ t) (U t) + appHs g b c n (Φ t) U')) := by
    simpa only [add_zero] using (hcoeff.add hfixed).add hrem'
  have hseg : ∀ᶠ h in 𝓝[≠] (0 : ℝ), Set.uIcc t (t + h) ⊆ S :=
    (segment_eventually (hS.mem_nhds ht)).filter_mono inf_le_left
  have hslope : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      h⁻¹ •
          (appHs g b c n (Φ (t + h)) (U (t + h)) -
            appHs g b c n (Φ t) (U t)) =
        appHs g b c n (dΦ t) (U (t + h)) +
          appHs g b c n (Φ t) (h⁻¹ • (U (t + h) - U t)) +
          appHs g b c n
            (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
            (U (t + h)) := by
    filter_upwards [hseg, self_mem_nhdsWithin] with h hseg hh
    have hh0 : h ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh
    have hrem_eq :
        coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h =
          coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint t h hseg := by
      simp only [coeffRem0, dif_pos hseg]
    have hsec := coeff_secant (I := I) (M := M)
      g b c Φ dΦ hS hdjoint hderiv t h hseg
    have hact := congrArg
      (fun Q : SmoothCcTensor g b c => appHs g b c n Q (U (t + h))) hsec
    simp only [appHs_sub, appHs_smul] at hact
    rw [← hrem_eq] at hact
    have hcoeff_eq :
        appHs g b c n (Φ (t + h)) (U (t + h)) -
            appHs g b c n (Φ t) (U (t + h)) =
          h • (appHs g b c n
              (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
              (U (t + h)) +
            appHs g b c n (dΦ t) (U (t + h))) := by
      calc
        appHs g b c n (Φ (t + h)) (U (t + h)) -
            appHs g b c n (Φ t) (U (t + h)) =
          h • appHs g b c n
              (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
              (U (t + h)) +
            h • appHs g b c n (dΦ t) (U (t + h)) :=
          sub_eq_iff_eq_add.mp hact
        _ = h • (appHs g b c n
              (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
              (U (t + h)) +
            appHs g b c n (dΦ t) (U (t + h))) := by
          rw [smul_add]
    have hdiff :
        appHs g b c n (Φ (t + h)) (U (t + h)) -
            appHs g b c n (Φ t) (U t) =
          h • (appHs g b c n
              (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
              (U (t + h)) +
            appHs g b c n (dΦ t) (U (t + h))) +
            appHs g b c n (Φ t) (U (t + h) - U t) := by
      calc
        appHs g b c n (Φ (t + h)) (U (t + h)) -
            appHs g b c n (Φ t) (U t) =
          (appHs g b c n (Φ (t + h)) (U (t + h)) -
              appHs g b c n (Φ t) (U (t + h))) +
            (appHs g b c n (Φ t) (U (t + h)) -
              appHs g b c n (Φ t) (U t)) := by
          module
        _ = h • (appHs g b c n
              (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
              (U (t + h)) +
            appHs g b c n (dΦ t) (U (t + h))) +
            appHs g b c n (Φ t) (U (t + h) - U t) := by
          rw [hcoeff_eq, map_sub]
    calc
      h⁻¹ •
          (appHs g b c n (Φ (t + h)) (U (t + h)) -
            appHs g b c n (Φ t) (U t)) =
        h⁻¹ • (h • (appHs g b c n
              (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
              (U (t + h)) +
            appHs g b c n (dΦ t) (U (t + h))) +
          appHs g b c n (Φ t) (U (t + h) - U t)) := by
        rw [hdiff]
      _ = (appHs g b c n
              (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
              (U (t + h)) +
            appHs g b c n (dΦ t) (U (t + h))) +
          appHs g b c n (Φ t) (h⁻¹ • (U (t + h) - U t)) := by
        simp only [smul_add, inv_smul_smul₀ hh0, map_smul]
      _ = appHs g b c n (dΦ t) (U (t + h)) +
          appHs g b c n (Φ t) (h⁻¹ • (U (t + h) - U t)) +
          appHs g b c n
            (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
            (U (t + h)) := by
        module
  exact htarget.congr' (hslope.mono fun _ hh => hh.symm)



theorem appHs_dyn_cont
    (g : SmoothRiemannianMetric I M) (b c n : ℕ)
    (Φ : ℝ → SmoothCcTensor g b c) {S : Set ℝ} (hS : IsOpen S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (U : ℝ → tensorHs (I := I) (M := M) g 0 b (n : ℝ))
    (hU : ContinuousOn U S) :
    ContinuousOn (fun t => appHs g b c n (Φ t) (U t)) S := by
  classical
  obtain ⟨dΦ, hdjoint, hderiv⟩ :=
    exists_timeDerivCc (I := I) (M := M) g b c Φ hS hjoint
  intro t ht
  have hUAt : ContinuousAt U t :=
    (hU t ht).continuousAt (hS.mem_nhds ht)
  have harg : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 t) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add tendsto_id :
        Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 (t + 0)))
  have hUt : Tendsto (fun h : ℝ => U (t + h)) (𝓝 0) (𝓝 (U t)) :=
    hUAt.tendsto.comp harg
  have hdiffU : Tendsto (fun h : ℝ => U (t + h) - U t)
      (𝓝 0) (𝓝 (0 : tensorHs (I := I) (M := M) g 0 b (n : ℝ))) := by
    simpa only [sub_self] using hUt.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => U t) (𝓝 0) (𝓝 (U t)))
  have hfixed : Tendsto
      (fun h : ℝ => appHs g b c n (Φ t) (U (t + h) - U t))
      (𝓝 0)
      (𝓝 (0 : tensorHs (I := I) (M := M) g 0 c (n : ℝ))) :=
    by
      simpa only [Function.comp_apply, map_zero] using
        ((appHs g b c n (Φ t)).continuous.tendsto 0).comp hdiffU
  have hdapp : Tendsto
      (fun h : ℝ => appHs g b c n (dΦ t) (U (t + h)))
      (𝓝 0) (𝓝 (appHs g b c n (dΦ t) (U t))) :=
    ((appHs g b c n (dΦ t)).continuous.tendsto (U t)).comp hUt
  have hdsmall : Tendsto
      (fun h : ℝ => h • appHs g b c n (dΦ t) (U (t + h)))
      (𝓝 0)
      (𝓝 (0 : tensorHs (I := I) (M := M) g 0 c (n : ℝ))) := by
    simpa only [zero_smul] using tendsto_id.smul hdapp
  have hrem := coeffRem0_move (I := I) (M := M)
    g b c n dΦ hS hdjoint ht U hUAt
  have hrsmall : Tendsto
      (fun h : ℝ => h • appHs g b c n
        (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
        (U (t + h)))
      (𝓝 0)
      (𝓝 (0 : tensorHs (I := I) (M := M) g 0 c (n : ℝ))) := by
    simpa only [zero_smul] using tendsto_id.smul hrem
  have htarget : Tendsto
      (fun h : ℝ =>
        h • appHs g b c n
            (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
            (U (t + h)) +
          h • appHs g b c n (dΦ t) (U (t + h)) +
          appHs g b c n (Φ t) (U (t + h) - U t))
      (𝓝 0)
      (𝓝 (0 : tensorHs (I := I) (M := M) g 0 c (n : ℝ))) := by
    simpa only [zero_add] using (hrsmall.add hdsmall).add hfixed
  have hseg : ∀ᶠ h in 𝓝 (0 : ℝ), Set.uIcc t (t + h) ⊆ S :=
    segment_eventually (hS.mem_nhds ht)
  have hdelta : ∀ᶠ h in 𝓝 (0 : ℝ),
      appHs g b c n (Φ (t + h)) (U (t + h)) -
          appHs g b c n (Φ t) (U t) =
        h • appHs g b c n
            (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
            (U (t + h)) +
          h • appHs g b c n (dΦ t) (U (t + h)) +
          appHs g b c n (Φ t) (U (t + h) - U t) := by
    filter_upwards [hseg] with h hseg
    have hrem_eq :
        coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h =
          coeffRem (I := I) (M := M) g b c dΦ S hS hdjoint t h hseg := by
      simp only [coeffRem0, dif_pos hseg]
    have hsec := coeff_secant (I := I) (M := M)
      g b c Φ dΦ hS hdjoint hderiv t h hseg
    have hact := congrArg
      (fun Q : SmoothCcTensor g b c => appHs g b c n Q (U (t + h))) hsec
    simp only [appHs_sub, appHs_smul] at hact
    rw [← hrem_eq] at hact
    have hcoeff_eq :
        appHs g b c n (Φ (t + h)) (U (t + h)) -
            appHs g b c n (Φ t) (U (t + h)) =
          h • (appHs g b c n
              (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
              (U (t + h)) +
            appHs g b c n (dΦ t) (U (t + h))) := by
      calc
        appHs g b c n (Φ (t + h)) (U (t + h)) -
            appHs g b c n (Φ t) (U (t + h)) =
          h • appHs g b c n
              (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
              (U (t + h)) +
            h • appHs g b c n (dΦ t) (U (t + h)) :=
          sub_eq_iff_eq_add.mp hact
        _ = h • (appHs g b c n
              (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
              (U (t + h)) +
            appHs g b c n (dΦ t) (U (t + h))) := by
          rw [smul_add]
    calc
      appHs g b c n (Φ (t + h)) (U (t + h)) -
          appHs g b c n (Φ t) (U t) =
        (appHs g b c n (Φ (t + h)) (U (t + h)) -
            appHs g b c n (Φ t) (U (t + h))) +
          (appHs g b c n (Φ t) (U (t + h)) -
            appHs g b c n (Φ t) (U t)) := by
        module
      _ = h • appHs g b c n
            (coeffRem0 (I := I) (M := M) g b c dΦ S hS hdjoint t h)
            (U (t + h)) +
          h • appHs g b c n (dΦ t) (U (t + h)) +
          appHs g b c n (Φ t) (U (t + h) - U t) := by
        rw [hcoeff_eq, map_sub, smul_add]
  have hzero : Tendsto
      (fun h : ℝ =>
        appHs g b c n (Φ (t + h)) (U (t + h)) -
          appHs g b c n (Φ t) (U t))
      (𝓝 0)
      (𝓝 (0 : tensorHs (I := I) (M := M) g 0 c (n : ℝ))) :=
    htarget.congr' (hdelta.mono fun _ hh => hh.symm)
  have hshift : Tendsto
      (fun h : ℝ => appHs g b c n (Φ (t + h)) (U (t + h)))
      (𝓝 0) (𝓝 (appHs g b c n (Φ t) (U t))) := by
    simpa only [sub_add_cancel, zero_add] using hzero.add
      (tendsto_const_nhds : Tendsto
        (fun _ : ℝ => appHs g b c n (Φ t) (U t))
        (𝓝 0) (𝓝 (appHs g b c n (Φ t) (U t))))
  have hsub : Tendsto (fun τ : ℝ => τ - t) (𝓝 t) (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_id : Tendsto (fun τ : ℝ => τ) (𝓝 t) (𝓝 t)).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => t) (𝓝 t) (𝓝 t))
  have hcomp := hshift.comp hsub
  have heq :
      (fun τ : ℝ => appHs g b c n (Φ (t + (τ - t))) (U (t + (τ - t)))) =
        fun τ => appHs g b c n (Φ τ) (U τ) := by
    funext τ
    rw [show t + (τ - t) = τ by ring]
  change Tendsto
    (fun τ : ℝ => appHs g b c n (Φ (t + (τ - t))) (U (t + (τ - t))))
    (𝓝 t) (𝓝 (appHs g b c n (Φ t) (U t))) at hcomp
  rw [heq] at hcomp
  have hAt : ContinuousAt (fun τ => appHs g b c n (Φ τ) (U τ)) t := hcomp
  exact hAt.continuousWithinAt



theorem appHs_dyn_fin
    (g : SmoothRiemannianMetric I M) (b c n k : ℕ)
    (Φ : ℝ → SmoothCcTensor g b c) {S : Set ℝ} (hS : IsOpen S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (U : ℝ → tensorHs (I := I) (M := M) g 0 b (n : ℝ))
    (hU : ContDiffOn ℝ k U S) :
    ContDiffOn ℝ k (fun t => appHs g b c n (Φ t) (U t)) S := by
  revert Φ U
  induction k with
  | zero =>
      intro Φ hjoint U hU
      apply contDiffOn_zero.mpr
      apply appHs_dyn_cont (I := I) (M := M) g b c n Φ hS hjoint U
      exact contDiffOn_zero.mp hU
  | succ k ih =>
      intro Φ hjoint U hU
      obtain ⟨dΦ, hdjoint, hderiv⟩ :=
        exists_appHsDyn (I := I) (M := M) g b c Φ hS hjoint
      have hU' : ContDiffOn ℝ ((k : WithTop ℕ∞) + 1) U S := by
        simpa only [Nat.cast_add, Nat.cast_one] using hU
      have hUdata := (contDiffOn_succ_iff_deriv_of_isOpen hS).mp hU'
      have hUlow : ContDiffOn ℝ k U S :=
        hU.of_le (by exact_mod_cast Nat.le_succ k)
      have hprodDiff : DifferentiableOn ℝ
          (fun t => appHs g b c n (Φ t) (U t)) S := by
        intro t ht
        have hUAt : DifferentiableAt ℝ U t :=
          (hUdata.1 t ht).differentiableAt (hS.mem_nhds ht)
        exact (hderiv n t ht U (deriv U t) hUAt.hasDerivAt).differentiableAt
          |>.differentiableWithinAt
      have hderiv_cd : ContDiffOn ℝ k
          (deriv (fun t => appHs g b c n (Φ t) (U t))) S := by
        refine ((ih dΦ hdjoint U hUlow).add
          (ih Φ hjoint (deriv U) hUdata.2.2)).congr ?_
        intro t ht
        have hUAt : DifferentiableAt ℝ U t :=
          (hUdata.1 t ht).differentiableAt (hS.mem_nhds ht)
        exact (hderiv n t ht U (deriv U t) hUAt.hasDerivAt).deriv
      simp only [Nat.cast_add, Nat.cast_one]
      rw [contDiffOn_succ_iff_deriv_of_isOpen hS]
      refine ⟨hprodDiff, ?_, hderiv_cd⟩
      intro hk
      norm_num at hk



theorem appHs_dyn_cd
    (g : SmoothRiemannianMetric I M) (b c n : ℕ)
    (Φ : ℝ → SmoothCcTensor g b c) {S : Set ℝ} (hS : IsOpen S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (U : ℝ → tensorHs (I := I) (M := M) g 0 b (n : ℝ))
    (hU : ContDiffOn ℝ ∞ U S) :
    ContDiffOn ℝ ∞ (fun t => appHs g b c n (Φ t) (U t)) S := by
  rw [contDiffOn_infty] at hU ⊢
  intro k
  exact appHs_dyn_fin (I := I) (M := M) g b c n k Φ hS hjoint U (hU k)



theorem appHs_path_cd
    (g : SmoothRiemannianMetric I M) (b c n : ℕ)
    (Φ : ℝ → SmoothCcTensor g b c) {S : Set ℝ} (hS : IsOpen S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (U : tensorHs (I := I) (M := M) g 0 b (n : ℝ)) :
    ContDiffOn ℝ ∞ (fun t => appHs g b c n (Φ t) U) S := by
  rw [contDiffOn_infty]
  intro k
  revert Φ
  induction k with
  | zero =>
      intro Φ hjoint
      obtain ⟨_, _, hderiv⟩ :=
        exists_appHsDeriv (I := I) (M := M) g b c Φ hS hjoint
      have hcont : ContinuousOn (fun t => appHs g b c n (Φ t) U) S := by
        intro t ht
        exact (hderiv n t ht U).continuousAt.continuousWithinAt
      have hzero : ContDiffOn ℝ (0 : WithTop ℕ∞)
          (fun t => appHs g b c n (Φ t) U) S :=
        contDiffOn_zero.mpr hcont
      exact hzero.of_le (by norm_num)
  | succ k ih =>
      intro Φ hjoint
      obtain ⟨dΦ, hdjoint, hderiv⟩ :=
        exists_appHsDeriv (I := I) (M := M) g b c Φ hS hjoint
      have hdiff : DifferentiableOn ℝ
          (fun t => appHs g b c n (Φ t) U) S := by
        intro t ht
        exact (hderiv n t ht U).differentiableAt.differentiableWithinAt
      have hderiv_cd : ContDiffOn ℝ k
          (deriv (fun t => appHs g b c n (Φ t) U)) S := by
        refine (ih dΦ hdjoint).congr ?_
        intro t ht
        exact (hderiv n t ht U).deriv
      simp only [Nat.cast_add, Nat.cast_one]
      rw [contDiffOn_succ_iff_deriv_of_isOpen hS]
      refine ⟨hdiff, ?_, hderiv_cd⟩
      intro hk
      norm_num at hk

end Connection
end Integral
end DifferentialGeometry

end
