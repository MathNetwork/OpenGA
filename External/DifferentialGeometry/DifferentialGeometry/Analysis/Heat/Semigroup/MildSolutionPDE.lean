import DifferentialGeometry.Analysis.Heat.Semigroup.Duhamel
import DifferentialGeometry.Analysis.Heat.Semigroup.Generator
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private lemma continuous_inner_basis_apply
    (g : SmoothRiemannianMetric I M)
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) (i : EigenIdx (I := I) (M := M) g) :
    Continuous (fun s : ℝ =>
      ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, f s⟫_ℝ) := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_innerCLM := (innerSL (𝕜 := ℝ)
      (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (b i)).continuous
  have h_eq : (fun s : ℝ => ⟪b i, f s⟫_ℝ) =
      (fun s : ℝ => (innerSL (𝕜 := ℝ)
        (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (b i)) (f s)) := by
    funext s; rw [innerSL_apply_apply]
  rw [h_eq]
  exact h_innerCLM.comp hf

private lemma intervalIntegrable_inner_basis_apply
    (g : SmoothRiemannianMetric I M)
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) (i : EigenIdx (I := I) (M := M) g)
    (a b' : ℝ) :
    IntervalIntegrable
      (fun s : ℝ =>
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, f s⟫_ℝ)
      MeasureTheory.volume a b' :=
  (continuous_inner_basis_apply (I := I) (M := M) g hf i).intervalIntegrable a b'

theorem mildSolution_inner_basis
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t)
    (i : EigenIdx (I := I) (M := M) g) :
    ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
      mildSolution (I := I) (M := M) g u_0 f t⟫_ℝ =
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u_0⟫_ℝ +
      ∫ s in (0 : ℝ)..t,
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * (t - s)) *
          ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, f s⟫_ℝ := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  set lam_i : ℝ := EigenIdx.lambda (I := I) (M := M) i with hlam_def
  unfold mildSolution
  rw [inner_add_right]
  congr 1
  · have h_self := heatSemigroup_isSelfAdjoint (I := I) (M := M) g ht
    have h_sym : (heatSemigroup (I := I) (M := M) g t :
        (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) →ₗ[ℝ] _).IsSymmetric :=
      ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric
        (A := heatSemigroup (I := I) (M := M) g t)).mp h_self)
    have h_swap : ⟪b i, heatSemigroup (I := I) (M := M) g t u_0⟫_ℝ =
        ⟪heatSemigroup (I := I) (M := M) g t (b i), u_0⟫_ℝ := by
      have h := h_sym.apply_clm (b i) u_0
      exact h.symm
    rw [h_swap]
    have h_basis_apply :
        heatSemigroup (I := I) (M := M) g t (b i) =
          Real.exp (-lam_i * t) • b i := by
      have h_eq : resolventEigenbasisSigma (I := I) (M := M) g i = b i := by
        rw [show b i = resolventHilbertEigenbasisSigma (I := I) (M := M) g i from rfl,
          (resolventEigenbasisSigma_eq_resolventEigenbasisVec (I := I) (M := M) g i),
          ← resolventHilbertEigenbasisSigma_apply (I := I) (M := M) g i]
      have h := heatSemigroup_apply_basis (I := I) (M := M) g ht i
      rw [h_eq] at h
      exact h
    rw [h_basis_apply]
    rw [real_inner_smul_left]
  · set φ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ :=
      innerSL (𝕜 := ℝ)
        (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (b i) with hφ_def
    have h_int := heatSemigroup_apply_f_continuous (I := I) (M := M) g hf t
    have h_uIcc : Set.uIcc (0 : ℝ) t = Set.Icc 0 t := Set.uIcc_of_le ht
    rw [← h_uIcc] at h_int
    have h_intInt : IntervalIntegrable
        (fun s : ℝ => heatSemigroup (I := I) (M := M) g (t - s) (f s))
        MeasureTheory.volume 0 t := h_int.intervalIntegrable
    have h_comm := ContinuousLinearMap.intervalIntegral_comp_comm
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := t)
      φ h_intInt
    have h_phi_apply : ∀ s,
        φ (heatSemigroup (I := I) (M := M) g (t - s) (f s)) =
          ⟪b i, heatSemigroup (I := I) (M := M) g (t - s) (f s)⟫_ℝ := by
      intro s; rfl
    change ⟪b i, ∫ s in (0 : ℝ)..t,
        heatSemigroup (I := I) (M := M) g (t - s) (f s)⟫_ℝ = _
    rw [show ⟪b i, ∫ s in (0 : ℝ)..t,
            heatSemigroup (I := I) (M := M) g (t - s) (f s)⟫_ℝ =
          φ (∫ s in (0 : ℝ)..t,
            heatSemigroup (I := I) (M := M) g (t - s) (f s)) from rfl]
    rw [← h_comm]
    have h_pointwise : ∀ s ∈ Set.Icc (0 : ℝ) t,
        φ (heatSemigroup (I := I) (M := M) g (t - s) (f s)) =
          Real.exp (-lam_i * (t - s)) * ⟪b i, f s⟫_ℝ := by
      intro s hs
      have hts_nn : 0 ≤ t - s := sub_nonneg.mpr hs.2
      rw [h_phi_apply]
      have h_self := heatSemigroup_isSelfAdjoint (I := I) (M := M) g hts_nn
      have h_sym : (heatSemigroup (I := I) (M := M) g (t - s) :
          (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) →ₗ[ℝ] _).IsSymmetric :=
        ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric
          (A := heatSemigroup (I := I) (M := M) g (t - s))).mp h_self)
      have h_swap : ⟪b i, heatSemigroup (I := I) (M := M) g (t - s) (f s)⟫_ℝ =
          ⟪heatSemigroup (I := I) (M := M) g (t - s) (b i), f s⟫_ℝ :=
        (h_sym.apply_clm (b i) (f s)).symm
      rw [h_swap]
      have h_basis_apply :
          heatSemigroup (I := I) (M := M) g (t - s) (b i) =
            Real.exp (-lam_i * (t - s)) • b i := by
        have h_eq : resolventEigenbasisSigma (I := I) (M := M) g i = b i := by
          rw [show b i = resolventHilbertEigenbasisSigma (I := I) (M := M) g i from rfl,
            (resolventEigenbasisSigma_eq_resolventEigenbasisVec (I := I) (M := M) g i),
            ← resolventHilbertEigenbasisSigma_apply (I := I) (M := M) g i]
        have h := heatSemigroup_apply_basis (I := I) (M := M) g hts_nn i
        rw [h_eq] at h
        exact h
      rw [h_basis_apply, real_inner_smul_left]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    exact h_pointwise s hs

private lemma exp_factor (lam : ℝ) (t s : ℝ) :
    Real.exp (-lam * (t - s)) = Real.exp (-lam * t) * Real.exp (lam * s) := by
  rw [← Real.exp_add]
  congr 1; ring

private lemma duhamel_inner_factor
    (lam : ℝ) {t : ℝ} (h : ℝ → ℝ)
    (_h_int : IntervalIntegrable (fun s => Real.exp (lam * s) * h s)
      MeasureTheory.volume 0 t) :
    ∫ s in (0 : ℝ)..t, Real.exp (-lam * (t - s)) * h s =
      Real.exp (-lam * t) * ∫ s in (0 : ℝ)..t, Real.exp (lam * s) * h s := by
  have h_eq : (fun s : ℝ => Real.exp (-lam * (t - s)) * h s) =
      (fun s : ℝ => Real.exp (-lam * t) * (Real.exp (lam * s) * h s)) := by
    funext s
    rw [exp_factor lam t s]; ring
  rw [h_eq]
  rw [intervalIntegral.integral_const_mul]

theorem hasDerivAt_mildSolution_inner_basis
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 < t)
    (i : EigenIdx (I := I) (M := M) g) :
    HasDerivAt
      (fun s : ℝ =>
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
          mildSolution (I := I) (M := M) g u_0 f s⟫_ℝ)
      (-(EigenIdx.lambda (I := I) (M := M) i) *
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
          mildSolution (I := I) (M := M) g u_0 f t⟫_ℝ +
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, f t⟫_ℝ)
      t := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g with hb_def
  set lam_i : ℝ := EigenIdx.lambda (I := I) (M := M) i with hlam_def
  set c_u : ℝ := ⟪b i, u_0⟫_ℝ with hcu_def
  set hf_scalar : ℝ → ℝ := fun s => ⟪b i, f s⟫_ℝ with hhf_def
  have hf_scalar_cont : Continuous hf_scalar :=
    continuous_inner_basis_apply (I := I) (M := M) g hf i
  set c1 : ℝ → ℝ := fun s => Real.exp (-lam_i * s) * c_u with hc1_def
  set G : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, Real.exp (lam_i * r) * hf_scalar r with hG_def
  set c2 : ℝ → ℝ := fun s => Real.exp (-lam_i * s) * G s with hc2_def
  have h_split : ∀ s, 0 ≤ s →
      ⟪b i, mildSolution (I := I) (M := M) g u_0 f s⟫_ℝ = c1 s + c2 s := by
    intro s hs
    have h_form := mildSolution_inner_basis (I := I) (M := M) g u_0 hf hs i
    rw [h_form]
    have h_int_factor : IntervalIntegrable
        (fun r => Real.exp (lam_i * r) * hf_scalar r)
        MeasureTheory.volume 0 s := by
      have h_cont_factor : Continuous
          (fun r : ℝ => Real.exp (lam_i * r) * hf_scalar r) :=
        ((Real.continuous_exp.comp
          (continuous_const.mul continuous_id)).mul hf_scalar_cont)
      exact h_cont_factor.intervalIntegrable _ _
    have h_factored := duhamel_inner_factor (t := s) lam_i hf_scalar h_int_factor
    change Real.exp (-lam_i * s) * c_u +
      ∫ r in (0 : ℝ)..s, Real.exp (-lam_i * (s - r)) * hf_scalar r =
      c1 s + c2 s
    rw [h_factored]
  have h_c1_deriv : HasDerivAt c1 (-lam_i * Real.exp (-lam_i * t) * c_u) t := by
    have h_lin : HasDerivAt (fun s : ℝ => -lam_i * s) (-lam_i) t := by
      have := (hasDerivAt_id (𝕜 := ℝ) t).const_mul (-lam_i)
      simpa using this
    have h_exp : HasDerivAt (fun s : ℝ => Real.exp (-lam_i * s))
        (Real.exp (-lam_i * t) * (-lam_i)) t := h_lin.exp
    have h_mul := h_exp.mul_const c_u
    have h_eq : Real.exp (-lam_i * t) * (-lam_i) * c_u = -lam_i * Real.exp (-lam_i * t) * c_u := by
      ring
    rw [h_eq] at h_mul
    exact h_mul
  have h_G_deriv : HasDerivAt G (Real.exp (lam_i * t) * hf_scalar t) t := by
    have h_cont_integrand : Continuous
        (fun r : ℝ => Real.exp (lam_i * r) * hf_scalar r) :=
      ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).mul hf_scalar_cont)
    have h_intInt :
        IntervalIntegrable (fun r : ℝ => Real.exp (lam_i * r) * hf_scalar r)
          MeasureTheory.volume 0 t :=
      h_cont_integrand.intervalIntegrable 0 t
    have h_meas : StronglyMeasurableAtFilter
        (fun r : ℝ => Real.exp (lam_i * r) * hf_scalar r)
        (𝓝 t) MeasureTheory.volume :=
      h_cont_integrand.aestronglyMeasurable.stronglyMeasurableAtFilter
    have h_at_t := h_cont_integrand.continuousAt (x := t)
    exact intervalIntegral.integral_hasDerivAt_right h_intInt h_meas h_at_t
  have h_exp_neg_deriv : HasDerivAt (fun s : ℝ => Real.exp (-lam_i * s))
      (-lam_i * Real.exp (-lam_i * t)) t := by
    have h_lin : HasDerivAt (fun s : ℝ => -lam_i * s) (-lam_i) t := by
      have := (hasDerivAt_id (𝕜 := ℝ) t).const_mul (-lam_i)
      simpa using this
    have h_exp : HasDerivAt (fun s : ℝ => Real.exp (-lam_i * s))
        (Real.exp (-lam_i * t) * (-lam_i)) t := h_lin.exp
    have h_eq : Real.exp (-lam_i * t) * (-lam_i) = -lam_i * Real.exp (-lam_i * t) := by ring
    rw [h_eq] at h_exp
    exact h_exp
  have h_c2_deriv_raw : HasDerivAt c2
      ((-lam_i * Real.exp (-lam_i * t)) * G t +
        Real.exp (-lam_i * t) * (Real.exp (lam_i * t) * hf_scalar t)) t :=
    h_exp_neg_deriv.mul h_G_deriv
  have h_exp_cancel : Real.exp (-lam_i * t) * Real.exp (lam_i * t) = 1 := by
    rw [← Real.exp_add]
    have h_sum : -lam_i * t + lam_i * t = 0 := by ring
    rw [h_sum, Real.exp_zero]
  have h_c2_value : c2 t = Real.exp (-lam_i * t) * G t := rfl
  have h_c2_deriv : HasDerivAt c2 (-lam_i * c2 t + hf_scalar t) t := by
    have h_target_eq :
        (-lam_i * Real.exp (-lam_i * t)) * G t +
          Real.exp (-lam_i * t) * (Real.exp (lam_i * t) * hf_scalar t) =
        -lam_i * c2 t + hf_scalar t := by
      rw [h_c2_value]
      have h_assoc : Real.exp (-lam_i * t) * (Real.exp (lam_i * t) * hf_scalar t) =
          (Real.exp (-lam_i * t) * Real.exp (lam_i * t)) * hf_scalar t := by ring
      rw [h_assoc, h_exp_cancel, one_mul]
      ring
    rw [← h_target_eq]
    exact h_c2_deriv_raw
  have h_c1_value : c1 t = Real.exp (-lam_i * t) * c_u := rfl
  have h_c1_deriv' : HasDerivAt c1 (-lam_i * c1 t) t := by
    have h_target_eq : -lam_i * Real.exp (-lam_i * t) * c_u = -lam_i * c1 t := by
      rw [h_c1_value]; ring
    rw [← h_target_eq]
    exact h_c1_deriv
  have h_sum_deriv : HasDerivAt (fun s => c1 s + c2 s)
      (-lam_i * c1 t + (-lam_i * c2 t + hf_scalar t)) t :=
    h_c1_deriv'.add h_c2_deriv
  have h_target_eq : -lam_i * c1 t + (-lam_i * c2 t + hf_scalar t) =
      -lam_i * (c1 t + c2 t) + hf_scalar t := by ring
  rw [h_target_eq] at h_sum_deriv
  have h_at_t : c1 t + c2 t = ⟪b i, mildSolution (I := I) (M := M) g u_0 f t⟫_ℝ :=
    (h_split t ht.le).symm
  rw [h_at_t] at h_sum_deriv
  have h_pos_nhds : Set.Ioi (0 : ℝ) ∈ 𝓝 t := Ioi_mem_nhds ht
  have h_eventually_eq :
      (fun s : ℝ =>
        ⟪b i, mildSolution (I := I) (M := M) g u_0 f s⟫_ℝ) =ᶠ[𝓝 t]
      (fun s : ℝ => c1 s + c2 s) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioi (0 : ℝ), h_pos_nhds, ?_⟩
    intro s hs
    have hs_nn : 0 ≤ s := le_of_lt hs
    exact h_split s hs_nn
  exact h_sum_deriv.congr_of_eventuallyEq h_eventually_eq

end HeatEquation
end Analysis
end DifferentialGeometry

end
