import DifferentialGeometry.Analysis.Integration.Measure.Family
import DifferentialGeometry.Bundle.PartialMfderiv
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false










noncomputable section

open Bundle Manifold Set MeasureTheory Matrix Filter
open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]





private def timeRetract (t δ w s : Real) : Real :=
  t + (s - t) * (1 - Real.smoothTransition ((s - t - δ) / w)) *
    (1 - Real.smoothTransition ((t - δ - s) / w))

private lemma timeRetract_smooth (t δ w : Real) :
    ContDiff Real ∞ (timeRetract t δ w) := by
  unfold timeRetract
  have hright : ContDiff Real ∞
      (fun s : Real => (1 : Real) - Real.smoothTransition ((s - t - δ) / w)) :=
    contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))
  have hleft : ContDiff Real ∞
      (fun s : Real => (1 : Real) - Real.smoothTransition ((t - δ - s) / w)) :=
    contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))
  exact contDiff_const.add (((contDiff_id.sub contDiff_const).mul hright).mul hleft)

private lemma timeRetract_eq_self (t δ w : Real) (hw : 0 < w) {s : Real}
    (hs : s ∈ Set.Icc (t - δ) (t + δ)) :
    timeRetract t δ w s = s := by
  obtain ⟨hs1, hs2⟩ := hs
  unfold timeRetract
  have hright : Real.smoothTransition ((s - t - δ) / w) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hw)
  have hleft : Real.smoothTransition ((t - δ - s) / w) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hw)
  rw [hright, hleft]
  ring

private lemma timeRetract_abs_le (t δ w : Real) (hδ : 0 ≤ δ) (hw : 0 < w)
    (s : Real) :
    |timeRetract t δ w s - t| ≤ δ + w := by
  unfold timeRetract
  rw [add_sub_cancel_left]
  by_cases hin : s ∈ Set.Icc (t - δ - w) (t + δ + w)
  · obtain ⟨hin1, hin2⟩ := hin
    have hright : (1 : Real) - Real.smoothTransition ((s - t - δ) / w) ∈
        Set.Icc (0 : Real) 1 :=
      ⟨by linarith [Real.smoothTransition.le_one ((s - t - δ) / w)],
        by linarith [Real.smoothTransition.nonneg ((s - t - δ) / w)]⟩
    have hleft : (1 : Real) - Real.smoothTransition ((t - δ - s) / w) ∈
        Set.Icc (0 : Real) 1 :=
      ⟨by linarith [Real.smoothTransition.le_one ((t - δ - s) / w)],
        by linarith [Real.smoothTransition.nonneg ((t - δ - s) / w)]⟩
    rw [abs_mul, abs_mul]
    have hright_le :
        |(1 : Real) - Real.smoothTransition ((s - t - δ) / w)| ≤ 1 := by
      rw [abs_of_nonneg hright.1]
      exact hright.2
    have hleft_le :
        |(1 : Real) - Real.smoothTransition ((t - δ - s) / w)| ≤ 1 := by
      rw [abs_of_nonneg hleft.1]
      exact hleft.2
    have hst : |s - t| ≤ δ + w := by
      rw [abs_le]
      constructor <;> linarith
    calc
      |s - t| * |(1 : Real) - Real.smoothTransition ((s - t - δ) / w)| *
          |(1 : Real) - Real.smoothTransition ((t - δ - s) / w)|
          ≤ (δ + w) * 1 * 1 := by
            apply mul_le_mul
              (mul_le_mul hst hright_le (abs_nonneg _) (by linarith))
              hleft_le (abs_nonneg _)
            positivity
      _ = δ + w := by ring
  · rw [Set.mem_Icc, not_and_or] at hin
    have hzero :
        (s - t) * (1 - Real.smoothTransition ((s - t - δ) / w)) *
            (1 - Real.smoothTransition ((t - δ - s) / w)) = 0 := by
      rcases hin with hin | hin
      · have hlt : s < t - δ - w := lt_of_not_ge hin
        have hone : Real.smoothTransition ((t - δ - s) / w) = 1 := by
          apply Real.smoothTransition.one_of_one_le
          rw [le_div_iff₀ hw]
          linarith
        rw [hone]
        ring
      · have hlt : t + δ + w < s := lt_of_not_ge hin
        have hone : Real.smoothTransition ((s - t - δ) / w) = 1 := by
          apply Real.smoothTransition.one_of_one_le
          rw [le_div_iff₀ hw]
          linarith
        rw [hone]
        ring
    rw [hzero, abs_zero]
    linarith



theorem exists_time_retract {U : Set Real} (hU : IsOpen U) {t : Real}
    (ht : t ∈ U) :
    ∃ ρ : Real → Real, ContDiff Real ∞ ρ ∧
      (∀ s : Real, ρ s ∈ U) ∧ ρ =ᶠ[𝓝 t] (fun s : Real => s) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU t ht
  let η : Real := ε / 4
  have hη : 0 < η := by
    dsimp [η]
    positivity
  let ρ : Real → Real := timeRetract t η η
  refine ⟨ρ, timeRetract_smooth t η η, ?_, ?_⟩
  · intro s
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have hbound := timeRetract_abs_le t η η (le_of_lt hη) hη s
    change |timeRetract t η η s - t| < ε
    calc
      |timeRetract t η η s - t| ≤ η + η := hbound
      _ < ε := by dsimp [η]; linarith
  · have hmem : Set.Icc (t - η) (t + η) ∈ 𝓝 t :=
      Icc_mem_nhds (sub_lt_self t hη) (lt_add_of_pos_right t hη)
    filter_upwards [hmem] with s hs
    exact timeRetract_eq_self t η η hη hs





theorem first_var_local
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g_fam : Real → SmoothRiemannianMetric I M}
    {f : Real → M → Real} {U : Set Real} {t : Real}
    (hg : MetricFamilyRegularAt (I := I) g_fam t)
    (hU : IsOpen U) (ht : t ∈ U)
    (hf : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => f p.1 p.2) (U ×ˢ Set.univ)) :
    HasDerivAt
      (fun s : Real =>
        ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      (∫ x, (deriv (fun s : Real => f s x) t +
              (1 / 2) * traceTimeDerivMetric (I := I) g_fam t x * f t x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t)) t := by
  obtain ⟨ρ, hρsmooth, hρmem, hρeq⟩ := exists_time_retract hU ht
  let f' : Real → M → Real := fun s x => f (ρ s) x
  have hρmdiff : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ ρ := by
    rw [contMDiff_iff_contDiff]
    exact hρsmooth
  have hinner : ContMDiff (𝓘(Real, Real).prod I) (𝓘(Real, Real).prod I) ∞
      (fun p : Real × M => (ρ p.1, p.2)) :=
    (hρmdiff.comp contMDiff_fst).prodMk contMDiff_snd
  have hf'smooth : ContMDiff (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => f' p.1 p.2) := by
    exact hf.comp_contMDiff hinner (fun p => ⟨hρmem p.1, Set.mem_univ p.2⟩)
  let F' : C^∞⟮𝓘(Real, Real).prod I, Real × M; Real⟯ :=
    ⟨fun p : Real × M => f' p.1 p.2, hf'smooth⟩
  have hf'reg : FunctionRegularAt f' t := by
    refine
      { hasDerivAt_time := ?_
        continuous_joint := hf'smooth.continuous
        continuous_deriv_joint := ?_ }
    · intro x s
      have hslice : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞
          (fun r : Real => f' r x) := by
        exact hf'smooth.comp (contMDiff_id.prodMk contMDiff_const)
      have hdiff : DifferentiableAt Real (fun r : Real => f' r x) s := by
        rw [contMDiff_iff_contDiff] at hslice
        exact hslice.differentiable (by simp) s
      exact hdiff.hasDerivAt
    · exact (DifferentialGeometry.contMDiff_partial_deriv_fst I F').continuous
  have hvariation := first_variation_of_volume (I := I) (M := M) hg hf'reg
  have hmass_eq :
      (fun s : Real =>
        ∫ x, f' s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s)) =ᶠ[𝓝 t]
      (fun s : Real =>
        ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s)) := by
    filter_upwards [hρeq] with s hs
    simp only [f', hs]
  have hderiv_eq : ∀ x : M,
      deriv (fun s : Real => f' s x) t = deriv (fun s : Real => f s x) t := by
    intro x
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hρeq] with s hs
    simp only [f', hs]
  have hρt : ρ t = t := hρeq.eq_of_nhds
  have hvalue :
      (∫ x, (deriv (fun s : Real => f' s x) t +
              (1 / 2) * traceTimeDerivMetric (I := I) g_fam t x * f' t x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t)) =
        ∫ x, (deriv (fun s : Real => f s x) t +
              (1 / 2) * traceTimeDerivMetric (I := I) g_fam t x * f t x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hderiv_eq x]
    simp only [f', hρt]
  exact (hvariation.congr_deriv hvalue).congr_of_eventuallyEq hmass_eq.symm



theorem first_var_joint
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g_fam : Real → SmoothRiemannianMetric I M}
    {f : Real → M → Real} {U : Set Real} {t : Real}
    (hU : IsOpen U) (ht : t ∈ U)
    (hg : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hf : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => f p.1 p.2) (U ×ˢ Set.univ)) :
    HasDerivAt
      (fun s : Real =>
        ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      (∫ x, (deriv (fun s : Real => f s x) t +
              (1 / 2) * traceTimeDerivMetric (I := I) g_fam t x * f t x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t)) t := by
  classical
  obtain ⟨ρ, hρsmooth, hρmem, hρeq⟩ := exists_time_retract hU ht
  let g' : Real → SmoothRiemannianMetric I M := fun s => g_fam (ρ s)
  let f' : Real → M → Real := fun s x => f (ρ s) x
  have hρmdiff : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ ρ := by
    rw [contMDiff_iff_contDiff]
    exact hρsmooth
  have hinner : ContMDiff (𝓘(Real, Real).prod I) (𝓘(Real, Real).prod I) ∞
      (fun p : Real × M => (ρ p.1, p.2)) :=
    (hρmdiff.comp contMDiff_fst).prodMk contMDiff_snd
  have hg'smooth (x₀ : M) (i j : Fin (Module.finrank Real E)) :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          chartGramMatrix (I := I) (g' p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    have hcomp := (hg x₀ i j).comp hinner.contMDiffOn (by
      intro p (hp : p ∈ Set.univ ×ˢ
        (trivializationAt E (TangentSpace I) x₀).baseSet)
      exact ⟨hρmem p.1, hp.2⟩)
    simpa only [Function.comp_apply, g'] using hcomp
  have hg'reg : MetricFamilyRegularAt (I := I) g' t := by
    refine
      { hasDerivAt_chartGramMatrix := ?_
        continuousOn_chartGramMatrix := ?_
        continuousOn_deriv_chartGramMatrix := ?_ }
    · intro x₀ i j x hx s
      have hp :
          (s, x) ∈ Set.univ ×ˢ
            (trivializationAt E (TangentSpace I) x₀).baseSet :=
        ⟨Set.mem_univ _, hx⟩
      have hopen : IsOpen
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
        (isOpen_univ : IsOpen (Set.univ : Set Real)).prod
          (trivializationAt E (TangentSpace I) x₀).open_baseSet
      have hAt :
          ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
            (fun p : Real × M =>
              chartGramMatrix (I := I) (g' p.1) x₀ p.2 i j) (s, x) :=
        ((hg'smooth x₀ i j) (s, x) hp).contMDiffAt (hopen.mem_nhds hp)
      have hslice : ContMDiffAt 𝓘(Real, Real) 𝓘(Real, Real) ∞
          (fun r : Real => chartGramMatrix (I := I) (g' r) x₀ x i j) s := by
        simpa only [Function.comp_apply] using
          hAt.comp s (contMDiffAt_id.prodMk contMDiffAt_const)
      have hdiff : DifferentiableAt Real
          (fun r : Real => chartGramMatrix (I := I) (g' r) x₀ x i j) s :=
        (contMDiffAt_iff_contDiffAt.mp hslice).differentiableAt (by simp)
      exact hdiff.hasDerivAt
    · intro x₀ i j
      exact (hg'smooth x₀ i j).continuousOn
    · intro x₀ i j p hp
      have hopen : IsOpen
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
        (isOpen_univ : IsOpen (Set.univ : Set Real)).prod
          (trivializationAt E (TangentSpace I) x₀).open_baseSet
      have hAt :
          ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
            (fun q : Real × M =>
              chartGramMatrix (I := I) (g' q.1) x₀ q.2 i j) p :=
        ((hg'smooth x₀ i j) p hp).contMDiffAt (hopen.mem_nhds hp)
      have hdAt :
          ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
            (fun q : Real × M =>
              deriv (fun s : Real =>
                chartGramMatrix (I := I) (g' s) x₀ q.2 i j) q.1) p :=
        DifferentialGeometry.timeDeriv_smoothAt hAt (by simp)
      exact hdAt.continuousAt.continuousWithinAt
  have hf'smooth : ContMDiff (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => f' p.1 p.2) := by
    exact hf.comp_contMDiff hinner
      (fun p => ⟨hρmem p.1, Set.mem_univ p.2⟩)
  let F' : C^∞⟮𝓘(Real, Real).prod I, Real × M; Real⟯ :=
    ⟨fun p : Real × M => f' p.1 p.2, hf'smooth⟩
  have hf'reg : FunctionRegularAt f' t := by
    refine
      { hasDerivAt_time := ?_
        continuous_joint := hf'smooth.continuous
        continuous_deriv_joint := ?_ }
    · intro x s
      have hslice : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞
          (fun r : Real => f' r x) := by
        exact hf'smooth.comp (contMDiff_id.prodMk contMDiff_const)
      have hdiff : DifferentiableAt Real (fun r : Real => f' r x) s := by
        rw [contMDiff_iff_contDiff] at hslice
        exact hslice.differentiable (by simp) s
      exact hdiff.hasDerivAt
    · exact (DifferentialGeometry.contMDiff_partial_deriv_fst I F').continuous
  have hvariation := first_variation_of_volume (I := I) (M := M) hg'reg hf'reg
  have hρt : ρ t = t := hρeq.eq_of_nhds
  have hgt : g' t = g_fam t := by
    simp only [g', hρt]
  have hderiv_eq (x : M) :
      deriv (fun s : Real => f' s x) t = deriv (fun s : Real => f s x) t := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hρeq] with s hs
    simp only [f', hs]
  have hmatrix (x : M) :
      (Matrix.of fun i j : Fin (Module.finrank Real E) =>
        deriv (fun s : Real => chartGramMatrix (I := I) (g' s) x x i j) t) =
      Matrix.of fun i j : Fin (Module.finrank Real E) =>
        deriv (fun s : Real => chartGramMatrix (I := I) (g_fam s) x x i j) t := by
    ext i j
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hρeq] with s hs
    simp only [g', hs]
  have htrace_eq (x : M) :
      traceTimeDerivMetric (I := I) g' t x =
        traceTimeDerivMetric (I := I) g_fam t x := by
    unfold traceTimeDerivMetric
    rw [hgt, hmatrix x]
  have hmeasure :
      riemannianMeasureFamily (I := I) (M := M) g' t =
        riemannianMeasureFamily (I := I) (M := M) g_fam t := by
    simp only [riemannianMeasureFamily_def, hgt]
  have hmass_eq :
      (fun s : Real =>
        ∫ x, f' s x ∂(riemannianMeasureFamily (I := I) (M := M) g' s)) =ᶠ[𝓝 t]
      (fun s : Real =>
        ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s)) := by
    filter_upwards [hρeq] with s hs
    simp only [f', g', riemannianMeasureFamily_def, hs]
  have hvalue :
      (∫ x, (deriv (fun s : Real => f' s x) t +
              (1 / 2) * traceTimeDerivMetric (I := I) g' t x * f' t x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g' t)) =
        ∫ x, (deriv (fun s : Real => f s x) t +
              (1 / 2) * traceTimeDerivMetric (I := I) g_fam t x * f t x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
    rw [hmeasure]
    apply integral_congr_ae
    filter_upwards with x
    rw [hderiv_eq x, htrace_eq x]
    simp only [f', hρt]
  exact (hvariation.congr_deriv hvalue).congr_of_eventuallyEq hmass_eq.symm

end DifferentialGeometry.Integral.Measure
