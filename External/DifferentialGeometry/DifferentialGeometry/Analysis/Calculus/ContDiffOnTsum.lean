import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed

open Set Filter Topology

namespace DifferentialGeometry

namespace Analysis

section FDeriv

variable {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem tsum_compl_diff_le {f : α → E → F} {f' : α → E → E →L[ℝ] F} {u : α → ℝ}
    {s : Set E} (hf : ∀ (i : α) (z : E), z ∈ s → HasFDerivWithinAt (f i) (f' i z) s z)
    (hf' : ∀ (i : α) (z : E), z ∈ s → ‖f' i z‖ ≤ u i) (hu : Summable u) (hs : Convex ℝ s)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    (hsf : ∀ z ∈ s, Summable fun i => f i z) (t : Finset α) :
    ‖(∑' i : {i // i ∉ t}, f (i : α) y) - ∑' i : {i // i ∉ t}, f (i : α) x‖
      ≤ (∑' i : {i // i ∉ t}, u (i : α)) * ‖y - x‖ := by
  classical
  set C := ∑' i : {i // i ∉ t}, u (i : α) with hC
  have husub : Summable fun i : {i // i ∉ t} => u (i : α) := hu.subtype _
  have hunn : ∀ i : {i // i ∉ t}, 0 ≤ u (i : α) := fun i =>
    le_trans (norm_nonneg _) (hf' (i : α) x hx)
  have hsy : Summable fun i : {i // i ∉ t} => f (i : α) y := (hsf y hy).subtype _
  have hsx : Summable fun i : {i // i ∉ t} => f (i : α) x := (hsf x hx).subtype _
  have hbound_r : ∀ r : Finset {i // i ∉ t},
      ‖(∑ i ∈ r, f (i : α) y) - ∑ i ∈ r, f (i : α) x‖ ≤ C * ‖y - x‖ := by
    intro r
    have hD : ∀ z ∈ s, HasFDerivWithinAt (fun w => ∑ i ∈ r, f (i : α) w)
        (∑ i ∈ r, f' (i : α) z) s z := fun z hz =>
      HasFDerivWithinAt.fun_sum fun i _ => hf (i : α) z hz
    have hb : ∀ z ∈ s, ‖∑ i ∈ r, f' (i : α) z‖ ≤ C := by
      intro z hz
      calc ‖∑ i ∈ r, f' (i : α) z‖
          ≤ ∑ i ∈ r, ‖f' (i : α) z‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ r, u (i : α) := Finset.sum_le_sum fun i _ => hf' (i : α) z hz
        _ ≤ C := sum_le_hasSum r (fun i _ => hunn i) husub.hasSum
    exact hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hD hb hx hy
  have hlim : Tendsto (fun r : Finset {i // i ∉ t} =>
      ‖(∑ i ∈ r, f (i : α) y) - ∑ i ∈ r, f (i : α) x‖) atTop
      (𝓝 ‖(∑' i : {i // i ∉ t}, f (i : α) y) - ∑' i : {i // i ∉ t}, f (i : α) x‖) := by
    have h1 := hsy.hasSum
    have h2 := hsx.hasSum
    simp only [HasSum, SummationFilter.unconditional_filter] at h1 h2
    exact (h1.sub h2).norm
  exact le_of_tendsto hlim (Eventually.of_forall hbound_r)

private theorem norm_tsum_compl_fderiv_le {f' : α → E → E →L[ℝ] F} {u : α → ℝ} {s : Set E}
    {x : E} (hx : x ∈ s) (hf' : ∀ (i : α) (z : E), z ∈ s → ‖f' i z‖ ≤ u i) (hu : Summable u)
    (t : Finset α) :
    ‖(∑' i, f' i x) - ∑ i ∈ t, f' i x‖ ≤ ∑' i : {i // i ∉ t}, u (i : α) := by
  classical
  have hsumm : Summable fun i : {i // i ∉ t} => ‖f' (i : α) x‖ :=
    (hu.subtype _).of_nonneg_of_le (fun _ => norm_nonneg _) fun i => hf' (i : α) x hx
  have hfsumm : Summable fun i => f' i x := Summable.of_norm_bounded hu fun i => hf' i x hx
  have htail : (∑' i, f' i x) - ∑ i ∈ t, f' i x = ∑' i : {i // i ∉ t}, f' (i : α) x := by
    rw [eq_comm, eq_sub_iff_add_eq, add_comm]; exact hfsumm.sum_add_tsum_subtype_compl t
  rw [htail]
  calc ‖∑' i : {i // i ∉ t}, f' (i : α) x‖
      ≤ ∑' i : {i // i ∉ t}, ‖f' (i : α) x‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' i : {i // i ∉ t}, u (i : α) :=
        hsumm.tsum_le_tsum (fun i => hf' (i : α) x hx) (hu.subtype _)

theorem summable_of_summable_hasFDerivWithinAt {f : α → E → F} {f' : α → E → E →L[ℝ] F}
    {u : α → ℝ} {s : Set E} (hf : ∀ (i : α) (z : E), z ∈ s → HasFDerivWithinAt (f i) (f' i z) s z)
    (hf' : ∀ (i : α) (z : E), z ∈ s → ‖f' i z‖ ≤ u i) (hu : Summable u) (hs : Convex ℝ s)
    {x₀ : E} (hx₀ : x₀ ∈ s) (hf0 : Summable fun i => f i x₀) {y : E} (hy : y ∈ s) :
    Summable fun i => f i y := by
  have key : Summable fun i => f i y - f i x₀ := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
      (hu.mul_right ‖y - x₀‖))
    intro i
    have hD : ∀ z ∈ s, HasFDerivWithinAt (fun w => f i w) (f' i z) s z := fun z hz => hf i z hz
    have hb : ∀ z ∈ s, ‖f' i z‖ ≤ u i := fun z hz => hf' i z hz
    have := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hD hb hx₀ hy
    simpa using this
  have heq : (fun i => f i y) = fun i => (f i y - f i x₀) + f i x₀ := by ext i; abel
  rw [heq]; exact key.add hf0

theorem hasFDerivWithinAt_tsum {f : α → E → F} {f' : α → E → E →L[ℝ] F} {u : α → ℝ} {s : Set E}
    (hf : ∀ (i : α) (z : E), z ∈ s → HasFDerivWithinAt (f i) (f' i z) s z)
    (hf' : ∀ (i : α) (z : E), z ∈ s → ‖f' i z‖ ≤ u i) (hu : Summable u) (hs : Convex ℝ s)
    {x₀ : E} (hx₀ : x₀ ∈ s) (hf0 : Summable fun i => f i x₀) {x : E} (hx : x ∈ s) :
    HasFDerivWithinAt (fun y => ∑' i, f i y) (∑' i, f' i x) s x := by
  classical
  have hsf : ∀ z ∈ s, Summable fun i => f i z := fun z hz =>
    summable_of_summable_hasFDerivWithinAt hf hf' hu hs hx₀ hf0 hz
  rw [hasFDerivWithinAt_iff_tendsto, Metric.tendsto_nhds]
  intro ε hε
  have htail0 : Tendsto (fun t : Finset α => ∑' i : {i // i ∉ t}, u (i : α)) atTop (𝓝 0) :=
    tendsto_tsum_compl_atTop_zero u
  obtain ⟨t, ht⟩ := (htail0.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 3 by positivity))).exists
  set δ := ∑' i : {i // i ∉ t}, u (i : α) with hδ
  have hδlt : δ < ε / 3 := ht
  have hδnn : 0 ≤ δ := tsum_nonneg fun i => le_trans (norm_nonneg _) (hf' (i : α) x hx)
  have hSt : HasFDerivWithinAt (fun y => ∑ i ∈ t, f i y) (∑ i ∈ t, f' i x) s x :=
    HasFDerivWithinAt.fun_sum fun i _ => hf (i : α) x hx
  rw [hasFDerivWithinAt_iff_tendsto, Metric.tendsto_nhds] at hSt
  have hSt' := hSt (ε / 3) (by positivity)
  filter_upwards [hSt', self_mem_nhdsWithin] with y hyT2 hys
  simp only [dist_zero_right, Real.norm_eq_abs] at hyT2 ⊢
  rw [abs_of_nonneg (by positivity)]
  rw [abs_of_nonneg (by positivity)] at hyT2
  set g := fun y => ∑' i, f i y with hg
  set G := ∑' i, f' i x with hGdef
  set St := fun y => ∑ i ∈ t, f i y with hSt_def
  set St' := ∑ i ∈ t, f' i x with hSt'_def
  rw [show (∑ i ∈ t, f i y) = St y from rfl, show (∑ i ∈ t, f i x) = St x from rfl] at hyT2
  have hsplit : g y - g x - G (y - x)
      = (g y - St y - (g x - St x)) + (St y - St x - St' (y - x))
        + (St' - G) (y - x) := by
    simp only [hGdef, hSt'_def, ContinuousLinearMap.sub_apply]; abel
  have hT1 : ‖g y - St y - (g x - St x)‖ ≤ δ * ‖y - x‖ := by
    have hsy : (g y - St y) = ∑' i : {i // i ∉ t}, f (i : α) y := by
      rw [hg, hSt_def, eq_comm, eq_sub_iff_add_eq, add_comm]
      exact (hsf y hys).sum_add_tsum_subtype_compl t
    have hsx : (g x - St x) = ∑' i : {i // i ∉ t}, f (i : α) x := by
      rw [hg, hSt_def, eq_comm, eq_sub_iff_add_eq, add_comm]
      exact (hsf x hx).sum_add_tsum_subtype_compl t
    rw [hsy, hsx, hδ]
    exact tsum_compl_diff_le hf hf' hu hs hx hys hsf t
  have hT3 : ‖(St' - G) (y - x)‖ ≤ δ * ‖y - x‖ := by
    calc ‖(St' - G) (y - x)‖ ≤ ‖St' - G‖ * ‖y - x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ δ * ‖y - x‖ := by
          gcongr
          rw [show St' - G = -(G - St') by abel, norm_neg]
          rw [hGdef, hSt'_def, hδ]
          exact norm_tsum_compl_fderiv_le hx hf' hu t
  rcases eq_or_ne y x with rfl | hyne
  · simp [hε]
  · have hpos : 0 < ‖y - x‖ := by rw [norm_pos_iff]; exact sub_ne_zero.mpr hyne
    rw [hsplit]
    calc ‖y - x‖⁻¹ *
          ‖g y - St y - (g x - St x) + (St y - St x - St' (y - x)) + (St' - G) (y - x)‖
        ≤ ‖y - x‖⁻¹ * (‖g y - St y - (g x - St x)‖ + ‖St y - St x - St' (y - x)‖
            + ‖(St' - G) (y - x)‖) := by
          gcongr
          exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ = ‖y - x‖⁻¹ * ‖g y - St y - (g x - St x)‖
            + ‖y - x‖⁻¹ * ‖St y - St x - St' (y - x)‖
            + ‖y - x‖⁻¹ * ‖(St' - G) (y - x)‖ := by ring
      _ < ε / 3 + ε / 3 + ε / 3 := by
          have e1 : ‖y - x‖⁻¹ * ‖g y - St y - (g x - St x)‖ < ε / 3 := by
            calc ‖y - x‖⁻¹ * ‖g y - St y - (g x - St x)‖
                ≤ ‖y - x‖⁻¹ * (δ * ‖y - x‖) := by gcongr
              _ = δ := by field_simp
              _ < ε / 3 := hδlt
          have e3 : ‖y - x‖⁻¹ * ‖(St' - G) (y - x)‖ < ε / 3 := by
            calc ‖y - x‖⁻¹ * ‖(St' - G) (y - x)‖
                ≤ ‖y - x‖⁻¹ * (δ * ‖y - x‖) := by gcongr
              _ = δ := by field_simp
              _ < ε / 3 := hδlt
          gcongr
      _ = ε := by ring

theorem fderivWithin_tsum {f : α → E → F} {u : α → ℝ} {s : Set E} (hs : UniqueDiffOn ℝ s)
    (hconv : Convex ℝ s) (hf : ∀ i, DifferentiableOn ℝ (f i) s)
    (hf' : ∀ (i : α) (x : E), x ∈ s → ‖fderivWithin ℝ (f i) s x‖ ≤ u i) (hu : Summable u)
    {x₀ : E} (hx₀ : x₀ ∈ s) (hf0 : Summable fun i => f i x₀) {x : E} (hx : x ∈ s) :
    fderivWithin ℝ (fun y => ∑' n, f n y) s x = ∑' n, fderivWithin ℝ (f n) s x :=
  (hasFDerivWithinAt_tsum (fun i z hz => (hf i z hz).hasFDerivWithinAt) hf' hu hconv hx₀ hf0
    hx).fderivWithin (hs x hx)

end FDeriv

section ContDiffOn

variable {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem iteratedFDerivWithin_tsum {f : α → E → F} {v : ℕ → α → ℝ} {s : Set E} {N : ℕ∞}
    (hs : UniqueDiffOn ℝ s) (hconv : Convex ℝ s) (hf : ∀ i, ContDiffOn ℝ N (f i) s)
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α) (x : E), x ∈ s → (k : ℕ∞) ≤ N →
      ‖iteratedFDerivWithin ℝ k (f i) s x‖ ≤ v k i)
    {x₀ : E} (hx₀ : x₀ ∈ s) {k : ℕ} (hk : (k : ℕ∞) ≤ N) {x : E} (hx : x ∈ s) :
    iteratedFDerivWithin ℝ k (fun y => ∑' n, f n y) s x
      = ∑' n, iteratedFDerivWithin ℝ k (f n) s x := by
  induction k generalizing x with
  | zero =>
    simp_rw [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum
  | succ k IH =>
    have h'k : (k : ℕ∞) < N := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self k) hk
    have hIH : EqOn (iteratedFDerivWithin ℝ k (fun y => ∑' n, f n y) s)
        (fun y => ∑' n, iteratedFDerivWithin ℝ k (f n) s y) s := fun y hy => IH h'k.le hy
    have hsumm_k : ∀ y ∈ s, Summable fun n => iteratedFDerivWithin ℝ k (f n) s y := fun y hy =>
      Summable.of_norm_bounded (hv k h'k.le) fun n => h'f k n y hy h'k.le
    have hdiff : ∀ n, DifferentiableOn ℝ (iteratedFDerivWithin ℝ k (f n) s) s := fun n =>
      (hf n).differentiableOn_iteratedFDerivWithin (mod_cast h'k) hs
    have hbnd : ∀ (n : α) (y : E), y ∈ s →
        ‖fderivWithin ℝ (iteratedFDerivWithin ℝ k (f n) s) s y‖ ≤ v (k + 1) n := by
      intro n y hy
      rw [norm_fderivWithin_iteratedFDerivWithin]
      exact h'f (k + 1) n y hy hk
    have hfd : fderivWithin ℝ (fun y => ∑' n, iteratedFDerivWithin ℝ k (f n) s y) s x
        = ∑' n, fderivWithin ℝ (iteratedFDerivWithin ℝ k (f n) s) s x :=
      fderivWithin_tsum hs hconv hdiff hbnd (hv (k + 1) hk) hx₀ (hsumm_k x₀ hx₀) hx
    rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply]
    rw [fderivWithin_congr' hIH hx]
    rw [hfd]
    have hsucc : (fun n => iteratedFDerivWithin ℝ (k + 1) (f n) s x)
        = fun n => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm
            (fderivWithin ℝ (iteratedFDerivWithin ℝ k (f n) s) s x) := by
      ext1 n; rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply]
    rw [hsucc]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E)
      F).symm.toContinuousLinearEquiv.map_tsum

theorem iteratedFDerivWithin_tsum_apply {f : α → E → F} {v : ℕ → α → ℝ} {s : Set E} {N : ℕ∞}
    (hs : UniqueDiffOn ℝ s) (hconv : Convex ℝ s) (hf : ∀ i, ContDiffOn ℝ N (f i) s)
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α) (x : E), x ∈ s → (k : ℕ∞) ≤ N →
      ‖iteratedFDerivWithin ℝ k (f i) s x‖ ≤ v k i)
    {x₀ : E} (hx₀ : x₀ ∈ s) {k : ℕ} (hk : (k : ℕ∞) ≤ N) {x : E} (hx : x ∈ s) :
    iteratedFDerivWithin ℝ k (fun y => ∑' n, f n y) s x
      = ∑' n, iteratedFDerivWithin ℝ k (f n) s x :=
  iteratedFDerivWithin_tsum hs hconv hf hv h'f hx₀ hk hx

theorem contDiffOn_tsum {f : α → E → F} {v : ℕ → α → ℝ} {s : Set E} {N : ℕ∞}
    (hs : UniqueDiffOn ℝ s) (hconv : Convex ℝ s) (hf : ∀ i, ContDiffOn ℝ N (f i) s)
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α) (x : E), x ∈ s → (k : ℕ∞) ≤ N →
      ‖iteratedFDerivWithin ℝ k (f i) s x‖ ≤ v k i)
    {x₀ : E} (hx₀ : x₀ ∈ s) :
    ContDiffOn ℝ N (fun x => ∑' i, f i x) s := by
  rw [contDiffOn_iff_continuousOn_differentiableOn hs]
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · have hm' : (m : ℕ∞) ≤ N := by exact_mod_cast hm
    have hcont : ContinuousOn (fun x => ∑' n, iteratedFDerivWithin ℝ m (f n) s x) s := by
      refine continuousOn_tsum (fun i => ?_) (hv m hm') fun n x hx => h'f m n x hx hm'
      exact (hf i).continuousOn_iteratedFDerivWithin (by exact_mod_cast hm') hs
    exact hcont.congr fun x hx => iteratedFDerivWithin_tsum hs hconv hf hv h'f hx₀ hm' hx
  · have hm' : (m : ℕ∞) < N := by exact_mod_cast hm
    have hdiff : ∀ n, DifferentiableOn ℝ (iteratedFDerivWithin ℝ m (f n) s) s := fun n =>
      (hf n).differentiableOn_iteratedFDerivWithin (by exact_mod_cast hm') hs
    have hk1 : ((m + 1 : ℕ) : ℕ∞) ≤ N := by exact_mod_cast Order.add_one_le_of_lt hm'
    have hbnd : ∀ (n : α) (y : E), y ∈ s →
        ‖fderivWithin ℝ (iteratedFDerivWithin ℝ m (f n) s) s y‖ ≤ v (m + 1) n := by
      intro n y hy; rw [norm_fderivWithin_iteratedFDerivWithin]; exact h'f (m + 1) n y hy hk1
    have hsumm0 : Summable fun n => iteratedFDerivWithin ℝ m (f n) s x₀ :=
      Summable.of_norm_bounded (hv m hm'.le) fun n => h'f m n x₀ hx₀ hm'.le
    have hdtsum : DifferentiableOn ℝ (fun x => ∑' n, iteratedFDerivWithin ℝ m (f n) s x) s :=
      fun x hx => (hasFDerivWithinAt_tsum (fun i z hz => (hdiff i z hz).hasFDerivWithinAt) hbnd
        (hv (m + 1) hk1) hconv hx₀ hsumm0 hx).differentiableWithinAt
    exact hdtsum.congr fun x hx => iteratedFDerivWithin_tsum hs hconv hf hv h'f hx₀ hm'.le hx

end ContDiffOn

section Icc

theorem contDiffOn_tsum_Icc {α F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : α → ℝ → F} {v : ℕ → α → ℝ} {a b : ℝ} {N : ℕ∞} (hab : a < b)
    (hf : ∀ i, ContDiffOn ℝ N (f i) (Set.Icc a b))
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α) (x : ℝ), x ∈ Set.Icc a b → (k : ℕ∞) ≤ N →
      ‖iteratedFDerivWithin ℝ k (f i) (Set.Icc a b) x‖ ≤ v k i) :
    ContDiffOn ℝ N (fun x => ∑' i, f i x) (Set.Icc a b) :=
  contDiffOn_tsum (uniqueDiffOn_Icc hab) (convex_Icc a b) hf hv h'f
    (left_mem_Icc.mpr hab.le)

open Nat in

theorem contDiffOn_Icc_tsum_pow_div_factorial :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => ∑' n : ℕ, t ^ n / n !) (Set.Icc (0 : ℝ) 1) := by
  set v : ℕ → ℕ → ℝ := fun k n => (n.descFactorial k : ℝ) / n ! with hv_def
  have hsumm_v : ∀ k : ℕ, (k : ℕ∞) ≤ ⊤ → Summable (v k) := by
    intro k _
    simp only [hv_def]
    rw [← summable_nat_add_iff k]
    have hone : Summable fun n : ℕ => (1 : ℝ) / n ! := by
      simpa using Real.summable_pow_div_factorial (1 : ℝ)
    refine hone.congr fun n => ?_
    symm
    have hle : k ≤ n + k := Nat.le_add_left k n
    have hid : (n + k).descFactorial k * n ! = (n + k)! := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      have hch := Nat.choose_mul_factorial_mul_factorial hle
      rw [Nat.add_sub_cancel] at hch
      calc k ! * (n + k).choose k * n ! = (n + k).choose k * k ! * n ! := by ring
        _ = (n + k)! := hch
    have hpos : (0 : ℝ) < (n + k).descFactorial k := by
      exact_mod_cast Nat.descFactorial_pos.mpr hle
    rw [← hid]; push_cast; field_simp
  have hf : ∀ n : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => t ^ n / n !) (Set.Icc (0 : ℝ) 1) :=
    fun n => ((contDiff_id.pow n).div_const _).contDiffOn
  have h'f : ∀ (k n : ℕ) (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 → (k : ℕ∞) ≤ ⊤ →
      ‖iteratedFDerivWithin ℝ k (fun t : ℝ => t ^ n / n !) (Set.Icc (0 : ℝ) 1) x‖ ≤ v k n := by
    intro k n x hx _
    obtain ⟨hx0, hx1⟩ := hx
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    have hud : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
    have hxmem : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx0, hx1⟩
    have hdc : iteratedDerivWithin k (fun t : ℝ => t ^ n / (n ! : ℝ)) (Set.Icc (0 : ℝ) 1) x
        = iteratedDerivWithin k (fun t : ℝ => t ^ n) (Set.Icc (0 : ℝ) 1) x / n ! := by
      simp_rw [div_eq_mul_inv]; rw [iteratedDerivWithin_mul_const_field]
    rw [hdc, iteratedDerivWithin_pow hxmem hud]
    simp only [hv_def]
    rw [norm_div, norm_mul]
    have hnorm1 : ‖(n.descFactorial k : ℝ)‖ = (n.descFactorial k : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hnorm2 : ‖(n ! : ℝ)‖ = (n ! : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnorm1, hnorm2]
    have hnum : (n.descFactorial k : ℝ) * ‖x ^ (n - k)‖ ≤ (n.descFactorial k : ℝ) :=
      calc (n.descFactorial k : ℝ) * ‖x ^ (n - k)‖
          ≤ (n.descFactorial k : ℝ) * 1 := by
            gcongr
            rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg hx0]
            exact pow_le_one₀ hx0 hx1
        _ = (n.descFactorial k : ℝ) := by ring
    gcongr
  exact contDiffOn_tsum_Icc (by norm_num) hf hsumm_v h'f

end Icc

end Analysis

end DifferentialGeometry
