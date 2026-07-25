import DifferentialGeometry.Analysis.Calculus.TimeJetMatch
import DifferentialGeometry.Analysis.Calculus.TimeJetCommute

















noncomputable section

open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


def jet2 {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] (g : E → F') (w : E) :
    F' × (E →L[ℝ] F') × (E →L[ℝ] (E →L[ℝ] F')) :=
  (g w, fderiv ℝ g w, fderiv ℝ (fun y => fderiv ℝ g y) w)






theorem curveJet_match
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {sL sR : Set ℝ} {V : Set E}
    (hsL : UniqueDiffOn ℝ sL) (haccL : sL ⊆ closure (interior sL)) (h0L : (0 : ℝ) ∈ sL)
    (hsR : UniqueDiffOn ℝ sR) (haccR : sR ⊆ closure (interior sR)) (h0R : (0 : ℝ) ∈ sR)
    (hV : IsOpen V)
    {GL GR : ℝ → E → F'}
    (hGL : ContDiffOn ℝ ∞ (Function.uncurry GL) (sL ×ˢ V))
    (hGR : ContDiffOn ℝ ∞ (Function.uncurry GR) (sR ×ˢ V))
    (b : ℕ) {w : E} (hw : w ∈ V)
    (hcurveL : ContDiffWithinAt ℝ ∞ (fun t => jet2 (GL t) w) sL 0)
    (hcurveR : ContDiffWithinAt ℝ ∞ (fun t => jet2 (GR t) w) sR 0)
    (hval : ∀ u ∈ V, iteratedDerivWithin b (fun s => GL s u) sL 0
      = iteratedDerivWithin b (fun s => GR s u) sR 0) :
    iteratedDerivWithin b (fun t => jet2 (GL t) w) sL 0
      = iteratedDerivWithin b (fun t => jet2 (GR t) w) sR 0 := by
  have hbinf : (b : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

  have heqf : (fun u => iteratedDerivWithin b (fun s => GL s u) sL 0)
      =ᶠ[nhds w] (fun u => iteratedDerivWithin b (fun s => GR s u) sR 0) :=
    Filter.eventuallyEq_of_mem (hV.mem_nhds hw) (fun u hu => hval u hu)
  simp only [jet2] at hcurveL hcurveR ⊢
  rw [iteratedDerivWithin_prodMk (hcurveL.of_le hbinf).fst (hcurveL.of_le hbinf).snd hsL h0L,
    iteratedDerivWithin_prodMk (hcurveR.of_le hbinf).fst (hcurveR.of_le hbinf).snd hsR h0R]
  refine Prod.ext (hval w hw) ?_
  rw [iteratedDerivWithin_prodMk (hcurveL.of_le hbinf).snd.fst (hcurveL.of_le hbinf).snd.snd hsL h0L,
    iteratedDerivWithin_prodMk (hcurveR.of_le hbinf).snd.fst (hcurveR.of_le hbinf).snd.snd hsR h0R]
  refine Prod.ext ?_ ?_
  ·
    rw [← fderiv_iteratedDerivWithin_time_comm hsL haccL hV b h0L hw hGL,
      ← fderiv_iteratedDerivWithin_time_comm hsR haccR hV b h0R hw hGR]
    exact heqf.fderiv_eq
  ·

    have hKL := spatialFDeriv_contDiffOn hsL hV hGL
    have hKR := spatialFDeriv_contDiffOn hsR hV hGR
    rw [← fderiv_iteratedDerivWithin_time_comm hsL haccL hV b h0L hw hKL,
      ← fderiv_iteratedDerivWithin_time_comm hsR haccR hV b h0R hw hKR]
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hV.mem_nhds hw] with y hy
    rw [← fderiv_iteratedDerivWithin_time_comm hsL haccL hV b h0L hy hGL,
      ← fderiv_iteratedDerivWithin_time_comm hsR haccR hV b h0R hy hGR]
    exact (Filter.eventuallyEq_of_mem (hV.mem_nhds hy) (fun u hu => hval u hu)).fderiv_eq








theorem jetMatch_of_evolution
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {sL sR : Set ℝ} {V : Set E}
    (hsL : UniqueDiffOn ℝ sL) (haccL : sL ⊆ closure (interior sL)) (h0L : (0 : ℝ) ∈ sL)
    (hsR : UniqueDiffOn ℝ sR) (haccR : sR ⊆ closure (interior sR)) (h0R : (0 : ℝ) ∈ sR)
    (hV : IsOpen V)
    {GL GR : ℝ → E → F'}
    (hGL : ContDiffOn ℝ ∞ (Function.uncurry GL) (sL ×ˢ V))
    (hGR : ContDiffOn ℝ ∞ (Function.uncurry GR) (sR ×ˢ V))
    {Φ : F' × (E →L[ℝ] F') × (E →L[ℝ] (E →L[ℝ] F')) → F'}
    (hΦ : ∀ w ∈ V, ContDiffAt ℝ ∞ Φ (jet2 (GL 0) w))
    (hcurveL : ∀ w ∈ V, ContDiffWithinAt ℝ ∞ (fun t => jet2 (GL t) w) sL 0)
    (hcurveR : ∀ w ∈ V, ContDiffWithinAt ℝ ∞ (fun t => jet2 (GR t) w) sR 0)
    (hevolL : ∀ t ∈ sL, ∀ w ∈ V,
      derivWithin (fun s => GL s w) sL t = Φ (jet2 (GL t) w))
    (hevolR : ∀ t ∈ sR, ∀ w ∈ V,
      derivWithin (fun s => GR s w) sR t = Φ (jet2 (GR t) w))
    (hbdry : Set.EqOn (GL 0) (GR 0) V) :
    ∀ (n : ℕ), ∀ w ∈ V,
      iteratedDerivWithin n (fun s => GL s w) sL 0 = iteratedDerivWithin n (fun s => GR s w) sR 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw
    match n with
    | 0 => simpa only [iteratedDerivWithin_zero] using hbdry hw
    | k + 1 =>
      have hkinf : (k : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
      have hrwL : iteratedDerivWithin (k + 1) (fun s => GL s w) sL 0
          = iteratedDerivWithin k (fun t => Φ (jet2 (GL t) w)) sL 0 := by
        rw [iteratedDerivWithin_succ']
        exact iteratedDerivWithin_congr (fun t ht => hevolL t ht w hw) h0L
      have hrwR : iteratedDerivWithin (k + 1) (fun s => GR s w) sR 0
          = iteratedDerivWithin k (fun t => Φ (jet2 (GR t) w)) sR 0 := by
        rw [iteratedDerivWithin_succ']
        exact iteratedDerivWithin_congr (fun t ht => hevolR t ht w hw) h0R
      rw [hrwL, hrwR]
      exact iteratedDerivWithin_comp_jet_eq ((hΦ w hw).of_le hkinf)
        ((hcurveL w hw).of_le hkinf) ((hcurveR w hw).of_le hkinf) hsL hsR h0L h0R
        (fun b hb => curveJet_match hsL haccL h0L hsR haccR h0R hV hGL hGR b hw
          (hcurveL w hw) (hcurveR w hw) (fun u hu => ih b (by omega) u hu)) (le_refl k)

end Analysis
end DifferentialGeometry

end
