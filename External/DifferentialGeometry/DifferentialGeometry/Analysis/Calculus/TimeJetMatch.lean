import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno























noncomputable section

open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis




theorem iteratedDerivWithin_clm_comp {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : A →L[ℝ] B) {f : ℝ → A} {s : Set ℝ} {x : ℝ} {n : ℕ}
    (hf : ContDiffWithinAt ℝ n f s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    iteratedDerivWithin n (fun t => L (f t)) s x = L (iteratedDerivWithin n f s x) := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin,
    show (fun t => L (f t)) = ⇑L ∘ f from rfl, L.iteratedFDerivWithin_comp_left hf hs hx le_rfl]
  rfl


theorem iteratedDerivWithin_prodMk {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {f : ℝ → A} {g : ℝ → B} {s : Set ℝ} {x : ℝ} {n : ℕ}
    (hf : ContDiffWithinAt ℝ n f s x) (hg : ContDiffWithinAt ℝ n g s x)
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    iteratedDerivWithin n (fun t => (f t, g t)) s x
      = (iteratedDerivWithin n f s x, iteratedDerivWithin n g s x) :=
  Prod.ext
    (iteratedDerivWithin_clm_comp (ContinuousLinearMap.fst ℝ A B) (hf.prodMk hg) hs hx).symm
    (iteratedDerivWithin_clm_comp (ContinuousLinearMap.snd ℝ A B) (hf.prodMk hg) hs hx).symm

variable {J F' : Type*}
    [NormedAddCommGroup J] [NormedSpace ℝ J] [NormedAddCommGroup F'] [NormedSpace ℝ F']





theorem iteratedDeriv_comp_jet_eq {Φ : J → F'} {uL uR : ℝ → J} {n : ℕ}
    (hΦ : ContDiffAt ℝ n Φ (uL 0)) (huL : ContDiffAt ℝ n uL 0) (huR : ContDiffAt ℝ n uR 0)
    (hjet : ∀ a, a ≤ n → iteratedDeriv a uL 0 = iteratedDeriv a uR 0)
    {i : ℕ} (hi : i ≤ n) :
    iteratedDeriv i (Φ ∘ uL) 0 = iteratedDeriv i (Φ ∘ uR) 0 := by
  have hp : uL 0 = uR 0 := by
    have h := hjet 0 (Nat.zero_le n)
    rwa [iteratedDeriv_zero, iteratedDeriv_zero] at h
  have hΦR : ContDiffAt ℝ n Φ (uR 0) := hp ▸ hΦ
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hΦ huL (by exact_mod_cast hi),
    iteratedDeriv_vcomp_eq_sum_orderedFinpartition hΦR huR (by exact_mod_cast hi)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have htuple : (fun j => iteratedDeriv (c.partSize j) uL 0)
      = (fun j => iteratedDeriv (c.partSize j) uR 0) :=
    funext fun j => hjet (c.partSize j) (le_trans (c.partSize_le j) hi)
  rw [hp, htuple]











theorem iteratedDerivWithin_comp_jet_eq {Φ : J → F'} {uL uR : ℝ → J} {sL sR : Set ℝ} {n : ℕ}
    (hΦ : ContDiffAt ℝ n Φ (uL 0))
    (huL : ContDiffWithinAt ℝ n uL sL 0) (huR : ContDiffWithinAt ℝ n uR sR 0)
    (hsL : UniqueDiffOn ℝ sL) (hsR : UniqueDiffOn ℝ sR)
    (h0L : (0 : ℝ) ∈ sL) (h0R : (0 : ℝ) ∈ sR)
    (hjet : ∀ a, a ≤ n → iteratedDerivWithin a uL sL 0 = iteratedDerivWithin a uR sR 0)
    {i : ℕ} (hi : i ≤ n) :
    iteratedDerivWithin i (Φ ∘ uL) sL 0 = iteratedDerivWithin i (Φ ∘ uR) sR 0 := by
  have hp : uL 0 = uR 0 := by
    have h := hjet 0 (Nat.zero_le n)
    rwa [iteratedDerivWithin_zero, iteratedDerivWithin_zero] at h
  have hΦL : ContDiffWithinAt ℝ n Φ Set.univ (uL 0) := hΦ.contDiffWithinAt
  have hΦR : ContDiffWithinAt ℝ n Φ Set.univ (uR 0) := (hp ▸ hΦ).contDiffWithinAt
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hΦL huL uniqueDiffOn_univ hsL h0L
        (Set.mapsTo_univ _ _) (by exact_mod_cast hi),
    iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hΦR huR uniqueDiffOn_univ hsR h0R
        (Set.mapsTo_univ _ _) (by exact_mod_cast hi)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have htuple : (fun j => iteratedDerivWithin (c.partSize j) uL sL 0)
      = (fun j => iteratedDerivWithin (c.partSize j) uR sR 0) :=
    funext fun j => hjet (c.partSize j) (le_trans (c.partSize_le j) hi)
  rw [hp, htuple]

end Analysis
end DifferentialGeometry

end
