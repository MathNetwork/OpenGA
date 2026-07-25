import DifferentialGeometry.Analysis.Calculus.MapConvergence
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
set_option linter.style.longLine false






















namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology
open scoped ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]







theorem mapDerivNorm_fderivApply_le (r : ℕ) (v : E) {Φk Φinf : E → F} {x : E}
    (hk : ContDiff ℝ (∞ : WithTop ℕ∞) Φk) (hinf : ContDiff ℝ (∞ : WithTop ℕ∞) Φinf) :
    mapDerivNorm r (fun z => fderiv ℝ Φk z v) (fun z => fderiv ℝ Φinf z v) x
      ≤ ‖v‖ * mapDerivNorm (r + 1) Φk Φinf x := by
  have hfun : (fun z => fderiv ℝ Φk z v - fderiv ℝ Φinf z v)
      = (fun z => fderiv ℝ (fun y => Φk y - Φinf y) z v) := by
    funext z
    have hd : fderiv ℝ (fun y => Φk y - Φinf y) z = fderiv ℝ Φk z - fderiv ℝ Φinf z :=
      fderiv_sub (hk.differentiable (by simp)).differentiableAt
        (hinf.differentiable (by simp)).differentiableAt
    rw [hd, ContinuousLinearMap.sub_apply]
  rw [mapDerivNorm, hfun]
  set g : E → F := fun y => Φk y - Φinf y with hg
  have hgcd : ContDiff ℝ (∞ : WithTop ℕ∞) g := hk.sub hinf
  have hfd : ContDiffAt ℝ (r : WithTop ℕ∞) (fderiv ℝ g) x :=
    (hgcd.fderiv_right (m := (r : WithTop ℕ∞)) (by exact_mod_cast le_top)).contDiffAt
  calc ‖iteratedFDeriv ℝ r (fun z => fderiv ℝ g z v) x‖
      ≤ ‖v‖ * ‖iteratedFDeriv ℝ r (fderiv ℝ g) x‖ :=
        norm_iteratedFDeriv_clm_apply_const hfd le_rfl
    _ = ‖v‖ * ‖iteratedFDeriv ℝ (r + 1) g x‖ := by rw [norm_iteratedFDeriv_fderiv]
    _ = ‖v‖ * mapDerivNorm (r + 1) Φk Φinf x := by rw [mapDerivNorm, hg]





theorem MapCInfConvOnCompacts.fderivApply {U : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCInfConvOnCompacts U Φ Φinf)
    (hΦ : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (Φ k))
    (hΦinf : ContDiff ℝ (∞ : WithTop ℕ∞) Φinf) (v : E) :
    MapCInfConvOnCompacts U (fun k z => fderiv ℝ (Φ k) z v) (fun z => fderiv ℝ Φinf z v) := by
  intro K hK hKU p ε hε
  obtain ⟨k0, hk0⟩ := h K hK hKU (p + 1) (ε / (‖v‖ + 1)) (by positivity)
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  calc mapDerivNorm r (fun z => fderiv ℝ (Φ k) z v) (fun z => fderiv ℝ Φinf z v) x
      ≤ ‖v‖ * mapDerivNorm (r + 1) (Φ k) Φinf x :=
        mapDerivNorm_fderivApply_le r v (hΦ k) hΦinf
    _ ≤ ‖v‖ * (ε / (‖v‖ + 1)) := by
        gcongr
        exact hk0 k hk (r + 1) (by omega) x hx
    _ ≤ ε := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0:ℝ) < ‖v‖ + 1)]
        nlinarith [norm_nonneg v, hε.le]




theorem MapCInfConvOnCompacts.fderivOn {U : Set E} (hU : IsOpen U)
    {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCInfConvOnCompacts U Φ Φinf)
    (hΦ : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (Φ k) U)
    (hΦinf : ContDiffOn ℝ (∞ : WithTop ℕ∞) Φinf U) :
    MapCInfConvOnCompacts U
      (fun k x => fderiv ℝ (Φ k) x) (fun x => fderiv ℝ Φinf x) := by
  intro K hK hKU p ε hε
  obtain ⟨k0, hk0⟩ := h K hK hKU (p + 1) ε hε
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  let g : E → F := fun y => Φ k y - Φinf y
  have heq : (fun y => fderiv ℝ (Φ k) y - fderiv ℝ Φinf y) =ᶠ[nhds x]
      fun y => fderiv ℝ g y := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact (fderiv_sub
      (((hΦ k).differentiableOn (by simp)).differentiableAt
        (hU.mem_nhds hy))
      ((hΦinf.differentiableOn (by simp)).differentiableAt
        (hU.mem_nhds hy))).symm
  have hnorm :
      mapDerivNorm r (fun y => fderiv ℝ (Φ k) y)
          (fun y => fderiv ℝ Φinf y) x =
        mapDerivNorm (r + 1) (Φ k) Φinf x := by
    simp only [mapDerivNorm]
    rw [(heq.iteratedFDeriv ℝ r).eq_of_nhds]
    change ‖iteratedFDeriv ℝ r (fderiv ℝ g) x‖ =
      ‖iteratedFDeriv ℝ (r + 1) g x‖
    exact norm_iteratedFDeriv_fderiv
  rw [hnorm]
  exact hk0 k hk (r + 1) (by omega) x hx



theorem contDiff_clm_flip :
    ContDiff ℝ (∞ : WithTop ℕ∞) (ContinuousLinearMap.flip :
      (E →L[ℝ] F →L[ℝ] ℝ) → (F →L[ℝ] E →L[ℝ] ℝ)) := by
  let A := E →L[ℝ] F →L[ℝ] ℝ
  let B := F →L[ℝ] E →L[ℝ] ℝ
  letI : SeminormedAddCommGroup A := NormedAddCommGroup.toSeminormedAddCommGroup
  letI : NormedSpace ℝ A := inferInstance
  letI : SeminormedAddCommGroup B := NormedAddCommGroup.toSeminormedAddCommGroup
  letI : NormedSpace ℝ B := inferInstance
  let flipIso : A ≃ₗᵢ[ℝ] B := {
    toFun := ContinuousLinearMap.flip
    invFun := ContinuousLinearMap.flip
    map_add' := ContinuousLinearMap.flip_add
    map_smul' := ContinuousLinearMap.flip_smul
    left_inv := ContinuousLinearMap.flip_flip
    right_inv := ContinuousLinearMap.flip_flip
    norm_map' := ContinuousLinearMap.opNorm_flip }
  have h : ContDiff ℝ (∞ : WithTop ℕ∞) (flipIso : A → B) :=
    LinearIsometryEquiv.contDiff (𝕜 := ℝ) (n := ∞) flipIso
  simpa [A, B, flipIso] using h




noncomputable def pullbackForm
    (q : (F →L[ℝ] F →L[ℝ] ℝ) × (E →L[ℝ] F)) : E →L[ℝ] E →L[ℝ] ℝ :=
  q.1.bilinearComp q.2 q.2


@[simp]
theorem pullbackForm_apply (B : F →L[ℝ] F →L[ℝ] ℝ) (D : E →L[ℝ] F) (u v : E) :
    pullbackForm (B, D) u v = B (D u) (D v) :=
  rfl



theorem pullbackForm.contDiff :
    ContDiff ℝ (∞ : WithTop ℕ∞) (pullbackForm (E := E) (F := F)) := by
  unfold pullbackForm ContinuousLinearMap.bilinearComp
  have hcomp₁ : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun q : (F →L[ℝ] F →L[ℝ] ℝ) × (E →L[ℝ] F) => q.1.comp q.2) := by
    fun_prop
  have hflip₁ : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun q : (F →L[ℝ] F →L[ℝ] ℝ) × (E →L[ℝ] F) => (q.1.comp q.2).flip) :=
    contDiff_clm_flip.comp hcomp₁
  have hcomp₂ : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun q : (F →L[ℝ] F →L[ℝ] ℝ) × (E →L[ℝ] F) =>
        (q.1.comp q.2).flip.comp q.2) :=
    hflip₁.clm_comp contDiff_snd
  exact contDiff_clm_flip.comp hcomp₂



theorem MapCPConvOn.succ_of_fderiv {U K : Set E} {p : ℕ} (hU : IsOpen U)
    (hKU : K ⊆ U) {Φ : ℕ → E → F} {Φinf : E → F}
    (h0 : MapCPConvOn K 0 Φ Φinf)
    (hfd : MapCPConvOn K p
      (fun k x => fderiv ℝ (Φ k) x) (fun x => fderiv ℝ Φinf x))
    (hΦ : ∀ k, DifferentiableOn ℝ (Φ k) U)
    (hΦinf : DifferentiableOn ℝ Φinf U) :
    MapCPConvOn K (p + 1) Φ Φinf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h0 ε hε
  obtain ⟨k1, hk1⟩ := hfd ε hε
  refine ⟨max k0 k1, fun k hk r hr x hx => ?_⟩
  cases r with
  | zero =>
      exact hk0 k (le_trans (le_max_left _ _) hk) 0 le_rfl x hx
  | succ r =>
      have hxU : x ∈ U := hKU hx
      let g : E → F := fun y => Φ k y - Φinf y
      have heq : (fun y => fderiv ℝ (Φ k) y - fderiv ℝ Φinf y) =ᶠ[nhds x]
          fun y => fderiv ℝ g y := by
        filter_upwards [hU.mem_nhds hxU] with y hy
        exact (fderiv_sub
          ((hΦ k).differentiableAt (hU.mem_nhds hy))
          (hΦinf.differentiableAt (hU.mem_nhds hy))).symm
      have hnorm :
          mapDerivNorm r (fun y => fderiv ℝ (Φ k) y)
              (fun y => fderiv ℝ Φinf y) x =
            mapDerivNorm (r + 1) (Φ k) Φinf x := by
        simp only [mapDerivNorm]
        rw [(heq.iteratedFDeriv ℝ r).eq_of_nhds]
        change ‖iteratedFDeriv ℝ r (fderiv ℝ g) x‖ =
          ‖iteratedFDeriv ℝ (r + 1) g x‖
        exact norm_iteratedFDeriv_fderiv
      rw [← hnorm]
      exact hk1 k (le_trans (le_max_right _ _) hk) r (by omega) x hx




theorem MapCInfConvOnCompacts.add {U : Set E} {Φ Ψ : ℕ → E → F} {Φinf Ψinf : E → F}
    (hΦ : MapCInfConvOnCompacts U Φ Φinf) (hΨ : MapCInfConvOnCompacts U Ψ Ψinf)
    (hΦc : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (Φ k)) (hΦic : ContDiff ℝ (∞ : WithTop ℕ∞) Φinf)
    (hΨc : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (Ψ k)) (hΨic : ContDiff ℝ (∞ : WithTop ℕ∞) Ψinf) :
    MapCInfConvOnCompacts U (fun k z => Φ k z + Ψ k z) (fun z => Φinf z + Ψinf z) := by
  intro K hK hKU p ε hε
  obtain ⟨k1, hk1⟩ := hΦ K hK hKU p (ε / 2) (by positivity)
  obtain ⟨k2, hk2⟩ := hΨ K hK hKU p (ε / 2) (by positivity)
  refine ⟨max k1 k2, fun k hk r hr x hx => ?_⟩
  have hsplit : mapDerivNorm r (fun z => Φ k z + Ψ k z) (fun z => Φinf z + Ψinf z) x
      ≤ mapDerivNorm r (Φ k) Φinf x + mapDerivNorm r (Ψ k) Ψinf x := by
    have hfun : (fun y => (Φ k y + Ψ k y) - (Φinf y + Ψinf y))
        = (fun y => Φ k y - Φinf y) + (fun y => Ψ k y - Ψinf y) := by
      funext y
      change (Φ k y + Ψ k y) - (Φinf y + Ψinf y) = (Φ k y - Φinf y) + (Ψ k y - Ψinf y)
      abel
    have heq : mapDerivNorm r (fun z => Φ k z + Ψ k z) (fun z => Φinf z + Ψinf z) x
        = ‖iteratedFDeriv ℝ r ((fun y => Φ k y - Φinf y) + (fun y => Ψ k y - Ψinf y)) x‖ := by
      rw [show mapDerivNorm r (fun z => Φ k z + Ψ k z) (fun z => Φinf z + Ψinf z) x
          = ‖iteratedFDeriv ℝ r (fun y => (Φ k y + Ψ k y) - (Φinf y + Ψinf y)) x‖ from rfl, hfun]
    rw [heq, iteratedFDeriv_add_apply
      (((hΦc k).sub hΦic).contDiffAt.of_le (by exact_mod_cast le_top))
      (((hΨc k).sub hΨic).contDiffAt.of_le (by exact_mod_cast le_top))]
    exact norm_add_le _ _
  calc mapDerivNorm r (fun z => Φ k z + Ψ k z) (fun z => Φinf z + Ψinf z) x
      ≤ mapDerivNorm r (Φ k) Φinf x + mapDerivNorm r (Ψ k) Ψinf x := hsplit
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        · exact hk1 k (le_trans (le_max_left _ _) hk) r hr x hx
        · exact hk2 k (le_trans (le_max_right _ _) hk) r hr x hx
    _ = ε := by ring




theorem MapCInfConvOnCompacts.sub {U : Set E} {Φ Ψ : ℕ → E → F} {Φinf Ψinf : E → F}
    (hΦ : MapCInfConvOnCompacts U Φ Φinf) (hΨ : MapCInfConvOnCompacts U Ψ Ψinf)
    (hΦc : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (Φ k)) (hΦic : ContDiff ℝ (∞ : WithTop ℕ∞) Φinf)
    (hΨc : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (Ψ k)) (hΨic : ContDiff ℝ (∞ : WithTop ℕ∞) Ψinf) :
    MapCInfConvOnCompacts U (fun k z => Φ k z - Ψ k z) (fun z => Φinf z - Ψinf z) := by
  intro K hK hKU p ε hε
  obtain ⟨k1, hk1⟩ := hΦ K hK hKU p (ε / 2) (by positivity)
  obtain ⟨k2, hk2⟩ := hΨ K hK hKU p (ε / 2) (by positivity)
  refine ⟨max k1 k2, fun k hk r hr x hx => ?_⟩
  have hsplit : mapDerivNorm r (fun z => Φ k z - Ψ k z) (fun z => Φinf z - Ψinf z) x
      ≤ mapDerivNorm r (Φ k) Φinf x + mapDerivNorm r (Ψ k) Ψinf x := by
    have hfun : (fun y => (Φ k y - Ψ k y) - (Φinf y - Ψinf y))
        = (fun y => Φ k y - Φinf y) - (fun y => Ψ k y - Ψinf y) := by
      funext y
      change (Φ k y - Ψ k y) - (Φinf y - Ψinf y) = (Φ k y - Φinf y) - (Ψ k y - Ψinf y)
      abel
    have heq : mapDerivNorm r (fun z => Φ k z - Ψ k z) (fun z => Φinf z - Ψinf z) x
        = ‖iteratedFDeriv ℝ r ((fun y => Φ k y - Φinf y) - (fun y => Ψ k y - Ψinf y)) x‖ := by
      rw [show mapDerivNorm r (fun z => Φ k z - Ψ k z) (fun z => Φinf z - Ψinf z) x
          = ‖iteratedFDeriv ℝ r (fun y => (Φ k y - Ψ k y) - (Φinf y - Ψinf y)) x‖ from rfl, hfun]
    rw [heq, iteratedFDeriv_sub_apply
      (((hΦc k).sub hΦic).contDiffAt.of_le (by exact_mod_cast le_top))
      (((hΨc k).sub hΨic).contDiffAt.of_le (by exact_mod_cast le_top))]
    exact norm_sub_le _ _
  calc mapDerivNorm r (fun z => Φ k z - Ψ k z) (fun z => Φinf z - Ψinf z) x
      ≤ mapDerivNorm r (Φ k) Φinf x + mapDerivNorm r (Ψ k) Ψinf x := hsplit
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        · exact hk1 k (le_trans (le_max_left _ _) hk) r hr x hx
        · exact hk2 k (le_trans (le_max_right _ _) hk) r hr x hx
    _ = ε := by ring








theorem MapCInfConvOnCompacts.mulLeft {U : Set E} {Φ : ℕ → E → ℝ} {Φlim : E → ℝ}
    (h : MapCInfConvOnCompacts U Φ Φlim) {g : E → ℝ} (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (hΦc : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (Φ k)) (hΦic : ContDiff ℝ (∞ : WithTop ℕ∞) Φlim) :
    MapCInfConvOnCompacts U (fun k z => g z * Φ k z) (fun z => g z * Φlim z) := by
  intro K hK hKU p ε hε
  obtain ⟨Bg, hBg0, hBg⟩ : ∃ Bg : ℝ, 0 ≤ Bg ∧ ∀ i ≤ p, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i g x‖ ≤ Bg := by
    have hbd : ∀ i : ℕ, ∃ B : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i g x‖ ≤ B := by
      intro i
      obtain ⟨B, hB⟩ := hK.bddAbove_image
        (hg.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)).norm.continuousOn
      exact ⟨B, fun x hx => hB ⟨x, hx, rfl⟩⟩
    choose B hB using hbd
    refine ⟨∑ i ∈ Finset.range (p + 1), |B i|, Finset.sum_nonneg (fun _ _ => abs_nonneg _),
      fun i hi x hx => ?_⟩
    calc ‖iteratedFDeriv ℝ i g x‖ ≤ B i := hB i x hx
      _ ≤ |B i| := le_abs_self _
      _ ≤ ∑ j ∈ Finset.range (p + 1), |B j| :=
          Finset.single_le_sum (f := fun j => |B j|) (fun j _ => abs_nonneg (B j))
            (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  obtain ⟨k0, hk0⟩ := h K hK hKU p (ε / (2 ^ p * Bg + 1)) (by positivity)
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  have hle : mapDerivNorm r (fun z => g z * Φ k z) (fun z => g z * Φlim z) x
      ≤ ∑ i ∈ Finset.range (r + 1),
        (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i g x‖ * mapDerivNorm (r - i) (Φ k) Φlim x := by
    have hfun : (fun y => g y * Φ k y - g y * Φlim y) = (fun y => g y * (Φ k y - Φlim y)) := by
      funext y; ring
    have hfeq : mapDerivNorm r (fun z => g z * Φ k z) (fun z => g z * Φlim z) x
        = ‖iteratedFDeriv ℝ r (fun y => g y * (Φ k y - Φlim y)) x‖ := by
      rw [show mapDerivNorm r (fun z => g z * Φ k z) (fun z => g z * Φlim z) x
          = ‖iteratedFDeriv ℝ r (fun y => g y * Φ k y - g y * Φlim y) x‖ from rfl, hfun]
    rw [hfeq]
    exact norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := g) (g := fun y => Φ k y - Φlim y)
      hg ((hΦc k).sub hΦic) x (by exact_mod_cast le_top)
  refine hle.trans ?_
  have hstep : ∀ i ∈ Finset.range (r + 1),
      (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i g x‖ * mapDerivNorm (r - i) (Φ k) Φlim x
        ≤ (r.choose i : ℝ) * (Bg * (ε / (2 ^ p * Bg + 1))) := by
    intro i hi
    have hi' : i ≤ p := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hr
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul (hBg i hi' x hx) (hk0 k hk (r - i) (by omega) x hx)
      (mapDerivNorm_nonneg _ _ _ _) hBg0
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_mul,
    (by exact_mod_cast Nat.sum_range_choose r :
      (∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ)) = 2 ^ r)]
  have hD : (0:ℝ) < 2 ^ p * Bg + 1 := by positivity
  have h2r : (2:ℝ) ^ r ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hr
  rw [show (2:ℝ) ^ r * (Bg * (ε / (2 ^ p * Bg + 1)))
      = 2 ^ r * Bg * ε / (2 ^ p * Bg + 1) from by ring, div_le_iff₀ hD]
  nlinarith [mul_nonneg (mul_nonneg hε.le (sub_nonneg.mpr h2r)) hBg0, hε.le]





theorem MapCInfConvOnCompacts.sum {ι : Type*} {U : Set E} (s : Finset ι)
    {Φ : ι → ℕ → E → F} {Φinf : ι → E → F}
    (h : ∀ i, MapCInfConvOnCompacts U (Φ i) (Φinf i))
    (hc : ∀ i k, ContDiff ℝ (∞ : WithTop ℕ∞) (Φ i k))
    (hic : ∀ i, ContDiff ℝ (∞ : WithTop ℕ∞) (Φinf i)) :
    MapCInfConvOnCompacts U (fun k z => ∑ i ∈ s, Φ i k z) (fun z => ∑ i ∈ s, Φinf i z) := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro K hK hKU p ε hε
    refine ⟨0, fun k _ r _ x _ => ?_⟩
    simp only [Finset.sum_empty, mapDerivNorm, sub_self, iteratedFDeriv_fun_zero,
      Pi.zero_apply, norm_zero]
    exact hε.le
  | insert a t hat ih =>
    rw [show (fun k z => ∑ i ∈ insert a t, Φ i k z)
          = (fun k z => Φ a k z + ∑ i ∈ t, Φ i k z) from by
            funext k z; rw [Finset.sum_insert hat],
      show (fun z => ∑ i ∈ insert a t, Φinf i z)
          = (fun z => Φinf a z + ∑ i ∈ t, Φinf i z) from by
            funext z; rw [Finset.sum_insert hat]]
    exact MapCInfConvOnCompacts.add (h a) ih (fun k => hc a k) (hic a)
      (fun k => ContDiff.sum (fun i _ => hc i k)) (ContDiff.sum (fun i _ => hic i))



theorem MapCPConvOn.congr {U K : Set E} {p : ℕ}
    {Φ Φ' : ℕ → E → F} {Φinf Φ'inf : E → F}
    (h : MapCPConvOn K p Φ Φinf) (hU : IsOpen U) (hKU : K ⊆ U)
    (hΦ : ∀ k, Set.EqOn (Φ' k) (Φ k) U) (hΦinf : Set.EqOn Φ'inf Φinf U) :
    MapCPConvOn K p Φ' Φ'inf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have heq : (fun y => Φ' k y - Φ'inf y) =ᶠ[nhds x] (fun y => Φ k y - Φinf y) := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    rw [hΦ k hy, hΦinf hy]
  have hval : mapDerivNorm r (Φ' k) Φ'inf x = mapDerivNorm r (Φ k) Φinf x := by
    simp only [mapDerivNorm]
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ heq r).eq_of_nhds]
  rw [hval]
  exact hk0 k hk r hr x hx




theorem MapCInfConvOnCompacts.congr {U : Set E} {Φ Φ' : ℕ → E → F} {Φinf Φ'inf : E → F}
    (h : MapCInfConvOnCompacts U Φ Φinf) (hU : IsOpen U)
    (hΦ : ∀ k, Set.EqOn (Φ' k) (Φ k) U) (hΦinf : Set.EqOn Φ'inf Φinf U) :
    MapCInfConvOnCompacts U Φ' Φ'inf := by
  intro K hK hKU p
  exact (h K hK hKU p).congr hU hKU hΦ hΦinf





theorem MapCInfConvOnCompacts.congr_eventually
    {U : Set E} {Φ Φ' : ℕ → E → F} {Φinf Φ'inf : E → F}
    (h : MapCInfConvOnCompacts U Φ Φinf) (hU : IsOpen U)
    (hΦ : ∀ᶠ k in Filter.atTop, Set.EqOn (Φ' k) (Φ k) U)
    (hΦinf : Set.EqOn Φ'inf Φinf U) :
    MapCInfConvOnCompacts U Φ' Φ'inf := by
  intro K hK hKU p ε hε
  obtain ⟨k0, hk0⟩ := h K hK hKU p ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hΦ
  refine ⟨max k0 N, fun k hk r hr x hx => ?_⟩
  have hk0k : k0 ≤ k := (Nat.le_max_left k0 N).trans hk
  have hNk : N ≤ k := (Nat.le_max_right k0 N).trans hk
  have hxU : x ∈ U := hKU hx
  have heq : (fun y => Φ' k y - Φ'inf y) =ᶠ[nhds x]
      (fun y => Φ k y - Φinf y) := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    rw [hN k hNk hy, hΦinf hy]
  have hval : mapDerivNorm r (Φ' k) Φ'inf x = mapDerivNorm r (Φ k) Φinf x := by
    simp only [mapDerivNorm]
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ heq r).eq_of_nhds]
  rw [hval]
  exact hk0 k hk0k r hr x hx

end HCGCompactness
end DifferentialGeometry
