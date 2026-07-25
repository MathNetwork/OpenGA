import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry

namespace Analysis

section PdIter

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

private lemma inftyW_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 :=
  WithTop.coe_ne_zero.mpr ENat.top_ne_zero

noncomputable def dirDeriv (v : X) (u : X → ℝ) : X → ℝ := fun y => fderiv ℝ u y v

noncomputable def iteratedDirDeriv : List X → (X → ℝ) → X → ℝ
  | [], u => u
  | v :: L, u => iteratedDirDeriv L (dirDeriv v u)

@[simp] lemma pdIter_nil (u : X → ℝ) : iteratedDirDeriv ([] : List X) u = u := rfl

@[simp] lemma pdIter_cons (v : X) (L : List X) (u : X → ℝ) :
    iteratedDirDeriv (v :: L) u = iteratedDirDeriv L (dirDeriv v u) := rfl

lemma pdDir_congrOn {V : Set X} (hV : IsOpen V) {u₁ u₂ : X → ℝ}
    (h : Set.EqOn u₁ u₂ V) (v : X) : Set.EqOn (dirDeriv v u₁) (dirDeriv v u₂) V := by
  intro y hy
  have hev : u₁ =ᶠ[nhds y] u₂ :=
    Filter.eventuallyEq_of_mem (hV.mem_nhds hy) h
  unfold dirDeriv
  rw [hev.fderiv_eq]

lemma pdIter_congrOn {V : Set X} (hV : IsOpen V) {u₁ u₂ : X → ℝ}
    (h : Set.EqOn u₁ u₂ V) (L : List X) :
    Set.EqOn (iteratedDirDeriv L u₁) (iteratedDirDeriv L u₂) V := by
  induction L generalizing u₁ u₂ with
  | nil => exact h
  | cons v L ih => exact ih (pdDir_congrOn hV h v)

lemma pdDir_contDiffOn {V : Set X} (hV : IsOpen V) {u : X → ℝ}
    (hu : ContDiffOn ℝ ∞ u V) (v : X) : ContDiffOn ℝ ∞ (dirDeriv v u) V := by
  have hfd : ContDiffOn ℝ ∞ (fun y => fderiv ℝ u y) V :=
    hu.fderiv_of_isOpen hV (by exact_mod_cast le_top)
  exact hfd.clm_apply contDiffOn_const

lemma pdIter_contDiffOn {V : Set X} (hV : IsOpen V) {u : X → ℝ}
    (hu : ContDiffOn ℝ ∞ u V) (L : List X) : ContDiffOn ℝ ∞ (iteratedDirDeriv L u) V := by
  induction L generalizing u with
  | nil => exact hu
  | cons v L ih => exact ih (pdDir_contDiffOn hV hu v)

lemma differentiableAt_of_contDiffOn_isOpen {V : Set X} (hV : IsOpen V) {u : X → ℝ}
    (hu : ContDiffOn ℝ ∞ u V) {y : X} (hy : y ∈ V) : DifferentiableAt ℝ u y := by
  have hdo : DifferentiableOn ℝ u V := hu.differentiableOn inftyW_ne_zero
  exact (hdo y hy).differentiableAt (hV.mem_nhds hy)

lemma pdDir_add_eqOn {V : Set X} (hV : IsOpen V) {u₁ u₂ : X → ℝ}
    (hu₁ : ContDiffOn ℝ ∞ u₁ V) (hu₂ : ContDiffOn ℝ ∞ u₂ V) (v : X) :
    Set.EqOn (dirDeriv v (fun y => u₁ y + u₂ y))
      (fun y => dirDeriv v u₁ y + dirDeriv v u₂ y) V := by
  intro y hy
  unfold dirDeriv
  rw [fderiv_fun_add (differentiableAt_of_contDiffOn_isOpen hV hu₁ hy)
    (differentiableAt_of_contDiffOn_isOpen hV hu₂ hy)]
  rfl

lemma pdIter_add_eqOn {V : Set X} (hV : IsOpen V) {u₁ u₂ : X → ℝ}
    (hu₁ : ContDiffOn ℝ ∞ u₁ V) (hu₂ : ContDiffOn ℝ ∞ u₂ V) (L : List X) :
    Set.EqOn (iteratedDirDeriv L (fun y => u₁ y + u₂ y))
      (fun y => iteratedDirDeriv L u₁ y + iteratedDirDeriv L u₂ y) V := by
  induction L generalizing u₁ u₂ with
  | nil => intro y _; rfl
  | cons v L ih =>
      intro y hy
      have h1 : iteratedDirDeriv (v :: L) (fun y => u₁ y + u₂ y) y
          = iteratedDirDeriv L (dirDeriv v (fun y => u₁ y + u₂ y)) y := rfl
      have h2 := pdIter_congrOn hV (pdDir_add_eqOn hV hu₁ hu₂ v) L hy
      rw [h1, h2]
      exact ih (pdDir_contDiffOn hV hu₁ v) (pdDir_contDiffOn hV hu₂ v) hy

lemma pdDir_const (v : X) (c : ℝ) : dirDeriv v (fun _ => c) = fun _ => (0 : ℝ) := by
  funext y
  unfold dirDeriv
  rw [fderiv_fun_const]
  rfl

lemma pdIter_zero_fun (L : List X) :
    iteratedDirDeriv L (fun _ => (0 : ℝ)) = fun _ => (0 : ℝ) := by
  induction L with
  | nil => rfl
  | cons v L ih =>
      rw [pdIter_cons, pdDir_const]
      exact ih

lemma pdIter_const_of_ne_nil (c : ℝ) {L : List X} (hL : L ≠ []) :
    iteratedDirDeriv L (fun _ => c) = fun _ => (0 : ℝ) := by
  rcases L with - | ⟨v, L'⟩
  · exact absurd rfl hL
  · rw [pdIter_cons, pdDir_const]
    exact pdIter_zero_fun L'

lemma pdDir_smul_eqOn {V : Set X} (hV : IsOpen V) {u : X → ℝ}
    (hu : ContDiffOn ℝ ∞ u V) (c : ℝ) (v : X) :
    Set.EqOn (dirDeriv v (fun y => c * u y)) (fun y => c * dirDeriv v u y) V := by
  intro y hy
  unfold dirDeriv
  rw [fderiv_const_mul (differentiableAt_of_contDiffOn_isOpen hV hu hy) c]
  rfl

lemma pdIter_smul_eqOn {V : Set X} (hV : IsOpen V) {u : X → ℝ}
    (hu : ContDiffOn ℝ ∞ u V) (c : ℝ) (L : List X) :
    Set.EqOn (iteratedDirDeriv L (fun y => c * u y)) (fun y => c * iteratedDirDeriv L u y) V := by
  induction L generalizing u with
  | nil => intro y _; rfl
  | cons v L ih =>
      intro y hy
      have h2 := pdIter_congrOn hV (pdDir_smul_eqOn hV hu c v) L hy
      rw [pdIter_cons, h2]
      exact ih (pdDir_contDiffOn hV hu v) hy

lemma pdDir_mul_eqOn {V : Set X} (hV : IsOpen V) {u₁ u₂ : X → ℝ}
    (hu₁ : ContDiffOn ℝ ∞ u₁ V) (hu₂ : ContDiffOn ℝ ∞ u₂ V) (v : X) :
    Set.EqOn (dirDeriv v (fun y => u₁ y * u₂ y))
      (fun y => dirDeriv v u₁ y * u₂ y + u₁ y * dirDeriv v u₂ y) V := by
  intro y hy
  unfold dirDeriv
  rw [fderiv_fun_mul (differentiableAt_of_contDiffOn_isOpen hV hu₁ hy)
    (differentiableAt_of_contDiffOn_isOpen hV hu₂ hy)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma pdDir_inv_eqOn {V : Set X} (hV : IsOpen V) {u : X → ℝ}
    (hu : ContDiffOn ℝ ∞ u V) (hne : ∀ y ∈ V, u y ≠ 0) (v : X) :
    Set.EqOn (dirDeriv v (fun y => (u y)⁻¹))
      (fun y => -(u y ^ 2)⁻¹ * dirDeriv v u y) V := by
  intro y hy
  have hdu : HasFDerivAt u (fderiv ℝ u y) y :=
    (differentiableAt_of_contDiffOn_isOpen hV hu hy).hasFDerivAt
  have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-(u y ^ 2)⁻¹) (u y) :=
    hasDerivAt_inv (hne y hy)
  have hcomp : HasFDerivAt (fun z => (u z)⁻¹) ((-(u y ^ 2)⁻¹) • fderiv ℝ u y) y :=
    hinv.comp_hasFDerivAt y hdu
  unfold dirDeriv
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

end PdIter

section PdIterBounds

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma norm_iteratedFDerivWithin_pdDir_le {O : Set X} (hO : IsOpen O) {u : X → ℝ}
    (hu : ContDiffOn ℝ ∞ u O) (v : X) {y : X} (hy : y ∈ O) (n : ℕ) :
    ‖iteratedFDerivWithin ℝ n (dirDeriv v u) O y‖ ≤
      ‖v‖ * ‖iteratedFDerivWithin ℝ (n + 1) u O y‖ := by
  have hUD : UniqueDiffOn ℝ O := hO.uniqueDiffOn
  set A : (X →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v with hA_def
  have hA_norm : ‖A‖ ≤ ‖v‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) (fun f => ?_)
    rw [hA_def]
    calc ‖ContinuousLinearMap.apply ℝ ℝ v f‖ = ‖f v‖ := rfl
      _ ≤ ‖f‖ * ‖v‖ := f.le_opNorm v
      _ = ‖v‖ * ‖f‖ := by ring
  have heq : Set.EqOn (dirDeriv v u) (A ∘ (fun z => fderivWithin ℝ u O z)) O := by
    intro z hz
    unfold dirDeriv
    rw [Function.comp_apply, ← fderivWithin_of_isOpen hO hz]
    rfl
  have hfd : ContDiffOn ℝ ∞ (fun z => fderivWithin ℝ u O z) O :=
    hu.fderivWithin hUD (by exact_mod_cast le_top)
  calc ‖iteratedFDerivWithin ℝ n (dirDeriv v u) O y‖
      = ‖iteratedFDerivWithin ℝ n (A ∘ (fun z => fderivWithin ℝ u O z)) O y‖ := by
        rw [iteratedFDerivWithin_congr heq hy]
    _ ≤ ‖A‖ * ‖iteratedFDerivWithin ℝ n (fun z => fderivWithin ℝ u O z) O y‖ :=
        A.norm_iteratedFDerivWithin_comp_left (hfd y hy) hUD hy
          (by exact_mod_cast le_top)
    _ ≤ ‖v‖ * ‖iteratedFDerivWithin ℝ n (fun z => fderivWithin ℝ u O z) O y‖ :=
        mul_le_mul_of_nonneg_right hA_norm (norm_nonneg _)
    _ = ‖v‖ * ‖iteratedFDerivWithin ℝ (n + 1) u O y‖ := by
        rw [norm_iteratedFDerivWithin_fderivWithin hUD hy]

lemma norm_iteratedFDerivWithin_pdIter_le {O : Set X} (hO : IsOpen O) {u : X → ℝ}
    (hu : ContDiffOn ℝ ∞ u O) (L : List X) {y : X} (hy : y ∈ O) (n : ℕ) :
    ‖iteratedFDerivWithin ℝ n (iteratedDirDeriv L u) O y‖ ≤
      (L.map (fun v => ‖v‖)).prod * ‖iteratedFDerivWithin ℝ (n + L.length) u O y‖ := by
  induction L generalizing u n with
  | nil =>
      simp only [pdIter_nil, List.map_nil, List.prod_nil, one_mul, List.length_nil,
        Nat.add_zero]
      exact le_refl _
  | cons v L ih =>
      have h1 := ih (pdDir_contDiffOn hO hu v) n
      have h2 := norm_iteratedFDerivWithin_pdDir_le hO hu v hy (n + L.length)
      have hnn : (0 : ℝ) ≤ (L.map (fun w => ‖w‖)).prod :=
        List.prod_nonneg (by
          intro a ha
          simp only [List.mem_map] at ha
          obtain ⟨w, _, hw⟩ := ha
          rw [← hw]; exact norm_nonneg w)
      have h3 : ‖iteratedFDerivWithin ℝ n (iteratedDirDeriv (v :: L) u) O y‖ ≤
          (L.map (fun w => ‖w‖)).prod *
            (‖v‖ * ‖iteratedFDerivWithin ℝ (n + L.length + 1) u O y‖) :=
        le_trans h1 (mul_le_mul_of_nonneg_left h2 hnn)
      have h4 : ((v :: L).map (fun w => ‖w‖)).prod
          = ‖v‖ * (L.map (fun w => ‖w‖)).prod := by
        simp [List.prod_cons]
      have h5 : n + (v :: L).length = n + L.length + 1 := by
        simp [List.length_cons]
        omega
      refine le_trans h3 (le_of_eq ?_)
      rw [h4, h5]
      ring

@[simp] noncomputable def pdVec : (L : List X) → Fin L.length → X
  | [] => fun i => i.elim0
  | v :: L => Fin.snoc (pdVec L) v

lemma pdIter_eq_iteratedFDerivWithin_apply {O : Set X} (hO : IsOpen O) {u : X → ℝ}
    (hu : ContDiffOn ℝ ∞ u O) (L : List X) {y : X} (hy : y ∈ O) :
    iteratedDirDeriv L u y = iteratedFDerivWithin ℝ L.length u O y (pdVec L) := by
  have hUD : UniqueDiffOn ℝ O := hO.uniqueDiffOn
  induction L generalizing u with
  | nil => exact (iteratedFDerivWithin_zero_apply _).symm
  | cons v L ih =>
      have heq : Set.EqOn (dirDeriv v u)
          ((ContinuousLinearMap.apply ℝ ℝ v) ∘ (fun z => fderivWithin ℝ u O z)) O := by
        intro z hz
        unfold dirDeriv
        rw [Function.comp_apply, ← fderivWithin_of_isOpen hO hz]
        rfl
      have hfd : ContDiffOn ℝ ∞ (fun z => fderivWithin ℝ u O z) O :=
        hu.fderivWithin hUD (by exact_mod_cast le_top)
      have h2 := ih (pdDir_contDiffOn hO hu v)
      have h3 : iteratedFDerivWithin ℝ L.length (dirDeriv v u) O y
          = (ContinuousLinearMap.apply ℝ ℝ v).compContinuousMultilinearMap
              (iteratedFDerivWithin ℝ L.length (fun z => fderivWithin ℝ u O z) O y) := by
        rw [iteratedFDerivWithin_congr heq hy]
        exact (ContinuousLinearMap.apply ℝ ℝ v).iteratedFDerivWithin_comp_left
          (hfd y hy) hUD hy (by exact_mod_cast le_top)
      have h4 := iteratedFDerivWithin_succ_apply_right (𝕜 := ℝ) (f := u)
        (s := O) hUD hy (Fin.snoc (pdVec L) v : Fin (L.length + 1) → X)
      calc iteratedDirDeriv (v :: L) u y = iteratedDirDeriv L (dirDeriv v u) y := rfl
        _ = iteratedFDerivWithin ℝ L.length (dirDeriv v u) O y (pdVec L) := h2
        _ = (iteratedFDerivWithin ℝ L.length (fun z => fderivWithin ℝ u O z) O y
              (pdVec L)) v := by rw [h3]; rfl
        _ = iteratedFDerivWithin ℝ (L.length + 1) u O y (Fin.snoc (pdVec L) v) := by
              rw [h4]
              simp only [Fin.init_snoc, Fin.snoc_last]
        _ = iteratedFDerivWithin ℝ ((v :: L).length) u O y (pdVec (v :: L)) := rfl

end PdIterBounds

section AnisotropicJointContDiffOn

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def AnisotropicJointContDiffOn (k : ℕ) (T : ℝ) (V : Set X) (W : ℝ → X → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiffOn ℝ ∞ (W t) V) ∧
  (∀ L : List X, ContDiffOn ℝ (k : ℕ)
    (fun q : ℝ × X => iteratedDirDeriv L (W q.1) q.2) (Set.Icc (0 : ℝ) T ×ˢ V))

lemma AnisotropicJointContDiffOn.slice {k : ℕ} {T : ℝ} {V : Set X} {W : ℝ → X → ℝ}
    (h : AnisotropicJointContDiffOn k T V W) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ContDiffOn ℝ ∞ (W t) V := h.1 t ht

lemma AnisotropicJointContDiffOn.clause {k : ℕ} {T : ℝ} {V : Set X} {W : ℝ → X → ℝ}
    (h : AnisotropicJointContDiffOn k T V W) (L : List X) :
    ContDiffOn ℝ (k : ℕ) (fun q : ℝ × X => iteratedDirDeriv L (W q.1) q.2)
      (Set.Icc (0 : ℝ) T ×ˢ V) := h.2 L

lemma AnisotropicJointContDiffOn.joint {k : ℕ} {T : ℝ} {V : Set X} {W : ℝ → X → ℝ}
    (h : AnisotropicJointContDiffOn k T V W) :
    ContDiffOn ℝ (k : ℕ) (fun q : ℝ × X => W q.1 q.2)
      (Set.Icc (0 : ℝ) T ×ˢ V) := h.2 []

lemma AnisotropicJointContDiffOn.congr {k : ℕ} {T : ℝ} {V : Set X} (hV : IsOpen V)
    {W₁ : ℝ → X → ℝ} (W₂ : ℝ → X → ℝ) (h : AnisotropicJointContDiffOn k T V W₁)
    (heq : ∀ t ∈ Set.Icc (0 : ℝ) T, Set.EqOn (W₁ t) (W₂ t) V) :
    AnisotropicJointContDiffOn k T V W₂ := by
  refine ⟨fun t ht => (h.1 t ht).congr (fun y hy => (heq t ht hy).symm), fun L => ?_⟩
  refine (h.2 L).congr ?_
  rintro ⟨t, y⟩ ⟨ht, hy⟩
  exact (pdIter_congrOn hV (heq t ht) L hy).symm

lemma AnisotropicJointContDiffOn.mono {k : ℕ} {T : ℝ} {V V' : Set X} {W : ℝ → X → ℝ}
    (h : AnisotropicJointContDiffOn k T V W) (hsub : V' ⊆ V) : AnisotropicJointContDiffOn k T V' W :=
  ⟨fun t ht => (h.1 t ht).mono hsub,
   fun L => (h.2 L).mono (Set.prod_mono (le_refl _) hsub)⟩

lemma AnisotropicJointContDiffOn.pdShift {k : ℕ} {T : ℝ} {V : Set X} (hV : IsOpen V)
    {W : ℝ → X → ℝ} (h : AnisotropicJointContDiffOn k T V W) (v : X) :
    AnisotropicJointContDiffOn k T V (fun t => dirDeriv v (W t)) :=
  ⟨fun t ht => pdDir_contDiffOn hV (h.1 t ht) v, fun L => h.2 (v :: L)⟩

lemma anisoOn_const {k : ℕ} {T : ℝ} {V : Set X} (c : ℝ) :
    AnisotropicJointContDiffOn k T V (fun _ _ => c) := by
  refine ⟨fun t _ => contDiffOn_const, fun L => ?_⟩
  rcases L with - | ⟨v, L'⟩
  · exact contDiffOn_const
  · have hz : iteratedDirDeriv (v :: L') (fun _ => c) = fun _ => (0 : ℝ) :=
      pdIter_const_of_ne_nil c (by simp)
    simp only [hz]
    exact contDiffOn_const

lemma anisoOn_timeIndep {k : ℕ} {T : ℝ} {V : Set X} (hV : IsOpen V)
    {u : X → ℝ} (hu : ContDiffOn ℝ ∞ u V) :
    AnisotropicJointContDiffOn k T V (fun _ => u) := by
  refine ⟨fun t _ => hu, fun L => ?_⟩
  have hL : ContDiffOn ℝ ∞ (iteratedDirDeriv L u) V := pdIter_contDiffOn hV hu L
  exact (hL.of_le (by exact_mod_cast le_top)).comp contDiffOn_snd
    (fun q hq => hq.2)

lemma AnisotropicJointContDiffOn.add {k : ℕ} {T : ℝ} {V : Set X} (hV : IsOpen V)
    {W₁ W₂ : ℝ → X → ℝ} (h₁ : AnisotropicJointContDiffOn k T V W₁) (h₂ : AnisotropicJointContDiffOn k T V W₂) :
    AnisotropicJointContDiffOn k T V (fun t y => W₁ t y + W₂ t y) := by
  refine ⟨fun t ht => (h₁.1 t ht).add (h₂.1 t ht), fun L => ?_⟩
  refine ((h₁.2 L).add (h₂.2 L)).congr ?_
  rintro ⟨t, y⟩ ⟨ht, hy⟩
  exact pdIter_add_eqOn hV (h₁.1 t ht) (h₂.1 t ht) L hy

lemma AnisotropicJointContDiffOn.smul {k : ℕ} {T : ℝ} {V : Set X} (hV : IsOpen V)
    {W : ℝ → X → ℝ} (h : AnisotropicJointContDiffOn k T V W) (c : ℝ) :
    AnisotropicJointContDiffOn k T V (fun t y => c * W t y) := by
  refine ⟨fun t ht => contDiffOn_const.mul (h.1 t ht), fun L => ?_⟩
  refine ((contDiffOn_const (c := c)).mul (h.2 L)).congr ?_
  rintro ⟨t, y⟩ ⟨ht, hy⟩
  exact pdIter_smul_eqOn hV (h.1 t ht) c L hy

lemma AnisotropicJointContDiffOn.neg {k : ℕ} {T : ℝ} {V : Set X} (hV : IsOpen V)
    {W : ℝ → X → ℝ} (h : AnisotropicJointContDiffOn k T V W) :
    AnisotropicJointContDiffOn k T V (fun t y => -W t y) := by
  refine (h.smul hV (-1)).congr hV (fun t y => -W t y) (fun t ht z hz => by ring)

lemma AnisotropicJointContDiffOn.sub {k : ℕ} {T : ℝ} {V : Set X} (hV : IsOpen V)
    {W₁ W₂ : ℝ → X → ℝ} (h₁ : AnisotropicJointContDiffOn k T V W₁) (h₂ : AnisotropicJointContDiffOn k T V W₂) :
    AnisotropicJointContDiffOn k T V (fun t y => W₁ t y - W₂ t y) := by
  refine ((h₁.add hV (h₂.neg hV)).congr hV (fun t y => W₁ t y - W₂ t y)
    (fun t ht z hz => by ring))

lemma anisoOn_finsetSum {k : ℕ} {T : ℝ} {V : Set X} (hV : IsOpen V)
    {ι : Type*} (s : Finset ι) {W : ι → ℝ → X → ℝ}
    (h : ∀ i ∈ s, AnisotropicJointContDiffOn k T V (W i)) :
    AnisotropicJointContDiffOn k T V (fun t y => ∑ i ∈ s, W i t y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact (anisoOn_const 0).congr hV (fun t y => ∑ i ∈ (∅ : Finset ι), W i t y)
        (fun t _ y _ => by simp)
  | insert a s ha ih =>
      have hWa := h a (Finset.mem_insert_self a s)
      have hs := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      refine (hWa.add hV hs).congr hV _ (fun t _ y _ => ?_)
      rw [Finset.sum_insert ha]

private lemma anisoOn_mul_clause_graded {k : ℕ} {T : ℝ} {V : Set X} (hV : IsOpen V) :
    ∀ (m : ℕ) (L : List X), L.length ≤ m → ∀ (W₁ W₂ : ℝ → X → ℝ),
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiffOn ℝ ∞ (W₁ t) V) →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiffOn ℝ ∞ (W₂ t) V) →
      (∀ L₁ : List X, L₁.length ≤ m → ContDiffOn ℝ (k : ℕ)
        (fun q : ℝ × X => iteratedDirDeriv L₁ (W₁ q.1) q.2) (Set.Icc (0 : ℝ) T ×ˢ V)) →
      (∀ L₂ : List X, L₂.length ≤ m → ContDiffOn ℝ (k : ℕ)
        (fun q : ℝ × X => iteratedDirDeriv L₂ (W₂ q.1) q.2) (Set.Icc (0 : ℝ) T ×ˢ V)) →
      ContDiffOn ℝ (k : ℕ)
        (fun q : ℝ × X => iteratedDirDeriv L (fun y => W₁ q.1 y * W₂ q.1 y) q.2)
        (Set.Icc (0 : ℝ) T ×ˢ V) := by
  intro m
  induction m with
  | zero =>
      intro L hL W₁ W₂ hs₁ hs₂ hc₁ hc₂
      have hLnil : L = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hL)
      subst hLnil
      exact (hc₁ [] (le_refl _)).mul (hc₂ [] (le_refl _))
  | succ m ih =>
      intro L hL W₁ W₂ hs₁ hs₂ hc₁ hc₂
      rcases L with - | ⟨v, L'⟩
      · exact (hc₁ [] (Nat.zero_le _)).mul (hc₂ [] (Nat.zero_le _))
      · have hL' : L'.length ≤ m := by
          have hlen : L'.length + 1 ≤ m + 1 := by simpa using hL
          omega
        have hA := ih L' hL' (fun t => dirDeriv v (W₁ t)) W₂
          (fun t ht => pdDir_contDiffOn hV (hs₁ t ht) v) hs₂
          (fun L₁ hlen => hc₁ (v :: L₁) (by simpa using Nat.succ_le_succ hlen))
          (fun L₂ hlen => hc₂ L₂ (Nat.le_succ_of_le hlen))
        have hB := ih L' hL' W₁ (fun t => dirDeriv v (W₂ t)) hs₁
          (fun t ht => pdDir_contDiffOn hV (hs₂ t ht) v)
          (fun L₁ hlen => hc₁ L₁ (Nat.le_succ_of_le hlen))
          (fun L₂ hlen => hc₂ (v :: L₂) (by simpa using Nat.succ_le_succ hlen))
        refine (hA.add hB).congr ?_
        rintro ⟨t, y⟩ ⟨ht, hy⟩
        have hmul : Set.EqOn (dirDeriv v (fun z => W₁ t z * W₂ t z))
            (fun z => dirDeriv v (W₁ t) z * W₂ t z + W₁ t z * dirDeriv v (W₂ t) z) V :=
          pdDir_mul_eqOn hV (hs₁ t ht) (hs₂ t ht) v
        have hstep1 : iteratedDirDeriv (v :: L') (fun z => W₁ t z * W₂ t z) y
            = iteratedDirDeriv L' (fun z => dirDeriv v (W₁ t) z * W₂ t z +
                W₁ t z * dirDeriv v (W₂ t) z) y := by
          rw [pdIter_cons]
          exact pdIter_congrOn hV hmul L' hy
        have hsm₁ : ContDiffOn ℝ ∞ (fun z => dirDeriv v (W₁ t) z * W₂ t z) V :=
          (pdDir_contDiffOn hV (hs₁ t ht) v).mul (hs₂ t ht)
        have hsm₂ : ContDiffOn ℝ ∞ (fun z => W₁ t z * dirDeriv v (W₂ t) z) V :=
          (hs₁ t ht).mul (pdDir_contDiffOn hV (hs₂ t ht) v)
        have hstep2 := pdIter_add_eqOn hV hsm₁ hsm₂ L' hy
        rw [hstep1, hstep2]

lemma AnisotropicJointContDiffOn.mul {k : ℕ} {T : ℝ} {V : Set X} (hV : IsOpen V)
    {W₁ W₂ : ℝ → X → ℝ} (h₁ : AnisotropicJointContDiffOn k T V W₁) (h₂ : AnisotropicJointContDiffOn k T V W₂) :
    AnisotropicJointContDiffOn k T V (fun t y => W₁ t y * W₂ t y) :=
  ⟨fun t ht => (h₁.1 t ht).mul (h₂.1 t ht),
   fun L => anisoOn_mul_clause_graded hV L.length L (le_refl _) W₁ W₂ h₁.1 h₂.1
     (fun L₁ _ => h₁.2 L₁) (fun L₂ _ => h₂.2 L₂)⟩

lemma anisoOn_finsetProd {k : ℕ} {T : ℝ} {V : Set X} (hV : IsOpen V)
    {ι : Type*} (s : Finset ι) {W : ι → ℝ → X → ℝ}
    (h : ∀ i ∈ s, AnisotropicJointContDiffOn k T V (W i)) :
    AnisotropicJointContDiffOn k T V (fun t y => ∏ i ∈ s, W i t y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact (anisoOn_const 1).congr hV (fun t y => ∏ i ∈ (∅ : Finset ι), W i t y)
        (fun t _ y _ => by simp)
  | insert a s ha ih =>
      have hWa := h a (Finset.mem_insert_self a s)
      have hs := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      refine (hWa.mul hV hs).congr hV _ (fun t _ y _ => ?_)
      rw [Finset.prod_insert ha]

private lemma anisoOn_inv_clause {k : ℕ} {T : ℝ} {V : Set X} (hV : IsOpen V) :
    ∀ (m : ℕ) (L : List X), L.length ≤ m → ∀ (W : ℝ → X → ℝ),
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiffOn ℝ ∞ (W t) V) →
      (∀ L' : List X, L'.length ≤ m → ContDiffOn ℝ (k : ℕ)
        (fun q : ℝ × X => iteratedDirDeriv L' (W q.1) q.2) (Set.Icc (0 : ℝ) T ×ˢ V)) →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ V, W t y ≠ 0) →
      ContDiffOn ℝ (k : ℕ)
        (fun q : ℝ × X => iteratedDirDeriv L (fun y => (W q.1 y)⁻¹) q.2)
        (Set.Icc (0 : ℝ) T ×ˢ V) := by
  intro m
  induction m with
  | zero =>
      intro L hL W hsW hcW hne
      have hLnil : L = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hL)
      subst hLnil
      exact (hcW [] (le_refl _)).inv
        (by rintro ⟨t, y⟩ ⟨ht, hy⟩; exact hne t ht y hy)
  | succ m ih =>
      intro L hL W hsW hcW hne
      rcases L with - | ⟨v, L'⟩
      · exact (hcW [] (Nat.zero_le _)).inv
          (by rintro ⟨t, y⟩ ⟨ht, hy⟩; exact hne t ht y hy)
      · have hL' : L'.length ≤ m := by
          have hlen : L'.length + 1 ≤ m + 1 := by simpa using hL
          omega
        have hsInv : ∀ t ∈ Set.Icc (0 : ℝ) T,
            ContDiffOn ℝ ∞ (fun z => (W t z)⁻¹) V :=
          fun t ht => (hsW t ht).inv (fun y hy => hne t ht y hy)
        have hcInv : ∀ L'' : List X, L''.length ≤ m → ContDiffOn ℝ (k : ℕ)
            (fun q : ℝ × X => iteratedDirDeriv L'' (fun z => (W q.1 z)⁻¹) q.2)
            (Set.Icc (0 : ℝ) T ×ˢ V) :=
          fun L'' hlen => ih L'' hlen W hsW
            (fun L₃ hlen₃ => hcW L₃ (Nat.le_succ_of_le hlen₃)) hne
        have hsShift : ∀ t ∈ Set.Icc (0 : ℝ) T,
            ContDiffOn ℝ ∞ (dirDeriv v (W t)) V :=
          fun t ht => pdDir_contDiffOn hV (hsW t ht) v
        have hcShift : ∀ L'' : List X, L''.length ≤ m → ContDiffOn ℝ (k : ℕ)
            (fun q : ℝ × X => iteratedDirDeriv L'' (dirDeriv v (W q.1)) q.2)
            (Set.Icc (0 : ℝ) T ×ˢ V) :=
          fun L'' hlen => hcW (v :: L'') (by simpa using Nat.succ_le_succ hlen)
        have hsII : ∀ t ∈ Set.Icc (0 : ℝ) T,
            ContDiffOn ℝ ∞ (fun z => (W t z)⁻¹ * (W t z)⁻¹) V :=
          fun t ht => (hsInv t ht).mul (hsInv t ht)
        have hcII : ∀ L'' : List X, L''.length ≤ m → ContDiffOn ℝ (k : ℕ)
            (fun q : ℝ × X => iteratedDirDeriv L''
              (fun z => (W q.1 z)⁻¹ * (W q.1 z)⁻¹) q.2)
            (Set.Icc (0 : ℝ) T ×ˢ V) :=
          fun L'' hlen =>
            anisoOn_mul_clause_graded hV m L'' hlen _ _ hsInv hsInv hcInv hcInv
        have hcProd : ContDiffOn ℝ (k : ℕ)
            (fun q : ℝ × X => iteratedDirDeriv L'
              (fun z => ((W q.1 z)⁻¹ * (W q.1 z)⁻¹) * dirDeriv v (W q.1) z) q.2)
            (Set.Icc (0 : ℝ) T ×ˢ V) :=
          anisoOn_mul_clause_graded hV m L' hL' _ _ hsII hsShift hcII hcShift
        have hsProd : ∀ t ∈ Set.Icc (0 : ℝ) T,
            ContDiffOn ℝ ∞
              (fun z => ((W t z)⁻¹ * (W t z)⁻¹) * dirDeriv v (W t) z) V :=
          fun t ht => (hsII t ht).mul (hsShift t ht)
        refine ((contDiffOn_const (c := (-1 : ℝ))).mul hcProd).congr ?_
        rintro ⟨t, y⟩ ⟨ht, hy⟩
        have hinv_eq : Set.EqOn (dirDeriv v (fun z => (W t z)⁻¹))
            (fun z => (-1 : ℝ) *
              (((W t z)⁻¹ * (W t z)⁻¹) * dirDeriv v (W t) z)) V := by
          intro z hz
          have h := pdDir_inv_eqOn hV (hsW t ht) (fun w hw => hne t ht w hw) v hz
          rw [h]
          have hz2 : (W t z ^ 2)⁻¹ = (W t z)⁻¹ * (W t z)⁻¹ := by
            rw [sq, mul_inv]
          change -(W t z ^ 2)⁻¹ * dirDeriv v (W t) z
              = (-1 : ℝ) * ((W t z)⁻¹ * (W t z)⁻¹ * dirDeriv v (W t) z)
          rw [hz2]
          ring
        have hstep1 : iteratedDirDeriv (v :: L') (fun z => (W t z)⁻¹) y
            = iteratedDirDeriv L' (fun z => (-1 : ℝ) *
                (((W t z)⁻¹ * (W t z)⁻¹) * dirDeriv v (W t) z)) y := by
          rw [pdIter_cons]
          exact pdIter_congrOn hV hinv_eq L' hy
        have hstep2 := pdIter_smul_eqOn hV (hsProd t ht) (-1 : ℝ) L' hy
        rw [hstep1, hstep2]

lemma AnisotropicJointContDiffOn.inv {k : ℕ} {T : ℝ} {V : Set X} (hV : IsOpen V)
    {W : ℝ → X → ℝ} (h : AnisotropicJointContDiffOn k T V W)
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ V, W t y ≠ 0) :
    AnisotropicJointContDiffOn k T V (fun t y => (W t y)⁻¹) :=
  ⟨fun t ht => (h.1 t ht).inv (fun y hy => hne t ht y hy),
   fun L => anisoOn_inv_clause hV L.length L (le_refl _) W h.1
     (fun L' _ => h.2 L') hne⟩

lemma AnisotropicJointContDiffOn.comp_clequiv {k : ℕ} {T : ℝ} {V : Set X}
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : Y ≃L[ℝ] X) {W : ℝ → X → ℝ} (h : AnisotropicJointContDiffOn k T V W) (hV : IsOpen V) :
    AnisotropicJointContDiffOn k T ((A : Y → X) ⁻¹' V) (fun t z => W t (A z)) := by
  have hVY : IsOpen ((A : Y → X) ⁻¹' V) := hV.preimage A.continuous
  have hkey : ∀ (L : List Y) (u : X → ℝ), ContDiffOn ℝ ∞ u V →
      Set.EqOn (iteratedDirDeriv L (fun z => u (A z)))
        (fun z => iteratedDirDeriv (L.map (fun v => A v)) u (A z)) ((A : Y → X) ⁻¹' V) := by
    intro L
    induction L with
    | nil => intro u hu z hz; rfl
    | cons v L ih =>
        intro u hu z hz
        have hstep : Set.EqOn (dirDeriv v (fun w => u (A w)))
            (fun w => dirDeriv (A v) u (A w)) ((A : Y → X) ⁻¹' V) := by
          intro w hw
          unfold dirDeriv
          have hdu : DifferentiableAt ℝ u (A w) :=
            differentiableAt_of_contDiffOn_isOpen hV hu hw
          have hcomp : fderiv ℝ (fun x => u (A x)) w =
              (fderiv ℝ u (A w)).comp (A : Y →L[ℝ] X) := by
            rw [show (fun x => u (A x)) = u ∘ (A : Y → X) from rfl]
            rw [fderiv_comp w hdu (A.differentiable.differentiableAt)]
            congr 1
            exact A.fderiv
          rw [hcomp]
          rfl
        have h1 : iteratedDirDeriv (v :: L) (fun z => u (A z)) z
            = iteratedDirDeriv L (dirDeriv v (fun w => u (A w))) z := rfl
        have h2 := pdIter_congrOn hVY hstep L hz
        have h3 := ih (dirDeriv (A v) u) (pdDir_contDiffOn hV hu (A v)) hz
        rw [h1, h2, h3]
        rfl
  constructor
  · intro t ht
    exact (h.1 t ht).comp (A.contDiff.contDiffOn (s := (A : Y → X) ⁻¹' V))
      (fun z hz => hz)
  · intro L
    have hjoint := h.2 (L.map (fun v => A v))
    have hmap : ContDiffOn ℝ (k : ℕ)
        (fun q : ℝ × Y => (q.1, (A q.2 : X)))
        (Set.Icc (0 : ℝ) T ×ˢ ((A : Y → X) ⁻¹' V)) :=
      (contDiff_fst.prodMk (A.contDiff.comp contDiff_snd)).contDiffOn
    have hmaps : Set.MapsTo (fun q : ℝ × Y => (q.1, (A q.2 : X)))
        (Set.Icc (0 : ℝ) T ×ˢ ((A : Y → X) ⁻¹' V)) (Set.Icc (0 : ℝ) T ×ˢ V) :=
      fun q hq => ⟨hq.1, hq.2⟩
    refine ((hjoint.comp hmap hmaps)).congr ?_
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    exact hkey L (W t) (h.1 t ht) hz

end AnisotropicJointContDiffOn

end Analysis

end DifferentialGeometry
