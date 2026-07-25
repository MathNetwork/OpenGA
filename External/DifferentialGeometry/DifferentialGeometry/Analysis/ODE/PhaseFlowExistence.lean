import DifferentialGeometry.Analysis.ODE.PhaseFlowPerturbation
import DifferentialGeometry.Analysis.ODE.Flow.C1Regularity.VariationalSolutionOperator
import Mathlib.Analysis.Normed.Operator.NNNorm









noncomputable section

open Set Metric
open scoped NNReal

namespace DifferentialGeometry
namespace PhaseFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]


def phaseBox (P V : NNReal) : Set (E × E) :=
  {z | ‖z.1‖ ≤ (P : Real) ∧ ‖z.2‖ ≤ (V : Real)}


def phaseScale (P V : NNReal) : (E × E) →L[Real] (E × E) :=
  (((P : Real)⁻¹) • ContinuousLinearMap.fst Real E E).prod
    (((V : Real)⁻¹) • ContinuousLinearMap.snd Real E E)


def phaseUnscale (P V : NNReal) : (E × E) →L[Real] (E × E) :=
  ((P : Real) • ContinuousLinearMap.fst Real E E).prod
    ((V : Real) • ContinuousLinearMap.snd Real E E)

@[simp]
theorem phaseScale_apply (P V : NNReal) (z : E × E) :
    phaseScale P V z = ((P : Real)⁻¹ • z.1, (V : Real)⁻¹ • z.2) := by
  rfl

@[simp]
theorem phaseUnscale_apply (P V : NNReal) (z : E × E) :
    phaseUnscale P V z = ((P : Real) • z.1, (V : Real) • z.2) := by
  rfl

@[simp]
theorem unscale_scale {P V : NNReal} (hP : P ≠ 0) (hV : V ≠ 0)
    (z : E × E) : phaseUnscale P V (phaseScale P V z) = z := by
  ext <;> simp [phaseUnscale, phaseScale, hP, hV, smul_smul]

@[simp]
theorem scale_unscale {P V : NNReal} (hP : P ≠ 0) (hV : V ≠ 0)
    (z : E × E) : phaseScale P V (phaseUnscale P V z) = z := by
  ext <;> simp [phaseUnscale, phaseScale, hP, hV, smul_smul]


theorem unscale_maps_box (P V : NNReal) :
    MapsTo (phaseUnscale P V) (closedBall (0 : E × E) 1) (phaseBox P V) := by
  intro z hz
  rw [mem_closedBall_zero_iff] at hz
  have hz1 : ‖z.1‖ ≤ (1 : Real) := (norm_fst_le z).trans hz
  have hz2 : ‖z.2‖ ≤ (1 : Real) := (norm_snd_le z).trans hz
  constructor
  · rw [phaseUnscale_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg P.coe_nonneg]
    simpa using mul_le_mul_of_nonneg_left hz1 P.coe_nonneg
  · rw [phaseUnscale_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg V.coe_nonneg]
    simpa using mul_le_mul_of_nonneg_left hz2 V.coe_nonneg



theorem scale_maps_ball {P V b q : NNReal} (hP : 0 < P) (hV : 0 < V)
    (hqP : q ≤ b * P) (hqV : q ≤ b * V) :
    MapsTo (phaseScale (E := E) P V) (closedBall (0 : E × E) q)
      (closedBall (0 : E × E) b) := by
  intro z hz
  have hPr : (0 : Real) < P := by exact_mod_cast hP
  have hVr : (0 : Real) < V := by exact_mod_cast hV
  rw [mem_closedBall_zero_iff] at hz ⊢
  have hz1 : ‖z.1‖ ≤ (q : Real) := (norm_fst_le z).trans hz
  have hz2 : ‖z.2‖ ≤ (q : Real) := (norm_snd_le z).trans hz
  have hqPr : (q : Real) ≤ (b : Real) * (P : Real) := by exact_mod_cast hqP
  have hqVr : (q : Real) ≤ (b : Real) * (V : Real) := by exact_mod_cast hqV
  rw [Prod.norm_def]
  apply max_le
  · calc
      ‖(phaseScale P V z).1‖ = ‖z.1‖ / (P : Real) := by
        simp only [phaseScale_apply, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_pos hPr]
        rw [div_eq_inv_mul, mul_comm]
      _ ≤ (q : Real) / (P : Real) :=
        div_le_div_of_nonneg_right hz1 hPr.le
      _ ≤ (b : Real) := (div_le_iff₀ hPr).2 (by
        simpa only [mul_comm] using hqPr)
  · calc
      ‖(phaseScale P V z).2‖ = ‖z.2‖ / (V : Real) := by
        simp only [phaseScale_apply, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_pos hVr]
        rw [div_eq_inv_mul, mul_comm]
      _ ≤ (q : Real) / (V : Real) :=
        div_le_div_of_nonneg_right hz2 hVr.le
      _ ≤ (b : Real) := (div_le_iff₀ hVr).2 (by
        simpa only [mul_comm] using hqVr)


def scaledPhase (P V : NNReal) (a : E × E → E) (z : E × E) : E × E :=
  phaseScale P V (phaseField a (phaseUnscale P V z))



theorem scaledPhase_lip {P V κ : NNReal} {a : E × E → E}
    (ha : LipschitzOnWith κ a (phaseBox P V)) :
    LipschitzOnWith
      (‖phaseScale (E := E) P V‖₊ *
        (max 1 κ * ‖phaseUnscale (E := E) P V‖₊))
      (scaledPhase P V a) (closedBall (0 : E × E) 1) := by
  have hu : LipschitzOnWith ‖phaseUnscale (E := E) P V‖₊ (phaseUnscale P V)
      (closedBall (0 : E × E) 1) :=
    (phaseUnscale (E := E) P V).lipschitz.lipschitzOnWith
  have hm := (phaseField_lip (E := E) ha).comp hu
    (unscale_maps_box (E := E) P V)
  have hs := (phaseScale (E := E) P V).lipschitz.comp_lipschitzOnWith hm
  simpa only [scaledPhase, Function.comp_def, mul_assoc] using hs



theorem scaledPhase_norm {P V A L : NNReal} {a : E × E → E}
    (hP : 0 < P) (hV : 0 < V)
    (ha : ∀ z ∈ phaseBox P V, ‖a z‖ ≤ (A : Real))
    (hVP : V ≤ L * P) (hAV : A ≤ L * V)
    {z : E × E} (hz : z ∈ closedBall (0 : E × E) 1) :
    ‖scaledPhase P V a z‖ ≤ (L : Real) := by
  have hPr : (0 : Real) < P := by exact_mod_cast hP
  have hVr : (0 : Real) < V := by exact_mod_cast hV
  have hzNorm : ‖z‖ ≤ (1 : Real) := by
    simpa only [mem_closedBall_zero_iff] using hz
  have hz2 : ‖z.2‖ ≤ (1 : Real) := (norm_snd_le z).trans hzNorm
  have hw : phaseUnscale P V z ∈ phaseBox P V :=
    unscale_maps_box P V hz
  rw [Prod.norm_def]
  apply max_le
  · have hratio : (V : Real) / (P : Real) ≤ (L : Real) := by
      rw [div_le_iff₀ hPr]
      exact_mod_cast hVP
    calc
      ‖(scaledPhase P V a z).1‖ =
          ((V : Real) / (P : Real)) * ‖z.2‖ := by
        simp only [scaledPhase, phaseScale_apply, phaseUnscale_apply, phaseField,
          norm_smul, Real.norm_eq_abs, smul_smul]
        rw [abs_of_pos (mul_pos (inv_pos.mpr hPr) hVr), div_eq_inv_mul]
      _ ≤ ((V : Real) / (P : Real)) * 1 := by
        gcongr
      _ ≤ (L : Real) := by simpa using hratio
  · have hratio : (A : Real) / (V : Real) ≤ (L : Real) := by
      rw [div_le_iff₀ hVr]
      exact_mod_cast hAV
    calc
      ‖(scaledPhase P V a z).2‖ =
          ‖a (phaseUnscale P V z)‖ / (V : Real) := by
        simp only [scaledPhase, phaseScale_apply, phaseField, norm_smul,
          Real.norm_eq_abs, abs_inv, abs_of_pos hVr]
        rw [div_eq_inv_mul, mul_comm]
      _ ≤ (A : Real) / (V : Real) := by
        exact div_le_div_of_nonneg_right (ha _ hw) hVr.le
      _ ≤ (L : Real) := hratio

@[simp]
theorem unscale_scaled {P V : NNReal} (hP : P ≠ 0) (hV : V ≠ 0)
    (a : E × E → E) (z : E × E) :
    phaseUnscale P V (scaledPhase P V a z) =
      phaseField a (phaseUnscale P V z) := by
  exact unscale_scale hP hV _

private theorem exists_picard_mem
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    {f : Real → F → F} {tmin tmax : Real} {t₀ : Icc tmin tmax}
    {x₀ : F} {a r L K : NNReal}
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ Φ : F → Real → F, ∀ x ∈ closedBall x₀ r,
      Φ x t₀ = x ∧
      (∀ t ∈ Icc tmin tmax,
        HasDerivWithinAt (Φ x) (f t (Φ x t)) (Icc tmin tmax) t) ∧
      ∀ t ∈ Icc tmin tmax, Φ x t ∈ closedBall x₀ a := by
  classical
  have hex (x : F) (hx : x ∈ closedBall x₀ r) :=
    ODE.FunSpace.exists_isFixedPt_next hf hx
  choose α hα using hex
  let Φ : F → Real → F := fun x ↦
    if hx : x ∈ closedBall x₀ r then (α x hx).compProj else 0
  refine ⟨Φ, ?_⟩
  intro x hx
  have hinit : Φ x t₀ = x := by
    simp only [Φ, dif_pos hx]
    rw [ODE.FunSpace.compProj_val, ← hα x hx, ODE.FunSpace.next_apply₀]
  refine ⟨hinit, ?_, ?_⟩
  · intro t ht
    simp only [Φ, dif_pos hx]
    apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      ((α x hx).continuous_compProj.continuousOn)
      (fun _ _ ↦ (α x hx).compProj_mem_closedBall hf.mul_max_le)
      x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα x hx]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  · intro t ht
    simp only [Φ, dif_pos hx]
    exact (α x hx).compProj_mem_closedBall hf.mul_max_le

private theorem exists_fenced_Icc [CompleteSpace E]
    {P V A L b κ : NNReal} {a : E × E → E}
    {tmin tmax : Real} (hzero : (0 : Real) ∈ Icc tmin tmax)
    (hP : 0 < P) (hV : 0 < V)
    (haLip : LipschitzOnWith κ a (phaseBox P V))
    (haNorm : ∀ z ∈ phaseBox P V, ‖a z‖ ≤ (A : Real))
    (hVP : V ≤ L * P) (hAV : A ≤ L * V)
    (hLb : (L : Real) * max (tmax - 0) (0 - tmin) ≤ 1 - (b : Real)) :
    ∃ Φ : (E × E) → Real → E × E,
      ∀ z, phaseScale P V z ∈ closedBall (0 : E × E) b →
        Φ z 0 = z ∧
        ContinuousOn (Φ z) (Icc tmin tmax) ∧
        (∀ t ∈ Icc tmin tmax,
          HasDerivWithinAt (Φ z) (phaseField a (Φ z t)) (Icc tmin tmax) t) ∧
        ∀ t ∈ Icc tmin tmax, Φ z t ∈ phaseBox P V := by
  let t₀ : Icc tmin tmax := ⟨0, hzero⟩
  let K : NNReal := ‖phaseScale (E := E) P V‖₊ *
    (max 1 κ * ‖phaseUnscale (E := E) P V‖₊)
  have hpl : IsPicardLindelof
      (fun _ : Real ↦ scaledPhase P V a) t₀ (0 : E × E) 1 b L K := by
    refine
      { lipschitzOnWith := ?_,
        continuousOn := ?_,
        norm_le := ?_,
        mul_max_le := ?_ }
    · intro _ _
      simpa only [K] using scaledPhase_lip (E := E) haLip
    · intro _ _
      exact continuousOn_const
    · intro _ _ z hz
      exact scaledPhase_norm hP hV haNorm hVP hAV hz
    · exact hLb
  obtain ⟨Ψ, hΨ⟩ := exists_picard_mem hpl
  let Φ : (E × E) → Real → E × E := fun z t ↦
    phaseUnscale P V (Ψ (phaseScale P V z) t)
  refine ⟨Φ, ?_⟩
  intro z hz
  obtain ⟨hΨ0, hΨd, hΨmem⟩ := hΨ (phaseScale P V z) hz
  have hP0 : P ≠ 0 := hP.ne'
  have hV0 : V ≠ 0 := hV.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Φ]
    rw [show Ψ (phaseScale P V z) 0 = phaseScale P V z by
      simpa only [t₀] using hΨ0]
    exact unscale_scale hP0 hV0 z
  · exact (phaseUnscale P V).continuous.comp_continuousOn
      (HasDerivWithinAt.continuousOn hΨd)
  · intro t ht
    have hraw := (phaseUnscale P V).hasFDerivAt.comp_hasDerivWithinAt t
      (hΨd t ht)
    simpa only [Φ, unscale_scaled hP0 hV0] using hraw
  · intro t ht
    exact unscale_maps_box P V (hΨmem t ht)




theorem exists_fenced [CompleteSpace E]
    {P V A L b κ : NNReal} {a : E × E → E}
    (hP : 0 < P) (hV : 0 < V)
    (haLip : LipschitzOnWith κ a (phaseBox P V))
    (haNorm : ∀ z ∈ phaseBox P V, ‖a z‖ ≤ (A : Real))
    (hVP : V ≤ L * P) (hAV : A ≤ L * V)
    (hLb : (L : Real) ≤ 1 - (b : Real)) :
    ∃ Φ : (E × E) → Real → E × E,
      ∀ z, phaseScale P V z ∈ closedBall (0 : E × E) b →
        Φ z 0 = z ∧
        ContinuousOn (Φ z) (Icc 0 1) ∧
        (∀ t ∈ Ico 0 1,
          HasDerivWithinAt (Φ z) (phaseField a (Φ z t)) (Ici t) t) ∧
        ∀ t ∈ Icc 0 1, Φ z t ∈ phaseBox P V := by
  obtain ⟨Φ, hΦ⟩ := exists_fenced_Icc (E := E) (tmin := 0) (tmax := 1)
    (by norm_num) hP hV haLip haNorm hVP hAV (by simpa using hLb)
  refine ⟨Φ, ?_⟩
  intro z hz
  obtain ⟨hΦ0, hΦcont, hΦderiv, hΦmem⟩ := hΦ z hz
  refine ⟨hΦ0, hΦcont, ?_, hΦmem⟩
  intro t ht
  exact Analysis.ODE.Flow.hasDerivWithinAt_Ici_of_Icc
    (hΦderiv t ⟨ht.1, ht.2.le⟩) ht



theorem exists_fenced_on [CompleteSpace E]
    {P V A L b κ : NNReal} {T : Real} {a : E × E → E}
    (hT : 0 ≤ T) (hP : 0 < P) (hV : 0 < V)
    (haLip : LipschitzOnWith κ a (phaseBox P V))
    (haNorm : ∀ z ∈ phaseBox P V, ‖a z‖ ≤ (A : Real))
    (hVP : V ≤ L * P) (hAV : A ≤ L * V)
    (hLb : (L : Real) * T ≤ 1 - (b : Real)) :
    ∃ Φ : (E × E) → Real → E × E,
      ∀ z, phaseScale P V z ∈ closedBall (0 : E × E) b →
        Φ z 0 = z ∧
        ContinuousOn (Φ z) (Icc (-T) T) ∧
        (∀ t ∈ Icc (-T) T,
          HasDerivWithinAt (Φ z) (phaseField a (Φ z t)) (Icc (-T) T) t) ∧
        (∀ t ∈ Ioo (-T) T,
          HasDerivAt (Φ z) (phaseField a (Φ z t)) t) ∧
        ∀ t ∈ Icc (-T) T, Φ z t ∈ phaseBox P V := by
  obtain ⟨Φ, hΦ⟩ := exists_fenced_Icc (E := E) (tmin := -T) (tmax := T)
    (by constructor <;> linarith) hP hV haLip haNorm hVP hAV (by
      simpa only [sub_zero, zero_sub, neg_neg, max_self] using hLb)
  refine ⟨Φ, ?_⟩
  intro z hz
  obtain ⟨hΦ0, hΦcont, hΦderiv, hΦmem⟩ := hΦ z hz
  refine ⟨hΦ0, hΦcont, hΦderiv, ?_, hΦmem⟩
  intro t ht
  exact (hΦderiv t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)





theorem exists_fenced_sym [CompleteSpace E]
    {P V A L b κ : NNReal} {a : E × E → E}
    (hP : 0 < P) (hV : 0 < V)
    (haLip : LipschitzOnWith κ a (phaseBox P V))
    (haNorm : ∀ z ∈ phaseBox P V, ‖a z‖ ≤ (A : Real))
    (hVP : V ≤ L * P) (hAV : A ≤ L * V)
    (hLb : (L : Real) ≤ 1 - (b : Real)) :
    ∃ Φ : (E × E) → Real → E × E,
      ∀ z, phaseScale P V z ∈ closedBall (0 : E × E) b →
        Φ z 0 = z ∧
        ContinuousOn (Φ z) (Icc (-1) 1) ∧
        (∀ t ∈ Icc (-1) 1,
          HasDerivWithinAt (Φ z) (phaseField a (Φ z t)) (Icc (-1) 1) t) ∧
        (∀ t ∈ Ioo (-1) 1,
          HasDerivAt (Φ z) (phaseField a (Φ z t)) t) ∧
        ∀ t ∈ Icc (-1) 1, Φ z t ∈ phaseBox P V := by
  obtain ⟨Φ, hΦ⟩ := exists_fenced_Icc (E := E) (tmin := -1) (tmax := 1)
    (by norm_num) hP hV haLip haNorm hVP hAV (by simpa using hLb)
  refine ⟨Φ, ?_⟩
  intro z hz
  obtain ⟨hΦ0, hΦcont, hΦderiv, hΦmem⟩ := hΦ z hz
  refine ⟨hΦ0, hΦcont, hΦderiv, ?_, hΦmem⟩
  intro t ht
  exact (hΦderiv t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

end PhaseFlow
end DifferentialGeometry
