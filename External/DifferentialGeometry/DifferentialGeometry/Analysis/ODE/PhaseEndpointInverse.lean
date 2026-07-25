import DifferentialGeometry.Analysis.Calculus.ApproximatesLinearOn
import DifferentialGeometry.Analysis.ODE.PhaseFlowSmallness
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Basic








noncomputable section

open Set Metric
open scoped ContDiff NNReal Topology

namespace DifferentialGeometry
namespace PhaseFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]



theorem freeDiagInv_pos [Nontrivial E] :
    0 < ‖((freeDiagCLE (E := E)).symm : (E × E) →L[Real] (E × E))‖₊⁻¹ := by
  let L : (E × E) →L[Real] (E × E) :=
    ((freeDiagCLE (E := E)).symm : (E × E) →L[Real] (E × E))
  have hL : L ≠ 0 := by
    intro hzero
    apply not_subsingleton (E × E)
    constructor
    intro x y
    apply (freeDiagCLE (E := E)).symm.injective
    change L x = L y
    rw [hzero]
    rfl
  have hnorm : (0 : Real) < ‖L‖ := norm_pos_iff.mpr hL
  have hnn : (0 : NNReal) < ‖L‖₊ := by exact_mod_cast hnorm
  exact inv_pos.mpr hnn



theorem invErr_mono {N c c' : NNReal} (hcc' : c ≤ c') (hc' : c' < N⁻¹) :
    N * (N⁻¹ - c)⁻¹ * c ≤ N * (N⁻¹ - c')⁻¹ * c' := by
  have hnum : N * c ≤ N * c' :=
    mul_le_mul_of_nonneg_left hcc' N.2
  have hden_pos : 0 < N⁻¹ - c' := tsub_pos_iff_lt.mpr hc'
  have hden : N⁻¹ - c' ≤ N⁻¹ - c := tsub_le_tsub_left hcc' N⁻¹
  have hfrac : (N * c) / (N⁻¹ - c) ≤ (N * c') / (N⁻¹ - c') :=
    div_le_div₀ (mul_nonneg N.2 c'.2) hnum hden_pos hden
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hfrac



theorem invErr_lt_one {N c : NNReal}
    (hc : c < N⁻¹ / (2 * (N + 1))) :
    N * (N⁻¹ - c)⁻¹ * c < 1 := by
  have hden : 0 < 2 * (N + 1) := mul_pos (by norm_num) (by positivity)
  have hsmall : c * (2 * (N + 1)) < N⁻¹ :=
    (lt_div_iff₀ hden).mp hc
  have hN1 : 1 ≤ N + 1 := by exact le_add_of_nonneg_left N.2
  have hfac : 1 ≤ 2 * (N + 1) := by
    calc
      (1 : NNReal) ≤ 2 := by norm_num
      _ = 2 * (1 : NNReal) := by norm_num
      _ ≤ 2 * (N + 1) := mul_le_mul_of_nonneg_left hN1 (by norm_num)
  have hct : c < N⁻¹ := by
    calc
      c = c * 1 := by rw [mul_one]
      _ ≤ c * (2 * (N + 1)) := mul_le_mul_of_nonneg_left hfac c.2
      _ < N⁻¹ := hsmall
  have hdiff : 0 < N⁻¹ - c := tsub_pos_iff_lt.mpr hct
  have hnum : N * c < N⁻¹ - c := by
    rw [lt_tsub_iff_right]
    have hfac' : N + 1 ≤ 2 * (N + 1) := by
      calc
        N + 1 = 1 * (N + 1) := by rw [one_mul]
        _ ≤ 2 * (N + 1) :=
          mul_le_mul_of_nonneg_right (by norm_num) (N + 1).2
    calc
      N * c + c = c * (N + 1) := by ring
      _ ≤ c * (2 * (N + 1)) := mul_le_mul_of_nonneg_left hfac' c.2
      _ < N⁻¹ := hsmall
  calc
    N * (N⁻¹ - c)⁻¹ * c = (N * c) / (N⁻¹ - c) := by
      rw [div_eq_mul_inv]
      ring
    _ < 1 := (div_lt_one hdiff).2 hnum



theorem invVel_approx
    {F : E × E → E × E} {s : Set (E × E)} {c : NNReal}
    (hF : ApproximatesLinearOn F
      ((freeDiagCLE (E := E)).symm : (E × E) →L[Real] (E × E)) s c)
    (y : E) :
    ApproximatesLinearOn (fun x => (F (x, y)).2)
      (-(ContinuousLinearMap.id Real E)) {x | (x, y) ∈ s} c := by
  intro x hx x' hx'
  let z : E × E := (x, y)
  let z' : E × E := (x', y)
  let R : E × E := F z - F z' -
    ((freeDiagCLE (E := E)).symm : (E × E) →L[Real] (E × E)) (z - z')
  have hfull : ‖R‖ ≤ (c : Real) * ‖z - z'‖ := hF z hx z' hx'
  have hfree :
      (((freeDiagCLE (E := E)).symm : (E × E) →L[Real] (E × E))
        (z - z')).2 = -(x - x') := by
    change ((freeDiagCLE (E := E)).symm (z - z')).2 = -(x - x')
    rw [freeDiagInv_apply]
    simp only [z, z', Prod.fst_sub, Prod.snd_sub, sub_self, zero_sub]
  have hprod : ‖z - z'‖ = ‖x - x'‖ := by
    simp only [z, z', Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self,
      norm_zero, max_eq_left (norm_nonneg _)]
  calc
    ‖(F (x, y)).2 - (F (x', y)).2 -
        (-(ContinuousLinearMap.id Real E)) (x - x')‖ = ‖R.2‖ := by
      simp only [R, z, z', Prod.snd_sub, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.id_apply, hfree]
    _ ≤ ‖R‖ := norm_snd_le R
    _ ≤ (c : Real) * ‖z - z'‖ := hfull
    _ = (c : Real) * ‖x - x'‖ := by rw [hprod]




theorem invVel_fderiv_le
    {F : E × E → E × E} {s : Set (E × E)} {c : NNReal}
    (hF : ApproximatesLinearOn F
      ((freeDiagCLE (E := E)).symm : (E × E) →L[Real] (E × E)) s c)
    {x y : E} (hs : s ∈ 𝓝 (x, y))
    (hFd : DifferentiableAt Real F (x, y)) :
    ‖fderiv Real (fun u => (F (u, y)).2) x +
        ContinuousLinearMap.id Real E‖ ≤ (c : Real) := by
  have hs' : {u : E | (u, y) ∈ s} ∈ 𝓝 x :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds hs
  have hslice : DifferentiableAt Real (fun u => (F (u, y)).2) x := by
    exact (hFd.comp x
      (differentiableAt_id.prodMk (differentiableAt_const y))).snd
  simpa only [sub_neg_eq_add] using
    (invVel_approx hF y).fderiv_sub_le hs' hslice




theorem inv_smooth_of_approx [CompleteSpace E] [FiniteDimensional Real E]
    {f : E → E} {A : E ≃L[Real] E} {s : Set E} {c : NNReal}
    (hf : ApproximatesLinearOn f (A : E →L[Real] E) s c)
    (hc : Subsingleton E ∨ c < ‖(A.symm : E →L[Real] E)‖₊⁻¹)
    (hs : IsOpen s) (hsm : ContDiffOn Real ∞ f s)
    (e : OpenPartialHomeomorph E E) (hsource : e.source = s)
    (hcoe : (e : E → E) = f) :
    ContDiffOn Real ∞ e.symm e.target := by
  intro y hy
  have hx : e.symm y ∈ s := by
    rw [← hsource]
    exact e.map_target hy
  have hsmx : ContDiffAt Real ∞ f (e.symm y) :=
    hsm.contDiffAt (hs.mem_nhds hx)
  let D : E →L[Real] E := fderiv Real f (e.symm y)
  have hfD : HasFDerivAt f D (e.symm y) := by
    exact (hsmx.differentiableAt (by simp)).hasFDerivAt
  have hDnorm : ‖D - (A : E →L[Real] E)‖ ≤ (c : Real) := by
    simpa only [D] using
      hf.fderiv_sub_le (hs.mem_nhds hx) hfD.differentiableAt
  have hDapprox : ApproximatesLinearOn (D : E → E) (A : E →L[Real] E)
      Set.univ c := by
    intro u _ v _
    have hbound := (D - (A : E →L[Real] E)).le_opNorm (u - v)
    have hmul : ‖D - (A : E →L[Real] E)‖ * ‖u - v‖ ≤
        (c : Real) * ‖u - v‖ :=
      mul_le_mul_of_nonneg_right hDnorm (norm_nonneg _)
    calc
      ‖D u - D v - A (u - v)‖ =
          ‖(D - (A : E →L[Real] E)) (u - v)‖ := by
        rw [← D.map_sub]
        rfl
      _ ≤ ‖D - (A : E →L[Real] E)‖ * ‖u - v‖ := hbound
      _ ≤ (c : Real) * ‖u - v‖ := hmul
  have hDinj : Function.Injective D := by
    rw [← Set.injOn_univ]
    exact hDapprox.injOn hc
  have hDsurj : Function.Surjective D :=
    LinearMap.surjective_of_injective hDinj
  let D' : E ≃L[Real] E := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr hDinj) (LinearMap.range_eq_top.mpr hDsurj)
  have hfD' : HasFDerivAt f (D' : E →L[Real] E) (e.symm y) := by
    simpa only [D', ContinuousLinearEquiv.coe_ofBijective] using hfD
  have heD' : HasFDerivAt (e : E → E) (D' : E →L[Real] E) (e.symm y) := by
    rw [hcoe]
    exact hfD'
  have hesm : ContDiffAt Real ∞ (e : E → E) (e.symm y) := by
    rw [hcoe]
    exact hsmx
  exact (e.contDiffAt_symm hy heD' hesm).contDiffWithinAt



theorem quantInv_smooth [CompleteSpace E] [FiniteDimensional Real E]
    {f : E → E} {A : E ≃L[Real] E} {s : Set E} {c : NNReal}
    (hf : ApproximatesLinearOn f (A : E →L[Real] E) s c)
    (hc : Subsingleton E ∨ c < ‖(A.symm : E →L[Real] E)‖₊⁻¹)
    (hs : IsOpen s) (hsm : ContDiffOn Real ∞ f s) :
    ContDiffOn Real ∞
      (hf.toOpenPartialHomeomorph (f' := A) f s hc hs).symm
      (hf.toOpenPartialHomeomorph (f' := A) f s hc hs).target := by
  apply inv_smooth_of_approx hf hc hs hsm
  · rfl
  · rfl






theorem exists_quant_inv_bi [CompleteSpace E]
    {f : E × E → E × E} {q c : NNReal}
    (hq : 0 < q)
    (hf : ApproximatesLinearOn f freeDiag
      (closedBall (0 : E × E) q) c)
    (hc : c <
      ‖((freeDiagCLE (E := E)).symm : (E × E) →L[Real] (E × E))‖₊⁻¹) :
    ∃ (e : OpenPartialHomeomorph (E × E) (E × E)) (δ : Real),
      0 < δ ∧
      e.source = ball (0 : E × E) q ∧
      (e : E × E → E × E) = f ∧
      closedBall (f 0) δ ⊆ e.target ∧
      δ = ((‖((freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ - c : NNReal) : Real) *
        ((q : Real) / 2) ∧
      ApproximatesLinearOn
        (e.symm : E × E → E × E)
        ((freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))
        e.target
        (‖((freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊ *
          (‖((freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊⁻¹ - c)⁻¹ * c) := by
  let s : Set (E × E) := ball (0 : E × E) q
  have hfo : ApproximatesLinearOn f freeDiag s c :=
    hf.mono_set Metric.ball_subset_closedBall
  have hc' : Subsingleton (E × E) ∨ c <
      ‖((freeDiagCLE (E := E)).symm : (E × E) →L[Real] (E × E))‖₊⁻¹ :=
    Or.inr hc
  let e : OpenPartialHomeomorph (E × E) (E × E) :=
    hfo.toOpenPartialHomeomorph (f' := freeDiagCLE (E := E)) f s hc' Metric.isOpen_ball
  let δ : Real := ((‖((freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊⁻¹ - c : NNReal) : Real) *
    ((q : Real) / 2)
  have hmargin : 0 <
      ‖((freeDiagCLE (E := E)).symm : (E × E) →L[Real] (E × E))‖₊⁻¹ - c :=
    tsub_pos_iff_lt.mpr hc
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact mul_pos (by exact_mod_cast hmargin) (div_pos hqReal (by norm_num))
  have hhalf : closedBall (0 : E × E) ((q : Real) / 2) ⊆ s := by
    exact Metric.closedBall_subset_ball (half_lt_self hqReal)
  have htarget := hfo.closedBall_subset_target
    (f' := freeDiagCLE (E := E)) hc' Metric.isOpen_ball
    (b := (0 : E × E)) (ε := (q : Real) / 2) (by positivity) hhalf
  have hinv : ApproximatesLinearOn
      (e.symm : E × E → E × E)
      ((freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))
      e.target
      (‖((freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊ *
        (‖((freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊⁻¹ - c)⁻¹ * c) := by
    simpa only [e, s] using
      (hfo.to_inv (f' := freeDiagCLE (E := E)) hc')
  refine ⟨e, δ, hδ, ?_, ?_, ?_, rfl, hinv⟩
  · rfl
  · rfl
  · simpa [e, δ, s, NNReal.coe_sub hc.le] using htarget



theorem exists_quant_inv [CompleteSpace E]
    {f : E × E → E × E} {q c : NNReal}
    (hq : 0 < q)
    (hf : ApproximatesLinearOn f freeDiag
      (closedBall (0 : E × E) q) c)
    (hc : c <
      ‖((freeDiagCLE (E := E)).symm : (E × E) →L[Real] (E × E))‖₊⁻¹) :
    ∃ (e : OpenPartialHomeomorph (E × E) (E × E)) (δ : Real),
      0 < δ ∧
      e.source = ball (0 : E × E) q ∧
      (e : E × E → E × E) = f ∧
      closedBall (f 0) δ ⊆ e.target ∧
      δ = ((‖((freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ - c : NNReal) : Real) *
        ((q : Real) / 2) := by
  obtain ⟨e, δ, hδ, hsource, hcoe, htarget, hδeq, _hinv⟩ :=
    exists_quant_inv_bi (E := E) hq hf hc
  exact ⟨e, δ, hδ, hsource, hcoe, htarget, hδeq⟩

end PhaseFlow
end DifferentialGeometry
