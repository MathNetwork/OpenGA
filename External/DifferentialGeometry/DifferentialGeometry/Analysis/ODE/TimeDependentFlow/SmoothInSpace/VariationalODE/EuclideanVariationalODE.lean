import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.BanachIC
import Mathlib.Analysis.Calculus.FDeriv.Symmetric


noncomputable section

namespace DifferentialGeometry.Analysis.ODE.Flow

open Set Metric Function ContinuousLinearMap
open scoped Topology NNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
private theorem hasDerivAt_line (x δ : E) :
    HasDerivAt (fun rr : ℝ => x + rr • δ) δ 0 := by
  have h1 : HasDerivAt (fun rr : ℝ => rr • δ) δ 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const δ
  have h2 : HasDerivAt (fun rr : ℝ => x + rr • δ) (0 + δ) 0 :=
    (hasDerivAt_const (0 : ℝ) x).add h1
  simpa using h2

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem partial_spatial_fderiv_eq_comp_inl
    {x : E} {s : ℝ} (hΦdiff : DifferentiableAt ℝ Φ (x, s)) :
    fderiv ℝ (fun y => Φ (y, s)) x
      = (fderiv ℝ Φ (x, s)).comp (ContinuousLinearMap.inl ℝ E ℝ) := by
  have hslice : HasFDerivAt (fun y => Φ (y, s))
      ((fderiv ℝ Φ (x, s)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x :=
    hΦdiff.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x s)
  exact hslice.fderiv

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem flow_joint_fderiv_inr_eq
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {x : E} {s : ℝ} (hx : x ∈ closedBall x₀ r) (hs : s ∈ Ioo tmin tmax)
    (hΦdiff : DifferentiableAt ℝ Φ (x, s)) :
    fderiv ℝ Φ (x, s) (ContinuousLinearMap.inr ℝ E ℝ 1) = f s (Φ (x, s)) := by
  have hcurve : HasDerivAt (fun u => Φ (x, u))
      (fderiv ℝ Φ (x, s) (ContinuousLinearMap.inr ℝ E ℝ 1)) s := by
    have hcomp : HasDerivAt (fun u : ℝ => (x, u)) (ContinuousLinearMap.inr ℝ E ℝ 1) s := by
      have : HasDerivAt (fun u : ℝ => (x, u)) ((0 : E), (1 : ℝ)) s := by
        simpa using (hasDerivAt_const s x).prodMk (hasDerivAt_id s)
      simpa [ContinuousLinearMap.inr_apply] using this
    exact hΦdiff.hasFDerivAt.comp_hasDerivAt s hcomp
  have hflow : HasDerivAt (fun u => Φ (x, u)) (f s (Φ (x, s))) s := by
    have hwithin := hΦ.hasDerivWithinAt x hx s (Ioo_subset_Icc_self hs)
    exact hwithin.hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  exact hcurve.unique hflow

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
private theorem contDiffAt_of_mem {U : Set (E × ℝ)} (hUopen : IsOpen U)
    (hΦsmooth : ContDiffOn ℝ ∞ Φ U) {q : E × ℝ} (hq : q ∈ U) :
    ContDiffAt ℝ ∞ Φ q :=
  hΦsmooth.contDiffAt (hUopen.mem_nhds hq)

section PerDirection

variable (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
  (hf : ContDiff ℝ ∞ (uncurry f))
  {U : Set (E × ℝ)} (hUopen : IsOpen U)
  (hΦsmooth : ContDiffOn ℝ ∞ Φ U)

include hΦ hf hUopen hΦsmooth in

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem IsLocalFlow.hasDerivAt_partial_spatial_fderiv_apply
    {x : E} {s : ℝ} (hxsU : (x, s) ∈ U)
    (hx : x ∈ ball x₀ r) (hs : s ∈ Ioo tmin tmax) (δ : E) :
    HasDerivAt (fun u : ℝ => fderiv ℝ (fun y => Φ (y, u)) x δ)
      (fderiv ℝ (f s) (Φ (x, s)) (fderiv ℝ (fun y => Φ (y, s)) x δ)) s := by
  have hΦ_at : ∀ q ∈ U, ContDiffAt ℝ ∞ Φ q := fun q hq => contDiffAt_of_mem hUopen hΦsmooth hq
  have hΦ_xs : ContDiffAt ℝ ∞ Φ (x, s) := hΦ_at _ hxsU
  have hΦ_diffOn : ∀ q ∈ U, DifferentiableAt ℝ Φ q := fun q hq =>
    (hΦ_at q hq).differentiableAt (by simp)
  have hone_one_le : (1 + 1 : WithTop ℕ∞) ≤ ∞ := by decide
  have hsndDiff : DifferentiableAt ℝ (fderiv ℝ Φ) (x, s) :=
    (hΦ_xs.fderiv_right (m := 1) hone_one_le).differentiableAt (by simp)
  have hsndHas : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) (x, s)) (x, s) :=
    hsndDiff.hasFDerivAt
  set B := fderiv ℝ (fderiv ℝ Φ) (x, s) with hB
  have hsymm : IsSymmSndFDerivAt ℝ Φ (x, s) := by
    refine hΦ_xs.isSymmSndFDerivAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]; decide
  set eX : E × ℝ := ContinuousLinearMap.inl ℝ E ℝ δ with heX
  set eT : E × ℝ := ContinuousLinearMap.inr ℝ E ℝ 1 with heT
  have hcurveT : HasDerivAt (fun u : ℝ => (x, u)) eT s := by
    have : HasDerivAt (fun u : ℝ => (x, u)) ((0 : E), (1 : ℝ)) s := by
      simpa using (hasDerivAt_const s x).prodMk (hasDerivAt_id s)
    simpa [heT, ContinuousLinearMap.inr_apply] using this
  have hfderivCurve : HasDerivAt (fun u : ℝ => fderiv ℝ Φ (x, u)) (B eT) s :=
    hsndHas.comp_hasDerivAt s hcurveT
  have hslopeApply : HasDerivAt (fun u : ℝ => fderiv ℝ Φ (x, u) eX) (B eT eX) s := by
    have := (ContinuousLinearMap.apply ℝ E eX).hasFDerivAt.comp_hasDerivAt s hfderivCurve
    simpa [ContinuousLinearMap.apply_apply] using this
  have hUx_open : IsOpen {u : ℝ | (x, u) ∈ U} := hUopen.preimage (by fun_prop)
  have hEvEq : (fun u : ℝ => fderiv ℝ Φ (x, u) eX)
      =ᶠ[𝓝 s] (fun u : ℝ => fderiv ℝ (fun y => Φ (y, u)) x δ) := by
    filter_upwards [hUx_open.mem_nhds (show s ∈ {u : ℝ | (x, u) ∈ U} from hxsU)] with u hu
    rw [partial_spatial_fderiv_eq_comp_inl (hΦ_diffOn _ hu)]
    simp [heX, ContinuousLinearMap.comp_apply]
  have hLHS :
      HasDerivAt (fun u : ℝ => fderiv ℝ (fun y => Φ (y, u)) x δ) (B eT eX) s :=
    hEvEq.hasDerivAt_iff.mp hslopeApply
  have hswap : B eT eX = B eX eT := hsymm eT eX
  have hlineCurve : HasDerivAt (fun rr : ℝ => (x + rr • δ, s)) eX 0 := by
    have : HasDerivAt (fun rr : ℝ => (x + rr • δ, s)) (δ, (0 : ℝ)) 0 := by
      simpa using (hasDerivAt_line x δ).prodMk (hasDerivAt_const (0 : ℝ) s)
    simpa [heX, ContinuousLinearMap.inl_apply] using this
  have hcompLine :
      HasDerivAt (fun rr : ℝ => fderiv ℝ Φ (x + rr • δ, s) eT) (B eX eT) 0 := by
    have h1 : HasDerivAt (fun rr : ℝ => fderiv ℝ Φ (x + rr • δ, s)) (B eX) 0 :=
      hsndHas.comp_hasDerivAt_of_eq 0 hlineCurve (by simp)
    have := (ContinuousLinearMap.apply ℝ E eT).hasFDerivAt.comp_hasDerivAt 0 h1
    simpa [ContinuousLinearMap.apply_apply] using this
  have hball_open : IsOpen {rr : ℝ | (x + rr • δ) ∈ ball x₀ (r : ℝ)} :=
    (isOpen_ball).preimage (by fun_prop)
  have hball_mem : (0 : ℝ) ∈ {rr : ℝ | (x + rr • δ) ∈ ball x₀ (r : ℝ)} := by
    simpa using hx
  have hUline_open : IsOpen {rr : ℝ | (x + rr • δ, s) ∈ U} :=
    hUopen.preimage (by fun_prop)
  have hUline_mem : (0 : ℝ) ∈ {rr : ℝ | (x + rr • δ, s) ∈ U} := by simpa using hxsU
  have hEqLine : (fun rr : ℝ => fderiv ℝ Φ (x + rr • δ, s) eT)
      =ᶠ[𝓝 0] (fun rr : ℝ => f s (Φ (x + rr • δ, s))) := by
    filter_upwards [hball_open.mem_nhds hball_mem, hUline_open.mem_nhds hUline_mem]
      with rr hrr hrrU
    have hxb : (x + rr • δ) ∈ closedBall x₀ (r : ℝ) := ball_subset_closedBall hrr
    have hdiff : DifferentiableAt ℝ Φ (x + rr • δ, s) := hΦ_diffOn _ hrrU
    simpa [heT] using flow_joint_fderiv_inr_eq hΦ hxb hs hdiff
  have hRHSline :
      HasDerivAt (fun rr : ℝ => f s (Φ (x + rr • δ, s))) (B eX eT) 0 :=
    hEqLine.hasDerivAt_iff.mp hcompLine
  have hRHSchain :
      HasDerivAt (fun rr : ℝ => f s (Φ (x + rr • δ, s)))
        (fderiv ℝ (f s) (Φ (x, s)) (fderiv ℝ (fun y => Φ (y, s)) x δ)) 0 := by
    have hfs_diff : DifferentiableAt ℝ (f s) (Φ (x, s)) := by
      have : ContDiffAt ℝ ∞ (f s) (Φ (x, s)) := by
        have hcd : ContDiffAt ℝ ∞ (uncurry f) (s, Φ (x, s)) :=
          hf.contDiffAt
        exact hcd.comp _ (contDiffAt_const.prodMk contDiffAt_id)
      exact this.differentiableAt (by simp)
    have hinner : HasDerivAt (fun rr : ℝ => Φ (x + rr • δ, s))
        (fderiv ℝ (fun y => Φ (y, s)) x δ) 0 := by
      have hsliceDiff : DifferentiableAt ℝ (fun y => Φ (y, s)) x :=
        (hΦ_diffOn _ hxsU).comp x (differentiableAt_id.prodMk (differentiableAt_const s))
      have hsliceHas : HasFDerivAt (fun y => Φ (y, s))
          (fderiv ℝ (fun y => Φ (y, s)) x) x := hsliceDiff.hasFDerivAt
      have := hsliceHas.comp_hasDerivAt_of_eq 0 (hasDerivAt_line x δ) (by simp)
      simpa using this
    have := hfs_diff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hinner (by simp)
    simpa using this
  have hBval : B eX eT
      = fderiv ℝ (f s) (Φ (x, s)) (fderiv ℝ (fun y => Φ (y, s)) x δ) :=
    hRHSline.unique hRHSchain
  rw [hswap, hBval] at hLHS
  exact hLHS

end PerDirection

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem IsLocalFlow.hasDerivAt_partial_spatial_fderiv
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiff ℝ ∞ (uncurry f))
    {U : Set (E × ℝ)} (hUopen : IsOpen U) (hΦsmooth : ContDiffOn ℝ ∞ Φ U)
    {x : E} {s : ℝ} (hxsU : (x, s) ∈ U)
    (hx : x ∈ ball x₀ r) (hs : s ∈ Ioo tmin tmax) :
    HasDerivAt (fun u : ℝ => fderiv ℝ (fun y => Φ (y, u)) x)
      ((fderiv ℝ (f s) (Φ (x, s))).comp (fderiv ℝ (fun y => Φ (y, s)) x)) s := by
  have hΦ_at : ∀ q ∈ U, ContDiffAt ℝ ∞ Φ q := fun q hq => contDiffAt_of_mem hUopen hΦsmooth hq
  have hΦ_xs : ContDiffAt ℝ ∞ Φ (x, s) := hΦ_at _ hxsU
  have hΦ_diffOn : ∀ q ∈ U, DifferentiableAt ℝ Φ q := fun q hq =>
    (hΦ_at q hq).differentiableAt (by simp)
  set Lsp : E × ℝ → (E →L[ℝ] E) :=
    fun q => (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ) with hLsp
  have hfderivSmooth : ContDiffAt ℝ ∞ (fderiv ℝ Φ) (x, s) :=
    hΦ_xs.fderiv_right (m := ∞) (by simp)
  have hLspSmooth : ContDiffAt ℝ ∞ Lsp (x, s) := by
    have hpost : ContDiffAt ℝ ∞
        (fun L : E × ℝ →L[ℝ] E => L.comp (ContinuousLinearMap.inl ℝ E ℝ)) (fderiv ℝ Φ (x, s)) :=
      (ContinuousLinearMap.compL ℝ E (E × ℝ) E |>.flip
        (ContinuousLinearMap.inl ℝ E ℝ)).contDiff.contDiffAt
    exact hpost.comp _ hfderivSmooth
  have hLspTime : ContDiffAt ℝ ∞ (fun u : ℝ => Lsp (x, u)) s :=
    hLspSmooth.comp s (contDiffAt_const.prodMk contDiffAt_id)
  have hLspTimeDiff : DifferentiableAt ℝ (fun u : ℝ => Lsp (x, u)) s :=
    hLspTime.differentiableAt (by simp)
  set D' : E →L[ℝ] E := deriv (fun u : ℝ => Lsp (x, u)) s with hD'
  have hLspDeriv : HasDerivAt (fun u : ℝ => Lsp (x, u)) D' s := hLspTimeDiff.hasDerivAt
  have hUx_open : IsOpen {u : ℝ | (x, u) ∈ U} := hUopen.preimage (by fun_prop)
  have hSliceEq : (fun u : ℝ => Lsp (x, u))
      =ᶠ[𝓝 s] (fun u : ℝ => fderiv ℝ (fun y => Φ (y, u)) x) := by
    filter_upwards [hUx_open.mem_nhds (show s ∈ {u : ℝ | (x, u) ∈ U} from hxsU)] with u hu
    rw [hLsp, partial_spatial_fderiv_eq_comp_inl (hΦ_diffOn _ hu)]
  have hSliceDeriv : HasDerivAt (fun u : ℝ => fderiv ℝ (fun y => Φ (y, u)) x) D' s :=
    hSliceEq.hasDerivAt_iff.mp hLspDeriv
  set RHS : E →L[ℝ] E :=
    (fderiv ℝ (f s) (Φ (x, s))).comp (fderiv ℝ (fun y => Φ (y, s)) x) with hRHS
  have hDeq : D' = RHS := by
    apply ContinuousLinearMap.ext
    intro δ
    have hcurveδ : HasDerivAt (fun u : ℝ => fderiv ℝ (fun y => Φ (y, u)) x δ) (D' δ) s := by
      have := (ContinuousLinearMap.apply ℝ E δ).hasFDerivAt.comp_hasDerivAt s hSliceDeriv
      simpa [ContinuousLinearMap.apply_apply] using this
    have hvarδ := IsLocalFlow.hasDerivAt_partial_spatial_fderiv_apply hΦ hf hUopen hΦsmooth
      hxsU hx hs δ
    have := hcurveδ.unique hvarδ
    rw [this, hRHS, ContinuousLinearMap.comp_apply]
  rw [← hDeq]
  exact hSliceDeriv

end DifferentialGeometry.Analysis.ODE.Flow
