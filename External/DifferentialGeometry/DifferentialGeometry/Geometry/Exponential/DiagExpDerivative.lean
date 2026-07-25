import DifferentialGeometry.Geometry.Exponential.DiagInvBranch
import DifferentialGeometry.Geometry.Exponential.ExpVariationSmooth
import DifferentialGeometry.Geometry.Exponential.Smoothness.IntrinsicMfderivZero
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Analysis.ODE.PhaseFlowPerturbation
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
































noncomputable section

open Set Function Filter Metric Bundle Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

section DiagExpDerivative

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


private def chartedDiagExp
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) : E × E → E × E :=
  extChartAt (I.prod I) (diagExp (I := I) g hEnorm (⟨p, (0 : E)⟩ : TangentBundle I M)) ∘
    diagExp (I := I) g hEnorm ∘
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

private def diagExpZeroPt (p : M) : E × E :=
  extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)
    (⟨p, (0 : E)⟩ : TangentBundle I M)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [ConnectedSpace M] in
private lemma chartedDiagExp_contDiffAt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (n : ℕ) (hn : 1 ≤ n) :
    ContDiffAt ℝ (n : ℕ∞) (chartedDiagExp (I := I) g hEnorm p)
      (diagExpZeroPt (I := I) p) := by
  classical
  have hmd := diagExp_contMDiffAt_zero (I := I) g hEnorm p n hn
  rw [contMDiffAt_iff] at hmd
  obtain ⟨_, hcd⟩ := hmd
  have hrange : range (I.tangent) = (univ : Set (E × E)) :=
    ModelWithCorners.Boundaryless.range_eq_univ
  rw [hrange] at hcd
  exact contDiffWithinAt_univ.mp hcd

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
private lemma diagExp_zero_eq
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    diagExp (I := I) g hEnorm (⟨p, (0 : E)⟩ : TangentBundle I M) = (p, p) := by
  rw [diagExp_apply]
  refine Prod.ext rfl ?_
  change expMapIntrinsic (I := I) g hEnorm p 0 = p
  exact expMapIntrinsic_zero (I := I) g hEnorm p

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] in
private lemma diagExpZeroPt_eq [T2Space (TangentBundle I M)] (p : M) :
    diagExpZeroPt (I := I) p = ((extChartAt I p p, (0 : E)) : E × E) := by
  classical
  rw [diagExpZeroPt]
  rw [extChartAt_tangent_zero_apply_chartFiber (I := I) p
    (p := (⟨p, (0 : E)⟩ : TangentBundle I M)) (by exact mem_chart_source H p)]
  change ((extChartAt I p p, chartFiberCoord (I := I) p (⟨p, (0 : E)⟩ : TangentBundle I M)) : E × E)
    = ((extChartAt I p p, (0 : E)) : E × E)
  rw [chartFiberCoord_self_zero (I := I) p]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [ConnectedSpace M] in
private lemma exists_chartDiagInf
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ U : Set (E × E), IsOpen U ∧ diagExpZeroPt (I := I) p ∈ U ∧
      ContDiffOn ℝ ∞ (chartedDiagExp (I := I) g hEnorm p) U := by
  classical
  obtain ⟨Φ, ρ, T, t', hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd,
    hΦ_init, hΦ_ode, hΦ_target, _hΦ_cd⟩ :=
    exists_chartExp_jointContDiffOn_infty (I := I) g p
  set ctr : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hctr_def
  set R : E × E → E × E := fun z => (z.1, t'⁻¹ • z.2) with hR_def
  set G : E × E → E := fun z => (Φ ((z, t') : (E × E) × ℝ)).1 with hG_def
  set U : Set (E × E) := R ⁻¹' Metric.ball ctr ρ with hU_def
  have hReq : R = ⇑((ContinuousLinearMap.fst ℝ E E).prod
      (t'⁻¹ • ContinuousLinearMap.snd ℝ E E)) := by
    funext z
    rw [hR_def]
    simp
  have hR_cd : ContDiff ℝ ∞ R := by
    rw [hReq]
    exact ContinuousLinearMap.contDiff _
  have hU_open : IsOpen U := by
    rw [hU_def]
    exact Metric.isOpen_ball.preimage hR_cd.continuous
  have hRctr : R ctr = ctr := by
    rw [hR_def, hctr_def]
    simp
  have hctr_ball : ctr ∈ Metric.ball ctr ρ := Metric.mem_ball_self hρ_pos
  have hcU : diagExpZeroPt (I := I) p ∈ U := by
    rw [hU_def, diagExpZeroPt_eq (I := I) p]
    change R ctr ∈ Metric.ball ctr ρ
    rw [hRctr]
    exact hctr_ball
  have hGR_cd : ContDiffOn ℝ ∞ (fun z => G (R z)) U := by
    apply hG_cd.comp hR_cd.contDiffOn
    intro z hz
    exact hz
  have hmodel_cd : ContDiffOn ℝ ∞ (fun z : E × E => (z.1, G (R z))) U :=
    contDiff_fst.contDiffOn.prodMk hGR_cd
  refine ⟨U, hU_open, hcU, hmodel_cd.congr ?_⟩
  intro z hz
  have hRz_ball : R z ∈ Metric.ball ctr ρ := hz
  have hzero_Icc : (0 : ℝ) ∈ Set.Icc (-T) T := by
    constructor <;> linarith
  have hRz_target := hΦ_target (R z) hRz_ball 0 hzero_Icc
  rw [hΦ_init (R z) hRz_ball] at hRz_target
  have hz_target : z ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    refine ⟨?_, Set.mem_univ _⟩
    simpa [hR_def] using hRz_target.1
  set u : TangentBundle I M :=
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm z with hu_def
  have hu_proj_src : u.proj ∈ (chartAt H p).source := by
    rw [hu_def]
    exact chartAt_source_of_extChartAt_tangent_zero_symm (I := I) p hz_target
  have hchart_u :
      extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) u = z := by
    rw [hu_def]
    exact extChartAt_tangent_zero_apply_symm (I := I) p hz_target
  have hscaled : chartFiberCoord (I := I) p
        (⟨u.proj, t'⁻¹ • u.snd⟩ : TangentBundle I M) =
      t'⁻¹ • chartFiberCoord (I := I) p u :=
    chartFiberCoord_fiberScale (I := I) p (t'⁻¹) (q := u) hu_proj_src
  have hphase : ((extChartAt I p u.proj,
        chartFiberCoord (I := I) p
          (⟨u.proj, t'⁻¹ • u.snd⟩ : TangentBundle I M)) : E × E) = R z := by
    rw [hscaled, ← hchart_u,
      extChartAt_tangent_zero_apply_chartFiber (I := I) p (p := u) hu_proj_src, hR_def]
  have hG_cd_one : ContDiffOn ℝ (1 : ℕ∞) G (Metric.ball ctr ρ) :=
    hG_cd.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hbridge := expMapIntrinsic_eq_chartFlow_proj_residual (I := I) g hEnorm p
    1 le_rfl Φ ρ T t'
    ⟨hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd_one, hΦ_init, hΦ_ode, hΦ_target⟩
    u.proj hu_proj_src u.snd (hphase.symm ▸ hRz_ball)
  rw [hphase] at hbridge
  have hu_proj : u.proj = (extChartAt I p).symm z.1 := by
    rw [hu_def]
    exact extChartAt_tangent_zero_symm_proj (I := I) p hz_target
  have hdiag : diagExp (I := I) g hEnorm u =
      ((extChartAt I p).symm z.1, (extChartAt I p).symm (G (R z))) := by
    rw [diagExp_apply, hu_proj]
    exact Prod.ext rfl (by simpa [hG_def] using hbridge)
  have ht'_Icc : t' ∈ Set.Icc (-T) T := Set.Ioo_subset_Icc_self ht'_Ioo
  have hG_target : G (R z) ∈ (extChartAt I p).target := by
    have hmem := hΦ_target (R z) hRz_ball t' ht'_Icc
    exact interior_subset (by simpa [hG_def] using hmem.1)
  have hz1_target : z.1 ∈ (extChartAt I p).target := interior_subset hz_target.1
  simp only [chartedDiagExp, Function.comp_apply]
  rw [show (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm z = u
      from hu_def.symm,
    hdiag, diagExp_zero_eq (I := I) g hEnorm p, extChartAt_prod]
  simp only [PartialEquiv.prod_coe]
  rw [(extChartAt I p).right_inv hz1_target, (extChartAt I p).right_inv hG_target]




omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] in
private lemma chartFiberCoord_mk_zero (p q : M)
    (hq : q ∈ (chartAt H p).source) :
    chartFiberCoord (I := I) p (⟨q, (0 : E)⟩ : TangentBundle I M) = 0 := by
  classical
  have hq_base : q ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hq
  have hzero := (trivializationAt E (TangentSpace I) p).zeroSection ℝ (x := q) hq_base
  have hzero' : (trivializationAt E (TangentSpace I) p)
      (⟨q, (0 : TangentSpace I q)⟩ : TangentBundle I M) = (q, 0) := hzero
  change (trivializationAt E (TangentSpace I) p
      (⟨q, (0 : TangentSpace I q)⟩ : TangentBundle I M)).2 = 0
  rw [hzero']

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] in
private lemma extChartAt_tangent_zero_symm_zero_fiber
    [T2Space (TangentBundle I M)] (p : M) {z : E × E}
    (hz : z ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hz2 : z.2 = 0) :
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm z =
      (⟨(extChartAt I p).symm z.1, (0 : E)⟩ : TangentBundle I M) := by
  classical
  set q : M := (extChartAt I p).symm z.1 with hq_def
  have hz1_target : z.1 ∈ (extChartAt I p).target := interior_subset hz.1
  have hq_src : q ∈ (chartAt H p).source := by
    rw [hq_def, ← extChartAt_source I]; exact (extChartAt I p).map_target hz1_target

  have hchart_zero : extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)
      (⟨q, (0 : E)⟩ : TangentBundle I M) = z := by
    rw [extChartAt_tangent_zero_apply_chartFiber (I := I) p
      (p := (⟨q, (0 : E)⟩ : TangentBundle I M)) (by exact hq_src)]
    rw [chartFiberCoord_mk_zero (I := I) p q hq_src]
    have hz1 : extChartAt I p q = z.1 := by
      rw [hq_def, (extChartAt I p).right_inv hz1_target]
    rw [hz1, ← hz2]

  have hsymm := congrArg
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm hchart_zero
  rw [(extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).left_inv
    (by rw [extChartAt_source];
        exact (mem_chartAt_modelProd_zero_source_iff (I := I) p _).mpr hq_src)] at hsymm
  rw [← hsymm]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] in
private lemma extChartAt_tangent_zero_symm_at_base
    [T2Space (TangentBundle I M)] (p : M) {z : E × E}
    (hz : z ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hz1 : z.1 = extChartAt I p p) :
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm z =
      (⟨p, z.2⟩ : TangentBundle I M) := by
  classical
  set u : TangentBundle I M :=
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm z with hu_def
  have hproj : u.proj = p := by
    rw [hu_def, extChartAt_tangent_zero_symm_proj (I := I) p hz, hz1]
    exact (extChartAt I p).left_inv (mem_extChartAt_source (I := I) p)
  have hsrc : u.proj ∈ (chartAt H p).source := by
    rw [hproj]; exact mem_chart_source H p
  have happly : extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) u = z :=
    extChartAt_tangent_zero_apply_symm (I := I) p hz
  have hpair := extChartAt_tangent_zero_apply_chartFiber (I := I) p (p := u) hsrc
  rw [happly] at hpair
  have hfib : chartFiberCoord (I := I) p u = z.2 := by
    have := congrArg Prod.snd hpair
    exact this.symm

  have hu_eq : u = (⟨u.proj, u.snd⟩ : TangentBundle I M) := rfl
  have hmk : chartFiberCoord (I := I) p (⟨p, u.snd⟩ : TangentBundle I M) = u.snd :=
    chartFiberCoord_mk_self (I := I) p u.snd
  have hsnd : u.snd = z.2 := by
    have hfib' : chartFiberCoord (I := I) p (⟨p, u.snd⟩ : TangentBundle I M) = z.2 := by
      rw [← hfib]; congr 1; rw [← hproj]
    rw [← hmk, hfib']

  calc u = (⟨u.proj, u.snd⟩ : TangentBundle I M) := rfl
    _ = (⟨p, z.2⟩ : TangentBundle I M) := by rw [hproj, hsnd]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

private def chartedExpIntrinsic
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) : E → E :=
  fun v => extChartAt I p (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



omit [ConnectedSpace M] in
private lemma chartedExpIntrinsic_hasFDerivAt_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    HasFDerivAt (chartedExpIntrinsic (I := I) g hEnorm p)
      (ContinuousLinearMap.id ℝ E) (0 : E) := by
  classical
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))

  have hdiff : MDifferentiableAt 𝓘(ℝ, E) I
      (fun v : E => (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v) : M))
      (0 : E) := by
    by_contra hcon
    have h0 := mfderiv_expMapIntrinsic_at_zero (I := I) g hEnorm p
    rw [mfderiv_zero_of_not_mdifferentiableAt hcon] at h0
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have hvz : (0 : E) = v := by simpa using DFunLike.congr_fun h0 v
    exact hv hvz.symm
  have hexp_mfd : HasMFDerivAt 𝓘(ℝ, E) I
      (fun v : E => (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v) : M))
      (0 : E) (ContinuousLinearMap.id ℝ E) := by
    have h := hdiff.hasMFDerivAt
    rwa [mfderiv_expMapIntrinsic_at_zero (I := I) g hEnorm p] at h

  have hpt : (fun v : E => (expMapIntrinsic (I := I) g hEnorm p
      (show TangentSpace I p from v) : M)) 0 = p := by
    change expMapIntrinsic (I := I) g hEnorm p 0 = p
    exact expMapIntrinsic_zero (I := I) g hEnorm p
  have hext_hasMFD : HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I p) p
      (ContinuousLinearMap.id ℝ E) := by
    have hm := ((contMDiffAt_extChartAt (I := I) (x := p) (n := 1)).mdifferentiableAt
      one_ne_zero).hasMFDerivAt
    rw [mfderiv_extChartAt_self (I := I) (x := p)] at hm
    exact hm
  have hext_at_pt : HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I p)
      ((fun v : E => (expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from v) : M)) 0) (ContinuousLinearMap.id ℝ E) := by
    rw [hpt]; exact hext_hasMFD
  have hcomp_mfd : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      ((extChartAt I p) ∘
        (fun v : E => (expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from v) : M)))
      (0 : E) ((ContinuousLinearMap.id ℝ E).comp (ContinuousLinearMap.id ℝ E)) :=
    hext_at_pt.comp (0 : E) hexp_mfd
  rw [ContinuousLinearMap.id_comp] at hcomp_mfd
  exact hasMFDerivAt_iff_hasFDerivAt.mp hcomp_mfd

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in










omit [ConnectedSpace M] in
theorem diagExp_hasFDerivAt_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (n : ℕ) (hn : 1 ≤ n) :
    HasFDerivAt (chartedDiagExp (I := I) g hEnorm p)
      ((ContinuousLinearMap.fst ℝ E E).prod
        (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E))
      (diagExpZeroPt (I := I) p) := by
  classical
  rw [diagExpZeroPt_eq (I := I) p]
  set c : E := extChartAt I p p with hc_def

  have hc_int : c ∈ interior (extChartAt I p).target := by
    rw [hc_def]
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) p ((extChartAt I p).map_source (mem_extChartAt_source (I := I) p))

  have hcd := chartedDiagExp_contDiffAt (I := I) g hEnorm p n hn
  rw [diagExpZeroPt_eq (I := I) p] at hcd
  have hD : HasFDerivAt (chartedDiagExp (I := I) g hEnorm p)
      (fderiv ℝ (chartedDiagExp (I := I) g hEnorm p) ((c, (0 : E)) : E × E))
      ((c, (0 : E)) : E × E) :=
    (hcd.differentiableAt (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn)).hasFDerivAt
  set D := fderiv ℝ (chartedDiagExp (I := I) g hEnorm p) ((c, (0 : E)) : E × E) with hD_def

  have hbase_eq : (fun z₁ : E => chartedDiagExp (I := I) g hEnorm p ((z₁, (0 : E)) : E × E))
      =ᶠ[𝓝 c] (fun z₁ : E => ((z₁, z₁) : E × E)) := by
    filter_upwards [isOpen_interior.mem_nhds hc_int] with z₁ hz₁int
    have hz1t : z₁ ∈ (extChartAt I p).target := interior_subset hz₁int
    have hz : ((z₁, (0 : E)) : E × E) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := ⟨hz₁int, Set.mem_univ _⟩
    have hinner : diagExp (I := I) g hEnorm
          ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm ((z₁, (0 : E)) : E × E))
        = ((extChartAt I p).symm z₁, (extChartAt I p).symm z₁) := by
      rw [extChartAt_tangent_zero_symm_zero_fiber (I := I) p hz rfl, diagExp_apply]
      exact Prod.ext rfl (expMapIntrinsic_zero (I := I) g hEnorm _)
    simp only [chartedDiagExp, Function.comp_apply]
    rw [hinner, diagExp_zero_eq (I := I) g hEnorm p, extChartAt_prod]
    simp only [PartialEquiv.prod_coe]
    rw [(extChartAt I p).right_inv hz1t]

  have hfiber_eq : (fun z₂ : E => chartedDiagExp (I := I) g hEnorm p ((c, z₂) : E × E))
      =ᶠ[𝓝 (0 : E)] (fun z₂ : E => ((c, chartedExpIntrinsic (I := I) g hEnorm p z₂) : E × E)) := by
    filter_upwards with z₂
    have hz : ((c, z₂) : E × E) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := ⟨hc_int, Set.mem_univ _⟩
    have hinner : diagExp (I := I) g hEnorm
          ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm ((c, z₂) : E × E))
        = (p, expMapIntrinsic (I := I) g hEnorm p z₂) := by
      rw [extChartAt_tangent_zero_symm_at_base (I := I) p hz hc_def, diagExp_apply]
    simp only [chartedDiagExp, Function.comp_apply]
    rw [hinner, diagExp_zero_eq (I := I) g hEnorm p, extChartAt_prod]
    simp only [PartialEquiv.prod_coe]
    exact Prod.ext hc_def.symm rfl

  have hinl : D.comp ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E))
      = (ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E) := by
    have haff : HasFDerivAt (fun z₁ : E => ((z₁, (0 : E)) : E × E))
        ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E)) c :=
      (hasFDerivAt_id c).prodMk (hasFDerivAt_const (0 : E) c)
    have hc1 := hD.comp c haff
    have hid : HasFDerivAt (fun z₁ : E => ((z₁, z₁) : E × E))
        ((ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)) c :=
      (hasFDerivAt_id c).prodMk (hasFDerivAt_id c)
    exact (hc1.congr_of_eventuallyEq hbase_eq.symm).unique hid
  have hinr : D.comp ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E))
      = (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E) := by
    have haff : HasFDerivAt (fun z₂ : E => ((c, z₂) : E × E))
        ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) (0 : E) :=
      (hasFDerivAt_const c (0 : E)).prodMk (hasFDerivAt_id (0 : E))
    have hc2 := hD.comp (0 : E) haff
    have hpair : HasFDerivAt (fun z₂ : E => ((c, chartedExpIntrinsic (I := I) g hEnorm p z₂) : E × E))
        ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) (0 : E) :=
      (hasFDerivAt_const c (0 : E)).prodMk (chartedExpIntrinsic_hasFDerivAt_zero (I := I) g hEnorm p)
    exact (hc2.congr_of_eventuallyEq hfiber_eq.symm).unique hpair

  have hDL : D = (ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) := by
    apply ContinuousLinearMap.ext
    rintro ⟨a, b⟩
    have hsplit : ((a, b) : E × E) =
        ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E)) a +
          ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) b := by
      simp
    rw [hsplit, map_add, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
      hinl, hinr]
    simp
  rw [← hDL]; exact hD



def unipotentCLE : (E × E) ≃L[ℝ] (E × E) :=
  DifferentialGeometry.PhaseFlow.freeDiagCLE

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [ConnectedSpace M] in
theorem diagExp_hasFDerivAt_zero_unipotent
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (n : ℕ) (hn : 1 ≤ n) :
    HasFDerivAt (chartedDiagExp (I := I) g hEnorm p)
      (unipotentCLE (E := E) : (E × E) →L[ℝ] (E × E)) (diagExpZeroPt (I := I) p) :=
  diagExp_hasFDerivAt_zero (I := I) g hEnorm p n hn











attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [ConnectedSpace M] in
private lemma chartedDiagExp_cdaOne
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ContDiffAt ℝ 1 (chartedDiagExp (I := I) g hEnorm p) (diagExpZeroPt (I := I) p) := by
  simpa using chartedDiagExp_contDiffAt (I := I) g hEnorm p 1 le_rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


private def diagExpIFT
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) : OpenPartialHomeomorph (E × E) (E × E) :=
  ContDiffAt.toOpenPartialHomeomorph (𝕂 := ℝ)
    (f := chartedDiagExp (I := I) g hEnorm p)
    (f' := unipotentCLE (E := E))
    (chartedDiagExp_cdaOne (I := I) g hEnorm p)
    (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl)
    one_ne_zero

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
private lemma diagExpIFT_coe
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ⇑(diagExpIFT (I := I) g hEnorm p) = chartedDiagExp (I := I) g hEnorm p := rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [ConnectedSpace M] in
private lemma exists_chartInvInf
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ V : Set (E × E), IsOpen V ∧
      chartedDiagExp (I := I) g hEnorm p (diagExpZeroPt (I := I) p) ∈ V ∧
      ContDiffOn ℝ ∞ (diagExpIFT (I := I) g hEnorm p).symm V ∧
      ∀ y ∈ V,
        y ∈ (diagExpIFT (I := I) g hEnorm p).target ∧
        (diagExpIFT (I := I) g hEnorm p).symm y ∈
          (extChartAt I.tangent
            (⟨p, (0 : E)⟩ : TangentBundle I M)).target := by
  classical
  obtain ⟨U, hU_open, hcU, hfU⟩ := exists_chartDiagInf (I := I) g hEnorm p
  have hf_at : ContDiffAt ℝ ∞ (chartedDiagExp (I := I) g hEnorm p)
      (diagExpZeroPt (I := I) p) :=
    hfU.contDiffAt (hU_open.mem_nhds hcU)
  have hfd_eq : fderiv ℝ (chartedDiagExp (I := I) g hEnorm p)
        (diagExpZeroPt (I := I) p) =
      (unipotentCLE (E := E) : (E × E) →L[ℝ] (E × E)) :=
    (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl).fderiv
  have hinv_nhds :
      {L : (E × E) →L[ℝ] (E × E) | ∃ e : (E × E) ≃L[ℝ] (E × E), e = L} ∈
        𝓝 (fderiv ℝ (chartedDiagExp (I := I) g hEnorm p)
          (diagExpZeroPt (I := I) p)) := by
    rw [hfd_eq]
    exact (unipotentCLE (E := E)).nhds
  have hfd_cont : ContinuousAt
      (fderiv ℝ (chartedDiagExp (I := I) g hEnorm p))
      (diagExpZeroPt (I := I) p) :=
    hf_at.continuousAt_fderiv (by simp)
  have hinv_ev : ∀ᶠ x in 𝓝 (diagExpZeroPt (I := I) p),
      ∃ e : (E × E) ≃L[ℝ] (E × E),
        e = fderiv ℝ (chartedDiagExp (I := I) g hEnorm p) x :=
    hfd_cont.preimage_mem_nhds hinv_nhds
  have hsrc : diagExpZeroPt (I := I) p ∈
      (diagExpIFT (I := I) g hEnorm p).source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source
      (chartedDiagExp_cdaOne (I := I) g hEnorm p)
      (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl) one_ne_zero
  have hinner_target : diagExpZeroPt (I := I) p ∈
      (extChartAt I.tangent
        (⟨p, (0 : E)⟩ : TangentBundle I M)).target :=
    (extChartAt I.tangent
      (⟨p, (0 : E)⟩ : TangentBundle I M)).map_source
        (mem_extChartAt_source (I := I.tangent)
          (⟨p, (0 : E)⟩ : TangentBundle I M))
  have hgood : ∀ᶠ x in 𝓝 (diagExpZeroPt (I := I) p),
      x ∈ U ∧ x ∈ (diagExpIFT (I := I) g hEnorm p).source ∧
      x ∈ (extChartAt I.tangent
        (⟨p, (0 : E)⟩ : TangentBundle I M)).target ∧
      ∃ e : (E × E) ≃L[ℝ] (E × E),
        e = fderiv ℝ (chartedDiagExp (I := I) g hEnorm p) x := by
    filter_upwards [hU_open.mem_nhds hcU,
      (diagExpIFT (I := I) g hEnorm p).open_source.mem_nhds hsrc,
      extChartAt_target_mem_nhds' (I := I.tangent) hinner_target,
      hinv_ev] with x hxU hxsrc hxtarget hxe
    exact ⟨hxU, hxsrc, hxtarget, hxe⟩
  obtain ⟨W, hW, hW_open, hcW⟩ := _root_.mem_nhds_iff.mp hgood
  set V : Set (E × E) :=
    (diagExpIFT (I := I) g hEnorm p).target ∩
      (diagExpIFT (I := I) g hEnorm p).symm ⁻¹' W with hV_def
  have hV_open : IsOpen V := by
    rw [hV_def]
    exact (diagExpIFT (I := I) g hEnorm p).isOpen_inter_preimage_symm hW_open
  have hcenter_target : chartedDiagExp (I := I) g hEnorm p
        (diagExpZeroPt (I := I) p) ∈
      (diagExpIFT (I := I) g hEnorm p).target := by
    have h := (diagExpIFT (I := I) g hEnorm p).map_source hsrc
    rwa [diagExpIFT_coe (I := I) g hEnorm p] at h
  have hcenterV : chartedDiagExp (I := I) g hEnorm p
      (diagExpZeroPt (I := I) p) ∈ V := by
    rw [hV_def]
    refine ⟨hcenter_target, ?_⟩
    have hleft := (diagExpIFT (I := I) g hEnorm p).left_inv hsrc
    rw [diagExpIFT_coe (I := I) g hEnorm p] at hleft
    change (diagExpIFT (I := I) g hEnorm p).symm
      (chartedDiagExp (I := I) g hEnorm p (diagExpZeroPt (I := I) p)) ∈ W
    rw [hleft]
    exact hcW
  have hsymm : ContDiffOn ℝ ∞ (diagExpIFT (I := I) g hEnorm p).symm V := by
    intro y hy
    have hxgood := hW hy.2
    obtain ⟨hxU, _hxsrc, _hxtarget, e, he⟩ := hxgood
    have hforward : ContDiffAt ℝ ∞ (chartedDiagExp (I := I) g hEnorm p)
        ((diagExpIFT (I := I) g hEnorm p).symm y) :=
      hfU.contDiffAt (hU_open.mem_nhds hxU)
    have hderiv : HasFDerivAt (chartedDiagExp (I := I) g hEnorm p)
        (e : (E × E) →L[ℝ] (E × E))
        ((diagExpIFT (I := I) g hEnorm p).symm y) := by
      rw [he]
      exact (hforward.differentiableAt (by simp)).hasFDerivAt
    have hderiv_ift : HasFDerivAt (diagExpIFT (I := I) g hEnorm p)
        (e : (E × E) →L[ℝ] (E × E))
        ((diagExpIFT (I := I) g hEnorm p).symm y) := by
      rw [diagExpIFT_coe (I := I) g hEnorm p]
      exact hderiv
    have hforward_ift : ContDiffAt ℝ ∞ (diagExpIFT (I := I) g hEnorm p)
        ((diagExpIFT (I := I) g hEnorm p).symm y) := by
      rw [diagExpIFT_coe (I := I) g hEnorm p]
      exact hforward
    exact ((diagExpIFT (I := I) g hEnorm p).contDiffAt_symm
      hy.1 hderiv_ift hforward_ift).contDiffWithinAt
  refine ⟨V, hV_open, hcenterV, hsymm, ?_⟩
  intro y hy
  have hxgood := hW hy.2
  exact ⟨hy.1, hxgood.2.2.1⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] in
private lemma inner_symm_zeroPt
    [T2Space (TangentBundle I M)] (p : M) :
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm (diagExpZeroPt (I := I) p)
      = (⟨p, (0 : E)⟩ : TangentBundle I M) := by
  rw [diagExpZeroPt]
  exact (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).left_inv
    (mem_extChartAt_source (I := I.tangent) (⟨p, (0 : E)⟩ : TangentBundle I M))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [ConnectedSpace M] in
private lemma outer_center
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    extChartAt (I.prod I) (p, p) (p, p) =
      chartedDiagExp (I := I) g hEnorm p (diagExpZeroPt (I := I) p) := by
  change extChartAt (I.prod I) (p, p) (p, p)
    = extChartAt (I.prod I) (diagExp (I := I) g hEnorm (⟨p, (0 : E)⟩ : TangentBundle I M))
        (diagExp (I := I) g hEnorm
          ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
            (diagExpZeroPt (I := I) p)))
  rw [inner_symm_zeroPt (I := I) p, diagExp_zero_eq (I := I) g hEnorm p]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





def diagExpInv
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) : M × M → TangentBundle I M :=
  fun y => (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
    ((diagExpIFT (I := I) g hEnorm p).symm (extChartAt (I.prod I) (p, p) y))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [ConnectedSpace M] in
theorem diagExpInv_center
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    diagExpInv (I := I) g hEnorm p (p, p) = (⟨p, (0 : E)⟩ : TangentBundle I M) := by
  have hsrc : diagExpZeroPt (I := I) p ∈ (diagExpIFT (I := I) g hEnorm p).source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source
      (chartedDiagExp_cdaOne (I := I) g hEnorm p)
      (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl) one_ne_zero
  change (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
      ((diagExpIFT (I := I) g hEnorm p).symm (extChartAt (I.prod I) (p, p) (p, p)))
      = (⟨p, (0 : E)⟩ : TangentBundle I M)
  rw [outer_center (I := I) g hEnorm p, ← diagExpIFT_coe (I := I) g hEnorm p,
    (diagExpIFT (I := I) g hEnorm p).left_inv hsrc, inner_symm_zeroPt (I := I) p]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
theorem diagExpInv_contMDiffAt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ContMDiffAt (I.prod I) I.tangent 1 (diagExpInv (I := I) g hEnorm p) (p, p) := by
  have hsrc : diagExpZeroPt (I := I) p ∈ (diagExpIFT (I := I) g hEnorm p).source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source
      (chartedDiagExp_cdaOne (I := I) g hEnorm p)
      (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl) one_ne_zero
  have hsymm_eq : (diagExpIFT (I := I) g hEnorm p).symm =
      (chartedDiagExp_cdaOne (I := I) g hEnorm p).localInverse
        (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl) one_ne_zero := rfl
  have hsymm_cd : ContDiffAt ℝ 1 (diagExpIFT (I := I) g hEnorm p).symm
      (chartedDiagExp (I := I) g hEnorm p (diagExpZeroPt (I := I) p)) := by
    rw [hsymm_eq]
    exact (chartedDiagExp_cdaOne (I := I) g hEnorm p).to_localInverse
      (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl) one_ne_zero
  have h_outer : ContMDiffAt (I.prod I) 𝓘(ℝ, E × E) 1
      (extChartAt (I.prod I) (p, p)) (p, p) :=
    contMDiffAt_extChartAt (I := I.prod I) (x := (p, p)) (n := 1)
  have h_mid : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E × E) 1
      (diagExpIFT (I := I) g hEnorm p).symm (extChartAt (I.prod I) (p, p) (p, p)) := by
    rw [outer_center (I := I) g hEnorm p]
    exact contMDiffAt_iff_contDiffAt.mpr hsymm_cd
  have hpt : (diagExpIFT (I := I) g hEnorm p).symm (extChartAt (I.prod I) (p, p) (p, p))
      = diagExpZeroPt (I := I) p := by
    rw [outer_center (I := I) g hEnorm p, ← diagExpIFT_coe (I := I) g hEnorm p]
    exact (diagExpIFT (I := I) g hEnorm p).left_inv hsrc
  have h_inner : ContMDiffAt 𝓘(ℝ, E × E) I.tangent 1
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
      ((diagExpIFT (I := I) g hEnorm p).symm (extChartAt (I.prod I) (p, p) (p, p))) := by
    rw [hpt]
    have hb : range (I.tangent) = (univ : Set (E × E)) :=
      ModelWithCorners.Boundaryless.range_eq_univ
    have hsm := contMDiffWithinAt_extChartAt_symm_range_self (I := I.tangent) (n := 1)
      (⟨p, (0 : E)⟩ : TangentBundle I M)
    rw [hb, contMDiffWithinAt_univ] at hsm
    exact hsm
  exact h_inner.comp (p, p) (h_mid.comp (p, p) h_outer)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in






omit [ConnectedSpace M] in
theorem diagExpInv_contMDiffAt_order
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (n : ℕ) (hn : 1 ≤ n) :
    ContMDiffAt (I.prod I) I.tangent (n : ℕ∞) (diagExpInv (I := I) g hEnorm p) (p, p) := by
  have hn0 : ((n : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hsymm_eq : (diagExpIFT (I := I) g hEnorm p).symm =
      (chartedDiagExp_contDiffAt (I := I) g hEnorm p n hn).localInverse
        (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl) hn0 := rfl
  have hsymm_cd : ContDiffAt ℝ (n : ℕ∞) (diagExpIFT (I := I) g hEnorm p).symm
      (chartedDiagExp (I := I) g hEnorm p (diagExpZeroPt (I := I) p)) := by
    rw [hsymm_eq]
    exact (chartedDiagExp_contDiffAt (I := I) g hEnorm p n hn).to_localInverse
      (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl) hn0
  have h_outer : ContMDiffAt (I.prod I) 𝓘(ℝ, E × E) (n : ℕ∞)
      (extChartAt (I.prod I) (p, p)) (p, p) :=
    contMDiffAt_extChartAt (I := I.prod I) (x := (p, p)) (n := (n : ℕ∞))
  have h_mid : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E × E) (n : ℕ∞)
      (diagExpIFT (I := I) g hEnorm p).symm (extChartAt (I.prod I) (p, p) (p, p)) := by
    rw [outer_center (I := I) g hEnorm p]
    exact contMDiffAt_iff_contDiffAt.mpr hsymm_cd
  have hpt : (diagExpIFT (I := I) g hEnorm p).symm (extChartAt (I.prod I) (p, p) (p, p))
      = diagExpZeroPt (I := I) p := by
    have hsrc : diagExpZeroPt (I := I) p ∈ (diagExpIFT (I := I) g hEnorm p).source :=
      ContDiffAt.mem_toOpenPartialHomeomorph_source
        (chartedDiagExp_cdaOne (I := I) g hEnorm p)
        (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl) one_ne_zero
    rw [outer_center (I := I) g hEnorm p, ← diagExpIFT_coe (I := I) g hEnorm p]
    exact (diagExpIFT (I := I) g hEnorm p).left_inv hsrc
  have h_inner : ContMDiffAt 𝓘(ℝ, E × E) I.tangent (n : ℕ∞)
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
      ((diagExpIFT (I := I) g hEnorm p).symm (extChartAt (I.prod I) (p, p) (p, p))) := by
    rw [hpt]
    have hb : range (I.tangent) = (univ : Set (E × E)) :=
      ModelWithCorners.Boundaryless.range_eq_univ
    have hsm := contMDiffWithinAt_extChartAt_symm_range_self (I := I.tangent) (n := (n : ℕ∞))
      (⟨p, (0 : E)⟩ : TangentBundle I M)
    rw [hb, contMDiffWithinAt_univ] at hsm
    exact hsm
  exact h_inner.comp (p, p) (h_mid.comp (p, p) h_outer)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



omit [ConnectedSpace M] in
theorem diagExp_diagExpInv
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∀ᶠ y in nhds (p, p),
      diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y) = y := by
  have hsrc : diagExpZeroPt (I := I) p ∈ (diagExpIFT (I := I) g hEnorm p).source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source
      (chartedDiagExp_cdaOne (I := I) g hEnorm p)
      (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl) one_ne_zero
  have htarget : chartedDiagExp (I := I) g hEnorm p (diagExpZeroPt (I := I) p)
      ∈ (diagExpIFT (I := I) g hEnorm p).target := by
    have h := (diagExpIFT (I := I) g hEnorm p).map_source hsrc
    rwa [diagExpIFT_coe (I := I) g hEnorm p] at h
  have hev_ri := (diagExpIFT (I := I) g hEnorm p).eventually_right_inverse htarget
  have htend : Filter.Tendsto (extChartAt (I.prod I) (p, p)) (nhds (p, p))
      (nhds (chartedDiagExp (I := I) g hEnorm p (diagExpZeroPt (I := I) p))) := by
    rw [← outer_center (I := I) g hEnorm p]
    exact (continuousAt_extChartAt (I := I.prod I) (p, p)).tendsto
  have hev1 := htend.eventually hev_ri
  have hev_y : ∀ᶠ y in nhds (p, p), y ∈ (extChartAt (I.prod I) (p, p)).source :=
    extChartAt_source_mem_nhds (I := I.prod I) (p, p)
  have hcont : ContinuousAt
      (fun y => diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y)) (p, p) := by
    have h1 : ContinuousAt (diagExpInv (I := I) g hEnorm p) (p, p) :=
      (diagExpInv_contMDiffAt (I := I) g hEnorm p).continuousAt
    have h2 : ContinuousAt (diagExp (I := I) g hEnorm)
        (diagExpInv (I := I) g hEnorm p (p, p)) := by
      rw [diagExpInv_center (I := I) g hEnorm p]
      exact (diagExp_contMDiffAt_zero (I := I) g hEnorm p 1 le_rfl).continuousAt
    exact h2.comp h1
  have hfx : diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p (p, p)) = (p, p) := by
    rw [diagExpInv_center (I := I) g hEnorm p, diagExp_zero_eq (I := I) g hEnorm p]
  have hev_d : ∀ᶠ y in nhds (p, p),
      diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y)
        ∈ (extChartAt (I.prod I) (p, p)).source := by
    refine hcont.eventually_mem ?_
    rw [hfx]
    exact extChartAt_source_mem_nhds (I := I.prod I) (p, p)
  filter_upwards [hev1, hev_y, hev_d] with y hy1 hy2 hy3
  have e1 : (diagExpIFT (I := I) g hEnorm p) ((diagExpIFT (I := I) g hEnorm p).symm
      (extChartAt (I.prod I) (p, p) y)) =
      chartedDiagExp (I := I) g hEnorm p ((diagExpIFT (I := I) g hEnorm p).symm
        (extChartAt (I.prod I) (p, p) y)) :=
    congrFun (diagExpIFT_coe (I := I) g hEnorm p) _
  rw [e1] at hy1
  have e2 : chartedDiagExp (I := I) g hEnorm p ((diagExpIFT (I := I) g hEnorm p).symm
      (extChartAt (I.prod I) (p, p) y)) =
      extChartAt (I.prod I) (diagExp (I := I) g hEnorm (⟨p, (0 : E)⟩ : TangentBundle I M))
        (diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y)) := rfl
  rw [e2, diagExp_zero_eq (I := I) g hEnorm p] at hy1
  exact (extChartAt (I.prod I) (p, p)).injOn hy3 hy2 hy1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [ConnectedSpace M] in
theorem diagExpInv_diagExp
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∀ᶠ u in nhds (⟨p, (0 : E)⟩ : TangentBundle I M),
      diagExpInv (I := I) g hEnorm p (diagExp (I := I) g hEnorm u) = u := by
  have hsrc : diagExpZeroPt (I := I) p ∈ (diagExpIFT (I := I) g hEnorm p).source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source
      (chartedDiagExp_cdaOne (I := I) g hEnorm p)
      (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl) one_ne_zero
  have hev_li := (diagExpIFT (I := I) g hEnorm p).eventually_left_inverse hsrc
  have htend : Filter.Tendsto
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M))
      (nhds (⟨p, (0 : E)⟩ : TangentBundle I M))
      (nhds (diagExpZeroPt (I := I) p)) := by
    simpa only [diagExpZeroPt] using
      (continuousAt_extChartAt (I := I.tangent)
        (⟨p, (0 : E)⟩ : TangentBundle I M)).tendsto
  have hev1 := htend.eventually hev_li
  have hev_u : ∀ᶠ u in nhds (⟨p, (0 : E)⟩ : TangentBundle I M),
      u ∈ (extChartAt I.tangent
        (⟨p, (0 : E)⟩ : TangentBundle I M)).source :=
    extChartAt_source_mem_nhds (I := I.tangent)
      (⟨p, (0 : E)⟩ : TangentBundle I M)
  filter_upwards [hev1, hev_u] with u hu hu_src
  have hinner :
      (extChartAt I.tangent
        (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
          (extChartAt I.tangent
            (⟨p, (0 : E)⟩ : TangentBundle I M) u) = u :=
    (extChartAt I.tangent
      (⟨p, (0 : E)⟩ : TangentBundle I M)).left_inv hu_src
  have hforward :
      (diagExpIFT (I := I) g hEnorm p)
          (extChartAt I.tangent
            (⟨p, (0 : E)⟩ : TangentBundle I M) u) =
        extChartAt (I.prod I) (p, p) (diagExp (I := I) g hEnorm u) := by
    rw [diagExpIFT_coe (I := I) g hEnorm p]
    simp only [chartedDiagExp, Function.comp_apply]
    rw [hinner, diagExp_zero_eq (I := I) g hEnorm p]
  rw [hforward] at hu
  change (extChartAt I.tangent
      (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
        ((diagExpIFT (I := I) g hEnorm p).symm
          (extChartAt (I.prod I) (p, p) (diagExp (I := I) g hEnorm u))) = u
  rw [hu, hinner]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [ConnectedSpace M] in
theorem diagExpInv_proj
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∀ᶠ y in nhds (p, p), (diagExpInv (I := I) g hEnorm p y).proj = y.1 := by
  filter_upwards [diagExp_diagExpInv (I := I) g hEnorm p] with y hy
  have h := congrArg Prod.fst hy
  rwa [diagExp_fst] at h

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



omit [ConnectedSpace M] in
theorem expIntr_diagExpInv
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∀ᶠ y in nhds (p, p),
      expMapIntrinsic (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y).proj
        (diagExpInv (I := I) g hEnorm p y).snd = y.2 := by
  filter_upwards [diagExp_diagExpInv (I := I) g hEnorm p] with y hy
  have h := congrArg Prod.snd hy
  rwa [diagExp_snd] at h

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in






omit [ConnectedSpace M] in
theorem exists_diagInvDom
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (n : ℕ) (hn : 1 ≤ n) :
    ∃ U : Set (M × M), IsOpen U ∧ (p, p) ∈ U ∧
      ∀ y ∈ U,
        ContMDiffAt (I.prod I) I.tangent (n : ℕ∞)
          (diagExpInv (I := I) g hEnorm p) y ∧
        diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y) = y ∧
        (diagExpInv (I := I) g hEnorm p y).proj = y.1 ∧
        expMapIntrinsic (I := I) g hEnorm y.1
          (diagExpInv (I := I) g hEnorm p y).snd = y.2 := by
  have hfinite : (n : WithTop ℕ∞) ≠ ∞ := by simp
  have hsmooth : ∀ᶠ y in nhds (p, p),
      ContMDiffAt (I.prod I) I.tangent (n : ℕ∞)
        (diagExpInv (I := I) g hEnorm p) y :=
    (contMDiffAt_iff_contMDiffAt_nhds hfinite).mp
      (diagExpInv_contMDiffAt_order (I := I) g hEnorm p n hn)
  have hright := diagExp_diagExpInv (I := I) g hEnorm p
  obtain ⟨U, hU, hUopen, hpU⟩ := mem_nhds_iff.mp (hsmooth.and hright)
  refine ⟨U, hUopen, hpU, ?_⟩
  intro y hy
  obtain ⟨hsm, hri⟩ := hU hy
  have hproj : (diagExpInv (I := I) g hEnorm p y).proj = y.1 := by
    have h := congrArg Prod.fst hri
    rwa [diagExp_fst] at h
  have hexp : expMapIntrinsic (I := I) g hEnorm y.1
      (diagExpInv (I := I) g hEnorm p y).snd = y.2 := by
    have h := congrArg Prod.snd hri
    rw [diagExp_snd, hproj] at h
    exact h
  exact ⟨hsm, hri, hproj, hexp⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



omit [ConnectedSpace M] in
theorem exists_diagInvDom_inf
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ U : Set (M × M), IsOpen U ∧ (p, p) ∈ U ∧
      ContMDiffOn (I.prod I) I.tangent ∞
        (diagExpInv (I := I) g hEnorm p) U ∧
      ∀ y ∈ U,
        diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y) = y ∧
        (diagExpInv (I := I) g hEnorm p y).proj = y.1 ∧
        expMapIntrinsic (I := I) g hEnorm y.1
          (diagExpInv (I := I) g hEnorm p y).snd = y.2 := by
  classical
  obtain ⟨V, hV_open, hcenterV, hsymmV, hVprop⟩ :=
    exists_chartInvInf (I := I) g hEnorm p
  have hcenter_coord : extChartAt (I.prod I) (p, p) (p, p) ∈ V := by
    rw [outer_center (I := I) g hEnorm p]
    exact hcenterV
  have hcoordV : ∀ᶠ y in 𝓝 (p, p),
      extChartAt (I.prod I) (p, p) y ∈ V :=
    (continuousAt_extChartAt (I := I.prod I) (p, p)).preimage_mem_nhds
      (hV_open.mem_nhds hcenter_coord)
  have hchart_src : ∀ᶠ y in 𝓝 (p, p),
      y ∈ (extChartAt (I.prod I) (p, p)).source :=
    extChartAt_source_mem_nhds (I := I.prod I) (p, p)
  have hright := diagExp_diagExpInv (I := I) g hEnorm p
  have hgood : ∀ᶠ y in 𝓝 (p, p),
      extChartAt (I.prod I) (p, p) y ∈ V ∧
      y ∈ (extChartAt (I.prod I) (p, p)).source ∧
      diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y) = y := by
    filter_upwards [hcoordV, hchart_src, hright] with y hyV hysrc hyright
    exact ⟨hyV, hysrc, hyright⟩
  obtain ⟨U, hU, hU_open, hpU⟩ := _root_.mem_nhds_iff.mp hgood
  have hsmooth : ContMDiffOn (I.prod I) I.tangent ∞
      (diagExpInv (I := I) g hEnorm p) U := by
    intro y hy
    obtain ⟨hyV, hy_extsrc, _hyright⟩ := hU hy
    have hy_chsrc : y ∈ (chartAt (ModelProd H H) (p, p)).source := by
      rw [extChartAt_source (I := I.prod I)] at hy_extsrc
      exact hy_extsrc
    have houter : ContMDiffAt (I.prod I) 𝓘(ℝ, E × E) ∞
        (extChartAt (I.prod I) (p, p)) y :=
      contMDiffAt_extChartAt' (I := I.prod I) (n := ∞) hy_chsrc
    have hmid_cd : ContDiffAt ℝ ∞ (diagExpIFT (I := I) g hEnorm p).symm
        (extChartAt (I.prod I) (p, p) y) :=
      hsymmV.contDiffAt (hV_open.mem_nhds hyV)
    have hmid : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E × E) ∞
        (diagExpIFT (I := I) g hEnorm p).symm
        (extChartAt (I.prod I) (p, p) y) :=
      contMDiffAt_iff_contDiffAt.mpr hmid_cd
    have hinner_target :=
      (hVprop (extChartAt (I.prod I) (p, p) y) hyV).2
    have hinner : ContMDiffAt 𝓘(ℝ, E × E) I.tangent ∞
        (extChartAt I.tangent
          (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
        ((diagExpIFT (I := I) g hEnorm p).symm
          (extChartAt (I.prod I) (p, p) y)) := by
      have hwithin := contMDiffWithinAt_extChartAt_symm_target
        (I := I.tangent) (n := ∞)
        (⟨p, (0 : E)⟩ : TangentBundle I M) hinner_target
      exact hwithin.contMDiffAt
        (extChartAt_target_mem_nhds' (I := I.tangent) hinner_target)
    have hcomp := hinner.comp y (hmid.comp y houter)
    simpa [diagExpInv] using hcomp.contMDiffWithinAt
  refine ⟨U, hU_open, hpU, hsmooth, ?_⟩
  intro y hy
  have hri := (hU hy).2.2
  have hproj : (diagExpInv (I := I) g hEnorm p y).proj = y.1 := by
    have h := congrArg Prod.fst hri
    rwa [diagExp_fst] at h
  have hexp : expMapIntrinsic (I := I) g hEnorm y.1
      (diagExpInv (I := I) g hEnorm p y).snd = y.2 := by
    have h := congrArg Prod.snd hri
    rw [diagExp_snd, hproj] at h
    exact h
  exact ⟨hri, hproj, hexp⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


private def diagExpHome
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) : OpenPartialHomeomorph (TangentBundle I M) (M × M) :=
  let cO : OpenPartialHomeomorph (TangentBundle I M) (E × E) :=
    { toPartialEquiv :=
        extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)
      open_source := isOpen_extChartAt_source _
      open_target := isOpen_extChartAt_target _
      continuousOn_toFun := continuousOn_extChartAt _
      continuousOn_invFun := continuousOn_extChartAt_symm _ }
  let dO : OpenPartialHomeomorph (M × M) (E × E) :=
    { toPartialEquiv := extChartAt (I.prod I) (p, p)
      open_source := isOpen_extChartAt_source _
      open_target := isOpen_extChartAt_target _
      continuousOn_toFun := continuousOn_extChartAt _
      continuousOn_invFun := continuousOn_extChartAt_symm _ }
  (cO.trans (diagExpIFT (I := I) g hEnorm p)).trans dO.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] in
private theorem diagExpHome_inv
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ⇑(diagExpHome (I := I) g hEnorm p).symm =
      diagExpInv (I := I) g hEnorm p := by
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] in
private theorem exists_stdBranch
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ B : DiagInvBranch (I := I) g hEnorm p,
      B.inv = diagExpInv (I := I) g hEnorm p := by
  classical
  obtain ⟨U, hUopen, hpU, hUsmooth, hU⟩ :=
    exists_diagInvDom_inf (I := I) g hEnorm p
  let cO : OpenPartialHomeomorph (TangentBundle I M) (E × E) :=
    { toPartialEquiv :=
        extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)
      open_source := isOpen_extChartAt_source _
      open_target := isOpen_extChartAt_target _
      continuousOn_toFun := continuousOn_extChartAt _
      continuousOn_invFun := continuousOn_extChartAt_symm _ }
  let dO : OpenPartialHomeomorph (M × M) (E × E) :=
    { toPartialEquiv := extChartAt (I.prod I) (p, p)
      open_source := isOpen_extChartAt_source _
      open_target := isOpen_extChartAt_target _
      continuousOn_toFun := continuousOn_extChartAt _
      continuousOn_invFun := continuousOn_extChartAt_symm _ }
  let F : OpenPartialHomeomorph (TangentBundle I M) (M × M) :=
    diagExpHome (I := I) g hEnorm p
  let R : OpenPartialHomeomorph (M × M) (TangentBundle I M) :=
    F.symm.restrOpen U hUopen
  let H : OpenPartialHomeomorph (TangentBundle I M) (M × M) := R.symm
  have hHinv : ⇑H.symm = diagExpInv (I := I) g hEnorm p := by
    change ⇑(F.symm.restrOpen U hUopen) = diagExpInv (I := I) g hEnorm p
    rw [OpenPartialHomeomorph.coe_restrOpen]
    exact diagExpHome_inv (I := I) g hEnorm p
  have htarget_sub : H.target ⊆ U := by
    intro y hy
    change y ∈ (F.symm.restrOpen U hUopen).source at hy
    exact hy.2
  have hzeroIFT : diagExpZeroPt (I := I) p ∈
      (diagExpIFT (I := I) g hEnorm p).source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source
      (chartedDiagExp_cdaOne (I := I) g hEnorm p)
      (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl)
      one_ne_zero
  let u0 : TangentBundle I M := ⟨p, (0 : E)⟩
  have hu0c : u0 ∈ cO.source :=
    mem_extChartAt_source (I := I.tangent) u0
  have hc0 : cO u0 = diagExpZeroPt (I := I) p := rfl
  have hu0mid : u0 ∈ (cO.trans (diagExpIFT (I := I) g hEnorm p)).source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨hu0c, ?_⟩
    change cO u0 ∈ (diagExpIFT (I := I) g hEnorm p).source
    rw [hc0]
    exact hzeroIFT
  have hmid0 : (cO.trans (diagExpIFT (I := I) g hEnorm p)) u0 = dO (p, p) := by
    rw [OpenPartialHomeomorph.trans_apply, hc0,
      diagExpIFT_coe (I := I) g hEnorm p]
    exact (outer_center (I := I) g hEnorm p).symm
  have hmidTarget :
      (cO.trans (diagExpIFT (I := I) g hEnorm p)) u0 ∈ dO.symm.source := by
    change (cO.trans (diagExpIFT (I := I) g hEnorm p)) u0 ∈ dO.target
    rw [hmid0]
    exact dO.map_source (mem_extChartAt_source (I := I.prod I) (p, p))
  have hu0F : u0 ∈ F.source := by
    change u0 ∈
      ((cO.trans (diagExpIFT (I := I) g hEnorm p)).trans dO.symm).source
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hu0mid, hmidTarget⟩
  have hF0 : F u0 = (p, p) := by
    change dO.symm ((cO.trans (diagExpIFT (I := I) g hEnorm p)) u0) = (p, p)
    rw [hmid0]
    exact dO.left_inv (mem_extChartAt_source (I := I.prod I) (p, p))
  have hpF : (p, p) ∈ F.target := by
    have hmap := F.map_source hu0F
    rwa [hF0] at hmap
  have hpR : (p, p) ∈ R.source := by
    change (p, p) ∈ F.target ∩ U
    exact ⟨hpF, hpU⟩
  have hzeroH : u0 ∈ H.source := by
    have hmap := R.map_source hpR
    change R (p, p) ∈ H.source at hmap
    have hR0 : R (p, p) = u0 := by
      change F.symm (p, p) = u0
      rw [show F.symm = diagExpInv (I := I) g hEnorm p from
        diagExpHome_inv (I := I) g hEnorm p]
      exact diagExpInv_center (I := I) g hEnorm p
    rwa [hR0] at hmap
  have hhomEq : EqOn (fun u ↦ H u) (diagExp (I := I) g hEnorm) H.source := by
    intro u hu
    have hy : H u ∈ H.target := H.map_source hu
    have hleft := H.left_inv hu
    have hleft' : diagExpInv (I := I) g hEnorm p (H u) = u := by
      rw [← hHinv]
      exact hleft
    have hright := (hU (H u) (htarget_sub hy)).1
    rw [hleft'] at hright
    exact hright.symm
  have hinvInf : ContMDiffOn (I.prod I) I.tangent ∞ H.symm H.target := by
    rw [hHinv]
    exact hUsmooth.mono htarget_sub
  let B : DiagInvBranch (I := I) g hEnorm p :=
    { hom := H
      zero_mem := hzeroH
      hom_eq := hhomEq
      inv_inf := hinvInf }
  refine ⟨B, ?_⟩
  exact hHinv

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


noncomputable def stdBranch
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) : DiagInvBranch (I := I) g hEnorm p :=
  Classical.choose (exists_stdBranch (I := I) g hEnorm p)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
theorem std_inv_eq
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    (stdBranch (I := I) g hEnorm p).inv =
      diagExpInv (I := I) g hEnorm p :=
  Classical.choose_spec (exists_stdBranch (I := I) g hEnorm p)

end DiagExpDerivative

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
