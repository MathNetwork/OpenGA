import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartLieBracket
import DifferentialGeometry.Geometry.Connection.CovApplyCovRSChartBasisExtension


noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open Bundle Manifold Set FiberBundle Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma extDerivFun_comp_extChartAt_apply_basis [I.Boundaryless]
    (x : M) {gE : E → ℝ}
    (hgE : ContDiffAt ℝ ∞ gE (extChartAt I x x))
    (a : Fin (Module.finrank ℝ E)) :
    extDerivFun (I := I) (fun b : M => gE (extChartAt I x b)) x
        ((chartModelBasis E) a) =
      partialDeriv (E := E) a gE (extChartAt I x x) := by
  classical
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxsrc
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  set Gfun : M → ℝ := fun b : M => gE (extChartAt I x b) with hGfun_def
  have hgE_diff : DifferentiableAt ℝ gE (extChartAt I x x) :=
    hgE.differentiableAt (by simp)
  have hgE_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) gE (extChartAt I x x) := by
    rw [mdifferentiableAt_iff_differentiableAt]; exact hgE_diff
  have hphi_mdiff : MDiffAt (extChartAt I x) x :=
    mdifferentiableAt_extChartAt (I := I) (x := x) hxsrc
  have hG_mdiff : MDiffAt Gfun x := hgE_mdiff.comp x hphi_mdiff
  have hed_to_mfderiv :
      extDerivFun (I := I) Gfun x ((chartModelBasis E) a) =
        (mfderiv I 𝓘(ℝ) Gfun x : TangentSpace I x →L[ℝ] _) ((chartModelBasis E) a) := rfl
  rw [hed_to_mfderiv]
  rw [mfderiv_scalar_eq_chart_fderiv (I := I) x Gfun hxsrc hxint hG_mdiff
    ((chartModelBasis E) a)]
  rw [trivToE_self_apply (I := I) x ((chartModelBasis E) a)]
  have htgt_nhds : ((extChartAt I x).target : Set E) ∈ 𝓝 (extChartAt I x x) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hxint) interior_subset
  have hcompose_eq : (Gfun ∘ (extChartAt I x).symm) =ᶠ[𝓝 (extChartAt I x x)] gE := by
    filter_upwards [htgt_nhds] with y hy
    change gE (extChartAt I x ((extChartAt I x).symm y)) = gE y
    rw [(extChartAt I x).right_inv hy]
  rw [hcompose_eq.fderiv_eq]
  rw [partialDeriv]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma exists_globalSmooth_chartBasisVec_ext
    (x : M) (j : Fin (Module.finrank ℝ E)) :
    ∃ (Xext : Π b : M, TangentSpace I b) (U : Set M),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xext) ∧
        IsOpen U ∧ x ∈ U ∧ U ⊆ chartLeviCivitaGoodSet (I := I) x ∧
        ∀ y ∈ U, Xext y = chartBasisVecFiber (I := I) x j y := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hopen : IsOpen (chartLeviCivitaGoodSet (I := I) x) :=
    chartLeviCivitaGoodSet_isOpen (I := I) x
  have hnhds : chartLeviCivitaGoodSet (I := I) x ∈ 𝓝 x := hopen.mem_nhds hx_good
  obtain ⟨χ, _, hχ_tsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hnhds
  have hXext_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y : M => (χ : M → ℝ) y • chartBasisVecFiber (I := I) x j y)) :=
    bumpedChartBasis_contMDiff (I := I) x (b₀ := x) j χ hχ_tsupp
  have hχ_eq_one_nhds : ∀ᶠ y in 𝓝 x, (χ : M → ℝ) y = 1 := χ.eventuallyEq_one
  obtain ⟨V_set, hV_nhds, hχ_one_V⟩ :=
    Filter.eventually_iff_exists_mem.mp hχ_eq_one_nhds
  obtain ⟨V_open, hV_sub_V_set, hV_open_isOpen, hx_in_V_open⟩ :=
    mem_nhds_iff.mp hV_nhds
  refine ⟨fun y : M => (χ : M → ℝ) y • chartBasisVecFiber (I := I) x j y,
    V_open ∩ chartLeviCivitaGoodSet (I := I) x, hXext_smooth,
    hV_open_isOpen.inter hopen, ⟨hx_in_V_open, hx_good⟩, fun y hy => hy.2, ?_⟩
  intro y hyU
  have hχ_one_y : (χ : M → ℝ) y = 1 := hχ_one_V y (hV_sub_V_set hyU.1)
  change (χ : M → ℝ) y • chartBasisVecFiber (I := I) x j y = chartBasisVecFiber (I := I) x j y
  rw [hχ_one_y, one_smul]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartChristoffel_contDiffAt_self [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (b i m : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞ (chartChristoffel (I := I) g x b i m) (extChartAt I x x) := by
  classical
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxsrc
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  have hon : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g x b i m)
      (interior (extChartAt I x).target) :=
    chartChristoffel_contDiffOn_interior (I := I) g x b i m
  exact hon.contDiffAt (isOpen_interior.mem_nhds hxint)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
lemma leviCivita_finset_sum_apply
    {ι : Type*} (g : SmoothRiemannianMetric I M)
    (t : Finset ι) (σ : ι → Π y : M, TangentSpace I y)
    {x : M} (v : TangentSpace I x)
    (hσ : ∀ i, MDiffAt (T% (σ i)) x) :
    ((LeviCivita (I := I) g).toFun (t.sum σ) x) v =
      t.sum (fun i => ((LeviCivita (I := I) g).toFun (σ i) x) v) := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  induction t using Finset.induction_on with
  | empty => simp [cov.isCovariantDerivativeOnUniv.zero]
  | insert i t hit ih =>
      have hσi : MDiffAt (T% (σ i)) x := hσ i
      have hsum : MDiffAt (T% (t.sum σ)) x := by
        have hsum_raw := MDifferentiableAt.sum_section (s := t) (t := σ) hσ
        simpa using hsum_raw
      calc
        (cov.toFun ((insert i t).sum σ) x) v
            = (cov.toFun (σ i + t.sum σ) x) v := by
              simp [Finset.sum_insert, hit]
        _ = ((cov.toFun (σ i) x + cov.toFun (t.sum σ) x) v) := by
              rw [cov.isCovariantDerivativeOnUniv.add hσi hsum]
        _ = (cov.toFun (σ i) x) v + (cov.toFun (t.sum σ) x) v := by simp
        _ = (insert i t).sum (fun j => (cov.toFun (σ j) x) v) := by
              rw [ih]; simp [Finset.sum_insert, hit]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma LeviCivita_chartBasisVec_secondCovDeriv [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (a b i : Fin (Module.finrank ℝ E))
    {Xa Xb Xi : Π b : M, TangentSpace I b} {U : Set M}
    (_hXa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xa))
    (hXb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xb))
    (hXi : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xi))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) x)
    (hXa_eq : ∀ y ∈ U, Xa y = chartBasisVecFiber (I := I) x a y)
    (hXb_eq : ∀ y ∈ U, Xb y = chartBasisVecFiber (I := I) x b y)
    (hXi_eq : ∀ y ∈ U, Xi y = chartBasisVecFiber (I := I) x i y) :
    (LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) Xb Xi) x (Xa x) =
      ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) a (chartChristoffel (I := I) g x b i l) (extChartAt I x x) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x a m l (extChartAt I x x) *
              chartChristoffel (I := I) g x b i m (extChartAt I x x)) •
          (chartModelBasis E) l := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  have hXa_x : Xa x = chartBasisVecFiber (I := I) x a x := hXa_eq x hxU
  set S : Π y : M, TangentSpace I y := covApply cov Xb Xi with hS_def
  have hXi_plus : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% Xi) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]; exact hXi
  have hS_diff : MDiffAt (T% S) x :=
    covApply_mdifferentiableAt (cov := cov) hXb hXi_plus
  set Γc : Fin (Module.finrank ℝ E) → M → ℝ :=
    fun m y => chartChristoffel (I := I) g x b i m (extChartAt I x y) with hΓc_def
  set term : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun m y => Γc m y • chartBasisVecFiber (I := I) x m y with hterm_def
  have hS_eq_sum_on_U : ∀ y ∈ U, S y = ∑ m : Fin (Module.finrank ℝ E), term m y := by
    intro y hy
    have hy_good : y ∈ chartLeviCivitaGoodSet (I := I) x := hU_good hy
    have hSval : S y = cov.toFun Xi y (Xb y) := rfl
    rw [hSval]
    have hXi_diff_y : MDiffAt (T% Xi) y := (hXi y).mdifferentiableAt (by simp)
    have hchart_i_diff_y : MDiffAt (T% (fun z : M => chartBasisVecFiber (I := I) x i z)) y :=
      chartBasisVec_alpha_mdifferentiableAt (I := I) x i hy_good
    have hXi_ev : (fun z : M => Xi z) =ᶠ[𝓝 y]
        (fun z : M => chartBasisVecFiber (I := I) x i z) := by
      filter_upwards [hU_open.mem_nhds hy] with z hz using hXi_eq z hz
    have hcov_congr :
        cov.toFun Xi y = cov.toFun (fun z : M => chartBasisVecFiber (I := I) x i z) y :=
      cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hXi_diff_y hchart_i_diff_y
        Filter.univ_mem hXi_ev
    rw [hcov_congr]
    rw [hXb_eq y hy]
    rw [LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g x b i hy_good]
  have hΓc_diff : ∀ m : Fin (Module.finrank ℝ E), MDiffAt (Γc m) x := by
    intro m
    have hΓ_cda : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g x b i m) (extChartAt I x x) :=
      chartChristoffel_contDiffAt_self (I := I) g x b i m
    have hΓ_d : DifferentiableAt ℝ (chartChristoffel (I := I) g x b i m) (extChartAt I x x) :=
      hΓ_cda.differentiableAt (by simp)
    have hΓ_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
        (chartChristoffel (I := I) g x b i m) (extChartAt I x x) := by
      rw [mdifferentiableAt_iff_differentiableAt]; exact hΓ_d
    have hphi_mdiff : MDiffAt (extChartAt I x) x :=
      mdifferentiableAt_extChartAt (I := I) (x := x) (mem_chart_source H x)
    exact hΓ_mdiff.comp x hphi_mdiff
  have hframe_diff : ∀ m : Fin (Module.finrank ℝ E),
      MDiffAt (T% (fun y : M => chartBasisVecFiber (I := I) x m y)) x :=
    fun m => chartBasisVec_alpha_mdifferentiableAt (I := I) x m
      (self_mem_chartLeviCivitaGoodSet (I := I) (α := x))
  have hterm_diff : ∀ m : Fin (Module.finrank ℝ E), MDiffAt (T% (term m)) x :=
    fun m => MDifferentiableAt.smul_section (hΓc_diff m) (hframe_diff m)
  have hsum_diff :
      MDiffAt (T% fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) x :=
    MDifferentiableAt.sum_section (s := Finset.univ) (t := term) hterm_diff
  have hS_ev_sum :
      (fun y : M => S y) =ᶠ[𝓝 x]
        (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) := by
    filter_upwards [hU_open.mem_nhds hxU] with y hy using hS_eq_sum_on_U y hy
  have hcov_S_eq :
      cov.toFun S x =
        cov.toFun (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hS_diff hsum_diff
      Filter.univ_mem hS_ev_sum
  rw [hS_def] at hcov_S_eq ⊢
  rw [hcov_S_eq, hXa_x]
  have hsum_apply :
      (cov.toFun (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) x)
          (chartBasisVecFiber (I := I) x a x) =
        ∑ m : Fin (Module.finrank ℝ E),
          (cov.toFun (term m) x) (chartBasisVecFiber (I := I) x a x) := by
    have hfun :
        (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) =
          (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum term := by
      funext y; simp
    rw [hfun]
    exact leviCivita_finset_sum_apply (I := I) g
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))) term
      (chartBasisVecFiber (I := I) x a x) hterm_diff
  rw [hsum_apply]
  have hleib : ∀ m : Fin (Module.finrank ℝ E),
      (cov.toFun (term m) x) (chartBasisVecFiber (I := I) x a x) =
        extDerivFun (I := I) (Γc m) x (chartBasisVecFiber (I := I) x a x) •
            chartBasisVecFiber (I := I) x m x +
          Γc m x •
            (cov.toFun (fun y : M => chartBasisVecFiber (I := I) x m y) x)
              (chartBasisVecFiber (I := I) x a x) := by
    intro m
    have hleibniz := cov.isCovariantDerivativeOnUniv.leibniz
      (σ := fun y : M => chartBasisVecFiber (I := I) x m y) (g := Γc m) (x := x)
      (hframe_diff m) (hΓc_diff m)
    have hterm_eq : term m = (Γc m) • (fun y : M => chartBasisVecFiber (I := I) x m y) := by
      funext y; rfl
    rw [hterm_eq]
    have happ := congr($(hleibniz) (chartBasisVecFiber (I := I) x a x))
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply] at happ
    rw [happ]
    rw [add_comm]
  rw [Finset.sum_congr rfl (fun m _ => hleib m)]
  have hder : ∀ m : Fin (Module.finrank ℝ E),
      extDerivFun (I := I) (Γc m) x (chartBasisVecFiber (I := I) x a x) =
        partialDeriv (E := E) a (chartChristoffel (I := I) g x b i m) (extChartAt I x x) := by
    intro m
    rw [chartBasisVecFiber_self (I := I) x a]
    exact extDerivFun_comp_extChartAt_apply_basis (I := I) x
      (chartChristoffel_contDiffAt_self (I := I) g x b i m) a
  have hframe_x : ∀ m : Fin (Module.finrank ℝ E),
      chartBasisVecFiber (I := I) x m x = (chartModelBasis E) m :=
    fun m => chartBasisVecFiber_self (I := I) x m
  have hΓc_x : ∀ m : Fin (Module.finrank ℝ E),
      Γc m x = chartChristoffel (I := I) g x b i m (extChartAt I x x) := fun m => rfl
  have hinner : ∀ m : Fin (Module.finrank ℝ E),
      (cov.toFun (fun y : M => chartBasisVecFiber (I := I) x m y) x)
          (chartBasisVecFiber (I := I) x a x) =
        ∑ l : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g x a m l (extChartAt I x x) • (chartModelBasis E) l := by
    intro m
    have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
      self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
    rw [LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g x a m hx_good]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [chartBasisVecFiber_self (I := I) x l]
    rfl
  rw [Finset.sum_congr rfl (fun m _ => by
    rw [hder m, hframe_x m, hΓc_x m, hinner m])]
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun l => (chartModelBasis E) l with he_def
  set D : Fin (Module.finrank ℝ E) → ℝ :=
    fun m => partialDeriv (E := E) a (chartChristoffel (I := I) g x b i m) (extChartAt I x x)
    with hD_def
  set Γq : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun m l => chartChristoffel (I := I) g x a m l (extChartAt I x x) with hΓq_def
  set Γr : Fin (Module.finrank ℝ E) → ℝ :=
    fun m => chartChristoffel (I := I) g x b i m (extChartAt I x x) with hΓr_def
  calc
    (∑ m : Fin (Module.finrank ℝ E),
        (D m • e m + Γr m • ∑ l : Fin (Module.finrank ℝ E), Γq m l • e l))
        = (∑ m : Fin (Module.finrank ℝ E), D m • e m) +
            (∑ m : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E), (Γr m * Γq m l) • e l) := by
          rw [Finset.sum_add_distrib]
          refine congrArg (fun t => (∑ m : Fin (Module.finrank ℝ E), D m • e m) + t) ?_
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [smul_smul]
      _ = (∑ l : Fin (Module.finrank ℝ E), D l • e l) +
            (∑ l : Fin (Module.finrank ℝ E),
              ∑ m : Fin (Module.finrank ℝ E), (Γr m * Γq m l) • e l) := by
          rw [Finset.sum_comm]
      _ = ∑ l : Fin (Module.finrank ℝ E),
            (D l + ∑ m : Fin (Module.finrank ℝ E), Γq m l * Γr m) • e l := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [← Finset.sum_smul, ← add_smul]
          congr 1
          refine congrArg (fun t => D l + t) ?_
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [mul_comm]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
private lemma fderiv_chartE_section_repr_eq_zero_of_eventuallyEq [I.Boundaryless]
    (x : M) (j : Fin (Module.finrank ℝ E))
    {X : Π b : M, TangentSpace I b} {U : Set M}
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (hX_eq : ∀ y ∈ U, X y = chartBasisVecFiber (I := I) x j y) :
    fderiv ℝ (chartE_section_repr (I := I) x X ∘ (extChartAt I x).symm)
        (extChartAt I x x) = 0 := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxsrc
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  have hcont_symm : ContinuousOn (extChartAt I x).symm (extChartAt I x).target :=
    continuousOn_extChartAt_symm x
  set V : Set E :=
    (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' U with hV_def
  have hxV : extChartAt I x x ∈ V := by
    refine ⟨hxtgt, ?_⟩
    rw [Set.mem_preimage, (extChartAt I x).left_inv hxsrc_ext]; exact hxU
  have hopen_V : IsOpen V :=
    ContinuousOn.isOpen_inter_preimage hcont_symm (isOpen_extChartAt_target (I := I) x) hU_open
  have hev :
      (chartE_section_repr (I := I) x X ∘ (extChartAt I x).symm) =ᶠ[𝓝 (extChartAt I x x)]
        (chartE_section_repr (I := I) x
          (fun b : M => chartBasisVecFiber (I := I) x j b) ∘ (extChartAt I x).symm) := by
    filter_upwards [hopen_V.mem_nhds hxV] with y hy
    obtain ⟨_hy_tgt, hy_pre⟩ := hy
    rw [Set.mem_preimage] at hy_pre
    change chartE_section_repr (I := I) x X ((extChartAt I x).symm y) =
      chartE_section_repr (I := I) x
        (fun b : M => chartBasisVecFiber (I := I) x j b) ((extChartAt I x).symm y)
    unfold chartE_section_repr
    rw [hX_eq ((extChartAt I x).symm y) hy_pre]
  rw [hev.fderiv_eq]
  exact fderiv_chartE_chartBasisVec_alpha_eq_zero (I := I) x j hx_good

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
lemma mlieBracket_chartBasisVec_ext_self_eq_zero [I.Boundaryless]
    (x : M) (j k : Fin (Module.finrank ℝ E))
    {Xj Xk : Π b : M, TangentSpace I b} {U : Set M}
    (hXj : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xj))
    (hXk : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xk))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (hXj_eq : ∀ y ∈ U, Xj y = chartBasisVecFiber (I := I) x j y)
    (hXk_eq : ∀ y ∈ U, Xk y = chartBasisVecFiber (I := I) x k y) :
    VectorField.mlieBracket I Xj Xk x = 0 := by
  classical
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxsrc
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  have hXj_at : MDiffAt (T% Xj) x := (hXj x).mdifferentiableAt (by simp)
  have hXk_at : MDiffAt (T% Xk) x := (hXk x).mdifferentiableAt (by simp)
  rw [mlieBracket_eq_chart_fderiv_diff (I := I) x Xj Xk hxint hXj_at hXk_at]
  rw [fderiv_chartE_section_repr_eq_zero_of_eventuallyEq (I := I) x k hU_open hxU hXk_eq]
  rw [fderiv_chartE_section_repr_eq_zero_of_eventuallyEq (I := I) x j hU_open hxU hXj_eq]
  rw [ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply]
  exact sub_self 0

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma riemannOp_chartBasis_eq_chartRiemannCLM_basis [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    riemannOp (cov := LeviCivita (I := I) g) x
        ((chartModelBasis E) j) ((chartModelBasis E) k) ((chartModelBasis E) i) =
      chartRiemannCLM (I := I) g x
        ((chartModelBasis E) j) ((chartModelBasis E) k) ((chartModelBasis E) i) := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  obtain ⟨Xj, Uj, hXj_sm, hUj_open, hxUj, hUj_good, hXj_eq⟩ :=
    exists_globalSmooth_chartBasisVec_ext (I := I) x j
  obtain ⟨Xk, Uk, hXk_sm, hUk_open, hxUk, hUk_good, hXk_eq⟩ :=
    exists_globalSmooth_chartBasisVec_ext (I := I) x k
  obtain ⟨Xi, Ui, hXi_sm, hUi_open, hxUi, hUi_good, hXi_eq⟩ :=
    exists_globalSmooth_chartBasisVec_ext (I := I) x i
  set U : Set M := Uj ∩ Uk ∩ Ui with hU_def
  have hU_open : IsOpen U := (hUj_open.inter hUk_open).inter hUi_open
  have hxU : x ∈ U := ⟨⟨hxUj, hxUk⟩, hxUi⟩
  have hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) x :=
    fun y hy => hUj_good hy.1.1
  have hXj_eqU : ∀ y ∈ U, Xj y = chartBasisVecFiber (I := I) x j y :=
    fun y hy => hXj_eq y hy.1.1
  have hXk_eqU : ∀ y ∈ U, Xk y = chartBasisVecFiber (I := I) x k y :=
    fun y hy => hXk_eq y hy.1.2
  have hXi_eqU : ∀ y ∈ U, Xi y = chartBasisVecFiber (I := I) x i y :=
    fun y hy => hXi_eq y hy.2
  have hXj_x : Xj x = (chartModelBasis E) j := by
    rw [hXj_eqU x hxU, chartBasisVecFiber_self (I := I) x j]
  have hXk_x : Xk x = (chartModelBasis E) k := by
    rw [hXk_eqU x hxU, chartBasisVecFiber_self (I := I) x k]
  have hXi_x : Xi x = (chartModelBasis E) i := by
    rw [hXi_eqU x hxU, chartBasisVecFiber_self (I := I) x i]
  rw [show ((chartModelBasis E) j : TangentSpace I x) = Xj x from hXj_x.symm,
      show ((chartModelBasis E) k : TangentSpace I x) = Xk x from hXk_x.symm,
      show ((chartModelBasis E) i : TangentSpace I x) = Xi x from hXi_x.symm]
  rw [riemannOp_apply_smooth (cov := cov) hXj_sm hXk_sm hXi_sm]
  rw [riemannSec_def]
  rw [mlieBracket_chartBasisVec_ext_self_eq_zero (I := I) x j k hXj_sm hXk_sm
    hU_open hxU hXj_eqU hXk_eqU]
  rw [ContinuousLinearMap.map_zero, sub_zero]
  rw [LeviCivita_chartBasisVec_secondCovDeriv (I := I) g x j k i
    hXj_sm hXk_sm hXi_sm hU_open hxU hU_good hXj_eqU hXk_eqU hXi_eqU]
  rw [LeviCivita_chartBasisVec_secondCovDeriv (I := I) g x k j i
    hXk_sm hXj_sm hXi_sm hU_open hxU hU_good hXk_eqU hXj_eqU hXi_eqU]
  rw [hXj_x, hXk_x, hXi_x, chartRiemannCLM_basis_apply]
  have hcoeff : ∀ l : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) j (chartChristoffel (I := I) g x k i l) (extChartAt I x x) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x j m l (extChartAt I x x) *
              chartChristoffel (I := I) g x k i m (extChartAt I x x)) -
        (partialDeriv (E := E) k (chartChristoffel (I := I) g x j i l) (extChartAt I x x) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x k m l (extChartAt I x x) *
              chartChristoffel (I := I) g x j i m (extChartAt I x x)) =
      chartRiemannTensor (I := I) g x i j k l (extChartAt I x x) := by
    intro l
    rw [chartRiemannTensor_def]
    have hΓsym1 : (chartChristoffel (I := I) g x k i l) = (chartChristoffel (I := I) g x i k l) := by
      funext y; exact chartChristoffel_symm (I := I) g x k i l y
    have hΓsym2 : (chartChristoffel (I := I) g x j i l) = (chartChristoffel (I := I) g x i j l) := by
      funext y; exact chartChristoffel_symm (I := I) g x j i l y
    rw [hΓsym1, hΓsym2]
    have hquad :
        (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x j m l (extChartAt I x x) *
              chartChristoffel (I := I) g x i k m (extChartAt I x x)) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x k m l (extChartAt I x x) *
              chartChristoffel (I := I) g x i j m (extChartAt I x x)) =
        ∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g x j m l (extChartAt I x x) *
              chartChristoffel (I := I) g x i k m (extChartAt I x x) -
            chartChristoffel (I := I) g x k m l (extChartAt I x x) *
              chartChristoffel (I := I) g x i j m (extChartAt I x x)) :=
      (Finset.sum_sub_distrib _ _).symm
    have hq1 : ∀ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x j m l (extChartAt I x x) *
            chartChristoffel (I := I) g x k i m (extChartAt I x x) =
          chartChristoffel (I := I) g x j m l (extChartAt I x x) *
            chartChristoffel (I := I) g x i k m (extChartAt I x x) := by
      intro m; rw [chartChristoffel_symm (I := I) g x k i m]
    have hq2 : ∀ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x k m l (extChartAt I x x) *
            chartChristoffel (I := I) g x j i m (extChartAt I x x) =
          chartChristoffel (I := I) g x k m l (extChartAt I x x) *
            chartChristoffel (I := I) g x i j m (extChartAt I x x) := by
      intro m; rw [chartChristoffel_symm (I := I) g x j i m]
    rw [Finset.sum_congr rfl (fun m _ => hq1 m), Finset.sum_congr rfl (fun m _ => hq2 m)]
    rw [← hquad]
    ring
  refine (Finset.sum_sub_distrib _ _).symm.trans ?_
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← hcoeff l]
  exact (sub_smul _ _ _).symm

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartRiemannBasisIdentity_holds [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    chartRiemannBasisIdentity (I := I) g x := by
  rw [chartRiemannBasisIdentity_iff]
  intro i j k
  exact riemannOp_chartBasis_eq_chartRiemannCLM_basis (I := I) g x i j k

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem riemannOp_eq_chartRiemannCLM_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x) :
    riemannOp (cov := LeviCivita (I := I) g) x v w u =
      chartRiemannCLM (I := I) g x v w u :=
  riemannOp_eq_chartRiemannCLM_apply_of_basis_identity (I := I) g x
    (chartRiemannBasisIdentity_holds (I := I) g x) v w u

end Connection
end Integral
end DifferentialGeometry

end
