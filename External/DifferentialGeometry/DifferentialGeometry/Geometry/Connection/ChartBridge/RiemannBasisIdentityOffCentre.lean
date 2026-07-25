import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentity


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
lemma extDerivFun_comp_extChartAt_apply_basis_alpha [I.Boundaryless]
    (α : M) {gE : E → ℝ} {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hgE : ContDiffAt ℝ ∞ gE (extChartAt I α x))
    (a : Fin (Module.finrank ℝ E)) :
    extDerivFun (I := I) (fun b : M => gE (extChartAt I α b)) x
        (chartBasisVecFiber (I := I) α a x) =
      partialDeriv (E := E) a gE (extChartAt I α x) := by
  classical
  have hxchart : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hxsrc_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxchart
  have hxint : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  set Gfun : M → ℝ := fun b : M => gE (extChartAt I α b) with hGfun_def
  have hgE_diff : DifferentiableAt ℝ gE (extChartAt I α x) :=
    hgE.differentiableAt (by simp)
  have hgE_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) gE (extChartAt I α x) := by
    rw [mdifferentiableAt_iff_differentiableAt]; exact hgE_diff
  have hphi_mdiff : MDiffAt (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hxchart
  have hG_mdiff : MDiffAt Gfun x := hgE_mdiff.comp x hphi_mdiff
  have hed_to_mfderiv :
      extDerivFun (I := I) Gfun x (chartBasisVecFiber (I := I) α a x) =
        (mfderiv I 𝓘(ℝ) Gfun x : TangentSpace I x →L[ℝ] _)
          (chartBasisVecFiber (I := I) α a x) := rfl
  rw [hed_to_mfderiv]
  rw [mfderiv_chartBasisVecFiber_of_mdifferentiableAt (I := I) α hG_mdiff hxchart hxint a]
  have htgt_nhds : ((extChartAt I α).target : Set E) ∈ 𝓝 (extChartAt I α x) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hxint) interior_subset
  have hscalar_eq : (scalarOnE (I := I) α Gfun) =ᶠ[𝓝 (extChartAt I α x)] gE := by
    filter_upwards [htgt_nhds] with y hy
    change Gfun ((extChartAt I α).symm y) = gE y
    change gE (extChartAt I α ((extChartAt I α).symm y)) = gE y
    rw [(extChartAt I α).right_inv hy]
  change (fderiv ℝ (scalarOnE (I := I) α Gfun) (extChartAt I α x)) ((chartModelBasis E) a) =
    (fderiv ℝ gE (extChartAt I α x)) ((chartModelBasis E) a)
  rw [hscalar_eq.fderiv_eq]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartChristoffel_contDiffAt_alpha
    (g : SmoothRiemannianMetric I M) (α : M)
    (b i m : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞ (chartChristoffel (I := I) g α b i m) (extChartAt I α x) := by
  classical
  have hxint : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  have hon : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α b i m)
      (interior (extChartAt I α).target) :=
    chartChristoffel_contDiffOn_interior (I := I) g α b i m
  exact hon.contDiffAt (isOpen_interior.mem_nhds hxint)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
lemma exists_globalSmooth_chartBasisVec_ext_alpha
    (α : M) (j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    ∃ (Xext : Π b : M, TangentSpace I b) (U : Set M),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xext) ∧
        IsOpen U ∧ x ∈ U ∧ U ⊆ chartLeviCivitaGoodSet (I := I) α ∧
        ∀ y ∈ U, Xext y = chartBasisVecFiber (I := I) α j y := by
  classical
  have hopen : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  have hnhds : chartLeviCivitaGoodSet (I := I) α ∈ 𝓝 x := hopen.mem_nhds hx
  obtain ⟨χ, _, hχ_tsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hnhds
  have hXext_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y : M => (χ : M → ℝ) y • chartBasisVecFiber (I := I) α j y)) :=
    bumpedChartBasis_contMDiff (I := I) α (b₀ := x) j χ hχ_tsupp
  have hχ_eq_one_nhds : ∀ᶠ y in 𝓝 x, (χ : M → ℝ) y = 1 := χ.eventuallyEq_one
  obtain ⟨V_set, hV_nhds, hχ_one_V⟩ :=
    Filter.eventually_iff_exists_mem.mp hχ_eq_one_nhds
  obtain ⟨V_open, hV_sub_V_set, hV_open_isOpen, hx_in_V_open⟩ :=
    mem_nhds_iff.mp hV_nhds
  refine ⟨fun y : M => (χ : M → ℝ) y • chartBasisVecFiber (I := I) α j y,
    V_open ∩ chartLeviCivitaGoodSet (I := I) α, hXext_smooth,
    hV_open_isOpen.inter hopen, ⟨hx_in_V_open, hx⟩, fun y hy => hy.2, ?_⟩
  intro y hyU
  have hχ_one_y : (χ : M → ℝ) y = 1 := hχ_one_V y (hV_sub_V_set hyU.1)
  change (χ : M → ℝ) y • chartBasisVecFiber (I := I) α j y =
    chartBasisVecFiber (I := I) α j y
  rw [hχ_one_y, one_smul]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma LeviCivita_chartBasisVec_secondCovDeriv_alpha [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (a b i : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {Xa Xb Xi : Π b : M, TangentSpace I b} {U : Set M}
    (_hXa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xa))
    (hXb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xb))
    (hXi : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xi))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) α)
    (hXa_eq : ∀ y ∈ U, Xa y = chartBasisVecFiber (I := I) α a y)
    (hXb_eq : ∀ y ∈ U, Xb y = chartBasisVecFiber (I := I) α b y)
    (hXi_eq : ∀ y ∈ U, Xi y = chartBasisVecFiber (I := I) α i y) :
    (LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) Xb Xi) x (Xa x) =
      ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) a (chartChristoffel (I := I) g α b i l) (extChartAt I α x) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α a m l (extChartAt I α x) *
              chartChristoffel (I := I) g α b i m (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  have hXa_x : Xa x = chartBasisVecFiber (I := I) α a x := hXa_eq x hxU
  set S : Π y : M, TangentSpace I y := covApply cov Xb Xi with hS_def
  have hXi_plus : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% Xi) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]; exact hXi
  have hS_diff : MDiffAt (T% S) x :=
    covApply_mdifferentiableAt (cov := cov) hXb hXi_plus
  set Γc : Fin (Module.finrank ℝ E) → M → ℝ :=
    fun m y => chartChristoffel (I := I) g α b i m (extChartAt I α y) with hΓc_def
  set term : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun m y => Γc m y • chartBasisVecFiber (I := I) α m y with hterm_def
  have hS_eq_sum_on_U : ∀ y ∈ U, S y = ∑ m : Fin (Module.finrank ℝ E), term m y := by
    intro y hy
    have hy_good : y ∈ chartLeviCivitaGoodSet (I := I) α := hU_good hy
    have hSval : S y = cov.toFun Xi y (Xb y) := rfl
    rw [hSval]
    have hXi_diff_y : MDiffAt (T% Xi) y := (hXi y).mdifferentiableAt (by simp)
    have hchart_i_diff_y : MDiffAt (T% (fun z : M => chartBasisVecFiber (I := I) α i z)) y :=
      chartBasisVec_alpha_mdifferentiableAt (I := I) α i hy_good
    have hXi_ev : (fun z : M => Xi z) =ᶠ[𝓝 y]
        (fun z : M => chartBasisVecFiber (I := I) α i z) := by
      filter_upwards [hU_open.mem_nhds hy] with z hz using hXi_eq z hz
    have hcov_congr :
        cov.toFun Xi y = cov.toFun (fun z : M => chartBasisVecFiber (I := I) α i z) y :=
      cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hXi_diff_y hchart_i_diff_y
        Filter.univ_mem hXi_ev
    rw [hcov_congr]
    rw [hXb_eq y hy]
    rw [LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g α b i hy_good]
  have hxchart : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hΓc_diff : ∀ m : Fin (Module.finrank ℝ E), MDiffAt (Γc m) x := by
    intro m
    have hΓ_cda : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g α b i m) (extChartAt I α x) :=
      chartChristoffel_contDiffAt_alpha (I := I) g α b i m hx
    have hΓ_d : DifferentiableAt ℝ (chartChristoffel (I := I) g α b i m) (extChartAt I α x) :=
      hΓ_cda.differentiableAt (by simp)
    have hΓ_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
        (chartChristoffel (I := I) g α b i m) (extChartAt I α x) := by
      rw [mdifferentiableAt_iff_differentiableAt]; exact hΓ_d
    have hphi_mdiff : MDiffAt (extChartAt I α) x :=
      mdifferentiableAt_extChartAt (I := I) (x := α) hxchart
    exact hΓ_mdiff.comp x hphi_mdiff
  have hframe_diff : ∀ m : Fin (Module.finrank ℝ E),
      MDiffAt (T% (fun y : M => chartBasisVecFiber (I := I) α m y)) x :=
    fun m => chartBasisVec_alpha_mdifferentiableAt (I := I) α m hx
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
          (chartBasisVecFiber (I := I) α a x) =
        ∑ m : Fin (Module.finrank ℝ E),
          (cov.toFun (term m) x) (chartBasisVecFiber (I := I) α a x) := by
    have hfun :
        (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) =
          (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum term := by
      funext y; simp
    rw [hfun]
    exact leviCivita_finset_sum_apply (I := I) g
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))) term
      (chartBasisVecFiber (I := I) α a x) hterm_diff
  rw [hsum_apply]
  have hleib : ∀ m : Fin (Module.finrank ℝ E),
      (cov.toFun (term m) x) (chartBasisVecFiber (I := I) α a x) =
        extDerivFun (I := I) (Γc m) x (chartBasisVecFiber (I := I) α a x) •
            chartBasisVecFiber (I := I) α m x +
          Γc m x •
            (cov.toFun (fun y : M => chartBasisVecFiber (I := I) α m y) x)
              (chartBasisVecFiber (I := I) α a x) := by
    intro m
    have hleibniz := cov.isCovariantDerivativeOnUniv.leibniz
      (σ := fun y : M => chartBasisVecFiber (I := I) α m y) (g := Γc m) (x := x)
      (hframe_diff m) (hΓc_diff m)
    have hterm_eq : term m = (Γc m) • (fun y : M => chartBasisVecFiber (I := I) α m y) := by
      funext y; rfl
    rw [hterm_eq]
    have happ := congr($(hleibniz) (chartBasisVecFiber (I := I) α a x))
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply] at happ
    rw [happ]
    rw [add_comm]
  rw [Finset.sum_congr rfl (fun m _ => hleib m)]
  have hder : ∀ m : Fin (Module.finrank ℝ E),
      extDerivFun (I := I) (Γc m) x (chartBasisVecFiber (I := I) α a x) =
        partialDeriv (E := E) a (chartChristoffel (I := I) g α b i m) (extChartAt I α x) := by
    intro m
    exact extDerivFun_comp_extChartAt_apply_basis_alpha (I := I) α hx
      (chartChristoffel_contDiffAt_alpha (I := I) g α b i m hx) a
  have hΓc_x : ∀ m : Fin (Module.finrank ℝ E),
      Γc m x = chartChristoffel (I := I) g α b i m (extChartAt I α x) := fun m => rfl
  have hinner : ∀ m : Fin (Module.finrank ℝ E),
      (cov.toFun (fun y : M => chartBasisVecFiber (I := I) α m y) x)
          (chartBasisVecFiber (I := I) α a x) =
        ∑ l : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α a m l (extChartAt I α x) •
            chartBasisVecFiber (I := I) α l x := by
    intro m
    rw [LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g α a m hx]
  rw [Finset.sum_congr rfl (fun m _ => by
    rw [hder m, hΓc_x m, hinner m])]
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun l => chartBasisVecFiber (I := I) α l x with he_def
  set D : Fin (Module.finrank ℝ E) → ℝ :=
    fun m => partialDeriv (E := E) a (chartChristoffel (I := I) g α b i m) (extChartAt I α x)
    with hD_def
  set Γq : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun m l => chartChristoffel (I := I) g α a m l (extChartAt I α x) with hΓq_def
  set Γr : Fin (Module.finrank ℝ E) → ℝ :=
    fun m => chartChristoffel (I := I) g α b i m (extChartAt I α x) with hΓr_def
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

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma fderiv_chartE_section_repr_alpha_eq_zero_of_eventuallyEq [I.Boundaryless]
    (α : M) (j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {X : Π b : M, TangentSpace I b} {U : Set M}
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (hX_eq : ∀ y ∈ U, X y = chartBasisVecFiber (I := I) α j y) :
    fderiv ℝ (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm)
        (extChartAt I α x) = 0 := by
  classical
  have hxchart : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hxsrc_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxchart
  have hxtgt : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc_ext
  have hcont_symm : ContinuousOn (extChartAt I α).symm (extChartAt I α).target :=
    continuousOn_extChartAt_symm α
  set V : Set E :=
    (extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' U with hV_def
  have hxV : extChartAt I α x ∈ V := by
    refine ⟨hxtgt, ?_⟩
    rw [Set.mem_preimage, (extChartAt I α).left_inv hxsrc_ext]; exact hxU
  have hopen_V : IsOpen V :=
    ContinuousOn.isOpen_inter_preimage hcont_symm (isOpen_extChartAt_target (I := I) α) hU_open
  have hev :
      (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm) =ᶠ[𝓝 (extChartAt I α x)]
        (chartE_section_repr (I := I) α
          (fun b : M => chartBasisVecFiber (I := I) α j b) ∘ (extChartAt I α).symm) := by
    filter_upwards [hopen_V.mem_nhds hxV] with y hy
    obtain ⟨_hy_tgt, hy_pre⟩ := hy
    rw [Set.mem_preimage] at hy_pre
    change chartE_section_repr (I := I) α X ((extChartAt I α).symm y) =
      chartE_section_repr (I := I) α
        (fun b : M => chartBasisVecFiber (I := I) α j b) ((extChartAt I α).symm y)
    unfold chartE_section_repr
    rw [hX_eq ((extChartAt I α).symm y) hy_pre]
  rw [hev.fderiv_eq]
  exact fderiv_chartE_chartBasisVec_alpha_eq_zero (I := I) α j hx

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma mlieBracket_chartBasisVec_ext_self_eq_zero_alpha [I.Boundaryless]
    (α : M) (j k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {Xj Xk : Π b : M, TangentSpace I b} {U : Set M}
    (hXj : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xj))
    (hXk : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xk))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (hXj_eq : ∀ y ∈ U, Xj y = chartBasisVecFiber (I := I) α j y)
    (hXk_eq : ∀ y ∈ U, Xk y = chartBasisVecFiber (I := I) α k y) :
    VectorField.mlieBracket I Xj Xk x = 0 := by
  classical
  have hxchart : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hxsrc_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxchart
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hxint : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  have hXj_at : MDiffAt (T% Xj) x := (hXj x).mdifferentiableAt (by simp)
  have hXk_at : MDiffAt (T% Xk) x := (hXk x).mdifferentiableAt (by simp)
  rw [mlieBracket_eq_chart_fderiv_diff_general (I := I) α x Xj Xk hxsrc_ext hxbase hxint
    hXj_at hXk_at]
  rw [fderiv_chartE_section_repr_alpha_eq_zero_of_eventuallyEq (I := I) α k hx hU_open hxU hXk_eq]
  rw [fderiv_chartE_section_repr_alpha_eq_zero_of_eventuallyEq (I := I) α j hx hU_open hxU hXj_eq]
  rw [ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply, sub_self,
    ContinuousLinearMap.map_zero]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma riemannOp_chartBasisVec_alpha_eq [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    riemannOp (cov := LeviCivita (I := I) g) x
        (chartBasisVecFiber (I := I) α j x) (chartBasisVecFiber (I := I) α k x)
        (chartBasisVecFiber (I := I) α i x) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) g α i j k l (extChartAt I α x) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  obtain ⟨Xj, Uj, hXj_sm, hUj_open, hxUj, hUj_good, hXj_eq⟩ :=
    exists_globalSmooth_chartBasisVec_ext_alpha (I := I) α j hx
  obtain ⟨Xk, Uk, hXk_sm, hUk_open, hxUk, hUk_good, hXk_eq⟩ :=
    exists_globalSmooth_chartBasisVec_ext_alpha (I := I) α k hx
  obtain ⟨Xi, Ui, hXi_sm, hUi_open, hxUi, hUi_good, hXi_eq⟩ :=
    exists_globalSmooth_chartBasisVec_ext_alpha (I := I) α i hx
  set U : Set M := Uj ∩ Uk ∩ Ui with hU_def
  have hU_open : IsOpen U := (hUj_open.inter hUk_open).inter hUi_open
  have hxU : x ∈ U := ⟨⟨hxUj, hxUk⟩, hxUi⟩
  have hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) α :=
    fun y hy => hUj_good hy.1.1
  have hXj_eqU : ∀ y ∈ U, Xj y = chartBasisVecFiber (I := I) α j y :=
    fun y hy => hXj_eq y hy.1.1
  have hXk_eqU : ∀ y ∈ U, Xk y = chartBasisVecFiber (I := I) α k y :=
    fun y hy => hXk_eq y hy.1.2
  have hXi_eqU : ∀ y ∈ U, Xi y = chartBasisVecFiber (I := I) α i y :=
    fun y hy => hXi_eq y hy.2
  have hXj_x : Xj x = chartBasisVecFiber (I := I) α j x := hXj_eqU x hxU
  have hXk_x : Xk x = chartBasisVecFiber (I := I) α k x := hXk_eqU x hxU
  have hXi_x : Xi x = chartBasisVecFiber (I := I) α i x := hXi_eqU x hxU
  rw [show (chartBasisVecFiber (I := I) α j x : TangentSpace I x) = Xj x from hXj_x.symm,
      show (chartBasisVecFiber (I := I) α k x : TangentSpace I x) = Xk x from hXk_x.symm,
      show (chartBasisVecFiber (I := I) α i x : TangentSpace I x) = Xi x from hXi_x.symm]
  rw [riemannOp_apply_smooth (cov := cov) hXj_sm hXk_sm hXi_sm]
  rw [riemannSec_def]
  rw [mlieBracket_chartBasisVec_ext_self_eq_zero_alpha (I := I) α j k hx hXj_sm hXk_sm
    hU_open hxU hXj_eqU hXk_eqU]
  rw [ContinuousLinearMap.map_zero, sub_zero]
  rw [LeviCivita_chartBasisVec_secondCovDeriv_alpha (I := I) g α j k i hx
    hXj_sm hXk_sm hXi_sm hU_open hxU hU_good hXj_eqU hXk_eqU hXi_eqU]
  rw [LeviCivita_chartBasisVec_secondCovDeriv_alpha (I := I) g α k j i hx
    hXk_sm hXj_sm hXi_sm hU_open hxU hU_good hXk_eqU hXj_eqU hXi_eqU]
  have hcoeff : ∀ l : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) j (chartChristoffel (I := I) g α k i l) (extChartAt I α x) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m l (extChartAt I α x) *
              chartChristoffel (I := I) g α k i m (extChartAt I α x)) -
        (partialDeriv (E := E) k (chartChristoffel (I := I) g α j i l) (extChartAt I α x) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k m l (extChartAt I α x) *
              chartChristoffel (I := I) g α j i m (extChartAt I α x)) =
      chartRiemannTensor (I := I) g α i j k l (extChartAt I α x) := by
    intro l
    rw [chartRiemannTensor_def]
    have hΓsym1 : (chartChristoffel (I := I) g α k i l) = (chartChristoffel (I := I) g α i k l) := by
      funext y; exact chartChristoffel_symm (I := I) g α k i l y
    have hΓsym2 : (chartChristoffel (I := I) g α j i l) = (chartChristoffel (I := I) g α i j l) := by
      funext y; exact chartChristoffel_symm (I := I) g α j i l y
    rw [hΓsym1, hΓsym2]
    have hquad :
        (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m l (extChartAt I α x) *
              chartChristoffel (I := I) g α i k m (extChartAt I α x)) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k m l (extChartAt I α x) *
              chartChristoffel (I := I) g α i j m (extChartAt I α x)) =
        ∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α j m l (extChartAt I α x) *
              chartChristoffel (I := I) g α i k m (extChartAt I α x) -
            chartChristoffel (I := I) g α k m l (extChartAt I α x) *
              chartChristoffel (I := I) g α i j m (extChartAt I α x)) :=
      (Finset.sum_sub_distrib _ _).symm
    have hq1 : ∀ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α j m l (extChartAt I α x) *
            chartChristoffel (I := I) g α k i m (extChartAt I α x) =
          chartChristoffel (I := I) g α j m l (extChartAt I α x) *
            chartChristoffel (I := I) g α i k m (extChartAt I α x) := by
      intro m; rw [chartChristoffel_symm (I := I) g α k i m]
    have hq2 : ∀ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α k m l (extChartAt I α x) *
            chartChristoffel (I := I) g α j i m (extChartAt I α x) =
          chartChristoffel (I := I) g α k m l (extChartAt I α x) *
            chartChristoffel (I := I) g α i j m (extChartAt I α x) := by
      intro m; rw [chartChristoffel_symm (I := I) g α j i m]
    rw [Finset.sum_congr rfl (fun m _ => hq1 m), Finset.sum_congr rfl (fun m _ => hq2 m)]
    rw [← hquad]
    ring
  refine (Finset.sum_sub_distrib _ _).symm.trans ?_
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← hcoeff l]
  exact (sub_smul _ _ _).symm

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciTensor_chartBasisVec_alpha_eq [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    ricciTensor (I := I) g x
        (chartBasisVecFiber (I := I) α p x) (chartBasisVecFiber (I := I) α q x) =
      chartRicciTensor (I := I) g α p q (extChartAt I α x) := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  set bα : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    chartBasisFamily (I := I) α hxbase with hbα_def
  have hbα_apply : ∀ t : Fin (Module.finrank ℝ E),
      bα t = chartBasisVecFiber (I := I) α t x := fun t =>
    chartBasisFamily_apply (I := I) α hxbase t
  rw [ricciTensor_apply]
  rw [LinearMap.trace_eq_matrix_trace ℝ bα
        (ricciEndo (I := I) g x
          (chartBasisVecFiber (I := I) α p x) (chartBasisVecFiber (I := I) α q x))]
  unfold Matrix.trace
  have hdiag : ∀ t : Fin (Module.finrank ℝ E),
      (Matrix.diag
        (LinearMap.toMatrix bα bα
          (ricciEndo (I := I) g x
            (chartBasisVecFiber (I := I) α p x) (chartBasisVecFiber (I := I) α q x)))) t =
        chartRiemannTensor (I := I) g α q t p t (extChartAt I α x) := by
    intro t
    simp only [Matrix.diag_apply]
    rw [LinearMap.toMatrix_apply]
    rw [hbα_apply t]
    rw [show (ricciEndo (I := I) g x
          (chartBasisVecFiber (I := I) α p x) (chartBasisVecFiber (I := I) α q x))
          (chartBasisVecFiber (I := I) α t x) =
        riemannOp (cov := LeviCivita (I := I) g) x
          (chartBasisVecFiber (I := I) α t x)
          (chartBasisVecFiber (I := I) α p x)
          (chartBasisVecFiber (I := I) α q x) from rfl]
    rw [riemannOp_chartBasisVec_alpha_eq (I := I) g α q t p hx]
    rw [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single t]
    · rw [← hbα_apply t, LinearEquiv.map_smul, Finsupp.smul_apply,
        Module.Basis.repr_self_apply, smul_eq_mul, if_pos rfl, mul_one]
    · intro l _ hl_ne
      rw [← hbα_apply l, LinearEquiv.map_smul, Finsupp.smul_apply,
        Module.Basis.repr_self_apply, smul_eq_mul, if_neg hl_ne, mul_zero]
    · intro hl; exact absurd (Finset.mem_univ t) hl
  rw [Finset.sum_congr rfl (fun t _ => hdiag t)]
  have hricci_qp : (∑ t : Fin (Module.finrank ℝ E),
      chartRiemannTensor (I := I) g α q t p t (extChartAt I α x)) =
        chartRicciTensor (I := I) g α q p (extChartAt I α x) := by
    rw [chartRicciTensor_def]
  rw [hricci_qp]
  have hxchart : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  exact chartRicciTensor_symm_of_boundaryless (I := I) g α q p hxchart

end Connection
end Integral
end DifferentialGeometry

end
