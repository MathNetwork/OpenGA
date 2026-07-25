import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.Manifold
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge
import DifferentialGeometry.Analysis.ODE.ForwardVariationalFromZero
import Mathlib.Geometry.Manifold.IntegralCurve.Basic


open Set Function Filter Metric Bundle
open scoped Topology NNReal ContDiff Manifold

namespace DifferentialGeometry.PDE.RicciFlow.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]

noncomputable def fromZeroChartField (X : ℝ → ∀ x : M, TangentSpace I x) (α : M) :
    ℝ → E → E :=
  fun s c =>
    ((trivializationAt E (TangentSpace I) α)
      (TotalSpace.mk' E ((extChartAt I α).symm c) (X s ((extChartAt I α).symm c)))).2

omit [FiniteDimensional ℝ E] [CompleteSpace E] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] in
lemma fromZeroChartField_eq_tangentCoordChange
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M) (s : ℝ) (c : E) :
    fromZeroChartField (I := I) X α s c
      = tangentCoordChange I ((extChartAt I α).symm c) α ((extChartAt I α).symm c)
          (X s ((extChartAt I α).symm c)) := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] in
theorem fromZeroChartField_jointContDiffOn_Ioo
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M) (T : ℝ)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    {ρ : ℝ} (_hρ : 0 < ρ)
    (hρ_sub : Metric.ball (extChartAt I α α) ρ ⊆ (extChartAt I α).target) :
    ContDiffOn ℝ ∞ (Function.uncurry (fromZeroChartField (I := I) X α))
      (Set.Ioo (0 : ℝ) T ×ˢ Metric.ball (extChartAt I α α) ρ) := by
  set x₀ : E := extChartAt I α α with hx₀
  set e := trivializationAt E (TangentSpace I) α with he
  set f : ℝ × M → TangentBundle I M :=
    fun q => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M) with hf
  set S : Set (ℝ × M) :=
    Set.Ioo (0 : ℝ) T ×ˢ ((extChartAt I α).symm '' Metric.ball x₀ ρ) with hS
  have hX_on : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞ f S := by
    refine hint.mono ?_
    rintro ⟨s, p⟩ ⟨hs, _⟩
    exact ⟨hs, Set.mem_univ _⟩
  have hmaps : Set.MapsTo f S e.source := by
    rintro ⟨s, p⟩ hq
    obtain ⟨-, c, hc, rfl⟩ := hq
    have hcsrc : (extChartAt I α).symm c ∈ (chartAt H α).source := by
      have hmem : (extChartAt I α).symm c ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target (hρ_sub hc)
      rwa [extChartAt_source] at hmem
    rw [he, TangentBundle.trivializationAt_source]
    exact hcsrc
  have hreading : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => (e (f q)).2) S :=
    ((e.contMDiffOn_iff hmaps).mp hX_on).2
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm (Metric.ball x₀ ρ) :=
    (contMDiffOn_extChartAt_symm α).mono hρ_sub
  have hreindex :
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
        (Prod.map (id : ℝ → ℝ) (extChartAt I α).symm)
        (Set.Ioo (0 : ℝ) T ×ˢ Metric.ball x₀ ρ) :=
    (contMDiffOn_id (I := 𝓘(ℝ, ℝ))).prodMap hsymm
  have hsub :
      (Set.Ioo (0 : ℝ) T ×ˢ Metric.ball x₀ ρ) ⊆
        Prod.map (id : ℝ → ℝ) (extChartAt I α).symm ⁻¹' S := by
    rintro ⟨s, c⟩ ⟨hs, hc⟩
    exact ⟨hs, Set.mem_image_of_mem _ hc⟩
  have hcomp :
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        ((fun q : ℝ × M => (e (f q)).2) ∘ Prod.map (id : ℝ → ℝ) (extChartAt I α).symm)
        (Set.Ioo (0 : ℝ) T ×ˢ Metric.ball x₀ ρ) :=
    hreading.comp hreindex hsub
  have hfun :
      ((fun q : ℝ × M => (e (f q)).2) ∘ Prod.map (id : ℝ → ℝ) (extChartAt I α).symm)
        = Function.uncurry (fromZeroChartField (I := I) X α) := by
    funext q
    rfl
  rw [hfun] at hcomp
  rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hcomp

omit [FiniteDimensional ℝ E] [CompleteSpace E] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] in
theorem fromZeroChartField_continuousOn_time_from_zero
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M) {T δ : ℝ} (hδT : δ ≤ T)
    (hcont0 : ContinuousOn
      (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (c : E) :
    ContinuousOn (fun s : ℝ => fromZeroChartField (I := I) X α s c) (Set.Icc (0 : ℝ) δ) := by
  set y : M := (extChartAt I α).symm c with hy
  set T₀ : E →L[ℝ] E := tangentCoordChange I y α y with hT₀
  have hrw : (fun s : ℝ => fromZeroChartField (I := I) X α s c)
      = fun s : ℝ => T₀ (X s y) := by
    funext s
    rw [fromZeroChartField_eq_tangentCoordChange]
  rw [hrw]
  have hXy : ContinuousOn (fun s : ℝ => (X s y : TangentSpace I y)) (Set.Icc (0 : ℝ) δ) := by
    have hcomp : ContinuousOn (fun s : ℝ => (X s y : TangentSpace I y))
        (Set.Icc (0 : ℝ) T) := by
      have hmaps : Set.MapsTo (fun s : ℝ => ((s, y) : ℝ × M))
          (Set.Icc (0 : ℝ) T) (Set.Icc (0 : ℝ) T ×ˢ Set.univ) :=
        fun s hs => ⟨hs, Set.mem_univ _⟩
      have hpair : ContinuousOn (fun s : ℝ => ((s, y) : ℝ × M)) (Set.Icc (0 : ℝ) T) :=
        (continuous_id.prodMk continuous_const).continuousOn
      exact hcont0.comp hpair hmaps
    exact hcomp.mono (Set.Icc_subset_Icc_right hδT)
  exact T₀.continuous.comp_continuousOn hXy

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem fromZero_orbit_confined
    {f : ℝ → E → E} {x₀ : E} {a L : ℝ} {δ : ℝ} (hL : 0 ≤ L)
    (γ : ℝ → E) (hγ_init : γ 0 = x₀)
    (hγcont : ContinuousOn γ (Set.Icc (0 : ℝ) δ))
    (hγderiv : ∀ t ∈ Set.Ico (0 : ℝ) δ, HasDerivWithinAt γ (f t (γ t)) (Set.Ici (0 : ℝ)) t)
    (hfnorm : ∀ t ∈ Set.Icc (0 : ℝ) δ, ∀ y ∈ Metric.closedBall x₀ a, ‖f t y‖ ≤ L)
    (hLδ : L * δ < a) :
    ∀ s ∈ Set.Icc (0 : ℝ) δ, γ s ∈ Metric.closedBall x₀ a := by
  have hdist_continuousOn : ContinuousOn (fun t : ℝ => dist (γ t) x₀) (Set.Icc 0 δ) :=
    continuous_dist.comp_continuousOn (hγcont.prodMk continuousOn_const)
  set g : ℝ → ℝ := fun t => dist (γ t) x₀ - L * t with hg
  have hg_cont : ContinuousOn g (Set.Icc 0 δ) :=
    hdist_continuousOn.sub (continuousOn_const.mul continuousOn_id)
  set S : Set ℝ := {t : ℝ | dist (γ t) x₀ ≤ L * t} with hS
  have hbound_to_openball : ∀ s, s ∈ Set.Ico (0 : ℝ) δ → s ∈ S →
      dist (γ s) x₀ < a := by
    intro s hs hsS
    refine lt_of_le_of_lt hsS ?_
    have hsδ : s ≤ δ := le_of_lt hs.2
    calc L * s ≤ L * δ := by nlinarith [hL]
      _ < a := hLδ
  have hScl : IsClosed (S ∩ Set.Icc (0 : ℝ) δ) := by
    have hpre : IsClosed (Set.Icc (0 : ℝ) δ ∩ g ⁻¹' Set.Iic 0) :=
      hg_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have heq : Set.Icc (0 : ℝ) δ ∩ g ⁻¹' Set.Iic 0 = S ∩ Set.Icc (0 : ℝ) δ := by
      ext t
      simp only [hS, hg, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq,
        sub_nonpos]
      tauto
    rwa [heq] at hpre
  have h0S : (0 : ℝ) ∈ S := by
    simp only [hS, Set.mem_setOf_eq, hγ_init, dist_self, mul_zero, le_refl]
  have hgt : ∀ x ∈ S ∩ Set.Ico (0 : ℝ) δ, ∀ y ∈ Set.Ioi x, (S ∩ Set.Ioc x y).Nonempty := by
    rintro x ⟨hxS, hx_mem⟩ y hy
    have hxδ : x < δ := hx_mem.2
    have hx0 : 0 ≤ x := hx_mem.1
    have hopen_x : dist (γ x) x₀ < a := hbound_to_openball x hx_mem hxS
    have hballnbhd : {u : ℝ | dist (γ u) x₀ < a} ∈ nhdsWithin x (Set.Icc (0 : ℝ) δ) := by
      have hcontx : ContinuousWithinAt (fun u : ℝ => dist (γ u) x₀) (Set.Icc 0 δ) x :=
        hdist_continuousOn x ⟨hx0, le_of_lt hxδ⟩
      exact hcontx (isOpen_Iio.mem_nhds hopen_x)
    obtain ⟨ε, hε_pos, hε_sub⟩ : ∃ ε > 0, ∀ u ∈ Set.Icc x (x + ε),
        u ∈ Set.Icc (0 : ℝ) δ ∧ dist (γ u) x₀ ≤ a := by
      rw [Metric.mem_nhdsWithin_iff] at hballnbhd
      obtain ⟨ρ, hρ_pos, hρ_sub⟩ := hballnbhd
      have hm_pos : 0 < min ρ (δ - x) := lt_min hρ_pos (by linarith)
      refine ⟨min ρ (δ - x) / 2, by positivity, fun u hu => ?_⟩
      have hu1 : x ≤ u := hu.1
      have hu2 : u ≤ x + min ρ (δ - x) / 2 := hu.2
      have hux_lt : u - x < min ρ (δ - x) := by
        have : u - x ≤ min ρ (δ - x) / 2 := by linarith
        linarith [hm_pos]
      have hu_le_δ : u ≤ δ := by
        have h1 : u - x < δ - x := lt_of_lt_of_le hux_lt (min_le_right _ _)
        linarith
      have hu_mem : u ∈ Set.Icc (0 : ℝ) δ := ⟨le_trans hx0 hu1, hu_le_δ⟩
      refine ⟨hu_mem, le_of_lt ?_⟩
      have hu_ball : u ∈ Metric.ball x ρ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
        exact lt_of_lt_of_le hux_lt (min_le_left _ _)
      have := hρ_sub ⟨hu_ball, hu_mem⟩
      simpa using this
    set z : ℝ := min y (x + ε / 2) with hz
    have hxz : x < z := by
      rw [hz]; exact lt_min hy (by linarith)
    have hzy : z ≤ y := by rw [hz]; exact min_le_left _ _
    have hz_lt : z < x + ε := by
      rw [hz]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hvel : ∀ u ∈ Set.Ico x z, ‖f u (γ u)‖ ≤ L := by
      intro u hu
      have huicc : u ∈ Set.Icc x (x + ε) :=
        ⟨hu.1, le_of_lt (lt_trans hu.2 hz_lt)⟩
      obtain ⟨hu_mem, hu_ball⟩ := hε_sub u huicc
      exact hfnorm u hu_mem (γ u) (by rwa [Metric.mem_closedBall])
    have hz_le_δ : z ≤ δ := by
      have hxe : x + ε ≤ δ :=
        (hε_sub (x + ε) ⟨by linarith, le_refl _⟩).1.2
      linarith [hz_lt]
    have hseg : ‖γ z - γ x‖ ≤ L * (z - x) := by
      have hcont_xz : ContinuousOn γ (Set.Icc x z) :=
        hγcont.mono (fun u hu => ⟨le_trans hx0 hu.1, le_trans hu.2 hz_le_δ⟩)
      have hderiv_xz : ∀ u ∈ Set.Ico x z, HasDerivWithinAt γ (f u (γ u)) (Set.Ici u) u := by
        intro u hu
        have hu_mem : u ∈ Set.Ico (0 : ℝ) δ :=
          ⟨le_trans hx0 hu.1, lt_of_lt_of_le hu.2 hz_le_δ⟩
        exact (hγderiv u hu_mem).mono_of_mem_nhdsWithin
          (by
            apply Filter.mem_of_superset (self_mem_nhdsWithin)
            intro w hw; exact le_trans (le_trans hx0 hu.1) hw)
      exact norm_image_sub_le_of_norm_deriv_right_le_segment hcont_xz hderiv_xz hvel z
        (right_mem_Icc.2 (le_of_lt hxz))
    refine ⟨z, ?_, hxz, hzy⟩
    simp only [hS, Set.mem_setOf_eq]
    calc dist (γ z) x₀ ≤ dist (γ z) (γ x) + dist (γ x) x₀ := dist_triangle _ _ _
      _ = ‖γ z - γ x‖ + dist (γ x) x₀ := by rw [dist_eq_norm]
      _ ≤ L * (z - x) + L * x := by gcongr; exact hxS
      _ = L * z := by ring
  have hmain : Set.Icc (0 : ℝ) δ ⊆ S :=
    hScl.Icc_subset_of_forall_exists_gt h0S hgt
  intro s hs
  rw [Metric.mem_closedBall]
  rcases eq_or_lt_of_le hs.2 with hsδ | hsδ
  · have hsS : s ∈ S := hmain hs
    refine le_of_lt (lt_of_le_of_lt hsS ?_)
    rw [hsδ]; exact hLδ
  · exact le_of_lt (hbound_to_openball s ⟨hs.1, hsδ⟩ (hmain hs))

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] in
theorem fromZero_manifold_orbit_of_lipschitz
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    {a r : ℝ≥0} {K L : ℝ≥0} {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.closedBall (extChartAt I α α) (a : ℝ) ⊆ (extChartAt I α).target)
    (hlip : ∀ t ∈ Set.Icc (0 : ℝ) δ,
      LipschitzOnWith K (fromZeroChartField (I := I) X α t)
        (Metric.closedBall (extChartAt I α α) a))
    (hcont : ∀ c ∈ Metric.closedBall (extChartAt I α α) a,
      ContinuousOn (fun s : ℝ => fromZeroChartField (I := I) X α s c) (Set.Icc (0 : ℝ) δ))
    (hnorm : ∀ t ∈ Set.Icc (0 : ℝ) δ, ∀ c ∈ Metric.closedBall (extChartAt I α α) a,
      ‖fromZeroChartField (I := I) X α t c‖ ≤ L)
    (hmul : (L : ℝ) * δ < (a : ℝ) - r) (hr : (0 : ℝ) < r) :
    ∃ Φ : ℝ → M, Φ 0 = α ∧
      (∀ s ∈ Set.Ico (0 : ℝ) δ, Φ s ∈ (chartAt H α).source) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) δ,
        HasDerivWithinAt (fun s : ℝ => extChartAt I α (Φ s))
          (tangentCoordChange I (Φ t) α (Φ t) (X t (Φ t))) (Set.Ici (0 : ℝ)) t) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) δ,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s) (Set.Ici (0 : ℝ)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t)))) := by
  classical
  set x₀ : E := extChartAt I α α with hx₀
  set F : ℝ → E → E := fromZeroChartField (I := I) X α with hF
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have hmul_le : (L : ℝ) * δ ≤ (a : ℝ) - r := le_of_lt hmul
  have hxmem : x₀ ∈ Metric.closedBall x₀ (r : ℝ) := Metric.mem_closedBall_self r.coe_nonneg
  obtain ⟨γE, hγE0, hγEcont, hγEderiv⟩ :=
    DifferentialGeometry.Analysis.ODE.forward_picard_solution_from_zero
      (E := E) (f := F) (x₀ := x₀)
      (a := a) (r := r) (L := L) (K := K) (δ := δ) hδ hlip hcont hnorm hmul_le hxmem
  have hLδ_a : (L : ℝ) * δ < (a : ℝ) := lt_of_lt_of_le hmul (by linarith [r.coe_nonneg])
  have hconf : ∀ s ∈ Set.Icc (0 : ℝ) δ, γE s ∈ Metric.closedBall x₀ (a : ℝ) :=
    fromZero_orbit_confined (f := F) (x₀ := x₀) (a := a) (L := L) hLnn γE hγE0 hγEcont hγEderiv
      hnorm hLδ_a
  refine ⟨fun s => (extChartAt I α).symm (γE s), ?_, ?_, ?_, ?_⟩
  · simp only [hγE0, hx₀]
    exact (extChartAt I α).left_inv (mem_extChartAt_source α)
  · intro s hs
    have hsicc : s ∈ Set.Icc (0 : ℝ) δ := ⟨hs.1, le_of_lt hs.2⟩
    have htgt : γE s ∈ (extChartAt I α).target := hball (hconf s hsicc)
    have : (extChartAt I α).symm (γE s) ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target htgt
    rwa [extChartAt_source] at this
  · intro t ht
    have hticc : t ∈ Set.Icc (0 : ℝ) δ := ⟨ht.1, le_of_lt ht.2⟩
    have hIco_mem : Set.Ico (0 : ℝ) δ ∈ nhdsWithin t (Set.Ici (0 : ℝ)) := by
      have hIco_eq : Set.Ico (0 : ℝ) δ = Set.Ici (0 : ℝ) ∩ Set.Iio δ := by
        ext u; exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
      rw [hIco_eq]
      exact Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds ht.2))
    have hd : HasDerivWithinAt γE (F t (γE t)) (Set.Ici (0 : ℝ)) t := hγEderiv t ht
    have hvel_eq : F t (γE t)
        = tangentCoordChange I ((extChartAt I α).symm (γE t)) α ((extChartAt I α).symm (γE t))
            (X t ((extChartAt I α).symm (γE t))) := rfl
    have hcongr : (fun s : ℝ => extChartAt I α ((extChartAt I α).symm (γE s)))
        =ᶠ[nhdsWithin t (Set.Ici (0 : ℝ))] γE := by
      filter_upwards [hIco_mem] with u hu
      have huicc : u ∈ Set.Icc (0 : ℝ) δ := ⟨hu.1, le_of_lt hu.2⟩
      exact (extChartAt I α).right_inv (hball (hconf u huicc))
    have hd' : HasDerivWithinAt (fun s : ℝ => extChartAt I α ((extChartAt I α).symm (γE s)))
        (F t (γE t)) (Set.Ici (0 : ℝ)) t :=
      hd.congr_of_eventuallyEq hcongr
        ((extChartAt I α).right_inv (hball (hconf t hticc)))
    rw [hvel_eq] at hd'
    exact hd'
  · intro t ht
    have hticc : t ∈ Set.Icc (0 : ℝ) δ := ⟨ht.1, le_of_lt ht.2⟩
    have htgt_t : γE t ∈ (extChartAt I α).target := hball (hconf t hticc)
    have hIco_mem : Set.Ico (0 : ℝ) δ ∈ nhdsWithin t (Set.Ici (0 : ℝ)) := by
      have hIco_eq : Set.Ico (0 : ℝ) δ = Set.Ici (0 : ℝ) ∩ Set.Iio δ := by
        ext u; exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
      rw [hIco_eq]
      exact Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds ht.2))
    have hconf_range : γE ⁻¹' (Set.range I) ∈ nhdsWithin t (Set.Ici (0 : ℝ)) := by
      filter_upwards [hIco_mem] with u hu
      have huicc : u ∈ Set.Icc (0 : ℝ) δ := ⟨hu.1, le_of_lt hu.2⟩
      exact extChartAt_target_subset_range α (hball (hconf u huicc))
    have hd : HasDerivWithinAt γE (F t (γE t)) (Set.Ici (0 : ℝ)) t := hγEderiv t ht
    have hbridge := chartCoord_hasDerivWithinAt_to_manifold_hasMFDerivWithinAt
      (I := I) α γE (Set.Ici (0 : ℝ)) t (F t (γE t)) htgt_t hconf_range hd
    set q : M := (extChartAt I α).symm (γE t) with hq_def
    have hq_src : q ∈ (extChartAt I α).source := (extChartAt I α).map_target htgt_t
    have hq_round : extChartAt I α q = γE t := (extChartAt I α).right_inv htgt_t
    have hcancel :
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I) (γE t)) (F t (γE t))
          = X t q := by
      have hFeq : F t (γE t)
          = tangentCoordChange I q α q (X t q) := rfl
      rw [hFeq, ← hq_round]
      exact pushforward_velocity_cancellation (I := I) α q hq_src (X t q)
    have hvelCLM :
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I) (γE t)) ∘L
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (F t (γE t)))
          = (1 : ℝ →L[ℝ] ℝ).smulRight (X t q) :=
      ContinuousLinearMap.ext fun rr => by
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.id_apply, ContinuousLinearMap.one_apply, map_smul, hcancel]
    rw [← hvelCLM]
    exact hbridge

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] in
private theorem fromZero_orbit_of_window
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M) {T : ℝ}
    {a : ℝ≥0} {δ_w : ℝ} {K : ℝ≥0} {Mbd : ℝ}
    (ha_pos : 0 < (a : ℝ)) (hδw_pos : 0 < δ_w) (hδw_le : δ_w ≤ T)
    (hcont0 : ContinuousOn
      (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hball : Metric.closedBall (extChartAt I α α) (a : ℝ) ⊆ (extChartAt I α).target)
    (hlip0 : ∀ t ∈ Set.Icc (0 : ℝ) δ_w,
      LipschitzOnWith K (fromZeroChartField (I := I) X α t)
        (Metric.closedBall (extChartAt I α α) a))
    (hcenter : ∀ t ∈ Set.Icc (0 : ℝ) δ_w,
      ‖fromZeroChartField (I := I) X α t (extChartAt I α α)‖ ≤ Mbd)
    (hstrict : ((Real.toNNReal Mbd + K * a : ℝ≥0) : ℝ) * δ_w < (a : ℝ) / 2) :
    ∃ Φ : ℝ → M, Φ 0 = α ∧
      (∀ s ∈ Set.Ico (0 : ℝ) δ_w, Φ s ∈ (chartAt H α).source) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) δ_w,
        HasDerivWithinAt (fun s : ℝ => extChartAt I α (Φ s))
          (tangentCoordChange I (Φ t) α (Φ t) (X t (Φ t))) (Set.Ici (0 : ℝ)) t) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) δ_w,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s) (Set.Ici (0 : ℝ)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t)))) := by
  set x₀ : E := extChartAt I α α with hx₀
  set F : ℝ → E → E := fromZeroChartField (I := I) X α with hF
  set M₀N : ℝ≥0 := Real.toNNReal Mbd with hM₀N
  have hM₀N_coe : (M₀N : ℝ) = max Mbd 0 := by rw [hM₀N, Real.coe_toNNReal']
  set L : ℝ≥0 := M₀N + K * a with hL
  have hL_coe : (L : ℝ) = (M₀N : ℝ) + (K : ℝ) * (a : ℝ) := by push_cast [hL]; ring
  set r : ℝ≥0 := a / 2 with hr
  have hr_pos : (0 : ℝ) < (r : ℝ) := by rw [hr]; push_cast; positivity
  have har : (a : ℝ) - (r : ℝ) = (a : ℝ) / 2 := by rw [hr]; push_cast; ring
  have hnorm : ∀ t ∈ Set.Icc (0 : ℝ) δ_w, ∀ c ∈ Metric.closedBall x₀ (a : ℝ),
      ‖F t c‖ ≤ L := by
    intro t ht c hc
    have hdist : dist c x₀ ≤ (a : ℝ) := by rwa [Metric.mem_closedBall] at hc
    have hLip := (hlip0 t ht).dist_le_mul c hc x₀ (Metric.mem_closedBall_self ha_pos.le)
    have hcb : ‖F t x₀‖ ≤ (M₀N : ℝ) :=
      le_trans (hcenter t ht) (by rw [hM₀N_coe]; exact le_max_left _ _)
    calc ‖F t c‖
        ≤ ‖F t c - F t x₀‖ + ‖F t x₀‖ := norm_le_norm_sub_add _ _
      _ = dist (F t c) (F t x₀) + ‖F t x₀‖ := by rw [dist_eq_norm]
      _ ≤ (K : ℝ) * dist c x₀ + ‖F t x₀‖ := by gcongr
      _ ≤ (K : ℝ) * (a : ℝ) + (M₀N : ℝ) := by gcongr
      _ = (L : ℝ) := by rw [hL_coe]; ring
  have hstrict' : (L : ℝ) * δ_w < (a : ℝ) - r := by rw [har]; exact hstrict
  exact fromZero_manifold_orbit_of_lipschitz (I := I) X α (a := a) (r := r) (K := K) (L := L)
    (δ := δ_w) hδw_pos hball hlip0
    (fun c _ => fromZeroChartField_continuousOn_time_from_zero (I := I) X α hδw_le hcont0 c)
    hnorm hstrict' hr_pos

omit [FiniteDimensional ℝ E] [CompleteSpace E] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] in
private lemma fromZeroChartField_center_eq
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M) (t : ℝ) :
    fromZeroChartField (I := I) X α t (extChartAt I α α) = (X t α : TangentSpace I α) := by
  have hsymm : (extChartAt I α).symm (extChartAt I α α) = α :=
    (extChartAt I α).left_inv (mem_extChartAt_source α)
  rw [fromZeroChartField_eq_tangentCoordChange, hsymm]
  exact tangentCoordChange_self (I := I) (mem_extChartAt_source α)

end DifferentialGeometry.PDE.RicciFlow.ODE
