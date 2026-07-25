import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeExistence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false
set_option linter.style.longLine false












































































noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]













theorem tendsto_nhdsLT_of_bounded_deriv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f f' : ℝ → F} {a b C : ℝ} (hab : a < b)
    (hderiv : ∀ s : ℝ, s ∈ Set.Ioo a b → HasDerivAt f (f' s) s)
    (hbound : ∀ s : ℝ, s ∈ Set.Ioo a b → ‖f' s‖ ≤ C) :
    ∃ L : F, Tendsto f (𝓝[<] b) (𝓝 L) := by
  haveI hNB : (𝓝[<] b).NeBot := nhdsWithin_Iio_neBot (le_refl b)
  suffices hcauchy : Cauchy (Filter.map f (𝓝[<] b)) by
    exact cauchy_map_iff_exists_tendsto.mp hcauchy
  refine Metric.cauchy_iff.mpr ⟨Filter.map_neBot, ?_⟩
  have hC_nn : 0 ≤ C := by
    have hmid : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
    exact le_trans (norm_nonneg _) (hbound _ hmid)
  intro ε hε
  have hCC_pos : 0 < C + 1 := by linarith
  set η : ℝ := ε / (C + 1) with hη_def
  have hη_pos : 0 < η := div_pos hε hCC_pos
  set lo : ℝ := max a (b - η) with hlo_def
  have hlo_lt_b : lo < b := max_lt hab (by linarith)
  have ha_le_lo : a ≤ lo := le_max_left _ _
  have hsub : Set.Ioo lo b ⊆ Set.Ioo a b :=
    fun τ hτ => ⟨lt_of_le_of_lt ha_le_lo hτ.1, hτ.2⟩
  have hIoo_mem : f '' Set.Ioo lo b ∈ Filter.map f (𝓝[<] b) :=
    Filter.image_mem_map (Ioo_mem_nhdsLT hlo_lt_b)
  refine ⟨f '' Set.Ioo lo b, hIoo_mem, ?_⟩
  rintro x ⟨sx, hsx, rfl⟩ y ⟨sy, hsy, rfl⟩
  set s : ℝ := min sx sy with hs_def
  set t : ℝ := max sx sy with ht_def
  have hst : s ≤ t := min_le_max
  have ht_hi : t < b := max_lt hsx.2 hsy.2
  have hs_lo : lo < s := lt_min hsx.1 hsy.1
  have ht_sub_s_lt : t - s < η := by
    have hlo_ge : b - η ≤ lo := le_max_right _ _
    rcases le_total sx sy with h | h
    · rw [hs_def, ht_def, min_eq_left h, max_eq_right h]; linarith [hsy.2, hsx.1]
    · rw [hs_def, ht_def, min_eq_right h, max_eq_left h]; linarith [hsx.2, hsy.1]
  have hmvt : ‖f t - f s‖ ≤ C * (t - s) := by
    have hIcc_sub : Set.Icc s t ⊆ Set.Ioo a b := by
      intro τ hτ
      exact hsub ⟨lt_of_lt_of_le hs_lo hτ.1, lt_of_le_of_lt hτ.2 ht_hi⟩
    have hderivW : ∀ x ∈ Set.Icc s t, HasDerivWithinAt f (f' x) (Set.Icc s t) x :=
      fun x hx => (hderiv x (hIcc_sub hx)).hasDerivWithinAt
    have hboundW : ∀ x ∈ Set.Ico s t, ‖f' x‖ ≤ C :=
      fun x hx => hbound x (hIcc_sub (Set.Ico_subset_Icc_self hx))
    exact norm_image_sub_le_of_norm_deriv_le_segment' hderivW hboundW t
      (right_mem_Icc.mpr hst)
  have h_dist_eq : dist (f sx) (f sy) = ‖f t - f s‖ := by
    rcases le_total sx sy with h | h
    · rw [hs_def, ht_def, min_eq_left h, max_eq_right h, dist_eq_norm, norm_sub_rev]
    · rw [hs_def, ht_def, min_eq_right h, max_eq_left h, dist_eq_norm]
  rw [h_dist_eq]
  calc ‖f t - f s‖ ≤ C * (t - s) := hmvt
    _ ≤ C * η := mul_le_mul_of_nonneg_left ht_sub_s_lt.le hC_nn
    _ < ε := by
        rw [hη_def]
        have hrw : C * (ε / (C + 1)) = ε * (C / (C + 1)) := by ring
        rw [hrw]
        have hfrac : C / (C + 1) < 1 := by rw [div_lt_one hCC_pos]; linarith
        have := mul_lt_mul_of_pos_left hfrac hε
        rwa [mul_one] at this










omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartGramMatrix_tendsto_nhdsLT_of_bounded_deriv
    (g_fam : ℝ → SmoothRiemannianMetric I M) {α omega : ℝ} (hαomega : α < omega)
    (x₀ x : M) (i j : Fin (Module.finrank ℝ E))
    {C : ℝ}
    (hderiv : ∀ s : ℝ, s ∈ Set.Ioo α omega →
      HasDerivAt (fun u : ℝ =>
        Integral.Measure.chartGramMatrix (I := I) (g_fam u) x₀ x i j)
        (deriv (fun u : ℝ =>
          Integral.Measure.chartGramMatrix (I := I) (g_fam u) x₀ x i j) s) s)
    (hbound : ∀ s : ℝ, s ∈ Set.Ioo α omega →
      |deriv (fun u : ℝ =>
        Integral.Measure.chartGramMatrix (I := I) (g_fam u) x₀ x i j) s| ≤ C) :
    ∃ L : ℝ, Tendsto (fun s : ℝ =>
      Integral.Measure.chartGramMatrix (I := I) (g_fam s) x₀ x i j) (𝓝[<] omega) (𝓝 L) := by
  refine tendsto_nhdsLT_of_bounded_deriv (F := ℝ) (a := α) (b := omega) (C := C) hαomega
    hderiv (fun s hs => ?_)
  simpa [Real.norm_eq_abs] using hbound s hs


















structure CinftyLimitData
    (g_fam : ℝ → SmoothRiemannianMetric I M) (α omega : ℝ) (hαomega : α < omega) where

  limitMetric : SmoothRiemannianMetric I M

  tendsto_left :
    ∀ (x₀ x : M) (i j : Fin (Module.finrank ℝ E)),
      Tendsto (fun s : ℝ =>
        Integral.Measure.chartGramMatrix (I := I) (g_fam s) x₀ x i j) (𝓝[<] omega)
        (𝓝 (Integral.Measure.chartGramMatrix (I := I) limitMetric x₀ x i j))



  ricci_match :
    ∀ (x : M) (v w : TangentSpace I x),
      Tendsto
        (fun s : ℝ =>
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g_fam s) x v w)
        (𝓝[<] omega)
        (𝓝 (DifferentialGeometry.Integral.Connection.ricciTensor (I := I)
          limitMetric x v w))























theorem restart_short_time (gomega : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, 0 < T ∧ ∃ r : ℝ → SmoothRiemannianMetric I M,
      r 0 = gomega ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (r p.1) x₀ p.2 i j)
          (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (r p.1) x₀ p.2 i j)
          (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : ℝ => (r s).inner x v w)
          ((-2 : ℝ) *
            DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (r t) x v w)
          (Set.Ici 0) t) := by
  obtain ⟨T, hT, r, hr0, hsmooth, hpde⟩ :=
    ricci_flow_short_time_existence (I := I) (M := M) gomega
  refine ⟨T, hT, r, hr0, hsmooth, ?_, hpde⟩










  intro x₀ i j
  exact (hsmooth x₀ i j).continuousOn










def gluedFamily
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (r : ℝ → SmoothRiemannianMetric I M) (omega : ℝ) :
    ℝ → SmoothRiemannianMetric I M :=
  fun s => if s < omega then g_fam s else r (s - omega)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem gluedFamily_of_lt
    (g_fam r : ℝ → SmoothRiemannianMetric I M) (omega : ℝ) {s : ℝ} (hs : s < omega) :
    gluedFamily (I := I) g_fam r omega s = g_fam s := by
  simp [gluedFamily, hs]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem gluedFamily_of_ge
    (g_fam r : ℝ → SmoothRiemannianMetric I M) (omega : ℝ) {s : ℝ} (hs : omega ≤ s) :
    gluedFamily (I := I) g_fam r omega s = r (s - omega) := by
  simp [gluedFamily, not_lt.mpr hs]





omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem gluedFamily_eq_left
    (g_fam r : ℝ → SmoothRiemannianMetric I M) (omega : ℝ) :
    ∀ s : ℝ, s < omega → gluedFamily (I := I) g_fam r omega s = g_fam s :=
  fun _ hs => gluedFamily_of_lt (I := I) g_fam r omega hs



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem gluedFamily_at_endpoint
    (g_fam r : ℝ → SmoothRiemannianMetric I M) (omega : ℝ) :
    gluedFamily (I := I) g_fam r omega omega = r 0 := by
  rw [gluedFamily_of_ge (I := I) g_fam r omega (le_refl omega), sub_self]
























omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem gluedFamily_pde_cross_of_matching
    (g_fam r : ℝ → SmoothRiemannianMetric I M) (gomega : SmoothRiemannianMetric I M)
    {α omega : ℝ} (hαomega : α < omega) (hr0 : r 0 = gomega)
    (hleft : ∀ t ∈ Set.Ico α omega, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
        ((-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g_fam t) x v w)
        (Set.Ici α) t)
    (hcont : ∀ x : M, ∀ v w : TangentSpace I x,
      Tendsto (fun s : ℝ => (g_fam s).inner x v w) (𝓝[<] omega)
        (𝓝 ((gomega).inner x v w)))
    (hderiv_lim : ∀ x : M, ∀ v w : TangentSpace I x,
      Tendsto
        (fun s : ℝ => (-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g_fam s) x v w)
        (𝓝[<] omega)
        (𝓝 ((-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I) gomega x v w))) :
    ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (gluedFamily (I := I) g_fam r omega s).inner x v w)
        ((-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I)
            (gluedFamily (I := I) g_fam r omega omega) x v w)
        (Set.Iic omega) omega := by
  intro x v w

  set f : ℝ → ℝ := fun s => (gluedFamily (I := I) g_fam r omega s).inner x v w with hf
  set g0 : ℝ → ℝ := fun s => (g_fam s).inner x v w with hg0

  have hfg0 : ∀ s ∈ Set.Ioo α omega, f s = g0 s := by
    intro s hs
    simp only [hf, hg0, gluedFamily_of_lt (I := I) g_fam r omega hs.2]


  have hg0_hasDeriv : ∀ s ∈ Set.Ioo α omega,
      HasDerivAt g0
        ((-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g_fam s) x v w) s := by
    intro s hs
    have hIci : Set.Ici α ∈ 𝓝 s := Ici_mem_nhds hs.1
    exact (hleft s ⟨le_of_lt hs.1, hs.2⟩ x v w).hasDerivAt hIci

  have hf_omega : f omega = (gomega).inner x v w := by
    simp only [hf, gluedFamily_at_endpoint (I := I) g_fam r omega, hr0]

  have hric_omega :
      DifferentialGeometry.Integral.Connection.ricciTensor (I := I)
        (gluedFamily (I := I) g_fam r omega omega) x v w =
      DifferentialGeometry.Integral.Connection.ricciTensor (I := I) gomega x v w := by
    simp only [gluedFamily_at_endpoint (I := I) g_fam r omega, hr0]
  rw [hric_omega]

  refine hasDerivWithinAt_Iic_of_tendsto_deriv (s := Set.Ioo α omega) (e := (-2 : ℝ) *
      DifferentialGeometry.Integral.Connection.ricciTensor (I := I) gomega x v w)
    (f := f) ?_ ?_ (Ioo_mem_nhdsLT hαomega) ?_
  ·
    intro s hs
    have hg0d : DifferentiableWithinAt ℝ g0 (Set.Ioo α omega) s :=
      (hg0_hasDeriv s hs).differentiableAt.differentiableWithinAt
    exact hg0d.congr (fun t ht => hfg0 t ht) (hfg0 s hs)
  ·
    have hg0_lim : Tendsto g0 (𝓝[Set.Ioo α omega] omega) (𝓝 ((gomega).inner x v w)) :=
      (hcont x v w).mono_left (nhdsWithin_mono omega (fun s hs => hs.2))
    have hf_lim : Tendsto f (𝓝[Set.Ioo α omega] omega) (𝓝 ((gomega).inner x v w)) := by
      refine hg0_lim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs using (hfg0 s hs).symm
    rw [ContinuousWithinAt, hf_omega]
    exact hf_lim
  ·
    refine (hderiv_lim x v w).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hαomega] with s hs

    have hev : f =ᶠ[𝓝 s] g0 := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht using hfg0 t ht
    rw [hev.deriv_eq, (hg0_hasDeriv s hs).deriv]


























omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem gluedFamily_pde
    (g_fam r : ℝ → SmoothRiemannianMetric I M) {α omega ε T : ℝ}
    (hαω : α < omega) (hε : 0 < ε) (hεT : ε ≤ T)
    (hleft : ∀ t ∈ Set.Ico α omega, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
        ((-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g_fam t) x v w)
        (Set.Ici α) t)
    (hright : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun u : ℝ => (r u).inner x v w)
        ((-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (r t) x v w)
        (Set.Ici 0) t)
    (hcross : ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (gluedFamily (I := I) g_fam r omega s).inner x v w)
        ((-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I)
            (gluedFamily (I := I) g_fam r omega omega) x v w)
        (Set.Iic omega) omega) :
    ∀ t ∈ Set.Ico α (omega + ε), ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (gluedFamily (I := I) g_fam r omega s).inner x v w)
        ((-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I)
            (gluedFamily (I := I) g_fam r omega t) x v w)
        (Set.Ici α) t := by
  intro t ht x v w
  rcases lt_trichotomy t omega with htlt | hteq | htgt
  ·
    have hg_t : gluedFamily (I := I) g_fam r omega t = g_fam t :=
      gluedFamily_of_lt (I := I) g_fam r omega htlt
    have hleftt := hleft t ⟨ht.1, htlt⟩ x v w

    have hev : (fun s : ℝ => (gluedFamily (I := I) g_fam r omega s).inner x v w)
        =ᶠ[𝓝[Set.Ici α] t] (fun s : ℝ => (g_fam s).inner x v w) := by
      have hmem : Set.Iio omega ∈ 𝓝[Set.Ici α] t :=
        nhdsWithin_le_nhds (Iio_mem_nhds htlt)
      filter_upwards [hmem] with s hs
      rw [gluedFamily_of_lt (I := I) g_fam r omega hs]
    rw [hg_t]
    exact hleftt.congr_of_eventuallyEq hev
      (by rw [gluedFamily_of_lt (I := I) g_fam r omega htlt])
  ·

    subst hteq

    have h0memT : (0 : ℝ) ∈ Set.Ico (0 : ℝ) T := ⟨le_refl 0, lt_of_lt_of_le hε hεT⟩
    have hr_pde0 := hright 0 h0memT x v w

    have hshift : HasDerivWithinAt (fun s : ℝ => s - t) (1 : ℝ) (Set.Ici t) t := by
      simpa using (hasDerivWithinAt_id t (Set.Ici t)).sub_const t
    have hmaps : Set.MapsTo (fun s : ℝ => s - t) (Set.Ici t) (Set.Ici 0) := by
      intro s hs; simp only [Set.mem_Ici] at hs ⊢; linarith
    have hcomp :
        HasDerivWithinAt (fun s : ℝ => (r (s - t)).inner x v w)
          ((1 : ℝ) • ((-2 : ℝ) *
            DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (r 0) x v w))
          (Set.Ici t) t :=
      HasDerivWithinAt.scomp_of_eq t hr_pde0 hshift hmaps (sub_self t).symm
    have hright_one :
        HasDerivWithinAt
          (fun s : ℝ => (gluedFamily (I := I) g_fam r t s).inner x v w)
          ((-2 : ℝ) *
            DifferentialGeometry.Integral.Connection.ricciTensor (I := I)
              (gluedFamily (I := I) g_fam r t t) x v w)
          (Set.Ici t) t := by

      have hev : (fun s : ℝ => (gluedFamily (I := I) g_fam r t s).inner x v w)
          =ᶠ[𝓝[Set.Ici t] t] (fun s : ℝ => (r (s - t)).inner x v w) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [gluedFamily_of_ge (I := I) g_fam r t (Set.mem_Ici.mp hs)]
      have hval : gluedFamily (I := I) g_fam r t t = r 0 :=
        gluedFamily_at_endpoint (I := I) g_fam r t
      rw [hval]
      refine (hcomp.congr_of_eventuallyEq hev ?_).congr_deriv ?_
      · simp [sub_self]
      · simp

    have hleft_one := hcross x v w

    have hunion := hleft_one.union hright_one
    rw [Set.Iic_union_Ici] at hunion
    have hderiv : HasDerivAt
        (fun s : ℝ => (gluedFamily (I := I) g_fam r t s).inner x v w)
        ((-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I)
            (gluedFamily (I := I) g_fam r t t) x v w)
        t := hasDerivWithinAt_univ.mp hunion
    exact hderiv.hasDerivWithinAt
  ·
    have hg_t : gluedFamily (I := I) g_fam r omega t = r (t - omega) :=
      gluedFamily_of_ge (I := I) g_fam r omega (le_of_lt htgt)
    have htmem : t - omega ∈ Set.Ico (0 : ℝ) T :=
      ⟨by linarith, by linarith [hε, hεT, ht.2]⟩
    have hr_pdet := hright (t - omega) htmem x v w
    have htpos : (0 : ℝ) < t - omega := by linarith

    have hshift : HasDerivAt (fun s : ℝ => s - omega) (1 : ℝ) t := by
      simpa using (hasDerivAt_id t).sub_const omega
    have hcomp : HasDerivAt (fun s : ℝ => (r (s - omega)).inner x v w)
        ((1 : ℝ) • ((-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (r (t - omega)) x v w))
        t := by
      have hr_at : HasDerivAt (fun u : ℝ => (r u).inner x v w)
          ((-2 : ℝ) *
            DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (r (t - omega)) x v w)
          (t - omega) :=
        hr_pdet.hasDerivAt (Ici_mem_nhds htpos)
      exact hr_at.scomp t hshift

    have hev : (fun s : ℝ => (gluedFamily (I := I) g_fam r omega s).inner x v w)
        =ᶠ[𝓝[Set.Ici α] t] (fun s : ℝ => (r (s - omega)).inner x v w) := by
      have hmem : Set.Ioi omega ∈ 𝓝[Set.Ici α] t :=
        nhdsWithin_le_nhds (Ioi_mem_nhds htgt)
      filter_upwards [hmem] with s hs
      rw [gluedFamily_of_ge (I := I) g_fam r omega (le_of_lt (Set.mem_Ioi.mp hs))]
    rw [hg_t]
    refine (hcomp.hasDerivWithinAt.congr_of_eventuallyEq hev
      (by rw [gluedFamily_of_ge (I := I) g_fam r omega (le_of_lt htgt)])).congr_deriv ?_
    simp














structure CinftyGlueData
    (g_fam r : ℝ → SmoothRiemannianMetric I M) (α omega ε : ℝ) : Prop where

  gram_smooth :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I)
            (gluedFamily (I := I) g_fam r omega p.1) x₀ p.2 i j)
        (Set.Ioo α (omega + ε) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)


  gram_cont :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I)
            (gluedFamily (I := I) g_fam r omega p.1) x₀ p.2 i j)
        (Set.Ico α (omega + ε) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)








  metric_match :
    ∀ x : M, ∀ v w : TangentSpace I x,
      Tendsto (fun s : ℝ => (g_fam s).inner x v w) (𝓝[<] omega)
        (𝓝 ((r 0).inner x v w))








































theorem ricci_flow_extends_construction
    (g_fam : ℝ → SmoothRiemannianMetric I M) {α omega : ℝ} (hαomega : α < omega)
    (hleft : ∀ t ∈ Set.Ico α omega, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
        ((-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g_fam t) x v w)
        (Set.Ici α) t)
    (limit : CinftyLimitData (I := I) g_fam α omega hαomega)
    (glue : ∀ (r : ℝ → SmoothRiemannianMetric I M) (T : ℝ),
      r 0 = limit.limitMetric → 0 < T →
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (r p.1) x₀ p.2 i j)
          (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun u : ℝ => (r u).inner x v w)
          ((-2 : ℝ) *
            DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (r t) x v w)
          (Set.Ici 0) t) →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ T ∧ CinftyGlueData (I := I) g_fam r α omega ε) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ g_ext : ℝ → SmoothRiemannianMetric I M,
      (∀ s : ℝ, s < omega → g_ext s = g_fam s) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_ext p.1) x₀ p.2 i j)
          (Set.Ioo α (omega + ε) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_ext p.1) x₀ p.2 i j)
          (Set.Ico α (omega + ε) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ t ∈ Set.Ico α (omega + ε), ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : ℝ => (g_ext s).inner x v w)
          ((-2 : ℝ) *
            DifferentialGeometry.Integral.Connection.ricciTensor (I := I)
              (g_ext t) x v w)
          (Set.Ici α) t) := by

  obtain ⟨T, hT, r, hr0, hr_smooth_closed, _hr_cont, hr_pde⟩ :=
    restart_short_time (I := I) (M := M) limit.limitMetric


  obtain ⟨ε, hε, hεT, hglue⟩ := glue r T hr0 hT hr_smooth_closed hr_pde


  have hcont : ∀ x : M, ∀ v w : TangentSpace I x,
      Tendsto (fun s : ℝ => (g_fam s).inner x v w) (𝓝[<] omega)
        (𝓝 ((limit.limitMetric).inner x v w)) := by
    intro x v w
    have h := hglue.metric_match x v w
    rwa [hr0] at h
  have hderiv_lim : ∀ x : M, ∀ v w : TangentSpace I x,
      Tendsto
        (fun s : ℝ => (-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g_fam s) x v w)
        (𝓝[<] omega)
        (𝓝 ((-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I)
            limit.limitMetric x v w)) :=
    fun x v w => (limit.ricci_match x v w).const_mul (-2)
  have hcross :=
    gluedFamily_pde_cross_of_matching (I := I) g_fam r limit.limitMetric
      hαomega hr0 hleft hcont hderiv_lim
  refine ⟨ε, hε, gluedFamily (I := I) g_fam r omega, ?_, ?_, ?_, ?_⟩
  ·
    exact gluedFamily_eq_left (I := I) g_fam r omega
  · exact hglue.gram_smooth
  · exact hglue.gram_cont
  ·
    exact gluedFamily_pde (I := I) g_fam r hαomega hε hεT hleft hr_pde hcross

end DifferentialGeometry.PDE.RicciFlow
