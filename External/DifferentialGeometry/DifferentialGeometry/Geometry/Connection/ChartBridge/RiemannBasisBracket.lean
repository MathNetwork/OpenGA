import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import DifferentialGeometry.Bundle.Frame
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.MFDeriv.Atlas


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
private lemma chartBasis_baseSet_eq_chartSource (x₀ : M) :
    (trivializationAt E (TangentSpace I) x₀).baseSet = (chartAt H x₀).source := by
  rfl

private lemma chartBasisVecFiber_symmL_apply (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    chartBasisVecFiber (I := I) x₀ i x =
      (trivializationAt E (TangentSpace I) x₀).symmL ℝ x ((chartModelBasis E) i) := by
  rw [Trivialization.symmL_apply]
  rfl

private lemma chartBasisVecFiber_apply_of_mem {x₀ x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) x₀ i x =
      (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x))
        ((chartModelBasis E) i) := by
  have hx_src : x ∈ (chartAt H x₀).source := by
    rwa [chartBasis_baseSet_eq_chartSource (I := I) x₀] at hx
  rw [chartBasisVecFiber_symmL_apply (I := I) x₀ i x]
  exact congrArg (fun L : E →L[ℝ] TangentSpace I x => L ((chartModelBasis E) i))
    (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := ℝ) hx_src)

private lemma chartBasisVecFiber_pullback_eq_const (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm
        (chartBasisVecFiber (I := I) x₀ i) (Set.range I)
      =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        fun _ : E => ((chartModelBasis E) i : E) := by
  haveI : IsManifold I (1 : WithTop ℕ∞) M :=
    IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
  simp only [VectorField.mpullbackWithin_apply]
  have hy_src : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hy
  have hy_base : (extChartAt I x₀).symm y ∈
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rwa [chartBasis_baseSet_eq_chartSource (I := I) x₀]
  rw [chartBasisVecFiber_apply_of_mem (I := I) hy_base i]
  rw [(extChartAt I x₀).right_inv hy]
  exact ContinuousLinearMap.IsInvertible.inverse_apply_self
    (isInvertible_mfderivWithin_extChartAt_symm (I := I) hy)
    ((chartModelBasis E) i)

omit [FiniteDimensional ℝ E] in
private lemma lieBracketWithin_const_const {s : Set E} {x v w : E} :
    VectorField.lieBracketWithin ℝ (fun _ : E => v) (fun _ : E => w) s x = 0 := by
  simp [VectorField.lieBracketWithin]

theorem mlieBracket_chartBasisVec_self_eq_zero (x₀ : M)
    (j k : Fin (Module.finrank ℝ E)) :
    VectorField.mlieBracket I
        (chartBasisVecFiber (I := I) x₀ j)
        (chartBasisVecFiber (I := I) x₀ k) x₀ = 0 := by
  rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_apply]
  have hleft :
      VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm
          (chartBasisVecFiber (I := I) x₀ j) (Set.range I)
        =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' Set.univ ∩ Set.range I]
            (extChartAt I x₀ x₀)]
          fun _ : E => ((chartModelBasis E) j : E) := by
    simpa using chartBasisVecFiber_pullback_eq_const (I := I) x₀ j
  have hright :
      VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm
          (chartBasisVecFiber (I := I) x₀ k) (Set.range I)
        =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' Set.univ ∩ Set.range I]
            (extChartAt I x₀ x₀)]
          fun _ : E => ((chartModelBasis E) k : E) := by
    simpa using chartBasisVecFiber_pullback_eq_const (I := I) x₀ k
  rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem hleft hright (by simp)]
  rw [lieBracketWithin_const_const]
  exact ContinuousLinearMap.map_zero _

omit [FiniteDimensional ℝ E] in
private lemma trivToE_self_eq_id (x : M) :
    (trivToE (I := I) x x : TangentSpace I x →L[ℝ] E) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  classical
  have h := TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
    (x₀ := x) (x := x) (mem_chart_source H x)
  rw [show (trivToE (I := I) x x : TangentSpace I x →L[ℝ] E) =
        (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x from rfl]
  rw [h]
  exact mfderiv_extChartAt_self (I := I) (x := x)

omit [FiniteDimensional ℝ E] in
private lemma trivFromE_self_apply (x : M) (w : E) :
    trivFromE (I := I) x x w = w := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have h := trivToE_trivFromE (I := I) x hbase w
  have hid : trivToE (I := I) x x (trivFromE (I := I) x x w) = trivFromE (I := I) x x w := by
    rw [trivToE_self_eq_id (I := I) x]; rfl
  rwa [hid] at h

private lemma chartBasisVecFiber_self_aux (x : M) (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) x i x = (chartModelBasis E) i := by
  rw [chartBasisVecFiber_symmL_apply (I := I) x i x]
  exact trivFromE_self_apply (I := I) x ((chartModelBasis E) i)

variable [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem exists_smooth_chartBasisExtension (x : M) :
    ∃ X : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b,
      (∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (X i))) ∧
        (∀ᶠ b in 𝓝 x, ∀ i, X i b = chartBasisVecFiber (I := I) x i b) := by
  classical
  have hbase_open : IsOpen (trivializationAt E (TangentSpace I) x).baseSet :=
    (trivializationAt E (TangentSpace I) x).open_baseSet
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x
  have hs : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (T% (fun b : M => chartBasisVecFiber (I := I) x i b))
        (trivializationAt E (TangentSpace I) x).baseSet := by
    intro i
    have h := chartBasisVec_contMDiffOn (I := I) x i
    simpa using h
  obtain ⟨s', hs'⟩ :=
    exists_contMDiffSection_eqOn_nhd (I := I) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      (s := fun i b => chartBasisVecFiber (I := I) x i b) hs hbase_open hx_base
  refine ⟨fun i b => s' i b, fun i => (s' i).contMDiff, ?_⟩
  filter_upwards [hs'] with b hb i using hb i

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem LeviCivita_chartBasisVec_neighborhood_formula
    (g : SmoothRiemannianMetric I M) (x : M)
    {X : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hX : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (X i)))
    (hXnhds : ∀ᶠ b in 𝓝 x, ∀ i, X i b = chartBasisVecFiber (I := I) x i b)
    (i j k : Fin (Module.finrank ℝ E)) :
    riemannOp (cov := LeviCivita (I := I) g) x
        ((chartModelBasis E) j) ((chartModelBasis E) k)
        ((chartModelBasis E) i) =
      (LeviCivita (I := I) g).toFun
          (Connection.covApply (LeviCivita (I := I) g) (X k) (X i)) x (X j x) -
        (LeviCivita (I := I) g).toFun
          (Connection.covApply (LeviCivita (I := I) g) (X j) (X i)) x (X k x) := by
  classical
  have hXx : ∀ i, X i x = (chartModelBasis E) i := by
    intro i
    have hb : ∀ i, X i x = chartBasisVecFiber (I := I) x i x := hXnhds.self_of_nhds
    rw [hb i, chartBasisVecFiber_self_aux (I := I) x i]
  have hsec : riemannOp (cov := LeviCivita (I := I) g) x
      ((chartModelBasis E) j) ((chartModelBasis E) k) ((chartModelBasis E) i) =
      riemannSec (LeviCivita (I := I) g) (X j) (X k) (X i) x := by
    rw [show ((chartModelBasis E) j : TangentSpace I x) = X j x from (hXx j).symm,
        show ((chartModelBasis E) k : TangentSpace I x) = X k x from (hXx k).symm,
        show ((chartModelBasis E) i : TangentSpace I x) = X i x from (hXx i).symm]
    exact riemannOp_apply_smooth (cov := LeviCivita (I := I) g) (hX j) (hX k) (hX i)
  rw [hsec, riemannSec_def]
  have hXj_eq : (X j) =ᶠ[𝓝 x] chartBasisVecFiber (I := I) x j := by
    filter_upwards [hXnhds] with b hb using hb j
  have hXk_eq : (X k) =ᶠ[𝓝 x] chartBasisVecFiber (I := I) x k := by
    filter_upwards [hXnhds] with b hb using hb k
  have hbracket :
      VectorField.mlieBracket I (X j) (X k) x = 0 := by
    rw [Filter.EventuallyEq.mlieBracket_vectorField_eq (I := I) hXj_eq hXk_eq]
    exact mlieBracket_chartBasisVec_self_eq_zero (I := I) x j k
  rw [hbracket]
  rw [ContinuousLinearMap.map_zero, sub_zero]

open DifferentialGeometry.Integral.DivergenceTheorem

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartE_section_repr_chartBasisVec_baseSet
    (x : M) (i : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    chartE_section_repr (I := I) x
        (fun y : M => chartBasisVecFiber (I := I) x i y) b =
      (chartModelBasis E) i := by
  classical
  rw [chartE_section_repr_eq_trivToE]
  rw [show chartBasisVecFiber (I := I) x i b
        = trivFromE (I := I) x b ((chartModelBasis E) i) from
      chartBasisVecFiber_symmL_apply (I := I) x i b]
  exact trivToE_trivFromE (I := I) x hb ((chartModelBasis E) i)

omit [InnerProductSpace ℝ E] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma LeviCivita_covApply_firstLayer_pointwise
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (i k : Fin (Module.finrank ℝ E))
    {Xi : Π b : M, TangentSpace I b} {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) x)
    (hXi_nhds : Xi =ᶠ[𝓝 b] (fun y : M => chartBasisVecFiber (I := I) x i y))
    {vk : TangentSpace I b}
    (hvk : trivToE (I := I) x b vk = (chartModelBasis E) k) :
    (LeviCivita (I := I) g).toFun Xi b vk =
      trivFromE (I := I) x b
        (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g x k i m (extChartAt I x b) •
            (chartModelBasis E) m) := by
  classical
  have hbase : b ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hXi_at : MDiffAt (T% Xi) b := by
    have hcm := chartBasisVec_contMDiffOn (I := I) x i
    have hopen : IsOpen (trivializationAt E (TangentSpace I) x).baseSet :=
      (trivializationAt E (TangentSpace I) x).open_baseSet
    have hcb_at : MDiffAt (T% (fun y : M => chartBasisVecFiber (I := I) x i y)) b :=
      ((hcm b hbase).contMDiffAt (hopen.mem_nhds hbase)).mdifferentiableAt (by simp)
    apply hcb_at.congr_of_eventuallyEq
    filter_upwards [hXi_nhds] with y hy
    change (TotalSpace.mk' E y (Xi y) : TangentBundle I M)
        = TotalSpace.mk' E y (chartBasisVecFiber (I := I) x i y)
    rw [hy]
  rw [LeviCivita_chart_apply (I := I) g x hb hXi_at vk]
  rw [chartLeviCivita_apply (I := I) g x Xi hb vk]
  have hb_src_ext : b ∈ (extChartAt I x).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hfd0 :
      fderiv ℝ (chartE_section_repr (I := I) x Xi ∘ (extChartAt I x).symm)
          (extChartAt I x b) = 0 := by
    have hev : (chartE_section_repr (I := I) x Xi ∘ (extChartAt I x).symm)
        =ᶠ[𝓝 (extChartAt I x b)] (fun _ : E => ((chartModelBasis E) i : E)) := by
      rw [Filter.eventuallyEq_iff_exists_mem] at hXi_nhds
      obtain ⟨W, hW_nhds, hW_eq⟩ := hXi_nhds
      obtain ⟨W', hW'W, hW'_open, hbW'⟩ := mem_nhds_iff.mp hW_nhds
      set V : Set E :=
        (extChartAt I x).target ∩
          (extChartAt I x).symm ⁻¹'
            ((trivializationAt E (TangentSpace I) x).baseSet ∩ W') with hV_def
      have hcont_symm : ContinuousOn (extChartAt I x).symm (extChartAt I x).target :=
        continuousOn_extChartAt_symm x
      have hV_open : IsOpen V :=
        hcont_symm.isOpen_inter_preimage (isOpen_extChartAt_target (I := I) x)
          ((trivializationAt E (TangentSpace I) x).open_baseSet.inter hW'_open)
      have hbtgt : extChartAt I x b ∈ (extChartAt I x).target :=
        (extChartAt I x).map_source hb_src_ext
      have hφV : extChartAt I x b ∈ V := by
        refine ⟨hbtgt, ?_⟩
        rw [Set.mem_preimage, (extChartAt I x).left_inv hb_src_ext]
        exact ⟨hbase, hbW'⟩
      filter_upwards [hV_open.mem_nhds hφV] with y hy
      obtain ⟨hy_tgt, hy_pre⟩ := hy
      rw [Set.mem_preimage] at hy_pre
      obtain ⟨hy_base, hy_W'⟩ := hy_pre
      simp only [Function.comp_apply, chartE_section_repr_eq_trivToE]
      rw [show Xi ((extChartAt I x).symm y) =
            chartBasisVecFiber (I := I) x i ((extChartAt I x).symm y) from
          hW_eq (hW'W hy_W')]
      have := chartE_section_repr_chartBasisVec_baseSet (I := I) x i hy_base
      rw [chartE_section_repr_eq_trivToE] at this
      exact this
    rw [hev.fderiv_eq, fderiv_const_apply]
  rw [hfd0, ContinuousLinearMap.zero_apply, zero_add]
  rw [show chartE_section_repr (I := I) x Xi b = (chartModelBasis E) i from by
    rw [chartE_section_repr_eq_trivToE,
        show Xi b = chartBasisVecFiber (I := I) x i b from hXi_nhds.self_of_nhds]
    have := chartE_section_repr_chartBasisVec_baseSet (I := I) x i hbase
    rw [chartE_section_repr_eq_trivToE] at this
    exact this]
  congr 1
  rw [christoffelCorrection_apply (I := I) g x b ((chartModelBasis E) i) vk, hvk]
  have hrepr_basis : ∀ (r s : Fin (Module.finrank ℝ E)),
      ((chartModelBasis E).repr ((chartModelBasis E) r)) s =
        if r = s then (1 : ℝ) else 0 := by
    intro r s
    rw [Module.Basis.repr_self]
    by_cases h : r = s
    · subst h; simp
    · simp [h]
  rw [Finset.sum_eq_single k (fun p _ hp => ?_) (fun hk => ?_)]
  · rw [Finset.sum_eq_single i (fun q _ hq => ?_) (fun hi => ?_)]
    · rw [hrepr_basis k k, hrepr_basis i i, if_pos rfl, if_pos rfl]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [one_mul, one_mul]
    · refine Finset.sum_eq_zero (fun r _ => ?_)
      rw [hrepr_basis i q, if_neg (fun h => hq h.symm)]; simp
    · exact absurd (Finset.mem_univ i) hi
  · refine Finset.sum_eq_zero (fun q _ => Finset.sum_eq_zero (fun r _ => ?_))
    rw [hrepr_basis k p, if_neg (fun h => hp h.symm)]; simp
  · exact absurd (Finset.mem_univ k) hk

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma chartE_section_repr_covApply_eventuallyEq
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (i k : Fin (Module.finrank ℝ E))
    {X : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hXnhds : ∀ᶠ b in 𝓝 x, ∀ p, X p b = chartBasisVecFiber (I := I) x p b) :
    (chartE_section_repr (I := I) x
        (Connection.covApply (LeviCivita (I := I) g) (X k) (X i)) ∘ (extChartAt I x).symm)
      =ᶠ[𝓝 (extChartAt I x x)]
        (fun y : E =>
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x k i m y • (chartModelBasis E) m) := by
  classical
  rw [Filter.eventually_iff_exists_mem] at hXnhds
  obtain ⟨W₀, hW₀_nhds, hW₀_eq⟩ := hXnhds
  obtain ⟨W, hWW₀, hW_open, hxW⟩ := mem_nhds_iff.mp hW₀_nhds
  have hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) x) :=
    chartLeviCivitaGoodSet_isOpen (I := I) x
  set V : Set E :=
    (extChartAt I x).target ∩
      (extChartAt I x).symm ⁻¹' (chartLeviCivitaGoodSet (I := I) x ∩ W) with hV_def
  have hcont_symm : ContinuousOn (extChartAt I x).symm (extChartAt I x).target :=
    continuousOn_extChartAt_symm x
  have hV_open : IsOpen V :=
    hcont_symm.isOpen_inter_preimage (isOpen_extChartAt_target (I := I) x)
      (hgood_open.inter hW_open)
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact mem_chart_source H x
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hφxV : extChartAt I x x ∈ V := by
    refine ⟨hxtgt, ?_⟩
    rw [Set.mem_preimage, (extChartAt I x).left_inv hxsrc_ext]
    exact ⟨hx_good, hxW⟩
  filter_upwards [hV_open.mem_nhds hφxV] with y hy
  obtain ⟨hy_tgt, hy_pre⟩ := hy
  rw [Set.mem_preimage] at hy_pre
  obtain ⟨hy_good, hy_W⟩ := hy_pre
  set b : M := (extChartAt I x).symm y with hb_def
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hy_good
  have hXp_nhds : ∀ p, X p =ᶠ[𝓝 b]
      (fun y' : M => chartBasisVecFiber (I := I) x p y') := by
    intro p
    filter_upwards [hW_open.mem_nhds hy_W] with b' hb'W using hW₀_eq _ (hWW₀ hb'W) p
  have hvk : trivToE (I := I) x b (X k b) = (chartModelBasis E) k := by
    rw [show X k b = chartBasisVecFiber (I := I) x k b from (hXp_nhds k).self_of_nhds]
    have := chartE_section_repr_chartBasisVec_baseSet (I := I) x k hb_base
    rw [chartE_section_repr_eq_trivToE] at this
    exact this
  simp only [Function.comp_apply, chartE_section_repr_eq_trivToE,
    Connection.covApply_apply]
  rw [show (LeviCivita (I := I) g).toFun (X i) b (X k b) =
        trivFromE (I := I) x b
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x k i m (extChartAt I x b) •
              (chartModelBasis E) m) from
      LeviCivita_covApply_firstLayer_pointwise (I := I) g x i k hy_good (hXp_nhds i) hvk]
  rw [trivToE_trivFromE (I := I) x hb_base]
  rw [hb_def, (extChartAt I x).right_inv hy_tgt]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma chartChristoffel_differentiableAt_self
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (k i m : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ (chartChristoffel (I := I) g x k i m) (extChartAt I x x) := by
  classical
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact mem_chart_source H x
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  have hcd : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g x k i m)
      (interior (extChartAt I x).target) :=
    chartChristoffel_contDiffOn_interior (I := I) g x k i m
  exact (hcd.differentiableOn (by norm_num)).differentiableAt
    (isOpen_interior.mem_nhds hxint)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma fderiv_christoffelSum_apply
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    fderiv ℝ
        (fun y : E =>
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x k i m y • (chartModelBasis E) m)
        (extChartAt I x x) ((chartModelBasis E) j) =
      ∑ m : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) j (chartChristoffel (I := I) g x k i m)
            (extChartAt I x x) • (chartModelBasis E) m := by
  classical
  rw [fderiv_fun_sum (fun m _ =>
    (chartChristoffel_differentiableAt_self (I := I) g x k i m).smul_const
      ((chartModelBasis E) m))]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [fderiv_smul_const (chartChristoffel_differentiableAt_self (I := I) g x k i m)
    ((chartModelBasis E) m)]
  rw [ContinuousLinearMap.smulRight_apply]
  rfl

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma LeviCivita_covApply_secondLayer
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j k : Fin (Module.finrank ℝ E))
    {X : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hX : ∀ p, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (X p)))
    (hXnhds : ∀ᶠ b in 𝓝 x, ∀ p, X p b = chartBasisVecFiber (I := I) x p b) :
    (LeviCivita (I := I) g).toFun
        (Connection.covApply (LeviCivita (I := I) g) (X k) (X i)) x
        ((chartModelBasis E) j) =
      ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g x k i l)
              (extChartAt I x x) +
            ∑ m : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g x j m l (extChartAt I x x) *
                chartChristoffel (I := I) g x k i m (extChartAt I x x)) •
          (chartModelBasis E) l := by
  classical
  set S : Π b : M, TangentSpace I b :=
    Connection.covApply (LeviCivita (I := I) g) (X k) (X i) with hS_def
  have hXi1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (X i)) := by
    have h : ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) := by rw [ENat.coe_top_add_one]
    rw [h]; exact hX i
  have hS_at : MDiffAt (T% S) x :=
    Connection.covApply_mdifferentiableAt (cov := LeviCivita (I := I) g) (hX k) hXi1
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact mem_chart_source H x
  set c : Fin (Module.finrank ℝ E) → ℝ :=
    fun m => chartChristoffel (I := I) g x k i m (extChartAt I x x) with hc_def
  have hrepr_sum : ∀ q : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
          (∑ m : Fin (Module.finrank ℝ E), c m • (chartModelBasis E) m)) q = c q := by
    intro q
    rw [map_sum]
    simp only [map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single q
      (fun m _ hm => by rw [Module.Basis.repr_self_apply, if_neg hm, mul_zero])
      (fun hq => absurd (Finset.mem_univ q) hq)]
    rw [Module.Basis.repr_self_apply, if_pos rfl, mul_one]
  rw [LeviCivita_chart_apply (I := I) g x hx_good hS_at ((chartModelBasis E) j)]
  rw [chartLeviCivita_apply (I := I) g x S hx_good ((chartModelBasis E) j)]
  have hev := chartE_section_repr_covApply_eventuallyEq (I := I) g x i k hXnhds
  rw [show trivToE (I := I) x x ((chartModelBasis E) j) = (chartModelBasis E) j from by
    rw [trivToE_self_eq_id (I := I) x]; rfl]
  rw [hev.fderiv_eq, fderiv_christoffelSum_apply (I := I) g x i j k]
  have hSx_repr : chartE_section_repr (I := I) x S x =
      ∑ m : Fin (Module.finrank ℝ E), c m • (chartModelBasis E) m := by
    have h0 := hev.self_of_nhds
    simp only [Function.comp_apply] at h0
    rw [(extChartAt I x).left_inv hxsrc_ext] at h0
    exact h0
  rw [hSx_repr]
  rw [christoffelCorrection_apply (I := I) g x x
    (∑ m : Fin (Module.finrank ℝ E), c m • (chartModelBasis E) m)
    ((chartModelBasis E) j)]
  rw [show trivToE (I := I) x x ((chartModelBasis E) j) = (chartModelBasis E) j from by
    rw [trivToE_self_eq_id (I := I) x]; rfl]
  have hrepr_ej : ∀ p : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr ((chartModelBasis E) j)) p = if j = p then (1 : ℝ) else 0 := by
    intro p; rw [Module.Basis.repr_self_apply]
  have hcorr :
      (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
        ∑ r : Fin (Module.finrank ℝ E),
          (((chartModelBasis E).repr ((chartModelBasis E) j)) p *
              ((chartModelBasis E).repr
                (∑ m : Fin (Module.finrank ℝ E), c m • (chartModelBasis E) m)) q *
              chartChristoffel (I := I) g x p q r (extChartAt I x x)) •
            (chartModelBasis E) r) =
        ∑ r : Fin (Module.finrank ℝ E),
          (∑ q : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x j q r (extChartAt I x x) * c q) •
            (chartModelBasis E) r := by
    rw [Finset.sum_eq_single j (fun p _ hp => ?_) (fun hj => ?_)]
    · rw [show (∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr ((chartModelBasis E) j)) j *
                ((chartModelBasis E).repr
                  (∑ m : Fin (Module.finrank ℝ E), c m • (chartModelBasis E) m)) q *
                chartChristoffel (I := I) g x j q r (extChartAt I x x)) •
              (chartModelBasis E) r) =
          ∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E),
            (c q * chartChristoffel (I := I) g x j q r (extChartAt I x x)) •
              (chartModelBasis E) r from ?_]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [← Finset.sum_smul]
        refine congrArg (fun t => t • (chartModelBasis E) r) ?_
        refine Finset.sum_congr rfl (fun q _ => ?_)
        ring
      · refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun r _ => ?_))
        rw [hrepr_ej j, if_pos rfl, hrepr_sum q, one_mul]
    · refine Finset.sum_eq_zero (fun q _ => Finset.sum_eq_zero (fun r _ => ?_))
      rw [hrepr_ej p, if_neg (fun h => hp h.symm), zero_mul, zero_mul, zero_smul]
    · exact absurd (Finset.mem_univ j) hj
  rw [hcorr]
  have hmerge :
      (∑ m : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) j (chartChristoffel (I := I) g x k i m)
            (extChartAt I x x) • (chartModelBasis E) m) +
        (∑ r : Fin (Module.finrank ℝ E),
          (∑ q : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x j q r (extChartAt I x x) * c q) •
            (chartModelBasis E) r) =
      ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g x k i l)
              (extChartAt I x x) +
            ∑ m : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g x j m l (extChartAt I x x) *
                chartChristoffel (I := I) g x k i m (extChartAt I x x)) •
          (chartModelBasis E) l := by
    simp only [hc_def]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [add_smul]
  rw [hmerge]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [(trivFromE (I := I) x x).map_smul]
  congr 1
  exact trivFromE_self_apply (I := I) x ((chartModelBasis E) l)

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma coord_sum_smul_basis
    {b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E}
    (c : Fin (Module.finrank ℝ E) → ℝ) (l : Fin (Module.finrank ℝ E)) :
    (b.repr (∑ l' : Fin (Module.finrank ℝ E), c l' • b l')) l = c l := by
  classical
  rw [map_sum]
  simp only [map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single l
    (fun l' _ hl' => by rw [Module.Basis.repr_self_apply, if_neg hl', mul_zero])
    (fun hl => absurd (Finset.mem_univ l) hl)]
  rw [Module.Basis.repr_self_apply, if_pos rfl, mul_one]

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartRiemannBasisIdentity_LeviCivita [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    chartRiemannBasisIdentity (I := I) g x := by
  classical
  intro i j k l
  obtain ⟨X, hX, hXnhds⟩ := exists_smooth_chartBasisExtension (I := I) x
  have hXx : ∀ p, X p x = (chartModelBasis E) p := by
    intro p
    rw [hXnhds.self_of_nhds p, chartBasisVecFiber_self_aux (I := I) x p]
  have hvec :
      (LeviCivita (I := I) g).toFun
          (Connection.covApply (LeviCivita (I := I) g) (X k) (X i)) x (X j x) -
        (LeviCivita (I := I) g).toFun
          (Connection.covApply (LeviCivita (I := I) g) (X j) (X i)) x (X k x) =
      ∑ l' : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) g x i j k l' (extChartAt I x x) •
          (chartModelBasis E) l' := by
    rw [hXx j, hXx k]
    rw [LeviCivita_covApply_secondLayer (I := I) g x i j k hX hXnhds]
    rw [LeviCivita_covApply_secondLayer (I := I) g x i k j hX hXnhds]
    refine Eq.trans (Finset.sum_sub_distrib (s := Finset.univ)
      (f := fun l' : Fin (Module.finrank ℝ E) =>
        (partialDeriv (E := E) j (chartChristoffel (I := I) g x k i l')
              (extChartAt I x x) +
            ∑ m : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g x j m l' (extChartAt I x x) *
                chartChristoffel (I := I) g x k i m (extChartAt I x x)) •
          (chartModelBasis E) l')
      (g := fun l' : Fin (Module.finrank ℝ E) =>
        (partialDeriv (E := E) k (chartChristoffel (I := I) g x j i l')
              (extChartAt I x x) +
            ∑ m : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g x k m l' (extChartAt I x x) *
                chartChristoffel (I := I) g x j i m (extChartAt I x x)) •
          (chartModelBasis E) l')).symm ?_
    refine Finset.sum_congr rfl (fun l' _ => ?_)
    rw [← sub_smul]
    refine congrArg (fun t : ℝ => t • (chartModelBasis E) l') ?_
    rw [chartRiemannTensor_def]
    rw [show chartChristoffel (I := I) g x k i l' = chartChristoffel (I := I) g x i k l' from
      funext (fun y => chartChristoffel_symm (I := I) g x k i l' y)]
    rw [show chartChristoffel (I := I) g x j i l' = chartChristoffel (I := I) g x i j l' from
      funext (fun y => chartChristoffel_symm (I := I) g x j i l' y)]
    rw [show (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g x j m l' (extChartAt I x x) *
            chartChristoffel (I := I) g x k i m (extChartAt I x x)) =
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g x j m l' (extChartAt I x x) *
            chartChristoffel (I := I) g x i k m (extChartAt I x x) from
      Finset.sum_congr rfl (fun m _ => by
        rw [chartChristoffel_symm (I := I) g x k i m])]
    rw [show (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g x k m l' (extChartAt I x x) *
            chartChristoffel (I := I) g x j i m (extChartAt I x x)) =
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g x k m l' (extChartAt I x x) *
            chartChristoffel (I := I) g x i j m (extChartAt I x x) from
      Finset.sum_congr rfl (fun m _ => by
        rw [chartChristoffel_symm (I := I) g x j i m])]
    rw [Finset.sum_sub_distrib]
    ring
  rw [LeviCivita_chartBasisVec_neighborhood_formula (I := I) g x hX hXnhds i j k]
  rw [hvec]
  exact coord_sum_smul_basis (b := chartModelBasis E)
    (c := fun l' => chartRiemannTensor (I := I) g x i j k l' (extChartAt I x x)) l

end Connection
end Integral
end DifferentialGeometry
