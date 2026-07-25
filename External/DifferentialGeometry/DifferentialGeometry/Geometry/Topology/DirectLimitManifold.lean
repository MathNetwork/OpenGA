import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import DifferentialGeometry.Geometry.Topology.DirectLimit
import DifferentialGeometry.Geometry.Topology.FiberBundleT2
import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Bundle.ClmSectionSmooth

set_option autoImplicit false
set_option linter.style.longLine false



























noncomputable section

universe u uE uH

namespace DifferentialGeometry

open Set Topology
open scoped Manifold ContDiff

namespace SeqSystem

section Charted

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, Nonempty (A k)]
variable (S : SeqSystem A)



def inclHomeo (k : ℕ) : OpenPartialHomeomorph (A k) S.Lim :=
  (S.incl_isOpenEmb k).toOpenPartialHomeomorph (S.incl k)

@[simp] theorem inclHomeo_apply (k : ℕ) (x : A k) : S.inclHomeo k x = S.incl k x := rfl

@[simp] theorem inclHomeo_source (k : ℕ) : (S.inclHomeo k).source = univ :=
  (S.incl_isOpenEmb k).toOpenPartialHomeomorph_source (S.incl k)

@[simp] theorem inclHomeo_target (k : ℕ) : (S.inclHomeo k).target = range (S.incl k) :=
  (S.incl_isOpenEmb k).toOpenPartialHomeomorph_target (S.incl k)

theorem inclHomeo_symm_apply (k : ℕ) (x : A k) :
    (S.inclHomeo k).symm (S.incl k x) = x :=
  (S.incl_isOpenEmb k).toOpenPartialHomeomorph_left_inv (S.incl k)





def limChart (k : ℕ) (a : A k) : OpenPartialHomeomorph S.Lim H :=
  (S.inclHomeo k).symm.trans (chartAt H a)

theorem mem_limChart_source (k : ℕ) (a : A k) :
    S.incl k a ∈ (S.limChart (H := H) k a).source := by
  rw [limChart, OpenPartialHomeomorph.trans_source]
  refine ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.symm_source, inclHomeo_target]
    exact ⟨a, rfl⟩
  · change (S.inclHomeo k).symm (S.incl k a) ∈ (chartAt H a).source
    rw [inclHomeo_symm_apply]
    exact mem_chart_source H a


omit [∀ (k : ℕ), Nonempty (A k)] in
theorem exists_sigma_incl (z : S.Lim) : ∃ p : Σ k, A k, S.incl p.1 p.2 = z := by
  obtain ⟨k, x, hx⟩ := S.exists_incl_eq z
  exact ⟨⟨k, x⟩, hx⟩


def rep (z : S.Lim) : Σ k, A k := (S.exists_sigma_incl z).choose

omit [∀ (k : ℕ), Nonempty (A k)] in
theorem incl_rep (z : S.Lim) : S.incl (S.rep z).1 (S.rep z).2 = z :=
  (S.exists_sigma_incl z).choose_spec





instance instChartedSpaceLim : ChartedSpace H S.Lim where
  atlas := ⋃ (k : ℕ), ⋃ (a : A k), {S.limChart k a}
  chartAt z := S.limChart (S.rep z).1 (S.rep z).2
  mem_chart_source z := by
    have hz : S.incl (S.rep z).1 (S.rep z).2 = z := S.incl_rep z
    have hmem := S.mem_limChart_source (H := H) (S.rep z).1 (S.rep z).2
    rwa [hz] at hmem
  chart_mem_atlas z := by
    simp only [mem_iUnion, mem_singleton_iff]
    exact ⟨(S.rep z).1, (S.rep z).2, rfl⟩

theorem chartAt_lim (z : S.Lim) :
    chartAt H z = S.limChart (S.rep z).1 (S.rep z).2 := rfl

theorem limChart_mem_atlas (k : ℕ) (a : A k) : S.limChart k a ∈ atlas H S.Lim := by
  change S.limChart k a ∈ ⋃ (k : ℕ) (a : A k), {S.limChart k a}
  simp only [mem_iUnion, mem_singleton_iff]
  exact ⟨k, a, rfl⟩

theorem mem_atlas_iff {e : OpenPartialHomeomorph S.Lim H} :
    e ∈ atlas H S.Lim ↔ ∃ (k : ℕ) (a : A k), e = S.limChart k a := by
  change e ∈ ⋃ (k : ℕ) (a : A k), {S.limChart k a} ↔ _
  simp only [mem_iUnion, mem_singleton_iff]


instance instSigmaCompactSpaceLim [∀ k, SigmaCompactSpace (A k)] :
    SigmaCompactSpace S.Lim := S.sigmaCompact


instance instT2SpaceLim [∀ k, T2Space (A k)] : T2Space S.Lim := S.t2Space

instance instNonemptyLim : Nonempty S.Lim :=
  ⟨S.incl 0 (Classical.arbitrary (A 0))⟩




instance instPreconnectedLim [∀ k, PreconnectedSpace (A k)] :
    PreconnectedSpace S.Lim := by
  constructor
  rw [← S.iUnion_range_incl]
  refine isPreconnected_iUnion ⟨S.incl 0 (Classical.arbitrary (A 0)), ?_⟩ fun k => ?_
  · simp only [mem_iInter]
    intro k
    exact S.range_incl_mono (Nat.zero_le k) ⟨Classical.arbitrary (A 0), rfl⟩
  · have h := (isPreconnected_univ (α := A k)).image (S.incl k)
      (S.continuous_incl k).continuousOn
    rwa [Set.image_univ] at h

instance instConnectedSpaceLim [∀ k, PreconnectedSpace (A k)] :
    ConnectedSpace S.Lim where
  toPreconnectedSpace := S.instPreconnectedLim
  toNonempty := S.instNonemptyLim



def transitionHomeo (k ℓ : ℕ) : OpenPartialHomeomorph (A k) (A ℓ) :=
  (S.inclHomeo k).trans (S.inclHomeo ℓ).symm

theorem mem_transitionHomeo_source {k ℓ : ℕ} {w : A k} :
    w ∈ (S.transitionHomeo k ℓ).source ↔ S.incl k w ∈ range (S.incl ℓ) := by
  rw [transitionHomeo, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    inclHomeo_source, inclHomeo_target, univ_inter, mem_preimage, inclHomeo_apply]

theorem transitionHomeo_apply {k ℓ : ℕ} (w : A k) :
    S.transitionHomeo k ℓ w = (S.inclHomeo ℓ).symm (S.incl k w) := by
  rw [transitionHomeo, OpenPartialHomeomorph.trans_apply, inclHomeo_apply]

theorem incl_transitionHomeo {k ℓ : ℕ} {w : A k} (hw : w ∈ (S.transitionHomeo k ℓ).source) :
    S.incl ℓ (S.transitionHomeo k ℓ w) = S.incl k w := by
  have hmem : S.incl k w ∈ (S.inclHomeo ℓ).target := by
    rw [inclHomeo_target]; exact (S.mem_transitionHomeo_source).mp hw
  rw [transitionHomeo_apply, ← inclHomeo_apply, OpenPartialHomeomorph.right_inv _ hmem]




theorem limChart_symm_trans (k ℓ : ℕ) (a : A k) (b : A ℓ) :
    (S.limChart k a).symm.trans (S.limChart ℓ b)
      = ((chartAt H a).symm.trans (S.transitionHomeo k ℓ)).trans (chartAt H b) := by
  simp only [limChart, transitionHomeo, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc]

end Charted

end SeqSystem



















structure SmoothSeqSystem
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (A : ℕ → Type u) [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
    [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
    extends SeqSystem A where
  contMDiff_F : ∀ {k ℓ : ℕ} (h : k ≤ ℓ), ContMDiff I I ∞ (toSeqSystem.F h)
  contMDiffOn_invFun_F : ∀ {k ℓ : ℕ} (h : k ≤ ℓ),
    ContMDiffOn I I ∞ (Function.invFun (toSeqSystem.F h)) (Set.range (toSeqSystem.F h))




theorem modelSpace_contDiffOn
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] [Nonempty H] {I : ModelWithCorners ℝ E H}
    {f : H → H} {s : Set H} (hf : ContMDiffOn I I ∞ f s) :
    ContDiffOn ℝ ∞ (↑I ∘ f ∘ ↑I.symm) (↑I.symm ⁻¹' s ∩ range ↑I) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty H)
  have hs : s ⊆ (extChartAt I x₀).source := by
    simp only [extChartAt_source, chartAt_self_eq, OpenPartialHomeomorph.refl_source,
      subset_univ]
  have h2s : MapsTo f s (extChartAt I x₀).source := by
    simp only [extChartAt_source, chartAt_self_eq, OpenPartialHomeomorph.refl_source]
    exact mapsTo_univ _ _
  have h := (contMDiffOn_iff_of_subset_source' hs h2s).mp hf
  have hset : extChartAt I x₀ '' s = ↑I.symm ⁻¹' s ∩ range ↑I := by
    rw [← I.image_eq]
    apply Set.image_congr'
    intro z
    simp only [extChartAt_coe, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
      Function.comp_apply, id_eq]
  rw [hset] at h
  refine h.congr (fun z _ => ?_)
  simp only [Function.comp_apply, extChartAt_coe, extChartAt_coe_symm, chartAt_self_eq,
    OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id_eq]

namespace SmoothSeqSystem

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
variable (S : SmoothSeqSystem I A)


omit [∀ (k : ℕ), IsManifold I ∞ (A k)] [∀ (k : ℕ), Nonempty (A k)] in
theorem succMap_contMDiff (f : ∀ k, A k → A (k + 1))
    (hf : ∀ k, ContMDiff I I ∞ (f k)) {k ℓ : ℕ} (h : k ≤ ℓ) :
    ContMDiff I I ∞ (SeqSystem.succMap f h) := by
  induction ℓ, h using Nat.le_induction with
  | base =>
      change ContMDiff I I ∞ (SeqSystem.succMap f (Nat.le_refl k))
      have hfun : SeqSystem.succMap f (Nat.le_refl k) = id := by
        funext x
        exact Nat.leRecOn_self x
      rw [hfun]
      exact contMDiff_id
  | succ ℓ hkℓ ih =>
      have hfun : SeqSystem.succMap f (Nat.le.step hkℓ) =
          f ℓ ∘ SeqSystem.succMap f hkℓ := by
        funext x
        exact Nat.leRecOn_succ hkℓ x
      rw [hfun]
      exact (hf ℓ).comp ih



omit [∀ (k : ℕ), IsManifold I ∞ (A k)] in
theorem succMap_inv_mdiff (f : ∀ k, A k → A (k + 1))
    (hemb : ∀ k, IsOpenEmbedding (f k))
    (hfInv : ∀ k, ContMDiffOn I I ∞ (Function.invFun (f k)) (Set.range (f k)))
    {k ℓ : ℕ} (h : k ≤ ℓ) :
    ContMDiffOn I I ∞ (Function.invFun (SeqSystem.succMap f h))
      (Set.range (SeqSystem.succMap f h)) := by
  induction ℓ, h using Nat.le_induction with
  | base =>
      change ContMDiffOn I I ∞
        (Function.invFun (SeqSystem.succMap f (Nat.le_refl k)))
        (Set.range (SeqSystem.succMap f (Nat.le_refl k)))
      have hfun : SeqSystem.succMap f (Nat.le_refl k) = id := by
        funext x
        exact Nat.leRecOn_self x
      rw [hfun]
      have hinvId : Function.invFun (id : A k → A k) = id := by
        funext x
        exact Function.leftInverse_invFun Function.injective_id x
      rw [hinvId]
      simpa using
        (contMDiff_id : ContMDiff I I ∞ (id : A k → A k)).contMDiffOn
  | succ ℓ hkℓ ih =>
      let prev : A k → A ℓ := SeqSystem.succMap f hkℓ
      have hfun : SeqSystem.succMap f (Nat.le.step hkℓ) = f ℓ ∘ prev := by
        funext x
        exact Nat.leRecOn_succ hkℓ x
      rw [hfun]
      have hprev : Function.Injective prev :=
        (SeqSystem.succMap_isOpenEmb f hemb hkℓ).injective
      have htotal : Function.Injective (f ℓ ∘ prev) := (hemb ℓ).injective.comp hprev
      have hinvTotal : ContMDiffOn I I ∞ (Function.invFun (f ℓ))
          (Set.range (f ℓ ∘ prev)) := by
        refine (hfInv ℓ).mono ?_
        rintro y ⟨x, rfl⟩
        exact ⟨prev x, rfl⟩
      have hmaps : Set.MapsTo (Function.invFun (f ℓ)) (Set.range (f ℓ ∘ prev))
          (Set.range prev) := by
        rintro y ⟨x, rfl⟩
        simp only [Function.comp_apply]
        rw [Function.leftInverse_invFun (hemb ℓ).injective]
        exact ⟨x, rfl⟩
      have hiPrev : ContMDiffOn I I ∞ (Function.invFun prev) (Set.range prev) := by
        simpa only [prev] using ih
      have hsmooth := hiPrev.comp hinvTotal hmaps
      refine hsmooth.congr (fun y hy => ?_)
      obtain ⟨x, rfl⟩ := hy
      simp only [Function.comp_apply]
      rw [Function.leftInverse_invFun (hemb ℓ).injective,
        Function.leftInverse_invFun hprev]
      change Function.invFun (f ℓ ∘ prev) ((f ℓ ∘ prev) x) = x
      exact Function.leftInverse_invFun htotal x



def ofSucc (f : ∀ k, A k → A (k + 1))
    (hemb : ∀ k, IsOpenEmbedding (f k))
    (hf : ∀ k, ContMDiff I I ∞ (f k))
    (hfInv : ∀ k, ContMDiffOn I I ∞ (Function.invFun (f k)) (Set.range (f k))) :
    SmoothSeqSystem I A where
  toSeqSystem := SeqSystem.ofSucc f hemb
  contMDiff_F h := succMap_contMDiff f hf h
  contMDiffOn_invFun_F h := succMap_inv_mdiff f hemb hfInv h


@[simp] theorem ofSucc_F_succ (f : ∀ k, A k → A (k + 1))
    (hemb : ∀ k, IsOpenEmbedding (f k))
    (hf : ∀ k, ContMDiff I I ∞ (f k))
    (hfInv : ∀ k, ContMDiffOn I I ∞ (Function.invFun (f k)) (Set.range (f k)))
    (k : ℕ) :
    (ofSucc (I := I) f hemb hf hfInv).toSeqSystem.F (Nat.le_succ k) = f k := by
  funext x
  change SeqSystem.succMap f (Nat.le_succ k) x = f k x
  unfold SeqSystem.succMap
  rw [show Nat.le_succ k = Nat.le.step (Nat.le_refl k) by rfl,
    Nat.leRecOn_succ (Nat.le_refl k) x, Nat.leRecOn_self]






theorem transitionHomeo_contMDiffOn (k ℓ : ℕ) :
    ContMDiffOn I I ∞ (S.toSeqSystem.transitionHomeo k ℓ)
      (S.toSeqSystem.transitionHomeo k ℓ).source := by
  set m := max k ℓ with hm
  have hkm : k ≤ m := le_max_left k ℓ
  have hℓm : ℓ ≤ m := le_max_right k ℓ

  have hFeq : ∀ w ∈ (S.toSeqSystem.transitionHomeo k ℓ).source,
      S.toSeqSystem.F hℓm (S.toSeqSystem.transitionHomeo k ℓ w) = S.toSeqSystem.F hkm w := by
    intro w hw
    apply S.toSeqSystem.incl_injective m
    rw [S.toSeqSystem.incl_comp hℓm, S.toSeqSystem.incl_comp hkm,
      S.toSeqSystem.incl_transitionHomeo hw]

  have hpt : ∀ w ∈ (S.toSeqSystem.transitionHomeo k ℓ).source,
      S.toSeqSystem.transitionHomeo k ℓ w
        = (Function.invFun (S.toSeqSystem.F hℓm) ∘ S.toSeqSystem.F hkm) w := by
    intro w hw
    change S.toSeqSystem.transitionHomeo k ℓ w = Function.invFun (S.toSeqSystem.F hℓm)
      (S.toSeqSystem.F hkm w)
    rw [← hFeq w hw,
      Function.leftInverse_invFun (S.toSeqSystem.isOpenEmb hℓm).injective]

  have hrange : (S.toSeqSystem.transitionHomeo k ℓ).source ⊆
      S.toSeqSystem.F hkm ⁻¹' range (S.toSeqSystem.F hℓm) := by
    intro w hw
    exact ⟨S.toSeqSystem.transitionHomeo k ℓ w, hFeq w hw⟩
  refine ContMDiffOn.congr ?_ (fun w hw => hpt w hw)
  exact (S.contMDiffOn_invFun_F hℓm).comp ((S.contMDiff_F hkm).contMDiffOn) hrange






instance instIsManifoldLim : IsManifold I ∞ S.toSeqSystem.Lim := by
  haveI : Nonempty H :=
    ⟨chartAt H (Classical.arbitrary (A 0)) (Classical.arbitrary (A 0))⟩
  apply isManifold_of_contDiffOn I ∞ S.toSeqSystem.Lim
  intro e₁ e₂ h₁ h₂
  obtain ⟨k, a, rfl⟩ := (S.toSeqSystem.mem_atlas_iff).mp h₁
  obtain ⟨ℓ, b, rfl⟩ := (S.toSeqSystem.mem_atlas_iff).mp h₂
  rw [S.toSeqSystem.limChart_symm_trans]
  set T' := ((chartAt H a).symm.trans (S.toSeqSystem.transitionHomeo k ℓ)).trans (chartAt H b)
    with hT'
  apply modelSpace_contDiffOn

  have key : ContMDiffOn I I ∞
      (⇑(chartAt H b) ∘ ⇑(S.toSeqSystem.transitionHomeo k ℓ) ∘ ⇑(chartAt H a).symm)
      (((chartAt H a).target ∩ (chartAt H a).symm ⁻¹' (S.toSeqSystem.transitionHomeo k ℓ).source) ∩
        (⇑(S.toSeqSystem.transitionHomeo k ℓ) ∘ ⇑(chartAt H a).symm) ⁻¹' (chartAt H b).source) :=
    (contMDiffOn_chart).comp' ((S.transitionHomeo_contMDiffOn k ℓ).comp' contMDiffOn_chart_symm)
  have hsrc : T'.source =
      ((chartAt H a).target ∩ (chartAt H a).symm ⁻¹' (S.toSeqSystem.transitionHomeo k ℓ).source) ∩
        (⇑(S.toSeqSystem.transitionHomeo k ℓ) ∘ ⇑(chartAt H a).symm) ⁻¹' (chartAt H b).source := by
    simp only [hT', OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.coe_trans]
  rw [hsrc]
  refine key.congr (fun z _ => ?_)
  rw [hT']
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]





theorem contMDiff_incl (k : ℕ) : ContMDiff I I ∞ (S.toSeqSystem.incl k) := by
  intro a
  have hchart : ContMDiffAt I I ∞ (chartAt H a) a :=
    contMDiffOn_chart.contMDiffAt ((chartAt H a).open_source.mem_nhds (mem_chart_source H a))
  have hlim_max : S.toSeqSystem.limChart k a ∈ IsManifold.maximalAtlas I ∞ S.toSeqSystem.Lim :=
    IsManifold.subset_maximalAtlas (S.toSeqSystem.limChart_mem_atlas k a)
  have htarget : chartAt H a a ∈ (S.toSeqSystem.limChart k a).target := by
    have hmem : S.toSeqSystem.incl k a ∈ (S.toSeqSystem.limChart k a).source :=
      S.toSeqSystem.mem_limChart_source (H := H) k a
    have hval0 : S.toSeqSystem.limChart k a (S.toSeqSystem.incl k a) = chartAt H a a := by
      unfold SeqSystem.limChart
      rw [OpenPartialHomeomorph.trans_apply, SeqSystem.inclHomeo_symm_apply]
    rw [← hval0]
    exact (S.toSeqSystem.limChart k a).map_source hmem
  have hsymm : ContMDiffAt I I ∞ (S.toSeqSystem.limChart k a).symm (chartAt H a a) :=
    contMDiffAt_symm_of_mem_maximalAtlas hlim_max htarget
  refine (hsymm.comp a hchart).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt H a).open_source.mem_nhds (mem_chart_source H a)] with a' ha'
  have hmem : S.toSeqSystem.incl k a' ∈ (S.toSeqSystem.limChart (H := H) k a).source := by
    unfold SeqSystem.limChart
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.symm_source, SeqSystem.inclHomeo_target]; exact ⟨a', rfl⟩
    · change (S.toSeqSystem.inclHomeo k).symm (S.toSeqSystem.incl k a') ∈ (chartAt H a).source
      rw [SeqSystem.inclHomeo_symm_apply]; exact ha'
  have hval : S.toSeqSystem.limChart k a (S.toSeqSystem.incl k a') = chartAt H a a' := by
    unfold SeqSystem.limChart
    rw [OpenPartialHomeomorph.trans_apply, SeqSystem.inclHomeo_symm_apply]
  change S.toSeqSystem.incl k a' = (S.toSeqSystem.limChart k a).symm (chartAt H a a')
  rw [← hval, (S.toSeqSystem.limChart k a).left_inv hmem]

section MetricTransport














variable [FiniteDimensional ℝ E]
variable [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]

open Bundle



omit [FiniteDimensional ℝ E] in
private theorem mfd_comp_id
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂]
    {f : M₁ → M₂} {g' : M₂ → M₁} {x : M₁}
    (hfg : g' ∘ f =ᶠ[nhds x] id)
    (hg : MDifferentiableAt I I g' (f x)) (hf : MDifferentiableAt I I f x) :
    (mfderiv I I g' (f x)).comp (mfderiv I I f x)
      = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  rw [← mfderiv_comp x hg hf, hfg.mfderiv_eq]
  exact mfderiv_id

omit [FiniteDimensional ℝ E] in
private theorem mfd_comp_id_app
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂]
    {f : M₁ → M₂} {g' : M₂ → M₁} {x : M₁}
    (hfg : g' ∘ f =ᶠ[nhds x] id)
    (hg : MDifferentiableAt I I g' (f x)) (hf : MDifferentiableAt I I f x)
    (v : TangentSpace I x) :
    mfderiv I I g' (f x) (mfderiv I I f x v) = v := by
  have h := DFunLike.congr_fun (mfd_comp_id (I := I) hfg hg hf) v
  simpa using h



omit [FiniteDimensional ℝ E] in
private theorem inner_base_eq
    {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace H M₀] [IsManifold I ∞ M₀]
    (g₀ : SmoothRiemannianMetric I M₀) {x y : M₀} (hxy : x = y) (v w : E) :
    (g₀.inner x : E →L[ℝ] E →L[ℝ] ℝ) v w = (g₀.inner y : E →L[ℝ] E →L[ℝ] ℝ) v w := by
  subst hxy; rfl


omit [FiniteDimensional ℝ E] in
private theorem mfd_base_eq
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂]
    (f : M₁ → M₂) {x y : M₁} (hxy : x = y) (v : E) :
    (mfderiv I I f x : E →L[ℝ] E) v = (mfderiv I I f y : E →L[ℝ] E) v := by
  subst hxy; rfl




omit [FiniteDimensional ℝ E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
theorem contMDiffAt_invIncl (k : ℕ) {z : S.toSeqSystem.Lim}
    (hz : z ∈ Set.range (S.toSeqSystem.incl k)) :
    ContMDiffAt I I ∞ (Function.invFun (S.toSeqSystem.incl k)) z := by
  obtain ⟨a, rfl⟩ := hz
  have hchart : ContMDiffAt I I ∞ (S.toSeqSystem.limChart k a) (S.toSeqSystem.incl k a) :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (S.toSeqSystem.limChart_mem_atlas k a))
      (S.toSeqSystem.mem_limChart_source (H := H) k a)
  have hval0 : S.toSeqSystem.limChart k a (S.toSeqSystem.incl k a) = chartAt H a a := by
    unfold SeqSystem.limChart
    rw [OpenPartialHomeomorph.trans_apply, SeqSystem.inclHomeo_symm_apply]
  have hsymm : ContMDiffAt I I ∞ (chartAt H a).symm
      (S.toSeqSystem.limChart k a (S.toSeqSystem.incl k a)) := by
    rw [hval0]
    exact contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a)
      ((chartAt H a).map_source (mem_chart_source H a))
  refine (hsymm.comp _ hchart).congr_of_eventuallyEq ?_
  filter_upwards [(S.toSeqSystem.limChart (H := H) k a).open_source.mem_nhds
    (S.toSeqSystem.mem_limChart_source (H := H) k a)] with z' hz'

  rw [SeqSystem.limChart, OpenPartialHomeomorph.trans_source] at hz'
  obtain ⟨hz'r, hz'c⟩ := hz'
  rw [OpenPartialHomeomorph.symm_source, S.toSeqSystem.inclHomeo_target] at hz'r
  have hz'eq : S.toSeqSystem.incl k ((S.toSeqSystem.inclHomeo k).symm z') = z' := by
    have := (S.toSeqSystem.inclHomeo k).right_inv
      (by rw [S.toSeqSystem.inclHomeo_target]; exact hz'r)
    rwa [← S.toSeqSystem.inclHomeo_apply]
  have hmem_c : (S.toSeqSystem.inclHomeo k).symm z' ∈ (chartAt H a).source := hz'c

  rw [← hz'eq, Function.leftInverse_invFun (S.toSeqSystem.incl_injective k)]
  change (S.toSeqSystem.inclHomeo k).symm z'
    = ((chartAt H a).symm ∘ (S.toSeqSystem.limChart k a)) (S.toSeqSystem.incl k _)
  have hval : S.toSeqSystem.limChart k a
      (S.toSeqSystem.incl k ((S.toSeqSystem.inclHomeo k).symm z'))
        = chartAt H a ((S.toSeqSystem.inclHomeo k).symm z') := by
    unfold SeqSystem.limChart
    rw [OpenPartialHomeomorph.trans_apply, SeqSystem.inclHomeo_symm_apply]
  simp only [Function.comp_apply, hval, (chartAt H a).left_inv hmem_c]






noncomputable def inclPartialDiffeo (k : ℕ) :
    PartialDiffeomorph I I S.toSeqSystem.Lim (A k) (∞ : WithTop ℕ∞) where
  toFun := Function.invFun (S.toSeqSystem.incl k)
  invFun := S.toSeqSystem.incl k
  source := Set.range (S.toSeqSystem.incl k)
  target := Set.univ
  map_source' := fun _ _ => Set.mem_univ _
  map_target' := fun a _ => ⟨a, rfl⟩
  left_inv' := fun _ hz => Function.invFun_eq hz
  right_inv' := fun a _ => Function.leftInverse_invFun (S.toSeqSystem.incl_injective k) a
  open_source := (S.toSeqSystem.incl_isOpenEmb k).isOpen_range
  open_target := isOpen_univ
  contMDiffOn_toFun := fun _ hz => (S.contMDiffAt_invIncl k hz).contMDiffWithinAt
  contMDiffOn_invFun := fun a _ => ((S.contMDiff_incl k) a).contMDiffWithinAt

omit [FiniteDimensional ℝ E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
@[simp] theorem inclPartialDiffeo_source (k : ℕ) :
    (S.inclPartialDiffeo k).source = Set.range (S.toSeqSystem.incl k) := rfl

omit [FiniteDimensional ℝ E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
@[simp] theorem inclPartialDiffeo_apply (k : ℕ) (z : S.toSeqSystem.Lim) :
    S.inclPartialDiffeo k z = Function.invFun (S.toSeqSystem.incl k) z := rfl



omit [FiniteDimensional ℝ E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
theorem invIncl_incl_le {j k : ℕ} (hjk : j ≤ k) (a : A j) :
    Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl j a)
      = S.toSeqSystem.F hjk a := by
  conv_lhs => rw [← S.toSeqSystem.incl_comp hjk a]
  exact Function.leftInverse_invFun (S.toSeqSystem.incl_injective k) _














def MetricCocycle (g : ∀ k, SmoothRiemannianMetric I (A k)) : Prop :=
  ∀ ⦃k ℓ : ℕ⦄ (h : k ≤ ℓ) (a : A k) (v w : TangentSpace I a),
    (g ℓ).inner (S.toSeqSystem.F h a)
      (mfderiv I I (S.toSeqSystem.F h) a v) (mfderiv I I (S.toSeqSystem.F h) a w)
      = (g k).inner a v w


omit [FiniteDimensional ℝ E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
theorem MetricCocycle.ofSucc (g : ∀ k, SmoothRiemannianMetric I (A k))
    (hstep : ∀ k (a : A k) (v w : TangentSpace I a),
      (g (k + 1)).inner (S.toSeqSystem.F (Nat.le_succ k) a)
        (mfderiv I I (S.toSeqSystem.F (Nat.le_succ k)) a v)
        (mfderiv I I (S.toSeqSystem.F (Nat.le_succ k)) a w) =
      (g k).inner a v w) :
    S.MetricCocycle g := by
  intro k l h
  induction l, h using Nat.le_induction with
  | base =>
      intro a v w
      have hself : S.toSeqSystem.F (Nat.le_refl k) = id := by
        funext x
        exact S.toSeqSystem.map_self k x
      rw [hself, mfderiv_id]
      rfl
  | succ l hkl ih =>
      intro a v w
      let hs : l ≤ l + 1 := Nat.le_succ l
      have hcomp : S.toSeqSystem.F (Nat.le.step hkl) =
          S.toSeqSystem.F hs ∘ S.toSeqSystem.F hkl := by
        funext x
        calc
          S.toSeqSystem.F (Nat.le.step hkl) x =
              S.toSeqSystem.F (hkl.trans hs) x :=
            S.toSeqSystem.F_apply_irrel (Nat.le.step hkl) (hkl.trans hs) x
          _ = S.toSeqSystem.F hs (S.toSeqSystem.F hkl x) :=
            (S.toSeqSystem.map_map hkl hs x).symm
      have hhd : MDifferentiableAt I I (S.toSeqSystem.F hkl) a :=
        (S.contMDiff_F hkl).contMDiffAt.mdifferentiableAt (by decide)
      have hsd : MDifferentiableAt I I (S.toSeqSystem.F hs)
          (S.toSeqSystem.F hkl a) :=
        (S.contMDiff_F hs).contMDiffAt.mdifferentiableAt (by decide)
      rw [hcomp, mfderiv_comp a hsd hhd]
      simp only [Function.comp_apply]
      calc
        (g (l + 1)).inner (S.toSeqSystem.F hs (S.toSeqSystem.F hkl a))
            (mfderiv I I (S.toSeqSystem.F hs) (S.toSeqSystem.F hkl a)
              (mfderiv I I (S.toSeqSystem.F hkl) a v))
            (mfderiv I I (S.toSeqSystem.F hs) (S.toSeqSystem.F hkl a)
              (mfderiv I I (S.toSeqSystem.F hkl) a w)) =
          (g l).inner (S.toSeqSystem.F hkl a)
            (mfderiv I I (S.toSeqSystem.F hkl) a v)
            (mfderiv I I (S.toSeqSystem.F hkl) a w) :=
          hstep l (S.toSeqSystem.F hkl a)
            (mfderiv I I (S.toSeqSystem.F hkl) a v)
            (mfderiv I I (S.toSeqSystem.F hkl) a w)
        _ = (g k).inner a v w := ih a v w



noncomputable def stageInner (g : ∀ k, SmoothRiemannianMetric I (A k)) (k : ℕ)
    (z : S.toSeqSystem.Lim) :
    TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ :=
  let D := mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z
  let step1 : TangentSpace I z →L[ℝ]
      TangentSpace I (Function.invFun (S.toSeqSystem.incl k) z) →L[ℝ] ℝ :=
    ((g k).inner (Function.invFun (S.toSeqSystem.incl k) z)).comp D
  (ContinuousLinearMap.precomp ℝ D).comp step1

omit [FiniteDimensional ℝ E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
theorem stageInner_apply (g : ∀ k, SmoothRiemannianMetric I (A k)) (k : ℕ)
    (z : S.toSeqSystem.Lim) (v w : TangentSpace I z) :
    S.stageInner g k z v w
      = (g k).inner (Function.invFun (S.toSeqSystem.incl k) z)
          (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z v)
          (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z w) := by
  unfold stageInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]

omit [FiniteDimensional ℝ E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
theorem stageInner_symm (g : ∀ k, SmoothRiemannianMetric I (A k)) (k : ℕ)
    (z : S.toSeqSystem.Lim) (v w : TangentSpace I z) :
    S.stageInner g k z v w = S.stageInner g k z w v := by
  rw [stageInner_apply, stageInner_apply]
  exact (g k).symm _ _ _

omit [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
omit [FiniteDimensional ℝ E] in
theorem stageInner_pos (g : ∀ k, SmoothRiemannianMetric I (A k)) (k : ℕ)
    {z : S.toSeqSystem.Lim} (hz : z ∈ Set.range (S.toSeqSystem.incl k))
    (v : TangentSpace I z) (hv : v ≠ 0) : 0 < S.stageInner g k z v v := by
  have hfg : (S.toSeqSystem.incl k) ∘ (Function.invFun (S.toSeqSystem.incl k))
      =ᶠ[nhds z] id := by
    filter_upwards [(S.toSeqSystem.incl_isOpenEmb k).isOpen_range.mem_nhds hz] with z' hz'
    exact Function.invFun_eq hz'
  have happ := mfd_comp_id_app (I := I) hfg
    ((S.contMDiff_incl k).mdifferentiableAt (by decide))
    ((S.contMDiffAt_invIncl k hz).mdifferentiableAt (by decide)) v
  rw [stageInner_apply]
  refine (g k).pos _ _ (fun h0 => hv ?_)
  rw [← happ, h0]
  exact (mfderiv I I (S.toSeqSystem.incl k) _).map_zero

omit [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
omit [FiniteDimensional ℝ E] in
theorem stageInner_bounded (g : ∀ k, SmoothRiemannianMetric I (A k)) (k : ℕ)
    {z : S.toSeqSystem.Lim} (hz : z ∈ Set.range (S.toSeqSystem.incl k)) :
    Bornology.IsVonNBounded ℝ {v : TangentSpace I z | S.stageInner g k z v v < 1} := by
  classical
  have hza : S.toSeqSystem.incl k (Function.invFun (S.toSeqSystem.incl k) z) = z :=
    Function.invFun_eq hz
  have hfg1 : (S.toSeqSystem.incl k) ∘ (Function.invFun (S.toSeqSystem.incl k))
      =ᶠ[nhds z] id := by
    filter_upwards [(S.toSeqSystem.incl_isOpenEmb k).isOpen_range.mem_nhds hz] with z' hz'
    exact Function.invFun_eq hz'
  have hid1 := mfd_comp_id_app (I := I) hfg1
    ((S.contMDiff_incl k).mdifferentiableAt (by decide))
    ((S.contMDiffAt_invIncl k hz).mdifferentiableAt (by decide))
  have hfg2 : (Function.invFun (S.toSeqSystem.incl k)) ∘ (S.toSeqSystem.incl k)
      =ᶠ[nhds (Function.invFun (S.toSeqSystem.incl k) z)] id :=
    Filter.EventuallyEq.of_eq (Function.invFun_comp (S.toSeqSystem.incl_injective k))
  have hinv_at' : ContMDiffAt I I ∞ (Function.invFun (S.toSeqSystem.incl k))
      (S.toSeqSystem.incl k (Function.invFun (S.toSeqSystem.incl k) z)) := by
    rw [hza]; exact S.contMDiffAt_invIncl k hz
  have hid2 := mfd_comp_id_app (I := I) hfg2
    (hinv_at'.mdifferentiableAt (by decide))
    ((S.contMDiff_incl k).mdifferentiableAt (by decide))
  have hset : {v : TangentSpace I z | S.stageInner g k z v v < 1}
      = (mfderiv I I (S.toSeqSystem.incl k) (Function.invFun (S.toSeqSystem.incl k) z) :
            TangentSpace I (Function.invFun (S.toSeqSystem.incl k) z) →L[ℝ] TangentSpace I z) ''
          {u : TangentSpace I (Function.invFun (S.toSeqSystem.incl k) z) |
            (g k).inner (Function.invFun (S.toSeqSystem.incl k) z) u u < 1} := by
    ext v
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hv1
      refine ⟨mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z v, ?_, hid1 v⟩
      rw [stageInner_apply] at hv1
      exact hv1
    · rintro ⟨u, hu, rfl⟩
      rw [stageInner_apply]
      have hDu : mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z
          (mfderiv I I (S.toSeqSystem.incl k) (Function.invFun (S.toSeqSystem.incl k) z) u)
            = u := by
        have hb := mfd_base_eq (I := I) (Function.invFun (S.toSeqSystem.incl k)) hza
          (mfderiv I I (S.toSeqSystem.incl k) (Function.invFun (S.toSeqSystem.incl k) z) u)
        rw [← hb]
        exact hid2 u
      rw [hDu]
      exact hu
  rw [hset]
  exact ((g k).isVonNBounded _).image _




omit [FiniteDimensional ℝ E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
theorem stageInner_mono (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    {k m : ℕ} (hkm : k ≤ m) {z : S.toSeqSystem.Lim}
    (hz : z ∈ Set.range (S.toSeqSystem.incl k)) :
    S.stageInner g k z = S.stageInner g m z := by
  obtain ⟨a, rfl⟩ := hz
  have hinjk := S.toSeqSystem.incl_injective k
  have hinjm := S.toSeqSystem.incl_injective m
  have hφk : Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a) = a :=
    Function.leftInverse_invFun hinjk a
  have hcomp : S.toSeqSystem.incl m (S.toSeqSystem.F hkm a) = S.toSeqSystem.incl k a :=
    S.toSeqSystem.incl_comp hkm a
  have hφm : Function.invFun (S.toSeqSystem.incl m) (S.toSeqSystem.incl k a)
      = S.toSeqSystem.F hkm a := by
    conv_lhs => rw [← hcomp]
    exact Function.leftInverse_invFun hinjm _

  have hev : (S.toSeqSystem.F hkm) ∘ (Function.invFun (S.toSeqSystem.incl k))
      =ᶠ[nhds (S.toSeqSystem.incl k a)] Function.invFun (S.toSeqSystem.incl m) := by
    filter_upwards [(S.toSeqSystem.incl_isOpenEmb k).isOpen_range.mem_nhds ⟨a, rfl⟩] with z' hz'
    obtain ⟨a', rfl⟩ := hz'
    change S.toSeqSystem.F hkm (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a'))
      = Function.invFun (S.toSeqSystem.incl m) (S.toSeqSystem.incl k a')
    rw [Function.leftInverse_invFun hinjk a']
    conv_rhs => rw [← S.toSeqSystem.incl_comp hkm a']
    rw [Function.leftInverse_invFun hinjm _]
  have hφk_at : ContMDiffAt I I ∞ (Function.invFun (S.toSeqSystem.incl k))
      (S.toSeqSystem.incl k a) := S.contMDiffAt_invIncl k ⟨a, rfl⟩

  have hD : (mfderiv I I (S.toSeqSystem.F hkm)
        (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a))).comp
      (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) (S.toSeqSystem.incl k a))
      = mfderiv I I (Function.invFun (S.toSeqSystem.incl m)) (S.toSeqSystem.incl k a) := by
    rw [← mfderiv_comp _ ((S.contMDiff_F hkm).mdifferentiableAt (by decide))
      (hφk_at.mdifferentiableAt (by decide))]
    exact hev.mfderiv_eq
  have hDapp : ∀ u : TangentSpace I (S.toSeqSystem.incl k a),
      mfderiv I I (S.toSeqSystem.F hkm)
        (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a))
        (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) (S.toSeqSystem.incl k a) u)
      = mfderiv I I (Function.invFun (S.toSeqSystem.incl m)) (S.toSeqSystem.incl k a) u := by
    intro u
    have h := DFunLike.congr_fun hD u
    simpa using h
  have hFb : S.toSeqSystem.F hkm (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a))
      = Function.invFun (S.toSeqSystem.incl m) (S.toSeqSystem.incl k a) := by
    rw [hφk, hφm]
  apply ContinuousLinearMap.ext; intro v
  apply ContinuousLinearMap.ext; intro w
  rw [stageInner_apply, stageInner_apply]
  calc (g k).inner (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a))
        (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) (S.toSeqSystem.incl k a) v)
        (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) (S.toSeqSystem.incl k a) w)
      = (g m).inner (S.toSeqSystem.F hkm
            (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a)))
          (mfderiv I I (S.toSeqSystem.F hkm)
            (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a))
            (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) (S.toSeqSystem.incl k a) v))
          (mfderiv I I (S.toSeqSystem.F hkm)
            (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a))
            (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) (S.toSeqSystem.incl k a) w)) :=
        (hg hkm _ _ _).symm
    _ = (g m).inner (S.toSeqSystem.F hkm
            (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a)))
          (mfderiv I I (Function.invFun (S.toSeqSystem.incl m)) (S.toSeqSystem.incl k a) v)
          (mfderiv I I (Function.invFun (S.toSeqSystem.incl m)) (S.toSeqSystem.incl k a) w) := by
        rw [hDapp v, hDapp w]
    _ = (g m).inner (Function.invFun (S.toSeqSystem.incl m) (S.toSeqSystem.incl k a))
          (mfderiv I I (Function.invFun (S.toSeqSystem.incl m)) (S.toSeqSystem.incl k a) v)
          (mfderiv I I (Function.invFun (S.toSeqSystem.incl m)) (S.toSeqSystem.incl k a) w) :=
        inner_base_eq (g m) hFb _ _

omit [FiniteDimensional ℝ E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
theorem stageInner_congr (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    {k ℓ : ℕ} {z : S.toSeqSystem.Lim}
    (hzk : z ∈ Set.range (S.toSeqSystem.incl k)) (hzℓ : z ∈ Set.range (S.toSeqSystem.incl ℓ)) :
    S.stageInner g k z = S.stageInner g ℓ z :=
  (S.stageInner_mono g hg (le_max_left k ℓ) hzk).trans
    (S.stageInner_mono g hg (le_max_right k ℓ) hzℓ).symm

omit [FiniteDimensional ℝ E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
theorem mem_range_rep (z : S.toSeqSystem.Lim) :
    z ∈ Set.range (S.toSeqSystem.incl (S.toSeqSystem.rep z).1) :=
  ⟨(S.toSeqSystem.rep z).2, S.toSeqSystem.incl_rep z⟩









noncomputable def limitMetric (g : ∀ k, SmoothRiemannianMetric I (A k))
    (hg : S.MetricCocycle g) : SmoothRiemannianMetric I S.toSeqSystem.Lim where
  inner z := S.stageInner g (S.toSeqSystem.rep z).1 z
  symm z v w := S.stageInner_symm g _ z v w
  pos z v hv := S.stageInner_pos g _ (S.mem_range_rep z) v hv
  isVonNBounded z := S.stageInner_bounded g _ (S.mem_range_rep z)
  contMDiff := by
    apply cotangentCov_clmSection_smooth_aux
      (V₂ := fun z : S.toSeqSystem.Lim => TangentSpace I z →L[ℝ] ℝ)
      (φ := fun z => S.stageInner g (S.toSeqSystem.rep z).1 z)
    intro Y
    apply cotangentCov_clmSection_smooth_aux
      (V₂ := fun _ : S.toSeqSystem.Lim => ℝ)
      (φ := fun z => S.stageInner g (S.toSeqSystem.rep z).1 z (Y z))
    intro W z₀
    rw [Bundle.contMDiffAt_section]

    have hstage : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun z => S.stageInner g (S.toSeqSystem.rep z).1 z (Y z) (W z)) z₀ := by

      set k₀ := (S.toSeqSystem.rep z₀).1 with hk₀
      have hz₀ : z₀ ∈ Set.range (S.toSeqSystem.incl k₀) := S.mem_range_rep z₀
      have hs_open : IsOpen (Set.range (S.toSeqSystem.incl k₀)) :=
        (S.toSeqSystem.incl_isOpenEmb k₀).isOpen_range

      have hφ : ContMDiffAt I I ∞ (Function.invFun (S.toSeqSystem.incl k₀)) z₀ :=
        S.contMDiffAt_invIncl k₀ hz₀
      have hg' : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
          (fun z => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
            (E := fun b : A k₀ => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
            (Function.invFun (S.toSeqSystem.incl k₀) z)
            ((g k₀).inner (Function.invFun (S.toSeqSystem.incl k₀) z))) z₀ := by
        have h := ContMDiffAt.comp (I' := I) z₀
          ((g k₀).contMDiff (Function.invFun (S.toSeqSystem.incl k₀) z₀)) hφ
        exact h
      have hφOn : ContMDiffOn I I ∞ (Function.invFun (S.toSeqSystem.incl k₀))
          (Set.range (S.toSeqSystem.incl k₀)) :=
        fun z hz => (S.contMDiffAt_invIncl k₀ hz).contMDiffWithinAt
      have htm : ContMDiffOn I.tangent I.tangent ∞
          (tangentMapWithin I I (Function.invFun (S.toSeqSystem.incl k₀))
            (Set.range (S.toSeqSystem.incl k₀)))
          (Bundle.TotalSpace.proj ⁻¹' (Set.range (S.toSeqSystem.incl k₀))) :=
        hφOn.contMDiffOn_tangentMapWithin le_rfl hs_open.uniqueMDiffOn
      have hpre_open : IsOpen
          (Bundle.TotalSpace.proj ⁻¹' (Set.range (S.toSeqSystem.incl k₀)) :
            Set (TangentBundle I S.toSeqSystem.Lim)) :=
        hs_open.preimage (FiberBundle.continuous_proj E (TangentSpace I))

      have hsec : ∀ Y' : Cₛ^∞⟮I; E, (TangentSpace I : S.toSeqSystem.Lim → Type _)⟯,
          ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
            (fun z => TotalSpace.mk' E (E := fun b : A k₀ => TangentSpace I b)
              (Function.invFun (S.toSeqSystem.incl k₀) z)
              (mfderiv I I (Function.invFun (S.toSeqSystem.incl k₀)) z (Y' z))) z₀ := by
        intro Y'
        have hYs : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
            (fun z => TotalSpace.mk' E (E := fun b : S.toSeqSystem.Lim => TangentSpace I b)
              z (Y' z)) z₀ := Y'.contMDiff z₀
        have hmem : (TotalSpace.mk' E (E := fun b : S.toSeqSystem.Lim => TangentSpace I b)
              z₀ (Y' z₀) : TangentBundle I S.toSeqSystem.Lim)
            ∈ Bundle.TotalSpace.proj ⁻¹' (Set.range (S.toSeqSystem.incl k₀)) := hz₀
        have hcomp := (htm.contMDiffAt (hpre_open.mem_nhds hmem)).comp z₀ hYs
        refine hcomp.congr_of_eventuallyEq ?_
        filter_upwards [hs_open.mem_nhds hz₀] with z hz
        change TotalSpace.mk' E (E := fun b : A k₀ => TangentSpace I b)
            (Function.invFun (S.toSeqSystem.incl k₀) z)
            (mfderiv I I (Function.invFun (S.toSeqSystem.incl k₀)) z (Y' z))
          = TotalSpace.mk' E (E := fun b : A k₀ => TangentSpace I b)
            (Function.invFun (S.toSeqSystem.incl k₀) z)
            (mfderivWithin I I (Function.invFun (S.toSeqSystem.incl k₀))
              (Set.range (S.toSeqSystem.incl k₀)) z (Y' z))
        rw [mfderivWithin_of_isOpen hs_open hz]

      have h_total : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
          (fun z => TotalSpace.mk' ℝ (E := Bundle.Trivial (A k₀) ℝ)
            (Function.invFun (S.toSeqSystem.incl k₀) z)
            ((g k₀).inner (Function.invFun (S.toSeqSystem.incl k₀) z)
              (mfderiv I I (Function.invFun (S.toSeqSystem.incl k₀)) z (Y z))
              (mfderiv I I (Function.invFun (S.toSeqSystem.incl k₀)) z (W z)))) z₀ :=
        ContMDiffAt.clm_bundle_apply₂
          (E₁ := fun b : A k₀ => TangentSpace I b)
          (E₂ := fun b : A k₀ => TangentSpace I b)
          (E₃ := fun _ : A k₀ => ℝ)
          hg' (hsec Y) (hsec W)
      have h_scalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun z => (g k₀).inner (Function.invFun (S.toSeqSystem.incl k₀) z)
            (mfderiv I I (Function.invFun (S.toSeqSystem.incl k₀)) z (Y z))
            (mfderiv I I (Function.invFun (S.toSeqSystem.incl k₀)) z (W z))) z₀ := by
        rw [contMDiffAt_totalSpace] at h_total
        convert h_total.2 using 1

      refine h_scalar.congr_of_eventuallyEq ?_
      filter_upwards [hs_open.mem_nhds hz₀] with z hz
      rw [show S.stageInner g (S.toSeqSystem.rep z).1 z = S.stageInner g k₀ z from
        S.stageInner_congr g hg (S.mem_range_rep z) hz]
      exact S.stageInner_apply g k₀ z (Y z) (W z)
    refine hstage.congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl



theorem limitMetric_pullback (g : ∀ k, SmoothRiemannianMetric I (A k))
    (hg : S.MetricCocycle g) (k : ℕ) (a : A k) (v w : TangentSpace I a) :
    (S.limitMetric g hg).inner (S.toSeqSystem.incl k a)
        (mfderiv I I (S.toSeqSystem.incl k) a v) (mfderiv I I (S.toSeqSystem.incl k) a w)
      = (g k).inner a v w := by
  have hz : S.toSeqSystem.incl k a ∈ Set.range (S.toSeqSystem.incl k) := ⟨a, rfl⟩
  have hstage : (S.limitMetric g hg).inner (S.toSeqSystem.incl k a)
      = S.stageInner g k (S.toSeqSystem.incl k a) := by
    change S.stageInner g (S.toSeqSystem.rep (S.toSeqSystem.incl k a)).1 (S.toSeqSystem.incl k a)
      = S.stageInner g k (S.toSeqSystem.incl k a)
    exact S.stageInner_congr g hg (S.mem_range_rep _) hz
  rw [hstage, stageInner_apply]
  have hφk : Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a) = a :=
    Function.leftInverse_invFun (S.toSeqSystem.incl_injective k) a
  have hfg : (Function.invFun (S.toSeqSystem.incl k)) ∘ (S.toSeqSystem.incl k)
      =ᶠ[nhds a] id :=
    Filter.EventuallyEq.of_eq (Function.invFun_comp (S.toSeqSystem.incl_injective k))
  have hinv_at : ContMDiffAt I I ∞ (Function.invFun (S.toSeqSystem.incl k))
      (S.toSeqSystem.incl k a) := S.contMDiffAt_invIncl k hz
  have happ := mfd_comp_id_app (I := I) hfg
    (hinv_at.mdifferentiableAt (by decide))
    ((S.contMDiff_incl k).mdifferentiableAt (by decide))
  rw [happ v, happ w]
  exact inner_base_eq (g k) hφk v w



theorem limitMetric_of_mem (g : ∀ k, SmoothRiemannianMetric I (A k))
    (hg : S.MetricCocycle g) (k : ℕ) {z : S.toSeqSystem.Lim}
    (hz : z ∈ Set.range (S.toSeqSystem.incl k)) (v w : TangentSpace I z) :
    (S.limitMetric g hg).inner z v w =
      (g k).inner (Function.invFun (S.toSeqSystem.incl k) z)
        (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z v)
        (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z w) := by
  have hstage : (S.limitMetric g hg).inner z = S.stageInner g k z := by
    change S.stageInner g (S.toSeqSystem.rep z).1 z = S.stageInner g k z
    exact S.stageInner_congr g hg (S.mem_range_rep z) hz
  rw [hstage, S.stageInner_apply]

end MetricTransport






instance instT2SpaceTangentBundleLim [∀ k, T2Space (A k)] :
    T2Space (TangentBundle I S.toSeqSystem.Lim) := by
  haveI : IsManifold I 1 S.toSeqSystem.Lim :=
    IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  infer_instance

end SmoothSeqSystem

end DifferentialGeometry
