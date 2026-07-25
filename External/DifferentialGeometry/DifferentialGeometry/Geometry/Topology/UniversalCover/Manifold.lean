import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import DifferentialGeometry.Geometry.Topology.UniversalCover.CoveringMap
import DifferentialGeometry.Geometry.Topology.UniversalCover.CountablePi1

























open Set Function Filter
open scoped Topology ContDiff Manifold

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]







noncomputable def localSection
    (xt : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    OpenPartialHomeomorph
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) M :=
  Classical.choose
    ((UniversalCover.proj_isCoveringMap (X := M)).isLocalHomeomorph xt)

omit [T2Space M] [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
lemma mem_source_localSection
    (xt : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    xt ∈ (localSection xt).source :=
  (Classical.choose_spec
    ((UniversalCover.proj_isCoveringMap (X := M)).isLocalHomeomorph xt)).1

omit [T2Space M] [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
lemma proj_eq_localSection
    (xt : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
      = localSection xt :=
  (Classical.choose_spec
    ((UniversalCover.proj_isCoveringMap (X := M)).isLocalHomeomorph xt)).2



noncomputable def coverChartAt
    (xt : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    OpenPartialHomeomorph
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H :=
  (localSection xt).trans (chartAt H (proj xt))







noncomputable instance instChartedSpace :
    ChartedSpace H
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) where
  atlas := Set.range
    (fun xt : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
      => coverChartAt xt)
  chartAt := coverChartAt
  mem_chart_source xt := by
    rw [coverChartAt, OpenPartialHomeomorph.trans_source]
    refine ⟨mem_source_localSection xt, ?_⟩
    have hfun := proj_eq_localSection xt
    have h1 : localSection xt xt = proj xt := by
      have := congrArg (fun f => f xt) hfun
      simpa using this.symm
    simp only [Set.mem_preimage, h1]
    exact mem_chart_source H (proj xt)
  chart_mem_atlas xt := Set.mem_range_self xt



omit [T2Space M] [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
lemma coverChartAt_target_eq
    (a : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    ((coverChartAt a) :
        OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).target
      = (chartAt H (proj a)).target ∩
        (chartAt H (proj a)).symm ⁻¹' (localSection a).target := by
  unfold coverChartAt
  exact OpenPartialHomeomorph.trans_target _ _



omit [T2Space M] [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
lemma coverChartAt_source_eq
    (b : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    ((coverChartAt b) :
        OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).source
      = (localSection b).source ∩
        (localSection b) ⁻¹' (chartAt H (proj b)).source := by
  unfold coverChartAt
  exact OpenPartialHomeomorph.trans_source _ _




omit [T2Space M] [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
lemma localSection_collapse
    (a b : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    {y : M} (hy : y ∈ (localSection a).target) :
    (localSection b) ((localSection a).symm y) = y := by
  have hfun_b := proj_eq_localSection b
  have hfun_a := proj_eq_localSection a
  have h_b_to_proj :
      (localSection b) ((localSection a).symm y)
        = proj ((localSection a).symm y) := by
    have := congrArg (fun f => f ((localSection a).symm y)) hfun_b
    simpa using this.symm
  have h_proj_to_a :
      proj ((localSection a).symm y)
        = (localSection a) ((localSection a).symm y) := by
    have := congrArg (fun f => f ((localSection a).symm y)) hfun_a
    simpa using this
  rw [h_b_to_proj, h_proj_to_a, (localSection a).right_inv hy]







instance instIsManifold :
    IsManifold I ∞
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) where
  compatible := by
    rintro e e' ⟨a, rfl⟩ ⟨b, rfl⟩
    set CovT : OpenPartialHomeomorph H H :=
      (coverChartAt a).symm.trans (coverChartAt b) with hCovT_def
    set MTrans : OpenPartialHomeomorph H H :=
      (chartAt H (proj a)).symm.trans (chartAt H (proj b)) with hMTrans_def
    have hMTrans_in : MTrans ∈ contDiffGroupoid ∞ I :=
      StructureGroupoid.compatible (contDiffGroupoid ∞ I)
        (chart_mem_atlas H (proj a)) (chart_mem_atlas H (proj b))
    have hCovT_open : IsOpen CovT.source := CovT.open_source
    have hsub : CovT.source ⊆ MTrans.source := by
      intro h hh
      rw [hCovT_def, OpenPartialHomeomorph.trans_source] at hh
      obtain ⟨hhCa, hhCb⟩ := hh
      rw [OpenPartialHomeomorph.symm_source, coverChartAt_target_eq] at hhCa
      obtain ⟨hhCaH, hhCaTarget⟩ := hhCa
      rw [hMTrans_def, OpenPartialHomeomorph.trans_source]
      refine ⟨hhCaH, ?_⟩
      rw [Set.mem_preimage, coverChartAt_source_eq] at hhCb
      obtain ⟨_, hin⟩ := hhCb
      rw [Set.mem_preimage] at hin
      have hSymm : (coverChartAt a).symm h
          = (localSection a).symm ((chartAt H (proj a)).symm h) := rfl
      rw [hSymm] at hin
      rwa [localSection_collapse a b hhCaTarget] at hin
    have hMTrans_restr_src :
        (MTrans.restrOpen CovT.source hCovT_open).source = CovT.source := by
      rw [OpenPartialHomeomorph.restrOpen_source]
      exact Set.inter_eq_right.mpr hsub
    have hRestrIn :
        MTrans.restrOpen CovT.source hCovT_open ∈ contDiffGroupoid ∞ I := by
      have hCR : ClosedUnderRestriction (contDiffGroupoid ∞ I) := inferInstance
      have hMR := closedUnderRestriction' (G := contDiffGroupoid ∞ I)
        hMTrans_in hCovT_open
      have h_eq : MTrans.restr CovT.source =
          MTrans.restrOpen CovT.source hCovT_open := by
        apply OpenPartialHomeomorph.toPartialEquiv_injective
        rw [OpenPartialHomeomorph.restr_toPartialEquiv,
          OpenPartialHomeomorph.restrOpen_toPartialEquiv,
          hCovT_open.interior_eq]
      rw [h_eq] at hMR
      exact hMR
    have hEq : CovT ≈ MTrans.restrOpen CovT.source hCovT_open := by
      refine ⟨?_, ?_⟩
      · rw [hMTrans_restr_src]
      · intro h hh
        simp only [OpenPartialHomeomorph.coe_restrOpen]
        rw [hCovT_def, OpenPartialHomeomorph.trans_source] at hh
        obtain ⟨hhCa, _⟩ := hh
        rw [OpenPartialHomeomorph.symm_source, coverChartAt_target_eq] at hhCa
        obtain ⟨_, hhCaTarget⟩ := hhCa
        have hCovT_h : CovT h =
            (chartAt H (proj b)) (localSection b ((coverChartAt a).symm h)) := rfl
        have hMTrans_h : MTrans h =
            (chartAt H (proj b)) ((chartAt H (proj a)).symm h) := rfl
        rw [hCovT_h, hMTrans_h]
        have hSymm : (coverChartAt a).symm h
            = (localSection a).symm ((chartAt H (proj a)).symm h) := rfl
        rw [hSymm]
        congr 1
        exact localSection_collapse a b hhCaTarget
    exact StructureGroupoid.mem_of_eqOnSource _ hRestrIn hEq

















omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
theorem proj_contMDiff :
    ContMDiff I I ∞
      (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) := by
  apply contMDiff_of_locally_contMDiffOn
  intro xt
  refine ⟨((coverChartAt xt) :
      OpenPartialHomeomorph
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).source,
    ((coverChartAt xt) :
      OpenPartialHomeomorph
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).open_source,
    ?_, ?_⟩
  · exact (mem_chart_source H
      (M :=
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) xt)
  have hcongr :
      ∀ z ∈ ((coverChartAt xt) :
          OpenPartialHomeomorph
            (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).source,
        ((chartAt H (proj xt)).symm ∘ (coverChartAt xt)) z = proj z := by
    intro z hz
    rw [coverChartAt_source_eq] at hz
    obtain ⟨hzLS, hzLSproj⟩ := hz
    rw [Set.mem_preimage] at hzLSproj
    have hCovApp : (coverChartAt xt) z
        = (chartAt H (proj xt)) ((localSection xt) z) := by
      unfold coverChartAt
      rw [OpenPartialHomeomorph.trans_apply]
    have hLSproj : (localSection xt) z = proj z := by
      have hfun := proj_eq_localSection xt
      have := congrArg (fun f => f z) hfun
      simpa using this.symm
    have hprojSrc : proj z ∈ (chartAt H (proj xt)).source := by
      rw [← hLSproj]; exact hzLSproj
    change (chartAt H (proj xt)).symm ((coverChartAt xt) z) = proj z
    rw [hCovApp, hLSproj]
    exact (chartAt H (proj xt)).left_inv hprojSrc
  set CXT : OpenPartialHomeomorph
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H :=
    coverChartAt xt with hCXT_def
  have h_chart_xt : ContMDiffOn I I ∞ (CXT : _ → H) CXT.source := by
    have hgoal :
        ContMDiffOn I I ∞
          (chartAt H
            (M :=
              DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            xt :
            _ → H)
          (chartAt H
            (M :=
              DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            xt).source :=
      contMDiffOn_chart
    exact hgoal
  have h_chart_symm : ContMDiffOn I I ∞
      (chartAt H (M := M) (proj xt)).symm
      (chartAt H (M := M) (proj xt)).target := contMDiffOn_chart_symm
  have hMapsTo :
      CXT.source ⊆ (CXT : _ → H) ⁻¹' (chartAt H (M := M) (proj xt)).target := by
    intro z hz
    have hmap : CXT z ∈ CXT.target := CXT.map_source hz
    rw [hCXT_def, coverChartAt_target_eq] at hmap
    exact hmap.1
  have hcomp : ContMDiffOn I I ∞
      ((chartAt H (M := M) (proj xt)).symm ∘ (CXT : _ → H))
      CXT.source :=
    h_chart_symm.comp h_chart_xt hMapsTo
  rw [hCXT_def] at hcomp
  refine hcomp.congr ?_
  intro z hz
  exact (hcongr z hz).symm







instance instT2Space :
    T2Space
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) := by
  have hSep : IsSeparatedMap
      (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
    UniversalCover.proj_isCoveringMap.isSeparatedMap
  refine ⟨?_⟩
  intro a b hab
  by_cases h : proj a = proj b
  · obtain ⟨U, V, hUopen, hVopen, haU, hbV, hUVdisj⟩ := hSep a b h hab
    exact ⟨U, V, hUopen, hVopen, haU, hbV, hUVdisj⟩
  · obtain ⟨U, V, hUopen, hVopen, hpaU, hpbV, hUVdisj⟩ := t2_separation h
    have hpcont : Continuous
        (proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
      UniversalCover.proj_isCoveringMap.continuous
    refine ⟨proj ⁻¹' U, proj ⁻¹' V,
      hUopen.preimage hpcont, hVopen.preimage hpcont, hpaU, hpbV, ?_⟩
    rw [Set.disjoint_iff] at hUVdisj ⊢
    rintro z ⟨hzU, hzV⟩
    exact hUVdisj ⟨hzU, hzV⟩













theorem fundamentalGroup_isCountablyGenerated_aux
    (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X]
    [ConnectedSpace X] [LocPathConnectedSpace X]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X]
    (x : X)
    (B : ℕ → Set X)
    (hBopen : ∀ n, IsOpen (B n))
    (hBpc : ∀ n, IsPathConnected (B n))
    (hBnull : ∀ n, ∀ (y : X) (_ : y ∈ B n) (γ : _root_.Path y y),
      Set.range γ.toContinuousMap ⊆ B n →
        (⟦γ⟧ : _root_.Path.Homotopic.Quotient y y) = ⟦_root_.Path.refl y⟧)
    (hBbasis : TopologicalSpace.IsTopologicalBasis (Set.range B))
    (hpcInter :
      ∀ (m n : ℕ),
        ∀ a, a ∈ B m → a ∈ B n → ∀ b, b ∈ B m → b ∈ B n →
          JoinedIn (B m ∩ B n) a b) :
    ∃ (S : Type) (_ : Countable S) (f : S → FundamentalGroup X x),
      Function.Surjective f :=
  fundamentalGroup_countable_surjection_of_nullHomotopic_basis X x B hBopen hBpc hBnull hBbasis hpcInter















theorem fundamentalGroup_countable_of_secondCountable
    (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X]
    [ConnectedSpace X] [LocPathConnectedSpace X]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X]
    (x : X)
    (B : ℕ → Set X)
    (hBopen : ∀ n, IsOpen (B n))
    (hBpc : ∀ n, IsPathConnected (B n))
    (hBnull : ∀ n, ∀ (y : X) (_ : y ∈ B n) (γ : _root_.Path y y),
      Set.range γ.toContinuousMap ⊆ B n →
        (⟦γ⟧ : _root_.Path.Homotopic.Quotient y y) = ⟦_root_.Path.refl y⟧)
    (hBbasis : TopologicalSpace.IsTopologicalBasis (Set.range B))
    (hpcInter :
      ∀ (m n : ℕ),
        ∀ a, a ∈ B m → a ∈ B n → ∀ b, b ∈ B m → b ∈ B n →
          JoinedIn (B m ∩ B n) a b) :
    Countable (FundamentalGroup X x) := by
  obtain ⟨S, hS, f, hf⟩ :=
    fundamentalGroup_isCountablyGenerated_aux X x B hBopen hBpc hBnull hBbasis hpcInter
  exact Function.Surjective.countable hf














theorem fibre_countable
    [SecondCountableTopology M]
    (x : M) :
    Countable
      ((proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
        ⁻¹' {x}) := by
  obtain ⟨B, hBopen, hBpc, hBnull, hBbasis⟩ :=
    uc_pi1_countable_basis_refinement M
  have hpcInter :
      ∀ (m n : ℕ),
        ∀ a, a ∈ B m → a ∈ B n → ∀ b, b ∈ B m → b ∈ B n →
          JoinedIn (B m ∩ B n) a b := by
    sorry
  have h_pi1_countable :
      Countable (FundamentalGroup M (default : M)) :=
    fundamentalGroup_countable_of_secondCountable M default B hBopen hBpc hBnull hBbasis hpcInter
  haveI : PathConnectedSpace M := PathConnectedSpace.of_locPathConnectedSpace
  have hpath : Path (default : M) x := PathConnectedSpace.somePath default x
  let e_fibre :
      ((proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
        ⁻¹' {x}) ≃ Path.Homotopic.Quotient (default : M) x :=
    { toFun := fun p => by
        rcases p with ⟨⟨y, q⟩, hy⟩
        simp only [proj, Set.mem_preimage, Set.mem_singleton_iff] at hy
        subst hy
        exact q
      invFun := fun q => ⟨⟨x, q⟩, by simp [proj]⟩
      left_inv := by
        rintro ⟨⟨y, q⟩, hy⟩
        simp only [proj, Set.mem_preimage, Set.mem_singleton_iff] at hy
        subst hy
        rfl
      right_inv := fun q => rfl }
  let e_pathTrans :
      Path.Homotopic.Quotient (default : M) x ≃
        Path.Homotopic.Quotient (default : M) (default : M) :=
    { toFun := fun q =>
        Path.Homotopic.Quotient.trans q (Path.Homotopic.Quotient.mk hpath.symm)
      invFun := fun q =>
        Path.Homotopic.Quotient.trans q (Path.Homotopic.Quotient.mk hpath)
      left_inv := by
        intro q
        induction q using Path.Homotopic.Quotient.ind with | mk a =>
        simp only [Path.Homotopic.Quotient.mk_symm]
        rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
          Path.Homotopic.Quotient.trans_refl]
      right_inv := by
        intro q
        induction q using Path.Homotopic.Quotient.ind with | mk a =>
        simp only [Path.Homotopic.Quotient.mk_symm]
        rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
          Path.Homotopic.Quotient.trans_refl] }
  have hPHQ_countable :
      Countable (Path.Homotopic.Quotient (default : M) (default : M)) :=
    h_pi1_countable
  exact Countable.of_equiv _ (e_fibre.trans e_pathTrans).symm











theorem sigmaCompact_from_countable_fibre
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SigmaCompactSpace X] [T2Space X]
    {p : E → X} (hp : IsCoveringMap p)
    (hfib : ∀ x, Countable (p ⁻¹' {x})) :
    SigmaCompactSpace E := by
  rw [← isSigmaCompact_univ_iff]
  obtain ⟨K, hKcomp, hKcov⟩ :=
    SigmaCompactSpace.exists_compact_covering (X := X)
  have hunion : (Set.univ : Set E) = ⋃ n, p ⁻¹' (K n) := by
    rw [← Set.preimage_iUnion, hKcov, Set.preimage_univ]
  rw [hunion]
  refine isSigmaCompact_iUnion _ ?_
  intro n
  let U : X → Set X := fun x => Classical.choose (hp x).2
  have hUspec : ∀ x, x ∈ U x ∧ IsOpen (U x) ∧ IsOpen (p ⁻¹' U x) ∧
      ∃ H : (p ⁻¹' U x) ≃ₜ (U x) × (p ⁻¹' {x}), ∀ y, (H y).1.1 = p y :=
    fun x => Classical.choose_spec (hp x).2
  have hKsub : K n ⊆ ⋃ x : X, U x := by
    intro y _
    exact Set.mem_iUnion.mpr ⟨y, (hUspec y).1⟩
  obtain ⟨J, hJ⟩ :=
    (hKcomp n).elim_finite_subcover U (fun x => (hUspec x).2.1) hKsub
  haveI hKnCompact : CompactSpace ↥(K n) :=
    isCompact_iff_compactSpace.mp (hKcomp n)
  haveI : NormalSpace ↥(K n) := inferInstance
  haveI hJ_finite : Finite ↥(↑J : Set X) := (J.finite_toSet).to_subtype
  let V : ↥(↑J : Set X) → Set ↥(K n) := fun j =>
    Subtype.val ⁻¹' (U (j : X))
  have hVopen : ∀ j : ↥(↑J : Set X), IsOpen (V j) := fun j =>
    (hUspec (j : X)).2.1.preimage continuous_subtype_val
  have hVcover : (Set.univ : Set ↥(K n)) ⊆ ⋃ j : ↥(↑J : Set X), V j := by
    intro y _
    have hpy : (y : X) ∈ K n := y.2
    have hbig : (y : X) ∈ ⋃ j ∈ J, U j := hJ hpy
    rcases Set.mem_iUnion₂.mp hbig with ⟨j, hjJ, hjy⟩
    refine Set.mem_iUnion.mpr ⟨⟨j, hjJ⟩, ?_⟩
    exact hjy
  have hVptfin :
      ∀ x ∈ (Set.univ : Set ↥(K n)),
        {j : ↥(↑J : Set X) | x ∈ V j}.Finite := by
    intro x _
    exact Set.toFinite _
  obtain ⟨W, hWcov, hWclosed, hWsub⟩ :=
    exists_subset_iUnion_closed_subset (s := (Set.univ : Set ↥(K n)))
      (u := V) isClosed_univ hVopen hVptfin hVcover
  let Wproj : ↥(↑J : Set X) → Set X := fun j => Subtype.val '' (W j)
  have hWproj_compact : ∀ j, IsCompact (Wproj j) := by
    intro j
    have hWj_compact : IsCompact (W j) := (hWclosed j).isCompact
    exact hWj_compact.image continuous_subtype_val
  have hWproj_sub_U : ∀ j, Wproj j ⊆ U (j : X) := by
    intro j y hy
    rcases hy with ⟨w, hw, rfl⟩
    exact hWsub j hw
  have hWproj_sub_Kn : ∀ j, Wproj j ⊆ K n := by
    intro j y hy
    rcases hy with ⟨w, _, rfl⟩
    exact w.2
  have hWproj_cover : K n ⊆ ⋃ j : ↥(↑J : Set X), Wproj j := by
    intro y hy
    have hyKn : (⟨y, hy⟩ : ↥(K n)) ∈ (Set.univ : Set ↥(K n)) := trivial
    rcases Set.mem_iUnion.mp (hWcov hyKn) with ⟨j, hyj⟩
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    exact ⟨⟨y, hy⟩, hyj, rfl⟩
  have hpKn_eq : p ⁻¹' (K n) = ⋃ j : ↥(↑J : Set X), p ⁻¹' (Wproj j) := by
    ext e
    constructor
    · intro he
      have hpeKn : p e ∈ K n := he
      rcases Set.mem_iUnion.mp (hWproj_cover hpeKn) with ⟨j, hje⟩
      exact Set.mem_iUnion.mpr ⟨j, hje⟩
    · intro he
      rcases Set.mem_iUnion.mp he with ⟨j, hje⟩
      exact hWproj_sub_Kn j hje
  rw [hpKn_eq]
  refine isSigmaCompact_iUnion _ ?_
  intro j
  obtain ⟨H, hHproj⟩ := (hUspec (j : X)).2.2.2
  set S : Set ↥(U (j : X)) := Subtype.val ⁻¹' (Wproj j) with hS_def
  have hS_compact : IsCompact S := by
    have hsubsetrange :
        Wproj j ⊆ Set.range (Subtype.val : ↥(U (j : X)) → X) := by
      rw [Subtype.range_val]
      exact hWproj_sub_U j
    have himg : Subtype.val '' S = Wproj j := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        rcases hsubsetrange hy with ⟨z, rfl⟩
        exact ⟨z, hy, rfl⟩
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]
    exact hWproj_compact j
  let g : (p ⁻¹' ({(j : X)} : Set X)) → ↥(U (j : X)) → E :=
    fun i u => (H.symm (u, i) : ↥(p ⁻¹' U (j : X)))
  have hg_cont : ∀ i, Continuous (g i) := by
    intro i
    have h₁ : Continuous (fun u : ↥(U (j : X)) => (u, i)) :=
      continuous_id.prodMk continuous_const
    have h₂ : Continuous
        (fun y : (↥(U (j : X))) × (p ⁻¹' ({(j : X)} : Set X)) =>
          (H.symm y : ↥(p ⁻¹' U (j : X)))) := H.symm.continuous
    have h₃ : Continuous (fun y : ↥(p ⁻¹' U (j : X)) => (y : E)) :=
      continuous_subtype_val
    exact h₃.comp (h₂.comp h₁)
  have hgS_compact : ∀ i, IsCompact (g i '' S) :=
    fun i => hS_compact.image (hg_cont i)
  have hp_eq :
      p ⁻¹' (Wproj j)
        = ⋃ i : (p ⁻¹' ({(j : X)} : Set X)), g i '' S := by
    ext e
    constructor
    · intro he
      have hpeU : p e ∈ U (j : X) := hWproj_sub_U j he
      have heU : e ∈ p ⁻¹' (U (j : X)) := hpeU
      let eU : ↥(p ⁻¹' U (j : X)) := ⟨e, heU⟩
      set pair := H eU with hpair_def
      have hpair1 : (pair.1 : X) = p e := hHproj eU
      have hpair_back : H.symm pair = eU := H.symm_apply_apply eU
      refine Set.mem_iUnion.mpr ⟨pair.2, ?_⟩
      refine ⟨pair.1, ?_, ?_⟩
      · change (pair.1 : X) ∈ Wproj j
        rw [hpair1]
        exact he
      · change ((H.symm (pair.1, pair.2) : ↥(p ⁻¹' U (j : X))) : E) = e
        have hsplit : (pair.1, pair.2) = pair := rfl
        rw [hsplit, hpair_back]
    · intro he
      rcases Set.mem_iUnion.mp he with ⟨i, hi⟩
      rcases hi with ⟨u, hu, rfl⟩
      change p ((H.symm (u, i) : ↥(p ⁻¹' U (j : X))) : E) ∈ Wproj j
      have heq1 :
          (H (H.symm (u, i))).1.1
            = p ((H.symm (u, i) : ↥(p ⁻¹' U (j : X))) : E) :=
        hHproj (H.symm (u, i))
      have heq2 : H (H.symm (u, i)) = (u, i) := H.apply_symm_apply (u, i)
      rw [heq2] at heq1
      rw [← heq1]
      exact hu
  rw [hp_eq]
  haveI : Countable (p ⁻¹' ({(j : X)} : Set X)) := hfib (j : X)
  exact isSigmaCompact_iUnion_of_isCompact _ hgS_compact

variable [SecondCountableTopology M] [Nonempty M]







instance instSigmaCompactSpace :
    SigmaCompactSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
  sigmaCompact_from_countable_fibre UniversalCover.proj_isCoveringMap fibre_countable




omit [InnerProductSpace ℝ E] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [LocPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M] [SecondCountableTopology M] [Nonempty M] in
theorem locallyCompactSpaceBase (I : ModelWithCorners ℝ E H) :
    LocallyCompactSpace M :=
  Manifold.locallyCompact_of_finiteDimensional I








instance instLocallyCompactSpace [LocallyCompactSpace M] :
    LocallyCompactSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) := by
  have hLH : IsLocalHomeomorph (proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
    UniversalCover.proj_isCoveringMap.isLocalHomeomorph
  refine ⟨fun xt n hn => ?_⟩
  obtain ⟨e, hxte, _hfe⟩ := hLH xt
  have hSrcNhd : e.source ∈ 𝓝 xt := e.open_source.mem_nhds hxte
  have hInterNhd : n ∩ e.source ∈ 𝓝 xt := Filter.inter_mem hn hSrcNhd
  have himg : e '' (n ∩ e.source) ∈ 𝓝 (e xt) :=
    e.image_mem_nhds hxte hInterNhd
  obtain ⟨K, hK_nhd, hKsub, hKcomp⟩ :=
    LocallyCompactSpace.local_compact_nhds (e xt) (e '' (n ∩ e.source)) himg
  have hKtgt : K ⊆ e.target := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := hKsub hy
    exact e.map_source ha.2
  have hSymmComp : IsCompact (e.symm '' K) :=
    hKcomp.image_of_continuousOn (e.continuousOn_symm.mono hKtgt)
  refine ⟨e.symm '' K, ?_, ?_, hSymmComp⟩
  · rw [← e.symm_map_nhds_eq hxte]
    exact Filter.image_mem_map hK_nhd
  · rintro _ ⟨y, hyK, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hKsub hyK
    rw [e.left_inv ha.2]
    exact ha.1

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
