import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.FlatIdentity
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.BoundaryExtension.SeeleyTimeExtension
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.BoundaryExtension.FullIntervalFlow
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ChartBridge


namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem flow_mfderiv_continuousWithinAt_zero_of_jointSmooth
    (Φ : ℝ → M → M) {lo hi : ℝ} (hlo : lo < 0) (hhi : 0 < hi)
    (hΦsm : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2)
      (Set.Ioo lo hi ×ˢ (Set.univ : Set M)))
    (x : M) (v : TangentSpace I x) :
    ContinuousWithinAt (fun s : ℝ =>
        (⟨Φ s x, mfderiv I I (fun y : M => Φ s y) x v⟩ : TangentBundle I M))
      (Set.Ici (0 : ℝ)) 0 := by
  classical
  set y₀ : M := Φ 0 x with hy₀
  set c : PartialEquiv M E := extChartAt I y₀ with hc
  have hmem0 : ((0 : ℝ), x) ∈ Set.Ioo lo hi ×ˢ (Set.univ : Set M) :=
    ⟨⟨hlo, hhi⟩, Set.mem_univ _⟩
  have hopen : IsOpen (Set.Ioo lo hi ×ˢ (Set.univ : Set M)) := isOpen_Ioo.prod isOpen_univ
  have hf : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) (0, x) :=
    (hΦsm _ hmem0).contMDiffAt (hopen.mem_nhds hmem0)
  have hg : ContMDiffAt 𝓘(ℝ, ℝ) I 0 (fun _ : ℝ => x) 0 := contMDiffAt_const
  have hP : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E →L[ℝ] E) 0
      (inTangentCoordinates I I (fun _ : ℝ => x) (fun s : ℝ => Φ s x)
        (fun s : ℝ => mfderiv I I (fun y : M => Φ s y) x) 0) 0 :=
    hf.mfderiv (fun s y => Φ s y) (fun _ => x) hg (by norm_num)
  set P : ℝ → E := fun s => inTangentCoordinates I I (fun _ : ℝ => x) (fun s : ℝ => Φ s x)
      (fun s : ℝ => mfderiv I I (fun y : M => Φ s y) x) 0 s v with hP_def
  have hPcont : ContinuousAt P 0 := hP.continuousAt.clm_apply continuousAt_const
  have horbit_cont : ContinuousAt (fun s : ℝ => Φ s x) 0 := by
    have hpair : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞ (fun s : ℝ => (s, x)) 0 :=
      contMDiffAt_id.prodMk contMDiffAt_const
    exact (hf.comp 0 hpair).continuousAt
  have hsrc_nhds : (fun s : ℝ => Φ s x) ⁻¹' (chartAt H y₀).source ∈ nhds (0 : ℝ) :=
    horbit_cont.preimage_mem_nhds ((chartAt H y₀).open_source.mem_nhds (mem_chart_source H y₀))
  have hctgt_open : IsOpen c.target := isOpen_extChartAt_target (I := I) y₀
  have hc0_tgt : c (Φ 0 x) ∈ c.target := by
    rw [show Φ 0 x = y₀ from rfl]; exact mem_extChartAt_target (I := I) y₀
  have hbase_cont : ContinuousAt (fun s : ℝ => c (Φ s x)) 0 := by
    have hcont_c : ContinuousAt c (Φ 0 x) := by
      rw [show Φ 0 x = y₀ from rfl]
      exact continuousAt_extChartAt (I := I) y₀
    exact ContinuousAt.comp (g := fun y : M => c y) (f := fun s : ℝ => Φ s x) hcont_c horbit_cont
  have hbase_nhds : (fun s : ℝ => c (Φ s x)) ⁻¹' c.target ∈ nhds (0 : ℝ) :=
    hbase_cont.preimage_mem_nhds (hctgt_open.mem_nhds hc0_tgt)
  have hfib : ∀ s : ℝ, Φ s x ∈ (chartAt H y₀).source →
      mfderivWithin 𝓘(ℝ, E) I c.symm c.target (c (Φ s x)) (P s)
        = mfderiv I I (fun y : M => Φ s y) x v := by
    intro s hs
    have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
    have hΦsrc : Φ s x ∈ (chartAt H y₀).source := hs
    have hcomp := inTangentCoordinates_eq_mfderiv_comp (I := I) (I' := I)
      (f := fun _ : ℝ => x) (g := fun s : ℝ => Φ s x)
      (ϕ := fun s : ℝ => mfderiv I I (fun y : M => Φ s y) x) (x₀ := 0) (x := s) hxsrc hΦsrc
    have hS₀ : mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) (extChartAt I x x)
        = ContinuousLinearMap.id ℝ (TangentSpace I x) :=
      mfderivWithin_range_extChartAt_symm (I := I) (x := x)
    have hPval : P s = mfderiv I 𝓘(ℝ, E) c (Φ s x) (mfderiv I I (fun y : M => Φ s y) x v) := by
      have hap := congrArg (fun L : E →L[ℝ] E => L v) hcomp
      simp only [hP_def, hS₀] at hap ⊢
      rw [hap]
      rfl
    have hΦtgt : c (Φ s x) ∈ c.target := by
      rw [hc]; exact (extChartAt I y₀).map_source (by rw [extChartAt_source]; exact hΦsrc)
    have heqd : mfderivWithin 𝓘(ℝ, E) I c.symm c.target (c (Φ s x))
        = mfderivWithin 𝓘(ℝ, E) I c.symm (Set.range I) (c (Φ s x)) := by
      rw [mfderivWithin_of_isOpen hctgt_open hΦtgt,
        mfderivWithin_of_mem_nhds (Filter.mem_of_superset (hctgt_open.mem_nhds hΦtgt)
          (extChartAt_target_subset_range y₀))]
    rw [heqd, hPval]
    have hΦsrc' : Φ s x ∈ (extChartAt I y₀).source := by rw [extChartAt_source]; exact hΦsrc
    have hcancel := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I) (x := y₀)
      (y := Φ s x) hΦsrc'
    have := congrArg (fun L : TangentSpace I (Φ s x) →L[ℝ] TangentSpace I (Φ s x) =>
        L (mfderiv I I (fun y : M => Φ s y) x v)) hcancel
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hc] using this
  have hrecon : (fun s : ℝ =>
        (⟨Φ s x, mfderiv I I (fun y : M => Φ s y) x v⟩ : TangentBundle I M))
      =ᶠ[nhds (0 : ℝ)]
      (fun s : ℝ => tangentMapWithin 𝓘(ℝ, E) I c.symm c.target
        (TotalSpace.mk' E (c (Φ s x)) (P s))) := by
    filter_upwards [hsrc_nhds] with s hs
    have hbase : c.symm (c (Φ s x)) = Φ s x := by
      rw [hc]; exact (extChartAt I y₀).left_inv (by rw [extChartAt_source]; exact hs)
    change (⟨Φ s x, mfderiv I I (fun y : M => Φ s y) x v⟩ : TangentBundle I M)
      = ⟨c.symm (c (Φ s x)), mfderivWithin 𝓘(ℝ, E) I c.symm c.target (c (Φ s x)) (P s)⟩
    refine Bundle.TotalSpace.ext (x := ⟨Φ s x, mfderiv I I (fun y : M => Φ s y) x v⟩)
      (y := ⟨c.symm (c (Φ s x)), mfderivWithin 𝓘(ℝ, E) I c.symm c.target (c (Φ s x)) (P s)⟩)
      hbase.symm ?_
    exact heq_of_eq (hfib s hs).symm
  have hRHScont : ContinuousAt
      (fun s : ℝ => tangentMapWithin 𝓘(ℝ, E) I c.symm c.target
        (TotalSpace.mk' E (c (Φ s x)) (P s))) 0 := by
    have hcsm : ContMDiffOn 𝓘(ℝ, E) I 1 c.symm c.target :=
      (contMDiffOn_extChartAt_symm (I := I) (n := ∞) y₀).of_le (by
        exact le_of_lt (by exact_mod_cast ENat.coe_lt_top 1))
    have htm : ContinuousOn (tangentMapWithin 𝓘(ℝ, E) I c.symm c.target)
        (Bundle.TotalSpace.proj ⁻¹' c.target) :=
      hcsm.continuousOn_tangentMapWithin le_rfl hctgt_open.uniqueMDiffOn
    have hpath : ContinuousAt
        (fun s : ℝ => (TotalSpace.mk' E (c (Φ s x)) (P s) : TangentBundle 𝓘(ℝ, E) E)) 0 := by
      have hpair : ContinuousAt (fun s : ℝ => ((c (Φ s x), P s) : ModelProd E E)) 0 :=
        hbase_cont.prodMk hPcont
      exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E) (H := E)).symm.continuous.continuousAt.comp
        hpair
    have htgt_nhds : Bundle.TotalSpace.proj ⁻¹' c.target ∈
        nhds (TotalSpace.mk' E (c (Φ 0 x)) (P 0) : TangentBundle 𝓘(ℝ, E) E) :=
      (hctgt_open.preimage (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E)))).mem_nhds
        hc0_tgt
    have htm_at : ContinuousAt (tangentMapWithin 𝓘(ℝ, E) I c.symm c.target)
        (TotalSpace.mk' E (c (Φ 0 x)) (P 0)) := htm.continuousAt htgt_nhds
    exact ContinuousAt.comp'
      (g := tangentMapWithin 𝓘(ℝ, E) I c.symm c.target)
      (f := fun s : ℝ => (TotalSpace.mk' E (c (Φ s x)) (P s) : TangentBundle 𝓘(ℝ, E) E))
      htm_at hpath
  exact (hRHScont.congr hrecon.symm).continuousWithinAt


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem flow_chartBasis_section_contMDiffWithinAt_of_jointSmooth
    (Φ : ℝ → M → M) {lo hi : ℝ}
    (hΦsm : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2)
      (Set.Ioo lo hi ×ˢ (Set.univ : Set M)))
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) (m : ℕ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo lo hi) (b₀ : M)
    (hb₀ : b₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) (m : ℕ)
      (fun p : ℝ × M =>
        (TotalSpace.mk' E (Φ p.1 p.2)
          (mfderiv I I (fun y : M => Φ p.1 y) p.2
            (Integral.Measure.chartBasisVecFiber (I := I) x₀ i p.2))
          : TangentBundle I M))
      (Set.Ioo lo hi ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) (t₀, b₀) := by
  classical
  set S : Set (ℝ × M) := Set.Ioo lo hi ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet
    with hS
  have hS_sub : S ⊆ Set.Ioo lo hi ×ˢ (Set.univ : Set M) := by
    rw [hS]; exact Set.prod_mono_right (Set.subset_univ _)
  have ht₀b₀ : (t₀, b₀) ∈ S := ⟨ht₀, hb₀⟩
  have hm1top : (((m : ℕ) + 1 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr (le_top : (((m : ℕ) + 1 : ℕ) : ℕ∞) ≤ ⊤)
  have hmtop : ((m : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr (le_top : ((m : ℕ) : ℕ∞) ≤ ⊤)
  set f : (ℝ × M) → M → M := fun q y => Φ q.1 y with hf_def
  have hf_uncurry_eq : Function.uncurry f
      = (fun r : (ℝ × M) × M => Φ r.1.1 r.2) := rfl
  have hf : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod I) I ((m : ℕ) + 1 : ℕ)
      (Function.uncurry f) (S ×ˢ (Set.univ : Set M)) ((t₀, b₀), b₀) := by
    rw [hf_uncurry_eq]
    have hjointN : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ((m : ℕ) + 1 : ℕ)
        (fun q : ℝ × M => Φ q.1 q.2) (Set.Ioo lo hi ×ˢ Set.univ) :=
      hΦsm.of_le hm1top
    have hpre : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod I) (𝓘(ℝ, ℝ).prod I) ((m : ℕ) + 1 : ℕ)
        (fun r : (ℝ × M) × M => ((r.1.1, r.2) : ℝ × M)) (S ×ˢ (Set.univ : Set M)) ((t₀, b₀), b₀) :=
      (contMDiffWithinAt_fst.fst).prodMk contMDiffWithinAt_snd
    have hmaps : Set.MapsTo (fun r : (ℝ × M) × M => ((r.1.1, r.2) : ℝ × M))
        (S ×ˢ (Set.univ : Set M)) (Set.Ioo lo hi ×ˢ (Set.univ : Set M)) := by
      rintro ⟨⟨t, b⟩, y⟩ ⟨hq, -⟩
      exact ⟨(hS_sub hq).1, Set.mem_univ _⟩
    have hmem' : ((fun r : (ℝ × M) × M => ((r.1.1, r.2) : ℝ × M)) ((t₀, b₀), b₀))
        ∈ Set.Ioo lo hi ×ˢ (Set.univ : Set M) := ⟨ht₀, Set.mem_univ _⟩
    exact (hjointN _ hmem').comp ((t₀, b₀), b₀) hpre hmaps
  have hg : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I (m : ℕ)
      (fun q : ℝ × M => q.2) S (t₀, b₀) := contMDiffWithinAt_snd
  have hu : Set.MapsTo (fun q : ℝ × M => q.2) S (Set.univ : Set M) := fun _ _ => Set.mem_univ _
  have hϕ := ContMDiffWithinAt.mfderivWithin
    (I := I) (I' := I) (n := ((m : ℕ) + 1 : ℕ)) (m := (m : ℕ))
    (f := f) (g := fun q : ℝ × M => q.2) (t := S) (u := (Set.univ : Set M))
    (x₀ := (t₀, b₀))
    hf hg ht₀b₀ hu le_rfl uniqueMDiffOn_univ
  have hv : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) (m : ℕ)
      (fun q : ℝ × M => (Integral.Measure.chartBasisVec (I := I) x₀ i q.2 : TangentBundle I M))
      S (t₀, b₀) := by
    have hcb : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (m : ℕ)
        (Integral.Measure.chartBasisVec (I := I) x₀ i)
        (trivializationAt E (TangentSpace I) x₀).baseSet b₀ :=
      (Integral.Measure.chartBasisVec_contMDiffOn (I := I) x₀ i b₀ hb₀).of_le hmtop
    have hsnd : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I (m : ℕ)
        (fun q : ℝ × M => q.2) S (t₀, b₀) := contMDiffWithinAt_snd
    have hmaps2 : Set.MapsTo (fun q : ℝ × M => q.2) S
        (trivializationAt E (TangentSpace I) x₀).baseSet := fun q hq => hq.2
    exact hcb.comp (t₀, b₀) hsnd hmaps2
  have hb₂ : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I (m : ℕ)
      (fun q : ℝ × M => Φ q.1 q.2) S (t₀, b₀) :=
    ((hΦsm.of_le hmtop) _ (hS_sub ht₀b₀)).mono hS_sub
  have hkey := ContMDiffWithinAt.clm_apply_of_inCoordinates
    (IB₁ := I) (IB₂ := I) (F₁ := E) (F₂ := E)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (b₁ := fun q : ℝ × M => q.2) (b₂ := fun q : ℝ × M => Φ q.1 q.2)
    (ϕ := fun q : ℝ × M => mfderiv I I (fun y : M => Φ q.1 y) q.2)
    (v := fun q : ℝ × M => Integral.Measure.chartBasisVecFiber (I := I) x₀ i q.2)
    (m₀ := (t₀, b₀)) (s := S) (n := (m : ℕ))
    ?_ hv hb₂
  · convert hkey using 2
  · have hrw : (fun q : ℝ × M =>
          ContinuousLinearMap.inCoordinates E (TangentSpace I (M := M)) E (TangentSpace I (M := M))
          ((fun q : ℝ × M => q.2) (t₀, b₀)) ((fun q : ℝ × M => q.2) q)
          ((fun q : ℝ × M => Φ q.1 q.2) (t₀, b₀))
          ((fun q : ℝ × M => Φ q.1 q.2) q)
          ((fun q : ℝ × M => mfderiv I I (fun y : M => Φ q.1 y) q.2) q))
        = (fun q : ℝ × M => inTangentCoordinates I I (fun q : ℝ × M => q.2)
            (fun x => f x ((fun q : ℝ × M => q.2) x))
            (fun x => mfderivWithin I I (f x) (Set.univ) ((fun q : ℝ × M => q.2) x))
            (t₀, b₀) q) := by
      funext q
      rw [inTangentCoordinates, mfderivWithin_univ]
    rw [hrw]
    exact hϕ

omit [NeZero (Module.finrank ℝ E)] in
theorem forward_flow_existence_smooth_neighborhood_of_jointsmooth_field
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hsmooth0 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ)) :
    ∃ Φ : ℝ → M → M, (∀ x : M, Φ 0 x = x) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x)
        (Set.Ici (0 : ℝ)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φ t x)))) ∧
      (∀ x : M, ContinuousWithinAt (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) 0) ∧
      (∀ (x : M) (v : TangentSpace I x),
        ContinuousWithinAt (fun s : ℝ => (TotalSpace.mk' E (Φ s x)
          (mfderiv I I (fun y : M => Φ s y) x v) : TangentBundle I M)) (Set.Ici (0 : ℝ)) 0) ∧
      (ContinuousOn (fun p : ℝ × M => Φ p.1 p.2) (Set.Ico 0 T ×ˢ Set.univ)) ∧
      (∀ (x₀ : M) (i : Fin (Module.finrank ℝ E)),
        ContinuousOn (fun p : ℝ × M =>
          (TotalSpace.mk' E (Φ p.1 p.2)
            (mfderiv I I (fun y : M => Φ p.1 y) p.2
              (Integral.Measure.chartBasisVecFiber (I := I) x₀ i p.2)) : TangentBundle I M))
          (Set.Ico 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∃ lo hi : ℝ, lo < 0 ∧ T < hi ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2)
          (Set.Ioo lo hi ×ˢ Set.univ)) := by
  obtain ⟨Xext, hXsm, hXeq⟩ := seeley_time_extend X_DT T hT hsmooth0
  obtain ⟨Φ, Ψ, lo, hi, hlo, hhi, hΦ0, hΦsm, hΦvel, hΨsm, hΨΦ, hΦΨ⟩ :=
    global_flow_full_interval_with_reverse_on_closed_manifold Xext hXsm T hT

  have hsub : Set.Ioo (0 : ℝ) T ⊆ Set.Ioo lo hi := fun t ht =>
    ⟨lt_trans hlo ht.1, lt_trans ht.2 hhi⟩
  have hIcoSub : Set.Ico (0 : ℝ) T ⊆ Set.Ioo lo hi := fun t ht =>
    ⟨lt_of_lt_of_le hlo ht.1, lt_trans ht.2 hhi⟩

  have hvel_eq : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φ t x))) := by
    intro t ht x
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hat : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Xext t (Φ t x))) := hΦvel t (hsub ht) x
    have hrw : Xext t (Φ t x) = X_DT t (Φ t x) := hXeq t htIcc (Φ t x)
    rw [hrw] at hat
    exact hat.hasMFDerivWithinAt

  have hΦ_slice : ∀ t ∈ Set.Ioo lo hi, ContMDiff I I ∞ (Φ t) := by
    intro t ht x
    have hmem : ((t, x) : ℝ × M) ∈ Set.Ioo lo hi ×ˢ (Set.univ : Set M) :=
      ⟨ht, Set.mem_univ _⟩
    have hxsm : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2)
        (Set.Ioo lo hi ×ˢ (Set.univ : Set M)) (t, x) := hΦsm _ hmem
    have hpair : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞ (fun y : M => ((t, y) : ℝ × M)) x :=
      contMDiffAt_const.prodMk contMDiffAt_id
    have hmaps : Set.MapsTo (fun y : M => ((t, y) : ℝ × M)) (Set.univ : Set M)
        (Set.Ioo lo hi ×ˢ (Set.univ : Set M)) := fun y _ => ⟨ht, Set.mem_univ _⟩
    have hcomp := hxsm.comp x hpair.contMDiffWithinAt hmaps
    simpa using hcomp.contMDiffAt Filter.univ_mem
  refine ⟨Φ, hΦ0, ?_, hvel_eq, ?_, ?_, ?_, ?_, ⟨lo, hi, hlo, hhi, hΦsm⟩⟩
  · intro t ht
    have ht0 : 0 < t := ht.1
    have htHi : t < hi := lt_trans ht.2 hhi
    have htIco : t ∈ Set.Ico (0 : ℝ) hi := ⟨ht0.le, htHi⟩
    obtain ⟨d, hd_fwd, _hd_rev⟩ :=
      time_dependent_vf_diffeomorph_slice_of_smooth_bijective (Φ t) (Ψ t)
        (hΦ_slice t (hsub ht)) (hΨsm t ht0 htHi)
        (fun x => hΨΦ t htIco x) (fun x => hΦΨ t htIco x)
    exact ⟨d, hd_fwd⟩
  · intro x
    have hmem : ((0 : ℝ), x) ∈ Set.Ioo lo hi ×ˢ (Set.univ : Set M) :=
      ⟨⟨hlo, lt_trans hT hhi⟩, Set.mem_univ _⟩
    have hopen : IsOpen (Set.Ioo lo hi ×ˢ (Set.univ : Set M)) := isOpen_Ioo.prod isOpen_univ
    have hjoint : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) (0, x) :=
      (hΦsm _ hmem).contMDiffAt (hopen.mem_nhds hmem)
    have hpair : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun s : ℝ => (s, x)) 0 := contMDiffAt_id.prodMk contMDiffAt_const
    have horbit : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun s : ℝ => Φ s x) 0 :=
      hjoint.comp 0 hpair
    exact horbit.continuousAt.continuousWithinAt
  · intro x v
    exact flow_mfderiv_continuousWithinAt_zero_of_jointSmooth Φ hlo (lt_trans hT hhi) hΦsm x v
  · have hcontOn : ContinuousOn (fun q : ℝ × M => Φ q.1 q.2)
        (Set.Ioo lo hi ×ˢ (Set.univ : Set M)) := hΦsm.continuousOn
    exact hcontOn.mono (Set.prod_mono hIcoSub (subset_refl _))
  · intro x₀ i
    have hsecOn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) (0 : ℕ)
        (fun p : ℝ × M =>
          (TotalSpace.mk' E (Φ p.1 p.2)
            (mfderiv I I (fun y : M => Φ p.1 y) p.2
              (Integral.Measure.chartBasisVecFiber (I := I) x₀ i p.2)) : TangentBundle I M))
        (Set.Ioo lo hi ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      intro p hp
      exact flow_chartBasis_section_contMDiffWithinAt_of_jointSmooth Φ hΦsm x₀ i 0 p.1 hp.1 p.2 hp.2
    have hcontOn := hsecOn.continuousOn
    exact hcontOn.mono (Set.prod_mono hIcoSub (subset_refl _))

omit [NeZero (Module.finrank ℝ E)] in
theorem forward_flow_existence_onesided_of_jointsmooth_field
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hsmooth0 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ)) :
    ∃ Φ : ℝ → M → M, (∀ x : M, Φ 0 x = x) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x)
        (Set.Ici (0 : ℝ)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φ t x)))) ∧
      (∀ x : M, ContinuousWithinAt (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) 0) ∧
      (∀ (x : M) (v : TangentSpace I x),
        ContinuousWithinAt (fun s : ℝ => (TotalSpace.mk' E (Φ s x)
          (mfderiv I I (fun y : M => Φ s y) x v) : TangentBundle I M)) (Set.Ici (0 : ℝ)) 0) ∧
      (ContinuousOn (fun p : ℝ × M => Φ p.1 p.2) (Set.Ico 0 T ×ˢ Set.univ)) ∧
      (∀ (x₀ : M) (i : Fin (Module.finrank ℝ E)),
        ContinuousOn (fun p : ℝ × M =>
          (TotalSpace.mk' E (Φ p.1 p.2)
            (mfderiv I I (fun y : M => Φ p.1 y) p.2
              (Integral.Measure.chartBasisVecFiber (I := I) x₀ i p.2)) : TangentBundle I M))
          (Set.Ico 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) := by
  obtain ⟨Φ, hΦ0, hdiffeo, hode, hcont0, hbundle0, horbit, hsection, -⟩ :=
    forward_flow_existence_smooth_neighborhood_of_jointsmooth_field (I := I) X_DT T hT hsmooth0
  exact ⟨Φ, hΦ0, hdiffeo, hode, hcont0, hbundle0, horbit, hsection⟩

end DifferentialGeometry.PDE.RicciFlow
