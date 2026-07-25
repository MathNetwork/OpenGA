import DifferentialGeometry.Geometry.Topology.UniversalCover.Riemannian
import DifferentialGeometry.Geometry.Topology.UniversalCover.ChartPullback
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling
import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import Mathlib.Topology.Covering
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Finite.Defs











open Set Function Filter Bundle
open scoped Topology ContDiff
open DifferentialGeometry.Integral.Measure (SmoothRiemannianMetric chartModelBasis)
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem (chartRiemannTensor)
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M] [PseudoEMetricSpace M] [SecondCountableTopology M]










omit [PseudoEMetricSpace M] [SecondCountableTopology M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem hasMFDerivAt_proj
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    HasMFDerivAt I I
      (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
      x' (ContinuousLinearMap.id ℝ E) := by
  refine ⟨(proj_contMDiff (I := I) (M := M)).continuous.continuousAt, ?_⟩
  have hEq :
      writtenInExtChartAt I I x'
          (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
        =ᶠ[𝓝[range I] (extChartAt I x' x')] (id : E → E) := by
    have hmem : (extChartAt I x').target ∈ 𝓝[range I] (extChartAt I x' x') :=
      extChartAt_target_mem_nhdsWithin x'
    refine Filter.eventuallyEq_of_mem hmem ?_
    intro y hy
    show extChartAt I (proj (X := M) x')
        (proj (X := M) ((extChartAt I x').symm y)) = y
    have hproj :=
      (extChartAt_proj_eq (I := I) (M := M) x' ((extChartAt I x').symm y)).symm
    rw [hproj]
    exact (extChartAt I x').right_inv hy
  have hId : HasFDerivWithinAt (id : E → E) (ContinuousLinearMap.id ℝ E)
      (range I) (extChartAt I x' x') :=
    (hasFDerivAt_id _).hasFDerivWithinAt
  have hx0 :
      writtenInExtChartAt I I x'
          (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
          (extChartAt I x' x') = (id : E → E) (extChartAt I x' x') := by
    show extChartAt I (proj (X := M) x')
        (proj (X := M) ((extChartAt I x').symm (extChartAt I x' x'))) =
        extChartAt I x' x'
    have hproj :=
      (extChartAt_proj_eq (I := I) (M := M) x'
        ((extChartAt I x').symm (extChartAt I x' x'))).symm
    rw [hproj]
    rw [extChartAt_to_inv]
  exact hId.congr_of_eventuallyEq hEq hx0


section ProjLipschitz

open Manifold MeasureTheory

variable [Nonempty M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in










omit [Nonempty M] in
omit [PseudoEMetricSpace M] [SecondCountableTopology M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem proj_pathELength_eq
    (g : SmoothRiemannianMetric I M)
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [RiemannianBundle
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x)]
    (hEnormBase : ∀ (x : M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hEnormCover : ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (v : TangentSpace I x'),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((liftedMetric (I := I) g).inner x' v v)))
    {γ : ℝ → DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc (0 : ℝ) 1)) :
    pathELength I (proj ∘ γ) 0 1 = pathELength I γ 0 1 := by
  rw [pathELength_eq_lintegral_mfderivWithin_Icc, pathELength_eq_lintegral_mfderivWithin_Icc]
  rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun t ht ↦ ?_)
  have hproj_mfderiv : mfderiv I I (proj (X := M)) (γ t) = ContinuousLinearMap.id ℝ E :=
    (hasMFDerivAt_proj (I := I) (M := M) (γ t)).mfderiv
  have huniq : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Set.Icc (0 : ℝ) 1) t := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact uniqueDiffOn_Icc zero_lt_one t ⟨ht.1.le, ht.2.le⟩
  have hγdiff : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) 1) t :=
    hγ.mdifferentiableOn one_ne_zero t ⟨ht.1.le, ht.2.le⟩
  have hcomp :
      mfderivWithin 𝓘(ℝ, ℝ) I (proj (X := M) ∘ γ) (Set.Icc (0 : ℝ) 1) t =
        (mfderiv I I (proj (X := M)) (γ t)).comp
          (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) 1) t) :=
    mfderiv_comp_mfderivWithin t
      ((proj_contMDiff (I := I) (M := M)).mdifferentiable (by norm_num) (γ t)) hγdiff huniq
  rw [hEnormBase ((proj (X := M) ∘ γ) t)
        (mfderivWithin 𝓘(ℝ, ℝ) I (proj (X := M) ∘ γ) (Set.Icc (0 : ℝ) 1) t 1),
      hEnormCover (γ t) (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) 1) t 1)]
  have hval :
      mfderivWithin 𝓘(ℝ, ℝ) I (proj (X := M) ∘ γ) (Set.Icc (0 : ℝ) 1) t 1 =
        mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) 1) t 1 := by
    rw [hcomp, hproj_mfderiv]; rfl
  rw [hval]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



















omit [Nonempty M] in
omit [SecondCountableTopology M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem proj_lipschitzWith_one [RegularSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)]
    (g : SmoothRiemannianMetric I M)
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hEnormBase : ∀ (x : M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hEnormCover :
        letI : RiemannianBundle
            (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
              TangentSpace I x) :=
          ⟨(liftedMetric (I := I) g).toRiemannianMetric⟩
        ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (v : TangentSpace I x'),
          ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((liftedMetric (I := I) g).inner x' v v))) :
    letI : PseudoEMetricSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
      uc_pseudoEMetricSpace (I := I) (M := M) (liftedMetric (I := I) g)
    LipschitzWith 1
      (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) := by
  letI hRB : RiemannianBundle
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x) :=
    ⟨(liftedMetric (I := I) g).toRiemannianMetric⟩
  letI hUCem : PseudoEMetricSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    uc_pseudoEMetricSpace (I := I) (M := M) (liftedMetric (I := I) g)
  haveI hUCRiem :
      IsRiemannianManifold I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    ⟨fun _ _ ↦ rfl⟩
  rw [LipschitzWith]
  intro x' y'
  rw [ENNReal.coe_one, one_mul]
  rw [IsRiemannianManifold.out (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) x' y',
      IsRiemannianManifold.out (I := I) (M := M) (proj (X := M) x') (proj (X := M) y')]
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  obtain ⟨γ, hγ0, hγ1, hγ_smooth, hγlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt (I := I)
      (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) hr
  have hbound :
      riemannianEDist I (proj (X := M) x') (proj (X := M) y') ≤
        pathELength I (proj (X := M) ∘ γ) 0 1 := by
    apply Manifold.riemannianEDist_le_pathELength (I := I) (M := M)
      (((proj_contMDiff (I := I) (M := M)).of_le (by norm_num)).comp_contMDiffOn hγ_smooth)
    · simp [Function.comp_apply, hγ0]
    · simp [Function.comp_apply, hγ1]
    · exact zero_le_one
  have hlen_eq : pathELength I (proj (X := M) ∘ γ) 0 1 = pathELength I γ 0 1 :=
    proj_pathELength_eq (I := I) (M := M) g hEnormBase hEnormCover hγ_smooth
  calc riemannianEDist I (proj (X := M) x') (proj (X := M) y')
      ≤ pathELength I (proj (X := M) ∘ γ) 0 1 := hbound
    _ = pathELength I γ 0 1 := hlen_eq
    _ ≤ r := hγlen.le

end ProjLipschitz

open Manifold MeasureTheory in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in













omit [NeZero (Module.finrank ℝ E)] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
theorem tail_in_single_sheet [Nonempty M] [CompleteSpace M]
    [RegularSpace (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)]
    (g : SmoothRiemannianMetric I M)
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hEnormBase : ∀ (x : M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hEnormCover :
        letI : RiemannianBundle
            (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
              TangentSpace I x) :=
          ⟨(liftedMetric (I := I) g).toRiemannianMetric⟩
        ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (v : TangentSpace I x'),
          ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((liftedMetric (I := I) g).inner x' v v)))
    {x' : ℕ →
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M}
    (hCauchy :
      letI : PseudoEMetricSpace
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
        uc_pseudoEMetricSpace (I := I) (M := M) (liftedMetric (I := I) g)
      CauchySeq x')
    {y : M}
    (hlim : Filter.Tendsto (fun n => proj (x' n)) Filter.atTop (𝓝 y)) :
    ∃ (y' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
      (e : OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) M),
      proj (X := M) y' = y ∧ y' ∈ e.source ∧
        (∀ z ∈ e.source, proj (X := M) z = e z) ∧
        (∀ᶠ n in Filter.atTop, x' n ∈ e.source) := by
  classical
  letI hRB : RiemannianBundle
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x) :=
    ⟨(liftedMetric (I := I) g).toRiemannianMetric⟩
  letI hUCem : PseudoEMetricSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    uc_pseudoEMetricSpace (I := I) (M := M) (liftedMetric (I := I) g)
  haveI hUCRiem :
      IsRiemannianManifold I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    ⟨fun _ _ ↦ rfl⟩
  have hbundle_inner : ∀ (x : M) (v w : TangentSpace I x),
      (inner ℝ v w : ℝ) = g.inner x v w := by
    intro x v w
    have hpos0 : ∀ z : TangentSpace I x, 0 ≤ g.inner x z z := by
      intro z
      rcases eq_or_ne z 0 with rfl | hz
      · simp
      · exact (g.pos x z hz).le
    have hdiag : ∀ z : TangentSpace I x, (inner ℝ z z : ℝ) = g.inner x z z := by
      intro z
      have h1 : ‖z‖ = Real.sqrt (g.inner x z z) := by
        have hz := hEnormBase x z
        have hnn : 0 ≤ Real.sqrt (g.inner x z z) := Real.sqrt_nonneg _
        rw [← ofReal_norm_eq_enorm] at hz
        exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg z) hnn).mp hz
      rw [real_inner_self_eq_norm_sq, h1, Real.sq_sqrt (hpos0 z)]
    have hsymm_g : g.inner x v w = g.inner x w v := g.symm x v w
    have hpolar : (inner ℝ v w : ℝ) =
        ((inner ℝ (v + w) (v + w) : ℝ) - inner ℝ v v - inner ℝ w w) / 2 := by
      rw [real_inner_add_add_self]; ring
    have hpolar_g : g.inner x v w =
        (g.inner x (v + w) (v + w) - g.inner x v v - g.inner x w w) / 2 := by
      have e1 : g.inner x (v + w) (v + w) =
          g.inner x v v + g.inner x v w + g.inner x w v + g.inner x w w := by
        simp [map_add, ContinuousLinearMap.add_apply]; ring
      rw [e1, hsymm_g]; ring
    rw [hpolar, hpolar_g, hdiag (v + w), hdiag v, hdiag w]
  haveI hCRB : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun x v w => hbundle_inner x v w⟩
  haveI hRegM : RegularSpace M := by
    haveI : LocallyCompactSpace M :=
      Manifold.locallyCompact_of_finiteDimensional (M := M) I
    infer_instance
  set p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M :=
    proj (X := M) with hp_def
  haveI : Nonempty (p ⁻¹' {y}) := by
    haveI hpc : PathConnectedSpace M :=
      (pathConnectedSpace_iff_connectedSpace).mpr inferInstance
    obtain ⟨γ0⟩ := PathConnectedSpace.joined (default : M) y
    exact ⟨⟨⟨y, Path.Homotopic.Quotient.mk γ0⟩, rfl⟩⟩
  have hEC :
      IsEvenlyCovered p y (p ⁻¹' {y}) :=
    (UniversalCover.proj_isCoveringMap (X := M)) y
  set t : Trivialization (p ⁻¹' {y}) p := hEC.toTrivialization with ht_def
  have hyU : y ∈ t.baseSet := hEC.mem_toTrivialization_baseSet
  set U : Set M := t.baseSet with hU_def
  have hUopen : IsOpen U := t.open_baseSet
  have hUnhds : U ∈ 𝓝 y := hUopen.mem_nhds hyU
  obtain ⟨c, hc_pos, hc_sub⟩ :=
    setOf_riemannianEDist_lt_subset_nhds' (I := I) (M := M) hUnhds
  set ε : ENNReal := c / 2 with hε_def
  have hε_pos : 0 < ε := ENNReal.half_pos (by exact_mod_cast hc_pos.ne')
  have htwoε : ε + ε ≤ c := by
    rw [hε_def, ENNReal.add_halves]
  have hproj_eps : ∀ᶠ n in Filter.atTop,
      Manifold.riemannianEDist I y (p (x' n)) < ε := by
    have hball : {z : M | Manifold.riemannianEDist I y z < ε} ∈ 𝓝 y := by
      have := eventually_riemannianEDist_lt (I := I) (M := M) y hε_pos
      exact this
    exact hlim.eventually hball
  have hsheet :
      ∀ z₁ z₂ :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M,
        Manifold.riemannianEDist I y (p z₁) < ε →
        edist z₁ z₂ < ε →
        (t z₁).2 = (t z₂).2 := by
    intro z₁ z₂ hz₁ball hz₁z₂
    have hedist : Manifold.riemannianEDist I z₁ z₂ < ε := by
      rw [← IsRiemannianManifold.out (I := I)
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) z₁ z₂]
      exact hz₁z₂
    obtain ⟨γ, hγ0, hγ1, hγ_smooth, hγlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) hedist
    have hin_source : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ t.source := by
      intro s hs
      have hproj_smooth_full :
          ContMDiffOn 𝓘(ℝ, ℝ) I 1 (p ∘ γ) (Set.Icc (0 : ℝ) 1) :=
        ((proj_contMDiff (I := I) (M := M)).of_le (by norm_num)).comp_contMDiffOn hγ_smooth
      have hproj_smooth_s :
          ContMDiffOn 𝓘(ℝ, ℝ) I 1 (p ∘ γ) (Set.Icc (0 : ℝ) s) :=
        hproj_smooth_full.mono (Set.Icc_subset_Icc le_rfl hs.2)
      have hbnd1 :
          Manifold.riemannianEDist I (p z₁) (p (γ s)) ≤
            pathELength I (p ∘ γ) 0 s := by
        apply Manifold.riemannianEDist_le_pathELength (I := I) (M := M) hproj_smooth_s
        · simp [Function.comp_apply, hγ0]
        · simp [Function.comp_apply]
        · exact hs.1
      have hlen_le :
          pathELength I (p ∘ γ) 0 s ≤ pathELength I (p ∘ γ) 0 1 :=
        pathELength_mono le_rfl hs.2
      have hlen_eq :
          pathELength I (p ∘ γ) 0 1 = pathELength I γ 0 1 :=
        proj_pathELength_eq (I := I) (M := M) g hEnormBase hEnormCover hγ_smooth
      have hbnd2 :
          Manifold.riemannianEDist I (p z₁) (p (γ s)) < ε := by
        calc Manifold.riemannianEDist I (p z₁) (p (γ s))
            ≤ pathELength I (p ∘ γ) 0 s := hbnd1
          _ ≤ pathELength I (p ∘ γ) 0 1 := hlen_le
          _ = pathELength I γ 0 1 := hlen_eq
          _ < ε := hγlen
      have hcomb : Manifold.riemannianEDist I y (p (γ s)) < c := by
        calc Manifold.riemannianEDist I y (p (γ s))
            ≤ Manifold.riemannianEDist I y (p z₁) +
                Manifold.riemannianEDist I (p z₁) (p (γ s)) :=
              Manifold.riemannianEDist_triangle
          _ < ε + ε := ENNReal.add_lt_add hz₁ball hbnd2
          _ ≤ c := htwoε
      have hmemU : p (γ s) ∈ U := hc_sub hcomb
      rw [t.mem_source]; exact hmemU
    have hfib_const :
        (t (γ 0)).2 = (t (γ 1)).2 := by
      have hcont_g2 : ContinuousOn (fun s : ℝ => (t (γ s)).2) (Set.Icc (0:ℝ) 1) := by
        have hγcont : ContinuousOn γ (Set.Icc (0:ℝ) 1) :=
          hγ_smooth.continuousOn
        have hmaps : Set.MapsTo γ (Set.Icc (0:ℝ) 1) t.source := hin_source
        have htcont : ContinuousOn (fun z => t z) t.source :=
          t.continuousOn_toFun
        exact (continuous_snd.comp_continuousOn (htcont.comp hγcont hmaps))
      have hpre : IsPreconnected (Set.Icc (0:ℝ) 1) := isPreconnected_Icc
      haveI : DiscreteTopology (p ⁻¹' {y}) := hEC.discreteTopology_fiber
      have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
      have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
      exact hpre.constant hcont_g2 h0 h1
    rw [hγ0, hγ1] at hfib_const
    exact hfib_const
  rw [EMetric.cauchySeq_iff] at hCauchy
  obtain ⟨N₁, hN₁⟩ := hCauchy ε hε_pos
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hproj_eps
  set N := max N₁ N₂ with hN_def
  set pt : p ⁻¹' {y} := (t (x' N)).2 with hpt_def
  have htail_fib : ∀ n, N ≤ n → (t (x' n)).2 = pt := by
    intro n hn
    have hnN₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
    have hNN₁ : N₁ ≤ N := le_max_left _ _
    have hNN₂ : N₂ ≤ N := le_max_right _ _
    have hballN : Manifold.riemannianEDist I y (p (x' N)) < ε := hN₂ N hNN₂
    have hdistNn : edist (x' N) (x' n) < ε := hN₁ N hNN₁ n hnN₁
    exact (hsheet (x' N) (x' n) hballN hdistNn).symm
  set slice : OpenPartialHomeomorph (M × (p ⁻¹' {y})) M :=
    { toFun := Prod.fst
      invFun := fun b => (b, pt)
      source := U ×ˢ ({pt} : Set (p ⁻¹' {y}))
      target := U
      map_source' := fun q hq => hq.1
      map_target' := fun b hb => ⟨hb, rfl⟩
      left_inv' := fun q hq => by
        obtain ⟨hq1, hq2⟩ := hq
        simp only [Set.mem_singleton_iff] at hq2
        exact Prod.ext rfl hq2.symm
      right_inv' := fun b _ => rfl
      open_source := hUopen.prod (by
        haveI : DiscreteTopology (p ⁻¹' {y}) := hEC.discreteTopology_fiber
        exact isOpen_discrete ({pt} : Set (p ⁻¹' {y})))
      open_target := hUopen
      continuousOn_toFun := continuousOn_fst
      continuousOn_invFun := by fun_prop } with hslice_def
  set e : OpenPartialHomeomorph
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) M :=
    t.toOpenPartialHomeomorph.trans slice with he_def
  refine ⟨t.toOpenPartialHomeomorph.symm (y, pt), e, ?_, ?_, ?_, ?_⟩
  · exact t.proj_symm_apply' hyU
  · have hmemsrc : t.toOpenPartialHomeomorph.symm (y, pt) ∈ t.source :=
      t.map_target (t.mem_target.2 hyU)
    rw [he_def, OpenPartialHomeomorph.trans_source]
    refine ⟨hmemsrc, ?_⟩
    have happ : t (t.toOpenPartialHomeomorph.symm (y, pt)) = (y, pt) :=
      t.apply_symm_apply (t.mem_target.2 hyU)
    show t (t.toOpenPartialHomeomorph.symm (y, pt)) ∈ slice.source
    rw [happ]
    exact ⟨hyU, Set.mem_singleton _⟩
  · intro z hz
    rw [he_def, OpenPartialHomeomorph.trans_source] at hz
    obtain ⟨hz_src, hz_slice⟩ := hz
    have hez : e z = (t z).1 := rfl
    rw [hez]
    exact (t.coe_fst hz_src).symm
  · filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hnN₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
    have hballn : Manifold.riemannianEDist I y (p (x' n)) < ε := hN₂ n hnN₂
    have hcn : Manifold.riemannianEDist I y (p (x' n)) < c :=
      lt_of_lt_of_le hballn (by rw [hε_def]; exact ENNReal.half_le_self)
    have hmemU : p (x' n) ∈ U := hc_sub hcn
    have hx_src : x' n ∈ t.source := t.mem_source.2 hmemU
    rw [he_def, OpenPartialHomeomorph.trans_source]
    refine ⟨hx_src, ?_⟩
    show t (x' n) ∈ slice.source
    have hfst : (t (x' n)).1 = p (x' n) := t.coe_fst hx_src
    have hsnd : (t (x' n)).2 = pt := htail_fib n hn
    rw [hslice_def]
    refine ⟨?_, ?_⟩
    · show (t (x' n)).1 ∈ U
      rw [hfst]; exact hmemU
    · show (t (x' n)).2 ∈ ({pt} : Set (p ⁻¹' {y}))
      rw [hsnd]; exact Set.mem_singleton _







omit [T2Space M] [SigmaCompactSpace M] [PseudoEMetricSpace M] [SecondCountableTopology M] in
theorem sheet_homeomorph [Nonempty M] (y : M) :
    ∃ (U : Set M) (_hU : IsOpen U) (_hyU : y ∈ U)
      (y' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
      (U' : Set (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))
      (_hU' : IsOpen U') (_hy'U : y' ∈ U') (_hproj : proj (X := M) y' = y),
      ∃ _h : (U' ≃ₜ U), True := by
  haveI hpc : PathConnectedSpace M :=
    (pathConnectedSpace_iff_connectedSpace).mpr inferInstance
  obtain ⟨γ⟩ := PathConnectedSpace.joined (default : M) y
  set y' :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M :=
    ⟨y, Path.Homotopic.Quotient.mk γ⟩ with hy'_def
  have hLH :
      IsLocalHomeomorph
        (proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
    UniversalCover.proj_isCoveringMap.isLocalHomeomorph
  obtain ⟨e, hy'e, hfe⟩ := hLH y'
  have hproj_y' : proj (X := M) y' = y := rfl
  have hy_eq : (e : _ → M) y' = y := by
    have h1 := congrFun hfe y'
    exact h1.symm.trans hproj_y'
  have hyU : y ∈ e.target := hy_eq ▸ e.map_source hy'e
  refine ⟨e.target, e.open_target, hyU, y', e.source, e.open_source, hy'e,
    hproj_y', e.toHomeomorphSourceTarget, trivial⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in













omit [NeZero (Module.finrank ℝ E)] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
theorem lift_the_limit [Nonempty M] [CompleteSpace M]
    [RegularSpace (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)]
    (g : SmoothRiemannianMetric I M)
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hEnormBase : ∀ (x : M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hEnormCover :
        letI : RiemannianBundle
            (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
              TangentSpace I x) :=
          ⟨(liftedMetric (I := I) g).toRiemannianMetric⟩
        ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (v : TangentSpace I x'),
          ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((liftedMetric (I := I) g).inner x' v v)))
    {x' : ℕ →
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M}
    (hCauchy :
      letI : PseudoEMetricSpace
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
        uc_pseudoEMetricSpace (I := I) (M := M) (liftedMetric (I := I) g)
      CauchySeq x')
    {y : M}
    (hlim : Filter.Tendsto (fun n => proj (x' n)) Filter.atTop (𝓝 y)) :
    ∃ y' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M,
      proj (X := M) y' = y ∧
        Filter.Tendsto x' Filter.atTop (𝓝 y') := by
  classical
  obtain ⟨y', e, hproj_y', hy'e, hproj_eq_e, htail⟩ :=
    tail_in_single_sheet (I := I) (M := M) g hEnormBase hEnormCover hCauchy hlim
  refine ⟨y', hproj_y', ?_⟩
  have hey' : (e : _ → M) y' = y := (hproj_eq_e y' hy'e).symm.trans hproj_y'
  have hytarget : y ∈ e.target := hey' ▸ e.map_source hy'e
  have hy'_symm : e.symm y = y' := by
    rw [← hey']; exact e.left_inv hy'e
  have htail_eq : ∀ᶠ n in Filter.atTop, e.symm (proj (X := M) (x' n)) = x' n := by
    filter_upwards [htail] with n hn
    rw [hproj_eq_e (x' n) hn]
    exact e.left_inv hn
  have hcont : ContinuousAt (e.symm) y :=
    e.continuousAt_symm hytarget
  have hcomp : Filter.Tendsto (fun n => e.symm (proj (X := M) (x' n))) Filter.atTop
      (𝓝 (e.symm y)) :=
    (hcont.tendsto).comp hlim
  rw [hy'_symm] at hcomp
  exact hcomp.congr' htail_eq

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in









omit [NeZero (Module.finrank ℝ E)] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
theorem completeSpace_of_complete [Nonempty M] [CompleteSpace M]
    [RegularSpace (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)]
    (g : SmoothRiemannianMetric I M)
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hEnormBase : ∀ (x : M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hEnormCover :
        letI : RiemannianBundle
            (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
              TangentSpace I x) :=
          ⟨(liftedMetric (I := I) g).toRiemannianMetric⟩
        ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (v : TangentSpace I x'),
          ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((liftedMetric (I := I) g).inner x' v v))) :
    letI : PseudoEMetricSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
      uc_pseudoEMetricSpace (I := I) (M := M) (liftedMetric (I := I) g)
    CompleteSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) := by
  letI hUCem : PseudoEMetricSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    uc_pseudoEMetricSpace (I := I) (M := M) (liftedMetric (I := I) g)
  have hLip :
      LipschitzWith 1
        (proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
    proj_lipschitzWith_one (I := I) (M := M) g hEnormBase hEnormCover
  have hUC :
      UniformContinuous
        (proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
    hLip.uniformContinuous
  refine UniformSpace.complete_of_cauchySeq_tendsto (fun u hu => ?_)
  have huM : CauchySeq (fun n => proj (X := M) (u n)) :=
    hUC.comp_cauchySeq hu
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete huM
  haveI hRegM : RegularSpace M := by
    haveI : LocallyCompactSpace M :=
      Manifold.locallyCompact_of_finiteDimensional (M := M) I
    infer_instance
  have hbundle_inner : ∀ (x : M) (v w : TangentSpace I x),
      (inner ℝ v w : ℝ) = g.inner x v w := by
    intro x v w
    have hpos0 : ∀ z : TangentSpace I x, 0 ≤ g.inner x z z := by
      intro z
      rcases eq_or_ne z 0 with rfl | hz
      · simp
      · exact (g.pos x z hz).le
    have hdiag : ∀ z : TangentSpace I x, (inner ℝ z z : ℝ) = g.inner x z z := by
      intro z
      have h1 : ‖z‖ = Real.sqrt (g.inner x z z) := by
        have hz := hEnormBase x z
        have hnn : 0 ≤ Real.sqrt (g.inner x z z) := Real.sqrt_nonneg _
        rw [← ofReal_norm_eq_enorm] at hz
        exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg z) hnn).mp hz
      rw [real_inner_self_eq_norm_sq, h1, Real.sq_sqrt (hpos0 z)]
    have hsymm_g : g.inner x v w = g.inner x w v := g.symm x v w
    have hpolar : (inner ℝ v w : ℝ) =
        ((inner ℝ (v + w) (v + w) : ℝ) - inner ℝ v v - inner ℝ w w) / 2 := by
      rw [real_inner_add_add_self]; ring
    have hpolar_g : g.inner x v w =
        (g.inner x (v + w) (v + w) - g.inner x v v - g.inner x w w) / 2 := by
      have e1 : g.inner x (v + w) (v + w) =
          g.inner x v v + g.inner x v w + g.inner x w v + g.inner x w w := by
        simp [map_add, ContinuousLinearMap.add_apply]; ring
      rw [e1, hsymm_g]; ring
    rw [hpolar, hpolar_g, hdiag (v + w), hdiag v, hdiag w]
  haveI hCRB : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun x v w => hbundle_inner x v w⟩
  have hy_eps := EMetric.tendsto_nhds.mp hy
  have hyM : Filter.Tendsto (fun n => proj (X := M) (u n)) Filter.atTop (𝓝 y) := by
    rw [Filter.tendsto_iff_forall_eventually_mem]
    intro s hs
    obtain ⟨c, hc_pos, hc_sub⟩ :=
      setOf_riemannianEDist_lt_subset_nhds' (I := I) (M := M) hs
    have hev := hy_eps c hc_pos
    filter_upwards [hev] with n hn
    have hrd : Manifold.riemannianEDist I y (proj (X := M) (u n)) < c := by
      rw [← IsRiemannianManifold.out (I := I) (M := M) y (proj (X := M) (u n)),
          edist_comm]
      exact hn
    exact hc_sub hrd
  obtain ⟨y', _hproj, htend⟩ :=
    lift_the_limit (I := I) (M := M) g hEnormBase hEnormCover hu hyM
  exact ⟨y', htend⟩

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
