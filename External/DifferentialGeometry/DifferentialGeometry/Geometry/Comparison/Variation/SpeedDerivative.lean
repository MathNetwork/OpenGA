import DifferentialGeometry.Geometry.Connection.ParallelTransport.ParallelTransport
import DifferentialGeometry.Geometry.Comparison.Variation.FixedChartIdentities
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Topology.Compactness.Compact
import DifferentialGeometry.Geometry.Comparison.Variation.ArcLength



noncomputable section

open Set Function Filter Manifold Bundle MeasureTheory intervalIntegral
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem speedSq_hasDerivAt
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (t : ℝ)
    (hf : IsSmoothVariation (I := I) f) :
    HasDerivAt (fun s : ℝ => speedSq (I := I) g f s t)
      (2 * g.inner (f 0 t)
        (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
          (I := I) g (fun s : ℝ => f s t)
          (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))) 0 := by
  classical
  open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
  set α : M := f 0 t with hα
  set γ : ℝ → M := fun s : ℝ => f s t with hγ
  set Vsec : ∀ s : ℝ, TangentSpace I (γ s) :=
    fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ) with hVsec
  set V : ℝ → E :=
    fun s : ℝ => fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ) with hV
  have hF2 : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t) := by
    have hext : ContMDiffAt I 𝓘(ℝ, E) (8 : ℕ) (extChartAt I α) (f 0 t) :=
      (contMDiffAt_extChartAt (I := I) (x := α)).of_le (by exact_mod_cast le_top)
    have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (8 : ℕ)
        (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t) :=
      hext.comp (0, t) hf.contMDiffAt
    have key : ContDiffAt ℝ (8 : ℕ)
        (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t) := by
      rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
        ← chartedSpaceSelf_prod]
      exact hcomp
    exact key.of_le (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 8))
  have hγ_smooth : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) γ := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun s : ℝ => (s, t)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hslice : ∀ s : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun u : ℝ => f s u) := by
    intro s
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun u : ℝ => (s, u)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  set S : Set ℝ := γ ⁻¹' (chartAt H α).source with hS
  have hS_open : IsOpen S := by
    have hsrc_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
    exact (hγ_smooth.continuous.isOpen_preimage _ hsrc_open)
  have h0S : (0 : ℝ) ∈ S := by
    change γ 0 ∈ (chartAt H α).source
    change f 0 t ∈ (chartAt H α).source
    rw [hα]; exact mem_chart_source H (f 0 t)
  have hS_nhds : S ∈ nhds (0 : ℝ) := hS_open.mem_nhds h0S
  have hVeq_chartRep : ∀ s ∈ S, V s =
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
        (I := I) γ Vsec 0 s := by
    intro s hs
    have hsrc : (fun u : ℝ => f s u) t ∈ (chartAt H α).source := hs
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun u : ℝ => f s u) ((hslice s).mdifferentiableAt (by norm_num)) α hsrc
    change V s =
      (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ s)
        (Vsec s)
    rw [hV]
    have hγ0 : γ 0 = α := by rw [hγ, hα]
    rw [hγ0]
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f s u))
        = (fun v : ℝ => extChartAt I α (f s v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge.symm
  have hV_hasDerivAt : HasDerivAt V
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)))
        (0, t) (1, 0) (0, 1)) 0 := by
    rw [hV]
    exact Aux2.hasDerivAt_partial_snd (fun u v => extChartAt I α (f u v)) 0 t hF2
  have hchartCurve_eq : AlongCurve.chartCurve (I := I) α γ
      = fun s : ℝ => extChartAt I α (f s t) := by
    funext s; rw [AlongCurve.chartCurve_def, hγ]
  have hF1diff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t) :=
    (hF2.of_le one_le_two).differentiableAt one_ne_zero
  have hu_hasDerivAt : HasDerivAt (AlongCurve.chartCurve (I := I) α γ)
      (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t) (1, 0)) 0 := by
    rw [hchartCurve_eq]
    exact Aux2.hasDerivAt_slice_fst (fun u v => extChartAt I α (f u v)) 0 t hF1diff
  have hmem : AlongCurve.chartCurve (I := I) α γ 0 ∈
      interior (extChartAt I α).target := by
    have hxsrc : γ 0 ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      change f 0 t ∈ (chartAt H α).source
      rw [hα]; exact mem_chart_source H (f 0 t)
    have hxtarget : AlongCurve.chartCurve (I := I) α γ 0 ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hxsrc
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α hxtarget
  have hbase := AlongCurve.chartGramAlongCurve_hasDerivAt_covariant
    (I := I) g α γ V V
    (uPrime := fun _ =>
      fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t) (1, 0))
    (Vprime := fun _ =>
      fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)))
        (0, t) (1, 0) (0, 1))
    (Wprime := fun _ =>
      fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)))
        (0, t) (1, 0) (0, 1))
    hu_hasDerivAt hmem hV_hasDerivAt hV_hasDerivAt
  have hspeed_eq : (fun s : ℝ => speedSq (I := I) g f s t)
      =ᶠ[nhds (0 : ℝ)] (fun s : ℝ => AlongCurve.chartGramAlongCurve (I := I) g α γ V V s) := by
    filter_upwards [hS_nhds] with s hs
    have hsrc : f s t ∈ (chartAt H α).source := hs
    have hbase_set : f s t ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hsrc
    have hxsrc : f s t ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hsrc
    have hsq : speedSq (I := I) g f s t = g.inner (f s t) (Vsec s) (Vsec s) := rfl
    rw [hsq]
    rw [DifferentialGeometry.Integral.Connection.g_inner_eq_chart_sum
      (I := I) g α hbase_set hxsrc (Vsec s) (Vsec s)]
    have hVcoord :
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (f s t) (Vsec s)
          = V s := by
      have := hVeq_chartRep s hs
      rw [this]
      change _ = (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ s) (Vsec s)
      have hγ0 : γ 0 = α := by rw [hγ, hα]
      have hγs : γ s = f s t := rfl
      rw [hγ0, hγs]
    rw [AlongCurve.chartGramAlongCurve_def]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    have hchart : extChartAt I α (f s t) = AlongCurve.chartCurve (I := I) α γ s := by
      rw [AlongCurve.chartCurve_def, hγ]
    rw [hchart]
    rw [show (chartModelBasis E).repr
            ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (f s t)
              (Vsec s)) i
          = chartCoord (E := E) i (V s) from by rw [hVcoord]; rfl,
       show (chartModelBasis E).repr
            ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (f s t)
              (Vsec s)) j
          = chartCoord (E := E) j (V s) from by rw [hVcoord]; rfl]
    ring
  have hderiv := hbase.congr_of_eventuallyEq hspeed_eq
  convert hderiv using 1
  set u0 : E := AlongCurve.chartCurve (I := I) α γ 0 with hu0
  set DV : E :=
    fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)))
        (0, t) (1, 0) (0, 1)
      + chartChristoffelContraction (I := I) g α
          (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t) (1, 0))
          (V 0) u0 with hDV
  have hγ0 : γ 0 = α := by rw [hγ, hα]
  have hbase_set0 : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hDV_eq :
      DV = chartCovDerivAlong (I := I) g α γ
        (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
          (I := I) γ Vsec 0) 0 := by
    rw [chartCovDerivAlong_def, hDV]
    have hVder0 : V 0 =
        DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
          (I := I) γ Vsec 0 0 := hVeq_chartRep 0 h0S
    have huPrime0 : deriv (AlongCurve.chartCurve (I := I) α γ) 0
          = fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t) (1, 0) :=
      hu_hasDerivAt.deriv
    have hrepDeriv : deriv
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
            (I := I) γ Vsec 0) 0
        = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)))
            (0, t) (1, 0) (0, 1) := by
      have hrep_hasDeriv :
          HasDerivAt
            (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
              (I := I) γ Vsec 0)
            (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)))
              (0, t) (1, 0) (0, 1)) 0 := by
        refine hV_hasDerivAt.congr_of_eventuallyEq ?_
        filter_upwards [hS_nhds] with s hs
        exact (hVeq_chartRep s hs).symm
      exact hrep_hasDeriv.deriv
    rw [hrepDeriv, huPrime0, hVder0]
  have hDV_intrinsic :
      DV = (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (I := I) g γ Vsec 0) := by
    rw [hDV_eq]
    have hcc := DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong_chartCoord
      (I := I) g γ Vsec 0
    rw [hγ0] at hcc
    exact hcc.symm
  have hVsec0_coord :
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α (Vsec 0) = V 0 := by
    have hcoord := hVeq_chartRep 0 h0S
    rw [hcoord]
    change _ = (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0) (Vsec 0)
    rw [hγ0]
  have hu0_eq : u0 = extChartAt I α α := by
    rw [hu0, AlongCurve.chartCurve_def, hγ, hα]
  have hGram_eq : ∀ l j : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α l j u0 = chartGramMatrix (I := I) g α α l j := by
    intro l j
    rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_def, hu0_eq, (extChartAt I α).left_inv (mem_extChartAt_source α)]
  have hinner_sum :
      g.inner α
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (I := I) g γ Vsec 0)
          (Vsec 0)
        = ∑ l : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α l j u0 * chartCoord (E := E) l DV
              * chartCoord (E := E) j (V 0) := by
    have hrt1 : (trivializationAt E (TangentSpace I) α).symmL ℝ α DV
        = DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (I := I) g γ Vsec 0 := by
      rw [hDV_intrinsic]
      exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
        (R := ℝ) hbase_set0 _
    have hrt2 : (trivializationAt E (TangentSpace I) α).symmL ℝ α (V 0) = Vsec 0 := by
      rw [← hVsec0_coord]
      exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
        (R := ℝ) hbase_set0 _
    rw [← hrt1, ← hrt2,
      AlongCurve.inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α DV (V 0)]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hGram_eq l j]
  rw [hinner_sum]
  have hT2 :
      (∑ i : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α i l u0 * chartCoord (E := E) i (V 0)
            * chartCoord (E := E) l DV)
        = ∑ l : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α l j u0 * chartCoord (E := E) l DV
              * chartCoord (E := E) j (V 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun i _ => ?_))
    rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_symm (I := I) g α i l u0]
    ring
  change (2 : ℝ) * (∑ l, ∑ j, DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α l j u0
        * chartCoord (E := E) l DV * chartCoord (E := E) j (V 0))
      = (∑ l, ∑ j, DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α l j u0
          * chartCoord (E := E) l DV * chartCoord (E := E) j (V 0))
        + (∑ i, ∑ l, DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α i l u0
            * chartCoord (E := E) i (V 0) * chartCoord (E := E) l DV)
  rw [hT2]; ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma speedSq_contDiff
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) :
    ContDiff ℝ (7 : ℕ) (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) := by
  have hvel := velocity_totalSpace_contMDiff (I := I) (M := M) f hf
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hinner := ContMDiff.inner_bundle (F := E) (B := M)
    (E := (TangentSpace I : M → Type _))
    (b := fun p : ℝ × ℝ => f p.1 p.2)
    (v := fun p : ℝ × ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f p.1 u) p.2 (1 : ℝ))
    (w := fun p : ℝ × ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f p.1 u) p.2 (1 : ℝ))
    hvel hvel
  have hcm : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (7 : ℕ)
      (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) := by
    refine hinner.congr ?_; intro p; rfl
  rw [← contMDiff_iff_contDiff, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hcm

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem speedIntegral_hasDerivAt
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (_hf : IsSmoothVariation (I := I) f) (_hL : 0 < L)
    (_hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L, speedSq (I := I) g f 0 t = 1) :
    HasDerivAt
      (fun s : ℝ => ∫ t in (0 : ℝ)..L, Real.sqrt (speedSq (I := I) g f s t))
      (∫ t in (0 : ℝ)..L,
        (2 * g.inner (f 0 t)
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)))
          / (2 * Real.sqrt (speedSq (I := I) g f 0 t)))
      0 := by
  classical
  set Φ : ℝ → ℝ → ℝ := fun s t => speedSq (I := I) g f s t with hΦdef
  set G : ℝ × ℝ → ℝ := fun p : ℝ × ℝ => Φ p.1 p.2 with hG
  set D : ℝ → ℝ := fun t : ℝ =>
    2 * g.inner (f 0 t)
      (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
        (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
      (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)) with hDdef
  have hΦ : ContDiff ℝ (7 : ℕ) G := by
    rw [hG, hΦdef]; exact speedSq_contDiff (I := I) (M := M) g f _hf
  have hΦcont : Continuous G := hΦ.continuous
  have hD : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Φ s t) (D t) 0 := by
    intro t
    have := speedSq_hasDerivAt (I := I) g f t _hf
    simpa only [hΦdef, hDdef] using this
  have hΦdiff : ∀ p : ℝ × ℝ, DifferentiableAt ℝ G p :=
    fun p => (hΦ.differentiable (by simp)).differentiableAt
  have hslice_deriv : ∀ s t : ℝ,
      HasDerivAt (fun u : ℝ => Φ u t) (fderiv ℝ G (s, t) (1, 0)) s := by
    intro s t
    have := Aux2.hasDerivAt_slice_fst (fun u v => Φ u v) s t (hΦdiff (s, t))
    simpa only [hG] using this
  have hD_eq : ∀ t : ℝ, D t = fderiv ℝ G (0, t) (1, 0) := by
    intro t
    exact (hD t).unique (hslice_deriv 0 t)
  have hpartial_cont : Continuous (fun p : ℝ × ℝ => fderiv ℝ G p (1, 0)) := by
    have hc : Continuous (fun p : ℝ × ℝ => fderiv ℝ G p) :=
      hΦ.continuous_fderiv (by simp)
    exact hc.clm_apply continuous_const
  have hDcont : Continuous D := by
    have : Continuous (fun t : ℝ => fderiv ℝ G (0, t) (1, 0)) :=
      hpartial_cont.comp (continuous_const.prodMk continuous_id)
    exact this.congr (fun t => (hD_eq t).symm)
  have hpos : ∃ δ > (0 : ℝ), ∃ c0 > (0 : ℝ), ∀ s ∈ Set.Ioo (-δ) δ,
      ∀ t ∈ Set.Icc (0 : ℝ) L, c0 ≤ Real.sqrt (Φ s t) := by
    obtain ⟨δ, hδ, c, hc, hbnd⟩ :=
      speed_positivity_on_regular_variation (I := I) (M := M) g f L _hf _hUnit
    exact ⟨δ, hδ, c, hc, fun s hs t ht => hbnd s hs t ht⟩
  obtain ⟨δ, hδ, c0, hc0, hposΦ⟩ := hpos
  set δ' : ℝ := δ / 2 with hδ'
  have hδ'pos : 0 < δ' := by positivity
  have hδ'lt : δ' < δ := by simp only [hδ']; linarith
  set Kset : Set (ℝ × ℝ) := Set.Icc (-δ') δ' ×ˢ Set.Icc 0 L with hKset
  have hKcompact : IsCompact Kset := (isCompact_Icc).prod isCompact_Icc
  have hKne : Kset.Nonempty :=
    ⟨(0, 0), ⟨⟨by linarith, le_of_lt hδ'pos⟩, ⟨le_refl 0, le_of_lt _hL⟩⟩⟩
  obtain ⟨pm, hpmKset, hpmMax⟩ := hKcompact.exists_isMaxOn hKne
    ((continuous_norm.comp hpartial_cont).continuousOn)
  set K1 : ℝ := ‖fderiv ℝ G pm (1, 0)‖ with hK1
  have hK1nonneg : 0 ≤ K1 := norm_nonneg _
  have hsqrtlb : ∀ s ∈ Set.Icc (-δ') δ', ∀ t ∈ Set.Icc (0 : ℝ) L,
      c0 ≤ Real.sqrt (Φ s t) := by
    intro s hs t ht
    refine hposΦ s ?_ t ht
    rcases hs with ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  have hΦne : ∀ s ∈ Set.Icc (-δ') δ', ∀ t ∈ Set.Icc (0 : ℝ) L, Φ s t ≠ 0 := by
    intro s hs t ht hcontra
    have hsqrt0 : Real.sqrt (Φ s t) = 0 := by rw [hcontra, Real.sqrt_zero]
    have := hsqrtlb s hs t ht
    rw [hsqrt0] at this; linarith
  set C0 : ℝ := K1 / (2 * c0) with hC0
  have hC0nonneg : 0 ≤ C0 := by positivity
  have hlip : ∀ t ∈ Set.Icc (0 : ℝ) L,
      LipschitzOnWith C0.toNNReal (fun s => Real.sqrt (Φ s t))
        (Set.Icc (-δ') δ') := by
    intro t ht
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le (𝕜 := ℝ) _ _ (convex_Icc _ _)
    · intro s hs
      exact ((hslice_deriv s t).sqrt (hΦne s hs t ht)).differentiableAt
    · intro s hs
      have hderiv_eq : deriv (fun u : ℝ => Real.sqrt (Φ u t)) s
          = fderiv ℝ G (s, t) (1, 0) / (2 * Real.sqrt (Φ s t)) :=
        ((hslice_deriv s t).sqrt (hΦne s hs t ht)).deriv
      have hnum_le : ‖fderiv ℝ G (s, t) (1, 0)‖ ≤ K1 :=
        hpmMax (⟨hs, ht⟩ : (s, t) ∈ Kset)
      have hden_ge : 2 * c0 ≤ 2 * Real.sqrt (Φ s t) := by
        have := hsqrtlb s hs t ht; linarith
      have hden_pos : (0 : ℝ) < 2 * Real.sqrt (Φ s t) := by
        have := hsqrtlb s hs t ht; linarith
      have hnorm_le : ‖deriv (fun u : ℝ => Real.sqrt (Φ u t)) s‖ ≤ C0 := by
        rw [hderiv_eq, norm_div, Real.norm_eq_abs (2 * Real.sqrt (Φ s t)),
          abs_of_nonneg (le_of_lt hden_pos), hC0,
          div_le_div_iff₀ hden_pos (by linarith : (0 : ℝ) < 2 * c0)]
        calc ‖fderiv ℝ G (s, t) (1, 0)‖ * (2 * c0)
              ≤ K1 * (2 * c0) :=
                mul_le_mul_of_nonneg_right hnum_le (by positivity)
          _ ≤ K1 * (2 * Real.sqrt (Φ s t)) :=
                mul_le_mul_of_nonneg_left hden_ge hK1nonneg
      have h1 : ‖deriv (fun u : ℝ => Real.sqrt (Φ u t)) s‖₊
          = Real.toNNReal ‖deriv (fun u : ℝ => Real.sqrt (Φ u t)) s‖ := by
        rw [Real.toNNReal_of_nonneg (norm_nonneg _)]; rfl
      rw [h1]; exact Real.toNNReal_le_toNNReal hnorm_le
  set Ffun : ℝ → ℝ → ℝ := fun s t => Real.sqrt (Φ s t) with hFfun
  set Ffun' : ℝ → ℝ := fun t => D t / (2 * Real.sqrt (Φ 0 t)) with hFfun'
  have hFcont : ∀ s : ℝ, Continuous (Ffun s) := fun s =>
    Real.continuous_sqrt.comp (hΦcont.comp (continuous_const.prodMk continuous_id))
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume) (a := (0 : ℝ)) (b := L) (F := Ffun) (F' := Ffun') (x₀ := (0 : ℝ))
    (bound := fun _ => C0) (s := Set.Ioo (-δ') δ')
    (Ioo_mem_nhds (by linarith) hδ'pos)
    (Filter.Eventually.of_forall (fun x => (hFcont x).aestronglyMeasurable))
    ((hFcont 0).intervalIntegrable 0 L)
    (by
      have hden_cont : Continuous (fun t : ℝ => 2 * Real.sqrt (Φ 0 t)) :=
        continuous_const.mul (Real.continuous_sqrt.comp
          (hΦcont.comp (continuous_const.prodMk continuous_id)))
      have hcoon : ContinuousOn Ffun' (Set.Ioc (0 : ℝ) L) := by
        apply ContinuousOn.div hDcont.continuousOn hden_cont.continuousOn
        intro t ht
        have htIcc : t ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt ht.1, ht.2⟩
        have h0 : (0 : ℝ) ∈ Set.Icc (-δ') δ' := ⟨by linarith, le_of_lt hδ'pos⟩
        have hsqrt_pos : (0 : ℝ) < Real.sqrt (Φ 0 t) := by
          have := hsqrtlb 0 h0 t htIcc; linarith
        exact ne_of_gt (by linarith)
      rw [Set.uIoc_of_le (le_of_lt _hL)]
      exact hcoon.aestronglyMeasurable measurableSet_Ioc)
    (by
      apply Filter.Eventually.of_forall
      intro t ht
      rw [Set.uIoc_of_le (le_of_lt _hL)] at ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt ht.1, ht.2⟩
      have hnn : Real.nnabs C0 = C0.toNNReal := by
        ext; simp [Real.coe_nnabs, Real.coe_toNNReal _ hC0nonneg,
          abs_of_nonneg hC0nonneg]
      rw [hnn]
      exact (hlip t htIcc).mono Set.Ioo_subset_Icc_self)
    (_root_.intervalIntegrable_const)
    (by
      apply Filter.Eventually.of_forall
      intro t ht
      rw [Set.uIoc_of_le (le_of_lt _hL)] at ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt ht.1, ht.2⟩
      have h0 : (0 : ℝ) ∈ Set.Icc (-δ') δ' := ⟨by linarith, le_of_lt hδ'pos⟩
      exact (hD t).sqrt (hΦne 0 h0 t htIcc))
  exact key.2

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
