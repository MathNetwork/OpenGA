import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.GeodesicEquationFromIntegralCurve
import DifferentialGeometry.Geometry.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Geodesic.ProjDerivative
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.ChartTransition
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Mul



noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [NeZero (Module.finrank ℝ E)] in
omit [Module.Finite ℝ E] in
private lemma tangentCoordChange_eq_chartTransitionAt [I.Boundaryless]
    (x y : M) (z : M) :
    tangentCoordChange I x y z =
      chartTransitionAt (I := I) x y (extChartAt I x z) := by
  rw [tangentCoordChange_def, chartTransitionAt_def, chartTransitionMap_def]
  have h : (Set.range I : Set E) = Set.univ :=
    ModelWithCorners.Boundaryless.range_eq_univ (I := I)
  rw [h, fderivWithin_univ]

private def applyJac (α : M) (p : TangentBundle I M) (z : E × E) : E :=
  chartTransitionAt (I := I) p.proj α z.1 z.2

omit [NeZero (Module.finrank ℝ E)] in
omit [Module.Finite ℝ E] in
private lemma secondaryTrivSndForm_eventuallyEq_applyJac [I.Boundaryless]
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    secondaryTrivFiberComponentMap (I := I) α p =ᶠ[𝓝 ((extChartAt I.tangent p) p)]
      applyJac (I := I) α p := by
  classical
  have hbp1 : ((extChartAt I.tangent p) p).1 = extChartAt I p.proj p.proj :=
    extChartAt_tangent_apply_fst (I := I) (q := p) (p := p) (mem_chart_source H p.proj)
  set U : Set (E × E) :=
    {z : E × E | z.1 ∈ (extChartAt I p.proj).target ∧
      (extChartAt I p.proj).symm z.1 ∈ (chartAt H α).source} with hU_def
  have hUopen : IsOpen U := by
    have h1 : IsOpen ((extChartAt I p.proj).target) :=
      isOpen_extChartAt_target (I := I) p.proj
    have hcont : ContinuousOn (extChartAt I p.proj).symm (extChartAt I p.proj).target :=
      continuousOn_extChartAt_symm (I := I) p.proj
    have hset : U = (Prod.fst ⁻¹' (extChartAt I p.proj).target) ∩
        (Prod.fst ⁻¹' ((extChartAt I p.proj).target ∩
          (extChartAt I p.proj).symm ⁻¹' (chartAt H α).source)) := by
      ext z
      simp only [hU_def, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h1, h2⟩
      · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
    rw [hset]
    refine (h1.preimage continuous_fst).inter ((IsOpen.preimage continuous_fst) ?_)
    exact hcont.isOpen_inter_preimage h1 (chartAt H α).open_source
  have hbp_memU : ((extChartAt I.tangent p) p) ∈ U := by
    rw [hU_def, Set.mem_setOf_eq, hbp1]
    refine ⟨(extChartAt I p.proj).map_source (mem_extChartAt_source (I := I) p.proj), ?_⟩
    rw [(extChartAt I p.proj).left_inv (mem_extChartAt_source (I := I) p.proj)]
    exact hp
  refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hbp_memU) ?_
  intro z hz
  obtain ⟨hz_tgt, hz_src⟩ := hz
  unfold secondaryTrivFiberComponentMap applyJac
  rw [tangentCoordChange_eq_chartTransitionAt (I := I) p.proj α ((extChartAt I p.proj).symm z.1)]
  congr 2
  exact (extChartAt I p.proj).right_inv hz_tgt

omit [NeZero (Module.finrank ℝ E)] in
omit [Module.Finite ℝ E] in
private lemma differentiableAt_chartTransitionAt [I.Boundaryless]
    (α β : M) {x : E} (hx : x ∈ chartTransitionSource (I := I) α β) :
    DifferentiableAt ℝ (fun z => chartTransitionAt (I := I) α β z) x := by
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  have hsmooth : ContDiffOn ℝ ∞ (fun z => (chartTransitionAt (I := I) α β z : E →L[ℝ] E))
      (chartTransitionSource (I := I) α β) :=
    chartTransitionAt_smooth (I := I) α β
  exact (hsmooth.contDiffAt (h_open.mem_nhds hx)).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
omit [Module.Finite ℝ E] in
private lemma fderiv_applyJac_apply [I.Boundaryless]
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source)
    (w : E × E) :
    fderiv ℝ (applyJac (I := I) α p) ((extChartAt I.tangent p) p) w =
      chartTransitionAt (I := I) p.proj α ((extChartAt I.tangent p) p).1 w.2 +
        (fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z)
          ((extChartAt I.tangent p) p).1 w.1) (((extChartAt I.tangent p) p).2) := by
  classical
  set bp := (extChartAt I.tangent p) p with hbp
  have hbp1 : bp.1 = extChartAt I p.proj p.proj := by
    rw [hbp]
    exact extChartAt_tangent_apply_fst (I := I) (q := p) (p := p) (mem_chart_source H p.proj)
  have hx_src : bp.1 ∈ chartTransitionSource (I := I) p.proj α := by
    rw [hbp1]
    exact extChartAt_mem_chartTransitionSource (I := I) p.proj α
      (mem_chart_source H p.proj) hp
  set c : E × E → (E →L[ℝ] E) := fun z => chartTransitionAt (I := I) p.proj α z.1 with hc
  set u : E × E → E := fun z => z.2 with hu
  have hcA : DifferentiableAt ℝ (fun z => chartTransitionAt (I := I) p.proj α z) bp.1 :=
    differentiableAt_chartTransitionAt (I := I) p.proj α hx_src
  have hc_diff : DifferentiableAt ℝ c bp :=
    hcA.comp bp (differentiableAt_fst)
  have hu_diff : DifferentiableAt ℝ u bp := differentiableAt_snd
  have hfd : fderiv ℝ (fun z => (c z) (u z)) bp =
      (c bp).comp (fderiv ℝ u bp) + (fderiv ℝ c bp).flip (u bp) :=
    fderiv_clm_apply hc_diff hu_diff
  have happly_eq : applyJac (I := I) α p = fun z => (c z) (u z) := by
    funext z; rfl
  rw [happly_eq, hfd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  have hu_fderiv : fderiv ℝ u bp = ContinuousLinearMap.snd ℝ E E := fderiv_snd
  rw [hu_fderiv]
  have hc_fderiv : fderiv ℝ c bp w =
      (fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z) bp.1) (w.1) := by
    have hceq : c = (fun x => chartTransitionAt (I := I) p.proj α x) ∘ Prod.fst := by
      funext z; rfl
    rw [hceq]
    rw [fderiv_comp bp hcA differentiableAt_fst]
    simp only [ContinuousLinearMap.comp_apply, fderiv_fst, ContinuousLinearMap.coe_fst']
  rw [hc_fderiv]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartCoord_fderiv_chartTransitionAt [I.Boundaryless]
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source)
    (c : Fin (Module.finrank ℝ E)) (v : E) :
    chartCoord (E := E) c
        ((fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z)
          (extChartAt I p.proj p.proj) v) v) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i
          (fun z => chartTransitionJacEntry (I := I) p.proj α z c j)
          (extChartAt I p.proj p.proj) *
          chartCoord (E := E) i v * chartCoord (E := E) j v := by
  classical
  set x₀ := extChartAt I p.proj p.proj with hx₀
  set A : E → (E →L[ℝ] E) := fun z => chartTransitionAt (I := I) p.proj α z with hA
  have hx_src : x₀ ∈ chartTransitionSource (I := I) p.proj α :=
    extChartAt_mem_chartTransitionSource (I := I) p.proj α (mem_chart_source H p.proj) hp
  have hcA : DifferentiableAt ℝ A x₀ :=
    differentiableAt_chartTransitionAt (I := I) p.proj α hx_src
  set coordCLM : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((chartModelBasis E).coord c) with hcoordCLM
  set eval : (E →L[ℝ] E) →L[ℝ] ℝ :=
    coordCLM.comp (ContinuousLinearMap.apply ℝ E v) with heval
  have hstep1 :
      chartCoord (E := E) c ((fderiv ℝ A x₀ v) v) = eval (fderiv ℝ A x₀ v) := by
    rw [heval, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      hcoordCLM]
    simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    rfl
  have hstep2 : eval (fderiv ℝ A x₀ v) = fderiv ℝ (fun z => eval (A z)) x₀ v := by
    have hcomp_hasD : HasFDerivAt (fun z => eval (A z))
        (eval.comp (fderiv ℝ A x₀)) x₀ :=
      eval.hasFDerivAt.comp x₀ hcA.hasFDerivAt
    rw [hcomp_hasD.fderiv]
    rfl
  have heval_eq : (fun z => eval (A z)) =
      (fun z => ∑ i : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) p.proj α z c i * chartCoord (E := E) i v) := by
    funext z
    rw [heval, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, hA,
      hcoordCLM]
    simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    change chartCoord (E := E) c (chartTransitionAt (I := I) p.proj α z v) = _
    exact chartCoord_chartTransitionAt (I := I) p.proj α z v c
  rw [hstep1, hstep2, heval_eq]
  have hsum_fderiv :
      fderiv ℝ (fun z => ∑ i : Fin (Module.finrank ℝ E),
          chartTransitionJacEntry (I := I) p.proj α z c i * chartCoord (E := E) i v) x₀ v =
        ∑ i : Fin (Module.finrank ℝ E),
          fderiv ℝ (fun z => chartTransitionJacEntry (I := I) p.proj α z c i *
            chartCoord (E := E) i v) x₀ v := by
    have hdiff : ∀ i : Fin (Module.finrank ℝ E),
        DifferentiableAt ℝ (fun z => chartTransitionJacEntry (I := I) p.proj α z c i *
          chartCoord (E := E) i v) x₀ := by
      intro i
      exact (chartTransitionJacEntry_differentiableAt (I := I) p.proj α c i hx_src).mul_const _
    rw [fderiv_fun_sum (fun i _ => hdiff i)]
    rw [ContinuousLinearMap.sum_apply]
  rw [hsum_fderiv]
  have hLHS_expand :
      (∑ i : Fin (Module.finrank ℝ E),
          fderiv ℝ (fun z => chartTransitionJacEntry (I := I) p.proj α z c i *
            chartCoord (E := E) i v) x₀ v) =
        ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) k
            (fun z => chartTransitionJacEntry (I := I) p.proj α z c i) x₀ *
            chartCoord (E := E) k v * chartCoord (E := E) i v := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [fderiv_mul_const (chartTransitionJacEntry_differentiableAt (I := I) p.proj α c i hx_src) _]
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_chartTransitionJacEntry_eq_sum_partialDeriv (I := I) p.proj α c i x₀ v]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [hLHS_expand]
  rw [Finset.sum_comm]

theorem geodesicVectorFieldChart_eq_geodesicVectorField
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    geodesicVectorFieldChart (I := I) g α p = geodesicVectorField (I := I) g p := by
  classical
  set x₀ := extChartAt I p.proj p.proj with hx₀
  set bp := (extChartAt I.tangent p) p with hbp
  have hbp1 : bp.1 = x₀ := by
    rw [hbp, hx₀]
    exact extChartAt_tangent_apply_fst (I := I) (q := p) (p := p) (mem_chart_source H p.proj)
  have hbp2 : bp.2 = (p.snd : E) := by
    rw [hbp]
    rw [extChartAt_tangent_apply_snd_tangentCoordChange (I := I) (q := p) (p := p)
      (mem_chart_source H p.proj)]
    exact tangentCoordChange_self (I := I) (x := p.proj) (z := p.proj) (v := p.snd)
      (mem_extChartAt_source (I := I) p.proj)
  have hfst : (geodesicVectorFieldChart (I := I) g α p : E × E).1 =
      (geodesicVectorField (I := I) g p : E × E).1 := by
    rw [geodesicVectorFieldChart_fst (I := I) g α hp]
    rfl
  have hsnd : (geodesicVectorFieldChart (I := I) g α p : E × E).2 =
      (geodesicVectorField (I := I) g p : E × E).2 := by
    set X := (geodesicVectorFieldChart (I := I) g α p : E × E).2 with hX
    have hgvf1 : (geodesicVectorFieldChart (I := I) g α p : E × E).1 = (p.snd : E) :=
      geodesicVectorFieldChart_fst (I := I) g α hp
    have hp_dom : p ∈ geodesicChartDomain (I := I) α := hp
    have htriv := trivializationAt_apply_geodesicVectorFieldChart
      (I := I) g α (p := p) hp_dom
    set e := trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M) with he_def
    have hp_base : p ∈ e.baseSet := by
      rw [he_def, ← geodesicChartDomain_eq_trivBaseSet (I := I) α]; exact hp_dom
    have hcoe := e.coe_linearMapAt_of_mem (R := ℝ) hp_base
    have hlin_at_gvf :
        (e.continuousLinearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p) =
          geodesicVectorFieldChartFiber (I := I) g α p := by
      have h2 := congrArg Prod.snd htriv
      change (e.linearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p) = _
      have hh := congrFun hcoe (geodesicVectorFieldChart (I := I) g α p)
      rw [hh]; exact h2
    have hsnd_clm :
        ((e.continuousLinearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p)).2 =
          (fderivWithin ℝ (secondaryTrivFiberComponentMap (I := I) α p) (range I.tangent) bp)
            (geodesicVectorFieldChart (I := I) g α p) :=
      snd_continuousLinearMapAt_secondaryTriv (I := I) (α := α) (p := p) hp
        (geodesicVectorFieldChart (I := I) g α p)
    have hkey0 : (geodesicVectorFieldChartFiber (I := I) g α p).2 =
        (fderivWithin ℝ (secondaryTrivFiberComponentMap (I := I) α p) (range I.tangent) bp)
          (geodesicVectorFieldChart (I := I) g α p) := by
      rw [← hsnd_clm, hlin_at_gvf]
    have hrangeT : (range (I.tangent) : Set (E × E)) = Set.univ :=
      ModelWithCorners.Boundaryless.range_eq_univ (I := I.tangent)
    have hfderiv_eq :
        fderivWithin ℝ (secondaryTrivFiberComponentMap (I := I) α p) (range I.tangent) bp =
          fderiv ℝ (applyJac (I := I) α p) bp := by
      rw [hrangeT, fderivWithin_univ]
      exact Filter.EventuallyEq.fderiv_eq
        (secondaryTrivSndForm_eventuallyEq_applyJac (I := I) α hp)
    rw [hfderiv_eq] at hkey0
    have hfderiv_apply :
        fderiv ℝ (applyJac (I := I) α p) bp (geodesicVectorFieldChart (I := I) g α p) =
          chartTransitionAt (I := I) p.proj α x₀ X +
            (fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z) x₀ (p.snd : E))
              (p.snd : E) := by
      have := fderiv_applyJac_apply (I := I) α hp (geodesicVectorFieldChart (I := I) g α p)
      rw [this, hbp1, hbp2, hgvf1]
    rw [hfderiv_apply] at hkey0
    set Dterm : E := (fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z) x₀
      (p.snd : E)) (p.snd : E) with hDterm
    set v := chartFiberCoord (I := I) α p with hv
    have hfiber2 : (geodesicVectorFieldChartFiber (I := I) g α p).2 =
        - chartChristoffelContraction (I := I) g α v v (extChartAt I α p.proj) := rfl
    rw [hfiber2] at hkey0
    have htransform :
        chartChristoffelContraction (I := I) g p.proj (p.snd) (p.snd) x₀ =
          chartTransitionAt (I := I) α p.proj
              (chartTransitionMap (I := I) p.proj α x₀)
              (chartChristoffelContraction (I := I) g α
                (chartTransitionAt (I := I) p.proj α x₀ (p.snd))
                (chartTransitionAt (I := I) p.proj α x₀ (p.snd))
                (chartTransitionMap (I := I) p.proj α x₀))
            + chartTransitionSecondDerivCorrection (I := I) p.proj α (p.snd) (p.snd) x₀ := by
      have := chartChristoffelContraction_transform (I := I) g p.proj α
        (p := p.proj) (mem_chart_source H p.proj) hp (p.snd) (p.snd)
      rw [hx₀]; exact this
    have hTx₀ : chartTransitionMap (I := I) p.proj α x₀ = extChartAt I α p.proj := by
      rw [hx₀]
      exact chartTransitionMap_apply_extChartAt (I := I) p.proj α (mem_chart_source H p.proj)
    have hJsnd : chartTransitionAt (I := I) p.proj α x₀ (p.snd) = v := by
      rw [hv, hx₀, ← tangentCoordChange_eq_chartTransitionAt (I := I) p.proj α p.proj]
      exact (chartFiberCoord_eq_tangentCoordChange (I := I) (α := α) (p := p) hp).symm
    rw [hTx₀, hJsnd] at htransform
    have hcorr :
        chartTransitionAt (I := I) α p.proj (extChartAt I α p.proj) Dterm =
          chartTransitionSecondDerivCorrection (I := I) p.proj α (p.snd) (p.snd) x₀ := by
      refine (chartModelBasis E).ext_elem (fun k => ?_)
      change chartCoord (E := E) k
          (chartTransitionAt (I := I) α p.proj (extChartAt I α p.proj) Dterm) =
        chartCoord (E := E) k
          (chartTransitionSecondDerivCorrection (I := I) p.proj α (p.snd) (p.snd) x₀)
      rw [chartCoord_chartTransitionAt (I := I) α p.proj (extChartAt I α p.proj) Dterm k]
      rw [chartTransitionSecondDerivCorrection_def]
      rw [show chartCoord (E := E) k
          (∑ k' : Fin (Module.finrank ℝ E),
            (∑ c : Fin (Module.finrank ℝ E),
              chartTransitionJacEntry (I := I) α p.proj
                (chartTransitionMap (I := I) p.proj α x₀) k' c *
                (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
                  partialDeriv (E := E) i
                    (fun z => chartTransitionJacEntry (I := I) p.proj α z c j) x₀ *
                    chartCoord (E := E) i (p.snd) * chartCoord (E := E) j (p.snd))) •
              chartModelBasis E k') =
          ∑ c : Fin (Module.finrank ℝ E),
              chartTransitionJacEntry (I := I) α p.proj
                (chartTransitionMap (I := I) p.proj α x₀) k c *
                (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
                  partialDeriv (E := E) i
                    (fun z => chartTransitionJacEntry (I := I) p.proj α z c j) x₀ *
                    chartCoord (E := E) i (p.snd) * chartCoord (E := E) j (p.snd)) from ?_]
      · rw [hTx₀]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [hDterm, chartCoord_fderiv_chartTransitionAt (I := I) α hp c (p.snd)]
      · rw [chartCoord_def, map_sum, Finsupp.finset_sum_apply]
        rw [Finset.sum_eq_single k]
        · rw [map_smul, Finsupp.smul_apply, (chartModelBasis E).repr_self k,
            Finsupp.single_eq_same, smul_eq_mul, mul_one]
        · intro k' _ hk'
          rw [map_smul, Finsupp.smul_apply, (chartModelBasis E).repr_self k']
          rw [Finsupp.single_eq_of_ne (Ne.symm hk'), smul_zero]
        · intro hk; exact absurd (Finset.mem_univ k) hk
    have hx_src : x₀ ∈ chartTransitionSource (I := I) p.proj α :=
      extChartAt_mem_chartTransitionSource (I := I) p.proj α (mem_chart_source H p.proj) hp
    have hinv : chartTransitionAt (I := I) α p.proj
        (chartTransitionMap (I := I) p.proj α x₀)
        (chartTransitionAt (I := I) p.proj α x₀ X) = X := by
      have hcomp := chartTransitionAt_comp_chartTransitionAt (I := I) p.proj α hx_src
      have := congrArg (fun L : E →L[ℝ] E => L X) hcomp
      simpa using this
    set RJ : E →L[ℝ] E := chartTransitionAt (I := I) α p.proj
      (chartTransitionMap (I := I) p.proj α x₀) with hRJ
    have happ := congrArg (fun y => RJ y) hkey0
    simp only at happ
    rw [map_add] at happ
    have hRJ_X : RJ (chartTransitionAt (I := I) p.proj α x₀ X) = X := by
      rw [hRJ]; exact hinv
    rw [hRJ_X] at happ
    have hRJ_D : RJ Dterm =
        chartTransitionSecondDerivCorrection (I := I) p.proj α (p.snd) (p.snd) x₀ := by
      rw [hRJ, hTx₀]; exact hcorr
    rw [hRJ_D] at happ
    rw [map_neg] at happ
    have hRJ_Gamma :
        RJ (chartChristoffelContraction (I := I) g α v v (extChartAt I α p.proj)) =
          chartChristoffelContraction (I := I) g p.proj (p.snd) (p.snd) x₀ -
            chartTransitionSecondDerivCorrection (I := I) p.proj α (p.snd) (p.snd) x₀ := by
      rw [hRJ, hTx₀]
      rw [eq_sub_iff_add_eq]
      exact htransform.symm
    rw [hRJ_Gamma] at happ
    have hXval : X = - chartChristoffelContraction (I := I) g p.proj (p.snd) (p.snd) x₀ := by
      rw [neg_sub, sub_eq_neg_add] at happ
      exact (add_right_cancel happ).symm
    rw [hXval, geodesicVectorField_snd]
  apply Prod.ext hfst hsnd

theorem geodesicVectorFieldChart_eq_of_proj_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α α' : M)
    {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (hα' : p.proj ∈ (chartAt H α').source) :
    geodesicVectorFieldChart (I := I) g α p =
      geodesicVectorFieldChart (I := I) g α' p := by
  rw [geodesicVectorFieldChart_eq_geodesicVectorField (I := I) g α hα,
    geodesicVectorFieldChart_eq_geodesicVectorField (I := I) g α' hα']

theorem gc_vf_chart_coincidence
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α α' : M)
    {f : ℝ → TangentBundle I M} {t₀ : ℝ}
    (hα : (f t₀).proj ∈ (chartAt H α).source)
    (hα' : (f t₀).proj ∈ (chartAt H α').source)
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀) :
    IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α') t₀ := by
  classical
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hf_contAt : ContinuousAt f t₀ := hf.continuousAt
  have hproj_contAt : ContinuousAt (fun t => (f t).proj) t₀ :=
    hπ_cont.continuousAt.comp hf_contAt
  have hα_nhds : (fun t => (f t).proj) ⁻¹' (chartAt H α).source ∈ 𝓝 t₀ :=
    hproj_contAt.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hα)
  have hα'_nhds : (fun t => (f t).proj) ⁻¹' (chartAt H α').source ∈ 𝓝 t₀ :=
    hproj_contAt.preimage_mem_nhds ((chartAt H α').open_source.mem_nhds hα')
  unfold IsMIntegralCurveAt at hf ⊢
  filter_upwards [hf, hα_nhds, hα'_nhds] with t htD ht_α ht_α'
  have ht_α2 : (f t).proj ∈ (chartAt H α).source := ht_α
  have ht_α'2 : (f t).proj ∈ (chartAt H α').source := ht_α'
  have hvf_eq : geodesicVectorFieldChart (I := I) g α (f t) =
      geodesicVectorFieldChart (I := I) g α' (f t) :=
    geodesicVectorFieldChart_eq_of_proj_mem (I := I) g α α' (p := f t) ht_α2 ht_α'2
  exact hvf_eq ▸ htD

theorem gc_cross_vf_projection_uniqueness
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀) :
    ∃ f₁ : ℝ → TangentBundle I M,
      (f₁ t₀).proj = γ t₀ ∧
      IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀ ∧
      γ =ᶠ[𝓝 t₀] (fun t => (f₁ t).proj) := by
  classical
  obtain ⟨α, f, hproj, hα_src, hf⟩ := hγ
  have hft₀ : (f t₀).proj = γ t₀ := hproj t₀
  have hγt₀_src : (f t₀).proj ∈ (chartAt H (γ t₀)).source := by
    rw [hft₀]; exact mem_chart_source H (γ t₀)
  obtain ⟨f₁, hf₁_init, hf₁⟩ :=
    exists_chartCenteredLift_at (I := I) g (γ t₀) ((f t₀).snd : E) t₀
  have hf₁_proj : (f₁ t₀).proj = γ t₀ := by rw [hf₁_init]
  refine ⟨f₁, hf₁_proj, hf₁, ?_⟩
  have hf_at_γ : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀ :=
    gc_vf_chart_coincidence (I := I) g α (γ t₀) hα_src hγt₀_src hf
  have h0 : f₁ t₀ = f t₀ := by
    rw [hf₁_init]
    rw [← hft₀]
  have hfe : f₁ =ᶠ[𝓝 t₀] f := by
    have hsrc₁ : (f₁ t₀).proj ∈ (chartAt H (γ t₀)).source := by
      rw [hf₁_proj]; exact mem_chart_source H (γ t₀)
    exact isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
      (I := I) (g := g) (α := γ t₀) (t₀ := t₀)
      (f₁ := f₁) (f₂ := f) hsrc₁ hf₁ hf_at_γ h0
  filter_upwards [hfe] with t ht
  rw [ht, hproj t]

theorem IsGeodesicAt.hasGeodesicEquationAt
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀) :
    HasGeodesicEquationAt (I := I) g γ t₀ := by
  obtain ⟨f₁, hf₁_proj_t₀, hf₁, hcross⟩ :=
    gc_cross_vf_projection_uniqueness (I := I) (g := g) (γ := γ) (t₀ := t₀) hγ
  exact IsGeodesicAt.hasGeodesicEquationAt_of_chartCentered_lift_eventuallyEq
    (I := I) (g := g) (γ := γ) (t₀ := t₀) hγ (f₁ := f₁) hf₁ hf₁_proj_t₀ hcross

section MovingFootToFixedChart

variable [I.Boundaryless]

theorem hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity
    (g : SmoothRiemannianMetric I M) (y : M) {γ : ℝ → M} {t : ℝ}
    (hγ_cont : ContinuousAt γ t)
    (hy : γ t ∈ (chartAt H y).source)
    (h : HasGeodesicEquationAt (I := I) g γ t) :
    HasDerivAt (deriv (chartCurve (I := I) y γ))
      (- chartChristoffelContraction (I := I) g y
          (deriv (chartCurve (I := I) y γ) t)
          (deriv (chartCurve (I := I) y γ) t)
          (chartCurve (I := I) y γ t)) t := by
  classical
  set α : M := γ t with hα_def
  set x : E := chartCurve (I := I) α γ t with hx_def
  obtain ⟨v, a, hv0, hev0, ha0, hgeo⟩ := h
  have hwdef : chartLocalCurve (I := I) γ t = chartCurve (I := I) α γ := by
    funext s; rw [chartLocalCurve_def, hα_def, chartCurve_def]
  rw [hwdef] at hv0 hev0 ha0
  have hα_src : γ t ∈ (chartAt H α).source := by
    rw [hα_def]; exact mem_chart_source H (γ t)
  have hx_src : x ∈ chartTransitionSource (I := I) α y :=
    extChartAt_mem_chartTransitionSource (I := I) α y hα_src hy
  have hx_eq : x = extChartAt I (γ t) (γ t) := by rw [hx_def, chartCurve_def, hα_def]
  have hboth_nhds : (fun s => γ s) ⁻¹'
      ((chartAt H α).source ∩ (chartAt H y).source) ∈ 𝓝 t :=
    hγ_cont.preimage_mem_nhds
      (((chartAt H α).open_source.inter (chartAt H y).open_source).mem_nhds ⟨hα_src, hy⟩)
  set u : ℝ → E := chartCurve (I := I) y γ with hu_def
  set w : ℝ → E := chartCurve (I := I) α γ with hw_def
  have hwt : w t = x := by rw [hw_def, hx_def]
  have hcurve_eq : u =ᶠ[𝓝 t]
      (fun s => chartTransitionMap (I := I) α y (w s)) := by
    filter_upwards [hboth_nhds] with s hs
    obtain ⟨hsα, _hsy⟩ := hs
    rw [hu_def, hw_def, chartCurve_def, chartCurve_def]
    exact (chartTransitionMap_apply_extChartAt (I := I) α y hsα).symm
  have hTdiff : ∀ {z : E}, z ∈ chartTransitionSource (I := I) α y →
      DifferentiableAt ℝ (chartTransitionMap (I := I) α y) z :=
    fun hz => chartTransitionMap_differentiableAt (I := I) α y hz
  have hu_hasDerivAt_ev : ∀ᶠ s in 𝓝 t,
      HasDerivAt u (chartTransitionAt (I := I) α y (w s) (deriv w s)) s := by
    filter_upwards [hev0, hboth_nhds, hcurve_eq.eventually_nhds] with s hs hs_both hs_eq
    have hws_src : w s ∈ chartTransitionSource (I := I) α y := by
      rw [hw_def, chartCurve_def]
      exact extChartAt_mem_chartTransitionSource (I := I) α y hs_both.1 hs_both.2
    have hcomp : HasDerivAt
        (fun r => chartTransitionMap (I := I) α y (w r))
        (chartTransitionAt (I := I) α y (w s) (deriv w s)) s := by
      have := (hTdiff hws_src).hasFDerivAt.comp_hasDerivAt s hs
      simpa [chartTransitionAt_def] using this
    exact hcomp.congr_of_eventuallyEq hs_eq
  have hdw_t : deriv w t = v := hv0.deriv
  have hu_deriv_t : HasDerivAt u (chartTransitionAt (I := I) α y x v) t := by
    have h0 := hu_hasDerivAt_ev.self_of_nhds
    rwa [hwt, hdw_t] at h0
  have hderiv_u_t : deriv u t = chartTransitionAt (I := I) α y x v := hu_deriv_t.deriv
  have hderiv_u_ev : (fun s => deriv u s) =ᶠ[𝓝 t]
      (fun s => chartTransitionAt (I := I) α y (w s) (deriv w s)) := by
    filter_upwards [hu_hasDerivAt_ev] with s hds
    exact hds.deriv
  have hAdiff : DifferentiableAt ℝ
      (fun z => (chartTransitionAt (I := I) α y z : E →L[ℝ] E)) x := by
    have h_open : IsOpen (chartTransitionSource (I := I) α y) :=
      chartTransitionSource_isOpen (I := I) α y
    exact ((chartTransitionAt_smooth (I := I) α y).contDiffAt
      (h_open.mem_nhds hx_src)).differentiableAt (by simp)
  have hAdiff_wt : DifferentiableAt ℝ
      (fun z => (chartTransitionAt (I := I) α y z : E →L[ℝ] E)) (w t) := by
    rw [hwt]; exact hAdiff
  have hcA : HasDerivAt
      (fun s => (chartTransitionAt (I := I) α y (w s) : E →L[ℝ] E))
      ((fderiv ℝ (fun z => chartTransitionAt (I := I) α y z) x) v) t := by
    have hc0 := hAdiff_wt.hasFDerivAt.comp_hasDerivAt t hv0
    rw [hwt] at hc0
    exact hc0
  have hVderiv : HasDerivAt
      (fun s => chartTransitionAt (I := I) α y (w s) (deriv w s))
      (((fderiv ℝ (fun z => chartTransitionAt (I := I) α y z) x) v) v
        + chartTransitionAt (I := I) α y x a) t := by
    have hclm := hcA.clm_apply ha0
    rw [hwt, hdw_t] at hclm
    exact hclm
  have hUderiv : HasDerivAt (deriv u)
      (((fderiv ℝ (fun z => chartTransitionAt (I := I) α y z) x) v) v
        + chartTransitionAt (I := I) α y x a) t :=
    hVderiv.congr_of_eventuallyEq hderiv_u_ev
  have hfoot :
      ((fderiv ℝ (fun z => chartTransitionAt (I := I) α y z) x) v) v =
        chartTransitionAt (I := I) α y x
          (chartTransitionSecondDerivCorrection (I := I) α y v v x) :=
    fderiv_chartTransitionAt_apply_eq_pushCorrection (I := I) α y hx_src v v
  have htransform :
      chartChristoffelContraction (I := I) g α v v x =
        chartTransitionAt (I := I) y α (chartTransitionMap (I := I) α y x)
            (chartChristoffelContraction (I := I) g y
              (chartTransitionAt (I := I) α y x v)
              (chartTransitionAt (I := I) α y x v)
              (chartTransitionMap (I := I) α y x))
          + chartTransitionSecondDerivCorrection (I := I) α y v v x := by
    rw [hx_eq]
    exact chartChristoffelContraction_transform (I := I) g α y hα_src hy v v
  have hu_t : u t = chartTransitionMap (I := I) α y x := by
    have hxα : x = extChartAt I α (γ t) := by rw [hx_def, hw_def, chartCurve_def]
    rw [hu_def, chartCurve_def, hxα]
    exact (chartTransitionMap_apply_extChartAt (I := I) α y hα_src).symm
  have hu'_t : deriv u t = chartTransitionAt (I := I) α y x v := hderiv_u_t
  have hDcollapse :
      ((fderiv ℝ (fun z => chartTransitionAt (I := I) α y z) x) v) v
        + chartTransitionAt (I := I) α y x a
        = - chartChristoffelContraction (I := I) g y
            (deriv u t) (deriv u t) (u t) := by
    have ha_eq : a = - chartChristoffelContraction (I := I) g α v v x := by
      rw [hx_eq]; exact eq_neg_of_add_eq_zero_left hgeo
    rw [hfoot, ha_eq, map_neg, ← sub_eq_add_neg, ← map_sub]
    have hsub :
        chartTransitionSecondDerivCorrection (I := I) α y v v x -
            chartChristoffelContraction (I := I) g α v v x =
          - chartTransitionAt (I := I) y α (chartTransitionMap (I := I) α y x)
              (chartChristoffelContraction (I := I) g y
                (chartTransitionAt (I := I) α y x v)
                (chartTransitionAt (I := I) α y x v)
                (chartTransitionMap (I := I) α y x)) := by
      rw [htransform]; abel
    rw [hsub, map_neg]
    have hinv := chartTransitionAt_comp_chartTransitionAt' (I := I) α y hx_src
    have hid := congrArg (fun L : E →L[ℝ] E => L
        (chartChristoffelContraction (I := I) g y
          (chartTransitionAt (I := I) α y x v)
          (chartTransitionAt (I := I) α y x v)
          (chartTransitionMap (I := I) α y x))) hinv
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hid
    rw [hid, hu_t, hu'_t]
  rw [hDcollapse] at hUderiv
  exact hUderiv

omit [NeZero (Module.finrank ℝ E)] in
theorem hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt
    (g : SmoothRiemannianMetric I M) (y : M) {γ : ℝ → M} {t : ℝ}
    (hγ_cont : ContinuousAt γ t)
    (hy : γ t ∈ (chartAt H y).source)
    (h : HasGeodesicEquationAt (I := I) g γ t) :
    ∀ᶠ s in nhds t,
      HasDerivAt (chartCurve (I := I) y γ) (deriv (chartCurve (I := I) y γ) s) s := by
  classical
  set α : M := γ t with hα_def
  obtain ⟨v, a, hv0, hev0, ha0, hgeo⟩ := h
  have hwdef : chartLocalCurve (I := I) γ t = chartCurve (I := I) α γ := by
    funext s; rw [chartLocalCurve_def, hα_def, chartCurve_def]
  rw [hwdef] at hev0
  have hα_src : γ t ∈ (chartAt H α).source := by
    rw [hα_def]; exact mem_chart_source H (γ t)
  have hboth_nhds : (fun s => γ s) ⁻¹'
      ((chartAt H α).source ∩ (chartAt H y).source) ∈ 𝓝 t :=
    hγ_cont.preimage_mem_nhds
      (((chartAt H α).open_source.inter (chartAt H y).open_source).mem_nhds ⟨hα_src, hy⟩)
  set u : ℝ → E := chartCurve (I := I) y γ with hu_def
  set w : ℝ → E := chartCurve (I := I) α γ with hw_def
  have hcurve_eq : u =ᶠ[𝓝 t]
      (fun s => chartTransitionMap (I := I) α y (w s)) := by
    filter_upwards [hboth_nhds] with s hs
    obtain ⟨hsα, _hsy⟩ := hs
    rw [hu_def, hw_def, chartCurve_def, chartCurve_def]
    exact (chartTransitionMap_apply_extChartAt (I := I) α y hsα).symm
  have hTdiff : ∀ {z : E}, z ∈ chartTransitionSource (I := I) α y →
      DifferentiableAt ℝ (chartTransitionMap (I := I) α y) z :=
    fun hz => chartTransitionMap_differentiableAt (I := I) α y hz
  have hu_hasDerivAt_ev : ∀ᶠ s in 𝓝 t,
      HasDerivAt u (chartTransitionAt (I := I) α y (w s) (deriv w s)) s := by
    filter_upwards [hev0, hboth_nhds, hcurve_eq.eventually_nhds] with s hs hs_both hs_eq
    have hws_src : w s ∈ chartTransitionSource (I := I) α y := by
      rw [hw_def, chartCurve_def]
      exact extChartAt_mem_chartTransitionSource (I := I) α y hs_both.1 hs_both.2
    have hcomp : HasDerivAt
        (fun r => chartTransitionMap (I := I) α y (w r))
        (chartTransitionAt (I := I) α y (w s) (deriv w s)) s := by
      have := (hTdiff hws_src).hasFDerivAt.comp_hasDerivAt s hs
      simpa [chartTransitionAt_def] using this
    exact hcomp.congr_of_eventuallyEq hs_eq
  filter_upwards [hu_hasDerivAt_ev] with s hs
  rw [hs.deriv]; exact hs

end MovingFootToFixedChart

omit [NeZero (Module.finrank ℝ E)] in
private lemma hasGeodesicEquationAt_comp_sub_const
    {g : SmoothRiemannianMetric I M} {η : ℝ → M} {T t : ℝ}
    (h : HasGeodesicEquationAt (I := I) g η (t - T)) :
    HasGeodesicEquationAt (I := I) g (fun s => η (s - T)) t := by
  obtain ⟨v, a, hv, hev, ha, hgeo⟩ := h
  have hshift : chartLocalCurve (I := I) (fun s => η (s - T)) t =
      fun s => chartLocalCurve (I := I) η (t - T) (s - T) := by funext s; rfl
  refine ⟨v, a, ?_, ?_, ?_, ?_⟩
  · rw [hshift]; exact hv.comp_sub_const t T
  · rw [hshift]
    have hderiv : ∀ s,
        deriv (fun s => chartLocalCurve (I := I) η (t - T) (s - T)) s =
          deriv (chartLocalCurve (I := I) η (t - T)) (s - T) := fun s =>
      deriv_comp_sub_const (chartLocalCurve (I := I) η (t - T)) T s
    have hev' : ∀ᶠ s in nhds t, HasDerivAt
        (chartLocalCurve (I := I) η (t - T))
        (deriv (chartLocalCurve (I := I) η (t - T)) (s - T)) (s - T) :=
      ((continuous_sub_right T).continuousAt).eventually hev
    filter_upwards [hev'] with s hs
    rw [hderiv s]; exact hs.comp_sub_const s T
  · rw [hshift]
    have hd2 : (fun s => deriv
        (fun s => chartLocalCurve (I := I) η (t - T) (s - T)) s) =
        fun s => deriv (chartLocalCurve (I := I) η (t - T)) (s - T) := by
      funext s; exact deriv_comp_sub_const (chartLocalCurve (I := I) η (t - T)) T s
    rw [hd2]; exact ha.comp_sub_const t T
  · exact hgeo

omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesicOn_glue_at_limit [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    {γ η : ℝ → M} {T δ : ℝ} (hδ : 0 < δ)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Iio T))
    (hη : IsGeodesicOn (I := I) g η (Set.Ioo (-δ) δ))
    (hmatch : γ =ᶠ[nhdsWithin T (Set.Iio T)] (fun t => η (t - T))) :
    IsGeodesicOn (I := I) g (fun t => if t < T then γ t else η (t - T))
      (Set.Iio (T + δ)) := by
  classical
  set G : ℝ → M := fun t => if t < T then γ t else η (t - T) with hG
  set ηT : ℝ → M := fun s => η (s - T) with hηT
  have hGγ_lt : G =ᶠ[𝓝[<] T] γ :=
    Filter.eventually_of_mem self_mem_nhdsWithin
      (fun t ht => by simp only [hG]; rw [if_pos (mem_Iio.mp ht)])
  have hGηT_ge : G =ᶠ[𝓝[≥] T] ηT :=
    Filter.eventually_of_mem self_mem_nhdsWithin
      (fun t ht => by simp only [hG, hηT]; rw [if_neg (not_lt.mpr (mem_Ici.mp ht))])
  have hGηT_lt : G =ᶠ[𝓝[<] T] ηT := hGγ_lt.trans hmatch
  have hGηT_T : G =ᶠ[𝓝 T] ηT := by
    rw [← nhdsLT_sup_nhdsGE T, Filter.EventuallyEq, eventually_sup]
    exact ⟨hGηT_lt, hGηT_ge⟩
  intro t ht
  rw [mem_Iio] at ht
  rcases lt_trichotomy t T with hlt | heq | hgt
  · have hGγ_t : G =ᶠ[𝓝 t] γ :=
      Filter.eventually_of_mem ((isOpen_Iio).mem_nhds hlt)
        (fun s hs => by simp only [hG]; rw [if_pos (mem_Iio.mp hs)])
    refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := γ) ?_ hGγ_t ?_
    · simp only [hG]; rw [if_pos hlt]
    · exact hγ t (mem_Iio.mpr hlt)
  · subst heq
    have hmem0 : t - t ∈ Set.Ioo (-δ) δ := by
      rw [sub_self]; exact ⟨neg_lt_zero.mpr hδ, hδ⟩
    have hηeq : HasGeodesicEquationAt (I := I) g ηT t :=
      hasGeodesicEquationAt_comp_sub_const (hη (t - t) hmem0)
    refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := ηT) ?_ hGηT_T hηeq
    simp only [hG, hηT]; rw [if_neg (lt_irrefl t)]
  · have hGηT_t : G =ᶠ[𝓝 t] ηT :=
      Filter.eventually_of_mem ((isOpen_Ioi).mem_nhds hgt)
        (fun s hs => by
          simp only [hG, hηT]; rw [if_neg (not_lt.mpr (le_of_lt (mem_Ioi.mp hs)))])
    have hmem : t - T ∈ Set.Ioo (-δ) δ := ⟨by linarith, by linarith⟩
    have hηeq : HasGeodesicEquationAt (I := I) g ηT t :=
      hasGeodesicEquationAt_comp_sub_const (hη (t - T) hmem)
    refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := ηT) ?_ hGηT_t hηeq
    simp only [hG, hηT]; rw [if_neg (not_lt.mpr (le_of_lt hgt))]

omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesicOn_glue_at_limit_Ioo [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    {γ η : ℝ → M} {a T δ : ℝ} (hδ : 0 < δ) (haT : a < T)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Ioo a T))
    (hη : IsGeodesicOn (I := I) g η (Set.Ioo (-δ) δ))
    (hmatch : γ =ᶠ[nhdsWithin T (Set.Iio T)] (fun t => η (t - T))) :
    IsGeodesicOn (I := I) g (fun t => if t < T then γ t else η (t - T))
      (Set.Ioo a (T + δ)) := by
  classical
  set G : ℝ → M := fun t => if t < T then γ t else η (t - T) with hG
  set ηT : ℝ → M := fun s => η (s - T) with hηT
  have hGγ_lt : G =ᶠ[𝓝[<] T] γ :=
    Filter.eventually_of_mem self_mem_nhdsWithin
      (fun t ht => by simp only [hG]; rw [if_pos (mem_Iio.mp ht)])
  have hGηT_ge : G =ᶠ[𝓝[≥] T] ηT :=
    Filter.eventually_of_mem self_mem_nhdsWithin
      (fun t ht => by simp only [hG, hηT]; rw [if_neg (not_lt.mpr (mem_Ici.mp ht))])
  have hGηT_lt : G =ᶠ[𝓝[<] T] ηT := hGγ_lt.trans hmatch
  have hGηT_T : G =ᶠ[𝓝 T] ηT := by
    rw [← nhdsLT_sup_nhdsGE T, Filter.EventuallyEq, eventually_sup]
    exact ⟨hGηT_lt, hGηT_ge⟩
  intro t ht
  obtain ⟨ht_lo, ht_hi⟩ := ht
  rcases lt_trichotomy t T with hlt | heq | hgt
  · have hGγ_t : G =ᶠ[𝓝 t] γ :=
      Filter.eventually_of_mem ((isOpen_Iio).mem_nhds hlt)
        (fun s hs => by simp only [hG]; rw [if_pos (mem_Iio.mp hs)])
    refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := γ) ?_ hGγ_t ?_
    · simp only [hG]; rw [if_pos hlt]
    · exact hγ t ⟨ht_lo, hlt⟩
  · subst heq
    have hmem0 : t - t ∈ Set.Ioo (-δ) δ := by
      rw [sub_self]; exact ⟨neg_lt_zero.mpr hδ, hδ⟩
    have hηeq : HasGeodesicEquationAt (I := I) g ηT t :=
      hasGeodesicEquationAt_comp_sub_const (hη (t - t) hmem0)
    refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := ηT) ?_ hGηT_T hηeq
    simp only [hG, hηT]; rw [if_neg (lt_irrefl t)]
  · have hGηT_t : G =ᶠ[𝓝 t] ηT :=
      Filter.eventually_of_mem ((isOpen_Ioi).mem_nhds hgt)
        (fun s hs => by
          simp only [hG, hηT]; rw [if_neg (not_lt.mpr (le_of_lt (mem_Ioi.mp hs)))])
    have hmem : t - T ∈ Set.Ioo (-δ) δ := ⟨by linarith, by linarith⟩
    have hηeq : HasGeodesicEquationAt (I := I) g ηT t :=
      hasGeodesicEquationAt_comp_sub_const (hη (t - T) hmem)
    refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := ηT) ?_ hGηT_t hηeq
    simp only [hG, hηT]; rw [if_neg (not_lt.mpr (le_of_lt hgt))]

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
