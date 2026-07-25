import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Flow.DeTurckVFChartCoord








noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem const_gram_joint
    (q : SmoothRiemannianMetric I M) (α : M) {S : Set ℝ} :
    ChartGramFamilyJointSmoothNondegenerate (I := I) (fun _ : ℝ => q) α S := by
  refine ⟨?_, ?_⟩
  · intro a b t₀ y₀ _ht hy
    have hsnd : ContDiffAt ℝ ∞ (Prod.snd : ℝ × E → E) (t₀, y₀) := contDiffAt_snd
    exact (((chartGramOnE_contDiffOn (I := I) q α a b).mono interior_subset).contDiffAt
      (isOpen_interior.mem_nhds hy)).comp (t₀, y₀) hsnd
  · intro _t _ht x hx
    exact chartGramMatrix_det_pos (I := I) q α hx

omit [BoundarylessManifold I M] in
omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem christ_const_joint
    (q : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) {S : Set ℝ} :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ =>
        chartChristoffel (I := I) q α i j k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) := by
  classical
  have hG := const_gram_joint (I := I) q α (S := S)
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst
      (fun _p hp => hp.1)
  intro p hp
  obtain ⟨hx, ht⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]
    exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_christoffel (I := I) (fun _ : ℝ => q) α hG i j k ht hy
  have hentryM : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartChristoffel (I := I) q α i j k r.2)
      (p.2, extChartAt I α p.1) := hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × E) ∞
      (fun z : M × ℝ => (z.2, extChartAt I α z.1))
      ((chartAt H α).source ×ˢ S) p :=
    by
      have hm := hmove p ⟨hx, ht⟩
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
      exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr (fun _z _hz => rfl) rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem covComp_joint
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, fun x : M => Tensor0SSpace 1 I x⟯)
    (α : M) (i : Fin (Module.finrank ℝ E)) {S : Set ℝ} :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ =>
        (om p.1) (fun _ : Fin 1 => chartBasisVecFiber (I := I) α i p.1))
      ((chartAt H α).source ×ˢ S) := by
  have hbase := cotangentSection_chartComponent_contMDiffOn (I := I) om α i
  have hcomp : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => Tensor0SSpace.toModel (om p.1)
        (fun _ : Fin 1 => chartBasisVecFiber (I := I) α i p.1))
      ((chartAt H α).source ×ˢ S) :=
    hbase.comp contMDiffOn_fst (fun _p hp => hp.1)
  simpa only [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using hcomp

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem conn_pair_joint
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (q : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, fun x : M => Tensor0SSpace 1 I x⟯)
    (α : M) (j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ =>
        ((show Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 from
            connDiffFib (I := I) (G.metric p.2) q p.1) (om p.1))
          ![chartBasisVecFiber (I := I) α j p.1,
            chartBasisVecFiber (I := I) α k p.1])
      ((chartAt H α).source ×ˢ D.regular) := by
  classical
  have hsum : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => ∑ a : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) (G.metric p.2) α k j a (extChartAt I α p.1) -
          chartChristoffel (I := I) q α k j a (extChartAt I α p.1)) *
        (om p.1) (fun _ : Fin 1 => chartBasisVecFiber (I := I) α a p.1))
      ((chartAt H α).source ×ˢ D.regular) := by
    refine contMDiffOn_finset_sum (fun a _ => ?_)
    exact ((christ_of_family (I := I) G hG α k j a).sub
      (christ_const_joint (I := I) q α k j a)).mul
        (covComp_joint (I := I) om α a)
  refine hsum.congr (fun p hp => ?_)
  obtain ⟨hx, _⟩ := hp
  have hxgood : p.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α,
      extChartAt_source (I := I)]
    exact hx
  rw [connDiffFib_apply_eval]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [DifferentialGeometry.PDE.DeTurck.connDiff_chartBasis_pair_eq_sum
    (I := I) (G.metric p.2) q α hxgood j k]
  set φ : TangentSpace I p.1 →L[ℝ] ℝ :=
    continuousMultilinearCurryFin1 ℝ (TangentSpace I p.1) ℝ (om p.1) with hφ
  have hφapply : ∀ v : TangentSpace I p.1,
      (om p.1) (fun _ : Fin 1 => v) = φ v := by
    intro v
    rw [hφ, continuousMultilinearCurryFin1_apply]
    rfl
  rw [hφapply, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_smul, smul_eq_mul, hφapply]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem connDiff_app_joint
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (q : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, fun x : M => Tensor0SSpace 1 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun x : M => Tensor0SSpace 2 I x) p.1
        ((show Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 from
          (connDiffSection (I := I) (G.metric p.2) q).toSection p.1) (om p.1)))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  classical
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  intro p₀ hp₀
  set α := p₀.1
  set e := trivializationAt (Tensor0SModel 2 ℝ E)
    (fun x : M => Tensor0SSpace 2 I x) α with he
  set Bcmm := continuousMultilinearMap_basis (𝕜 := ℝ) (F := E) (chartModelBasis E) 2
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  have hαsrc : α ∈ (chartAt H α).source := mem_chart_source H α
  have hαbase : α ∈ e.baseSet := by
    rw [he]
    exact mem_baseSet_trivializationAt _ _ α
  have hnhd : (chartAt H α).source ×ˢ D.regular ∈
      nhdsWithin p₀ ((Set.univ : Set M) ×ˢ D.regular) := by
    refine mem_nhdsWithin.mpr ⟨(chartAt H α).source ×ˢ D.regular,
      (chartAt H α).open_source.prod D.regular_isOpen,
      ⟨?_, hp₀.2⟩, fun z hz => hz.1⟩
    simpa only [α] using hαsrc
  have hcoordEach : ∀ σ : Fin 2 → Fin (Module.finrank ℝ E),
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Bcmm.repr
          (e ⟨p.1, (show Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 from
            (connDiffSection (I := I) (G.metric p.2) q).toSection p.1) (om p.1)⟩).2 σ)
        ((Set.univ : Set M) ×ˢ D.regular) p₀ := by
    intro σ
    have hscal := conn_pair_joint (I := I) G hG q om α (σ 0) (σ 1)
    have hscalAt := (hscal p₀ ⟨by simpa only [α] using hαsrc, hp₀.2⟩).mono_of_mem_nhdsWithin hnhd
    have hreadout : ∀ {z : M × ℝ}, z.1 ∈ e.baseSet →
        Bcmm.repr
            (e ⟨z.1, (show Tensor0SSpace 1 I z.1 →L[ℝ] Tensor0SSpace 2 I z.1 from
              (connDiffSection (I := I) (G.metric z.2) q).toSection z.1) (om z.1)⟩).2 σ =
          ((show Tensor0SSpace 1 I z.1 →L[ℝ] Tensor0SSpace 2 I z.1 from
              connDiffFib (I := I) (G.metric z.2) q z.1) (om z.1))
            ![chartBasisVecFiber (I := I) α (σ 0) z.1,
              chartBasisVecFiber (I := I) α (σ 1) z.1] := by
      intro z hzbase
      rw [continuousMultilinearMap_basis_repr]
      have hcoe :
          (e ⟨z.1, (show Tensor0SSpace 1 I z.1 →L[ℝ] Tensor0SSpace 2 I z.1 from
            (connDiffSection (I := I) (G.metric z.2) q).toSection z.1) (om z.1)⟩).2 =
            (e.linearMapAt ℝ z.1)
              ((show Tensor0SSpace 1 I z.1 →L[ℝ] Tensor0SSpace 2 I z.1 from
                (connDiffSection (I := I) (G.metric z.2) q).toSection z.1) (om z.1)) :=
        (congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e) hzbase) _).symm
      rw [hcoe]
      have happly := TensorMultilinear.tensor0SBundle_linearMapAt_apply_of_mem
        (I := I) α z.1 hzbase
        ((show Tensor0SSpace 1 I z.1 →L[ℝ] Tensor0SSpace 2 I z.1 from
          (connDiffSection (I := I) (G.metric z.2) q).toSection z.1) (om z.1))
        (fun a => (chartModelBasis E) (σ a))
      rw [tensor0SSpace_continuousLinearEquiv_symm_apply] at happly
      rw [happly]
      rw [connDiffSection_toSection]
      rw [show (fun a => (trivializationAt E (TangentSpace I) α).symmL ℝ z.1
            ((chartModelBasis E) (σ a))) =
          (fun a => chartBasisVecFiber (I := I) α (σ a) z.1) from by
        funext a
        rfl]
      rfl
    refine hscalAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hnhd] with z hz
      have hzbaseT : z.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
        exact hz.1
      have hzbase : z.1 ∈ e.baseSet := by
        rw [he]
        exact hzbaseT
      exact hreadout hzbase
    · exact hreadout hαbase
  have hcoordVec : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun p : M × ℝ => fun σ : Fin 2 → Fin (Module.finrank ℝ E) =>
        Bcmm.repr
          (e ⟨p.1, (show Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 from
            (connDiffSection (I := I) (G.metric p.2) q).toSection p.1) (om p.1)⟩).2 σ)
      ((Set.univ : Set M) ×ˢ D.regular) p₀ :=
    contMDiffWithinAt_pi_space.mpr (fun σ => hcoordEach σ)
  have hfinal : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SModel 2 ℝ E) ∞
      (fun p : M × ℝ =>
        (e ⟨p.1, (show Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 from
          (connDiffSection (I := I) (G.metric p.2) q).toSection p.1) (om p.1)⟩).2)
      ((Set.univ : Set M) ×ˢ D.regular) p₀ := by
    have hequiv :=
      (Bcmm.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt
        (x := Bcmm.equivFun
          (e ⟨p₀.1, (show Tensor0SSpace 1 I p₀.1 →L[ℝ] Tensor0SSpace 2 I p₀.1 from
            (connDiffSection (I := I) (G.metric p₀.2) q).toSection p₀.1) (om p₀.1)⟩).2)).comp_contMDiffWithinAt
        p₀ hcoordVec
    refine hequiv.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with z _
      exact (Bcmm.equivFun.symm_apply_apply _).symm
    · exact (Bcmm.equivFun.symm_apply_apply _).symm
  exact hfinal



omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connDiff_joint
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (q : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun x : M => TensorRSSpace 1 2 I x) p.1
        ((connDiffSection (I := I) (G.metric p.2) q).toSection p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 from
        (connDiffSection (I := I) (G.metric p.2) q).toSection p.1))
    (S := D.regular)
  intro om
  exact connDiff_app_joint (I := I) G hG q om

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
