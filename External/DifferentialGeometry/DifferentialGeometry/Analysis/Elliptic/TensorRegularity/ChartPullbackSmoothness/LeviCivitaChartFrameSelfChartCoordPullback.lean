import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.ChartPullbackSmoothness.ChartFrameCoordMatrixPullback
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.CovApplyFrameToCoordExpansion


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set MeasureTheory Filter Topology Function NormedSpace
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.MetricExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private noncomputable def chartModelBasisProj (m : Fin (Module.finrank ℝ E)) :
    E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (((LinearMap.proj m).comp ((chartModelBasis E).equivFun.toLinearMap)) :
      E →ₗ[ℝ] ℝ)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma chartModelBasisProj_apply (m : Fin (Module.finrank ℝ E))
    (v : E) :
    chartModelBasisProj (E := E) m v =
      ((chartModelBasis E).repr v) m := by
  classical
  unfold chartModelBasisProj
  change ((LinearMap.proj m).comp ((chartModelBasis E).equivFun.toLinearMap)) v = _
  rw [LinearMap.comp_apply]
  simp [Module.Basis.equivFun]

private lemma leviCivita_chartFrame_hom_contMDiff
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g).toFun
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun x⟩ :
          TotalSpace (E →L[ℝ] E) (fun x : M =>
            TangentSpace I x →L[ℝ] TangentSpace I x))) := by
  classical
  have hB :=
    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).contMDiff
  have hB' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun x))
      Set.univ := by
    have h_eq : (∞ : WithTop ℕ∞) + 1 = ∞ := by
      rw [ENat.coe_top_add_one]
    rw [h_eq]
    exact hB.contMDiffOn
  have h_hom_on :=
    LeviCivita_section_contMDiffOn_univ (I := I) g (σ := fun x : M =>
      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun x) hB'
  exact contMDiffOn_univ.mp h_hom_on

private lemma leviCivita_chartFrame_self_section_contMDiff
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g).toFun
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun x
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun x)⟩ :
          TotalSpace E (TangentSpace I : M → Type _))) := by
  classical
  have h_hom := leviCivita_chartFrame_hom_contMDiff (I := I) (M := M) g α i
  have hB :=
    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).contMDiff
  exact h_hom.clm_bundle_apply (v := fun x : M =>
    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun x) hB

private lemma leviCivita_chartFrame_self_trivialized_contMDiffOn
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b : M => (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
        ((LeviCivita (I := I) g).toFun
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have h_section :=
    leviCivita_chartFrame_self_section_contMDiff (I := I) (M := M) g α i
  have h_triv :
      ContMDiffOn I 𝓘(ℝ, E) ∞
        (fun b : M =>
          ((trivializationAt E (TangentSpace I) α)
            ⟨b, (LeviCivita (I := I) g).toFun
              (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)⟩).2)
        (trivializationAt E (TangentSpace I) α).baseSet := by
    have hiff := (trivializationAt E (TangentSpace I) α).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞)
      (s := fun b : M => (LeviCivita (I := I) g).toFun
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))
    exact hiff.mp h_section.contMDiffOn
  have h_eq_baseSet :
      Set.EqOn (fun b : M =>
          ((trivializationAt E (TangentSpace I) α)
            ⟨b, (LeviCivita (I := I) g).toFun
              (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)⟩).2)
        (fun b : M => (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          ((LeviCivita (I := I) g).toFun
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)))
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro b hb
    change ((trivializationAt E (TangentSpace I) α)
        ⟨b, (LeviCivita (I := I) g).toFun
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)⟩).2 =
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
        ((LeviCivita (I := I) g).toFun
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))
    have h₁ : ((trivializationAt E (TangentSpace I) α)
        ⟨b, (LeviCivita (I := I) g).toFun
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)⟩).2 =
        ((trivializationAt E (TangentSpace I) α).continuousLinearEquivAt ℝ b hb)
          ((LeviCivita (I := I) g).toFun
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)) := by
      have hp := Trivialization.apply_eq_prod_continuousLinearEquivAt
        (R := ℝ) (e := trivializationAt E (TangentSpace I) α) (b := b) hb
        ((LeviCivita (I := I) g).toFun
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))
      have hsnd := congrArg Prod.snd hp
      simp only at hsnd
      exact hsnd
    rw [h₁]
    have hclm := Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ)
      (e := trivializationAt E (TangentSpace I) α) (b := b) hb
    exact congrArg (fun (f : TangentSpace I b → E) => f
      ((LeviCivita (I := I) g).toFun
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))) hclm
  refine h_triv.congr ?_
  intro b hb
  exact (h_eq_baseSet hb).symm

private lemma leviCivita_chartFrame_self_coordProj_contMDiffOn
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i m : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => chartModelBasisProj (E := E) m
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          ((LeviCivita (I := I) g).toFun
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have h_triv :=
    leviCivita_chartFrame_self_trivialized_contMDiffOn (I := I) (M := M) g α i
  have h_proj : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (chartModelBasisProj (E := E) m : E → ℝ) :=
    (chartModelBasisProj (E := E) m).contMDiff
  exact h_proj.contMDiffOn.comp (t := Set.univ) h_triv (Set.subset_preimage_univ)

theorem leviCivita_chartFrame_self_chartCoord_pullback_contDiffOn_chartTarget
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        chartModelBasisProj (E := E) m
          ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            ((LeviCivita (I := I) g).toFun
              (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_chart :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) I ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) :=
    contMDiffOn_chart_symm (I := I) (M := M) α
  have h_coord :=
    leviCivita_chartFrame_self_coordProj_contMDiffOn (I := I) (M := M) g α i m
  have h_maps :
      MapsTo (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α)
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have h_src : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        (chartAt H α).source :=
      DifferentialGeometry.Analysis.Sobolev.Chart.symm_toEuclidean_symm_mem_chartAtSource
        (I := I) (M := M) α hy
    change (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H α).source
    exact h_src
  have h_comp :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 𝓘(ℝ, ℝ) ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          chartModelBasisProj (E := E) m
            ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              ((LeviCivita (I := I) g).toFun
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))))
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_coord.comp h_chart h_maps
  exact (contMDiffOn_iff_contDiffOn).mp h_comp

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
