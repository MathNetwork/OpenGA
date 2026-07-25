import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapChartProjFullExpansionViaChartInvGram
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.CovApplyFrameToCoordExpansion

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter NormedSpace
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [I.Boundaryless] in
theorem chartLeibnizRemainder_eq_firstDerivOnly
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      chartLeviCivitaGoodSet (I := I) α) :
    chartLeibnizRemainder (I := I) (M := M) g r s α T₀ Idx Jdx b =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
              (extDerivFun (I := I) (fun z : M =>
                  chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                    g α i k z) b
                  (chartBasisVecFiber (I := I) α l b)) *
              tensorChartComponentProjection (E := E) r s Idx Jdx
                ((trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                  ℝ b
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g))
                    (fun z : M => chartBasisVecFiber (I := I) α k z)
                    (fun z : M => T₀.toSection z) b)) := by
  classical
  set cov_RS := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_RS_def
  set triv := trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) α with htriv_def
  set proj : TensorRSSpace r s I b →L[ℝ] ℝ :=
    (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
      (triv.continuousLinearMapAt ℝ b) with hproj_def
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  have hb_pou : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := hb.1
  have hExpand := cov_RS_covApply_frameVec_eq_coord_expansion
    (I := I) (M := M) g r s α T₀
  unfold chartLeibnizRemainder chartFrameCoordMatrixWeightedDoubleSum
    chartInvGramPrincipalSum
  have hproj_lin_smul (c : ℝ) (v : TensorRSSpace r s I b) :
      proj (c • v) = c * proj v := by
    simp [hproj_def]
  have hproj_lin_add (v w : TensorRSSpace r s I b) :
      proj (v + w) = proj v + proj w := by
    simp [hproj_def]
  have hInner_rewrite (i l : Fin (Module.finrank ℝ E)) :
      proj ((cov_RS).toFun
            (covApply cov_RS
              (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
              (fun z : M => T₀.toSection z)) b
            (chartBasisVecFiber (I := I) α l b)) =
        (∑ k : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b *
            proj ((cov_RS).toFun
                (covApply cov_RS
                  (fun z : M => chartBasisVecFiber (I := I) α k z)
                  (fun z : M => T₀.toSection z)) b
                (chartBasisVecFiber (I := I) α l b))) +
        (∑ k : Fin (Module.finrank ℝ E),
          (extDerivFun (I := I) (fun z : M =>
              chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k z)
              b (chartBasisVecFiber (I := I) α l b)) *
            proj (covApply cov_RS
              (fun z : M => chartBasisVecFiber (I := I) α k z)
              (fun z : M => T₀.toSection z) b)) := by
    have h := hExpand (i := i) (b := b) hb_good l
    have hprojH := congrArg proj h
    rw [hproj_lin_add] at hprojH
    have hsum1 :
        proj (∑ k : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b •
              (cov_RS).toFun
                (covApply cov_RS
                  (fun z : M => chartBasisVecFiber (I := I) α k z)
                  (fun z : M => T₀.toSection z)) b
                (chartBasisVecFiber (I := I) α l b)) =
          ∑ k : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b *
              proj ((cov_RS).toFun
                  (covApply cov_RS
                    (fun z : M => chartBasisVecFiber (I := I) α k z)
                    (fun z : M => T₀.toSection z)) b
                  (chartBasisVecFiber (I := I) α l b)) := by
      rw [map_sum proj]
      refine Finset.sum_congr rfl ?_
      intro k _
      exact hproj_lin_smul _ _
    have hsum2 :
        proj (∑ k : Fin (Module.finrank ℝ E),
            (extDerivFun (I := I) (fun z : M =>
                chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                  g α i k z) b (chartBasisVecFiber (I := I) α l b)) •
              covApply cov_RS
                (fun z : M => chartBasisVecFiber (I := I) α k z)
                (fun z : M => T₀.toSection z) b) =
          ∑ k : Fin (Module.finrank ℝ E),
            (extDerivFun (I := I) (fun z : M =>
                chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                  g α i k z) b (chartBasisVecFiber (I := I) α l b)) *
              proj (covApply cov_RS
                (fun z : M => chartBasisVecFiber (I := I) α k z)
                (fun z : M => T₀.toSection z) b) := by
      rw [map_sum proj]
      refine Finset.sum_congr rfl ?_
      intro k _
      exact hproj_lin_smul _ _
    rw [hsum1, hsum2] at hprojH
    exact hprojH
  set Z₁ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ := fun i l k =>
    chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
      chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b *
      proj ((cov_RS).toFun
          (covApply cov_RS
            (fun z : M => chartBasisVecFiber (I := I) α k z)
            (fun z : M => T₀.toSection z)) b
          (chartBasisVecFiber (I := I) α l b)) with hZ₁_def
  set Z₂ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ := fun i l k =>
    chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
      (extDerivFun (I := I) (fun z : M =>
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k z) b
          (chartBasisVecFiber (I := I) α l b)) *
      proj (covApply cov_RS
        (fun z : M => chartBasisVecFiber (I := I) α k z)
        (fun z : M => T₀.toSection z) b) with hZ₂_def
  have hFrameDS_eq :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
            proj ((cov_RS).toFun
                (covApply cov_RS
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                  (fun z : M => T₀.toSection z)) b
                (chartBasisVecFiber (I := I) α l b)) =
        (∑ i, ∑ l, ∑ k, Z₁ i l k) + (∑ i, ∑ l, ∑ k, Z₂ i l k) := by
    have hper (i l : Fin (Module.finrank ℝ E)) :
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
          proj ((cov_RS).toFun
              (covApply cov_RS
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                (fun z : M => T₀.toSection z)) b
              (chartBasisVecFiber (I := I) α l b)) =
          (∑ k, Z₁ i l k) + (∑ k, Z₂ i l k) := by
      rw [hInner_rewrite i l]
      rw [mul_add]
      congr 1
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k _
        simp only [hZ₁_def]
        ring
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k _
        simp only [hZ₂_def]
        ring
    have hOuter :
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
              proj ((cov_RS).toFun
                  (covApply cov_RS
                    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                    (fun z : M => T₀.toSection z)) b
                  (chartBasisVecFiber (I := I) α l b)) =
          ∑ i, ∑ l, ((∑ k, Z₁ i l k) + (∑ k, Z₂ i l k)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro l _
      exact hper i l
    rw [hOuter]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ((∑ k, Z₁ i l k) + (∑ k, Z₂ i l k))) =
        (∑ i, ∑ l, ∑ k, Z₁ i l k) + (∑ i, ∑ l, ∑ k, Z₂ i l k) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]]
  have hOrtho (k l : Fin (Module.finrank ℝ E)) :
      ∑ i : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
              g α i k b =
        chartInvGramMatrix (I := I) g α b k l := by
    have h := chartFrameNormGlobalSmoothCoordMatrix_orthonormality
      (I := I) (M := M) g α (b := b) hb_pou hb_good k l
    rw [← h]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have hPrincipal_collapse :
      (∑ i : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E), Z₁ i l k) =
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b k l *
              tensorChartComponentProjection (E := E) r s Idx Jdx
                ((trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                  ℝ b
                  ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g)).toFun
                    (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g))
                      (chartBasisVecFiber (I := I) α k)
                      (fun z : M => T₀.toSection z)) b
                    (chartBasisVecFiber (I := I) α l b))) := by
    have hZ₁_factor (i l k : Fin (Module.finrank ℝ E)) :
        Z₁ i l k =
          (chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
              g α i k b) *
            proj ((cov_RS).toFun
                (covApply cov_RS
                  (fun z : M => chartBasisVecFiber (I := I) α k z)
                  (fun z : M => T₀.toSection z)) b
                (chartBasisVecFiber (I := I) α l b)) := by
      simp only [hZ₁_def]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E), Z₁ i l k) =
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ∑ i : Fin (Module.finrank ℝ E), Z₁ i l k) from by
      have h1 :
          (∑ i : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E), Z₁ i l k) =
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E), Z₁ i l k) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.sum_comm]
      have h2 :
          (∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E), Z₁ i l k) =
            (∑ k : Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E), Z₁ i l k) := by
        rw [Finset.sum_comm]
      have h3 :
          (∑ k : Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E), Z₁ i l k) =
            (∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ i : Fin (Module.finrank ℝ E), Z₁ i l k) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.sum_comm]
      rw [h1, h2, h3]]
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    have hFactor :
        ∑ i : Fin (Module.finrank ℝ E), Z₁ i l k =
          (∑ i : Fin (Module.finrank ℝ E),
              chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                g α i l b *
              chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                g α i k b) *
            proj ((cov_RS).toFun
                (covApply cov_RS
                  (fun z : M => chartBasisVecFiber (I := I) α k z)
                  (fun z : M => T₀.toSection z)) b
                (chartBasisVecFiber (I := I) α l b)) := by
      rw [Finset.sum_mul]
    rw [hFactor]
    rw [hOrtho]
    simp only [hproj_def, htriv_def, hcov_RS_def, ContinuousLinearMap.coe_comp',
      Function.comp_apply]
  have hCross_collapse :
      (∑ i : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E), Z₂ i l k) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                g α i l b *
                (extDerivFun (I := I) (fun z : M =>
                    chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                      g α i k z) b
                    (chartBasisVecFiber (I := I) α l b)) *
                tensorChartComponentProjection (E := E) r s Idx Jdx
                  ((trivializationAt (TensorRSModel r s ℝ E)
                      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                    (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g))
                      (fun z : M => chartBasisVecFiber (I := I) α k z)
                      (fun z : M => T₀.toSection z) b)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro l _
    refine Finset.sum_congr rfl ?_
    intro k _
    simp only [hZ₂_def, hproj_def, htriv_def, hcov_RS_def,
      ContinuousLinearMap.coe_comp', Function.comp_apply]
  change (∑ i : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
            tensorChartComponentProjection (E := E) r s Idx Jdx
              ((trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                ℝ b
                ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)).toFun
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g))
                    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                    (fun z : M => T₀.toSection z)) b
                  (chartBasisVecFiber (I := I) α l b)))) -
      (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b k l *
            tensorChartComponentProjection (E := E) r s Idx Jdx
              ((trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                ℝ b
                ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)).toFun
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g))
                    (chartBasisVecFiber (I := I) α k)
                    (fun z : M => T₀.toSection z)) b
                  (chartBasisVecFiber (I := I) α l b)))) = _
  have hFrameDS_eq' :
      (∑ i : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
              tensorChartComponentProjection (E := E) r s Idx Jdx
                ((trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                  ℝ b
                  ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g)).toFun
                    (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g))
                      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                      (fun z : M => T₀.toSection z)) b
                    (chartBasisVecFiber (I := I) α l b)))) =
        (∑ i, ∑ l, ∑ k, Z₁ i l k) + (∑ i, ∑ l, ∑ k, Z₂ i l k) := by
    have hRewrite :
        (∑ i : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                g α i l b *
                tensorChartComponentProjection (E := E) r s Idx Jdx
                  ((trivializationAt (TensorRSModel r s ℝ E)
                      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                    ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                        (LeviCivita (I := I) g)).toFun
                      (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                        (LeviCivita (I := I) g))
                        (chartFrameNormGlobalSmooth (I := I) (M := M)
                          g α i).toFun
                        (fun z : M => T₀.toSection z)) b
                      (chartBasisVecFiber (I := I) α l b)))) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                g α i l b *
                proj ((cov_RS).toFun
                    (covApply cov_RS
                      (chartFrameNormGlobalSmooth (I := I) (M := M)
                        g α i).toFun
                      (fun z : M => T₀.toSection z)) b
                    (chartBasisVecFiber (I := I) α l b))) := by
      simp only [hproj_def, htriv_def, hcov_RS_def, ContinuousLinearMap.coe_comp',
        Function.comp_apply]
    rw [hRewrite]
    exact hFrameDS_eq
  rw [hFrameDS_eq']
  rw [← hPrincipal_collapse]
  rw [← hCross_collapse]
  ring

end Connection
end Integral
end DifferentialGeometry

end
