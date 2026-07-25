import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedStep
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHSMemW1p

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma eigenvectorChartComponentFun_memWkp_of_pou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) N 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) N 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_res : MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      Ω :=
    h_pou α P₀
  have h_chart_eq := eigenvector_chartComponent_eq (I := I) (M := M)
    g r s i α P₀
  have h_ae : (eigenvectorChartComponentFun (I := I) (M := M)
        g r s i α P₀)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    have h_smul := Lp.coeFn_smul (i.fst.val)⁻¹
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α P₀)
    rw [← h_chart_eq] at h_smul
    filter_upwards [h_smul] with y hy
    change ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = _
    rw [hy, Pi.smul_apply, smul_eq_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_res (i.fst.val)⁻¹)

omit [CompleteSpace E] in
lemma eigenvectorChartRHSDiff_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)) :
    eigenvectorChartRHSDiff (I := I) (M := M) g r s i α P₀ m l
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  cases m with
  | zero =>
      rw [eigenvectorChartRHSDiff_zero]
      exact eigenvectorChartRHS_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀
  | succ m =>
      have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α) :=
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet.diff
          (chartPouKernel_measurableSet (I := I) (M := M) α)
      rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      exact eigenvectorChartRHSDiff_succ_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ m l hy.2

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem exists_eigenvectorIteratedCarrier
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (j : ℕ), j < m → ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (j + 2) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ D : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
        g r s i α P₀ m,
      D.directions = directions ∧
      D.diffChartForcing =
        eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ m directions := by
  classical
  induction m with
  | zero =>
      refine ⟨eigenvectorIteratedTensorChartBilinearData.ofBase
        (I := I) (M := M) g r s i α P₀, ?_, ?_⟩
      · exact Subsingleton.elim _ _
      · rw [eigenvectorChartRHSDiff_zero]
        rfl
  | succ m ih =>
      have h_pou_prev : ∀ (j : ℕ), j < m → ∀ (β : M)
          (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (j + 2) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) :=
        fun j hj => h_pou j (hj.trans (Nat.lt_succ_self m))
      obtain ⟨D_m, hD_m_dirs, hD_m_fChartEff⟩ :=
        ih (Fin.init directions) h_pou_prev
      set l : Fin (Module.finrank ℝ E) := directions (Fin.last m) with hl_def
      have h_comp_m1 : MemWkp (d := Module.finrank ℝ E) (m + 1) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) := by
        have h_pou_m : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
            MemWkp (d := Module.finrank ℝ E) (m + 2) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β) :=
          h_pou m (Nat.lt_succ_self m)
        have h_comp_m2 : MemWkp (d := Module.finrank ℝ E) (m + 2) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) :=
          eigenvectorChartComponentFun_memWkp_of_pou (I := I) (M := M)
            g r s i (m + 2) h_pou_m α P₀
        exact MemWkp.le_of_le (d := Module.finrank ℝ E)
          (by omega : m + 1 ≤ m + 2) h_comp_m2
      have h_comp_m2 : MemWkp (d := Module.finrank ℝ E) (m + 2) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) :=
        eigenvectorChartComponentFun_memWkp_of_pou (I := I) (M := M)
          g r s i (m + 2) (h_pou m (Nat.lt_succ_self m)) α P₀
      have h_fChartEff_memW1p :
          DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 D_m.diffChartForcing
            (chartTargetEuclid (I := I) (M := M) α) := by
        rw [hD_m_fChartEff]
        exact eigenvectorChartRHSDiff_memW1p (I := I) (M := M)
          g r s i α P₀ m (Fin.init directions)
          (h_pou m (Nat.lt_succ_self m))
      have h_fChartEff_ae_zero :
          D_m.diffChartForcing =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)]
            (fun _ : EuclN => (0 : ℝ)) := by
        rw [hD_m_fChartEff]
        exact eigenvectorChartRHSDiff_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ m (Fin.init directions)
      refine ⟨eigenvectorIteratedTensorChartBilinearData_step
        (I := I) (M := M) g r s i α P₀ D_m l
        h_comp_m1 h_comp_m2 h_fChartEff_memW1p h_fChartEff_ae_zero, ?_, ?_⟩
      · change Fin.snoc D_m.directions l = directions
        rw [hD_m_dirs, hl_def]
        exact Fin.snoc_init_self directions
      · change eigenvectorChartIteratedStep (I := I) (M := M)
            g r s i α P₀ m D_m.directions D_m.diffChartForcing l =
          eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ (m + 1) directions
        rw [hD_m_dirs, hD_m_fChartEff]
        rw [eigenvectorChartIteratedStep_eq_rhsDiff_succ
          (I := I) (M := M) g r s i α P₀ m (Fin.init directions) l]
        rw [hl_def, Fin.snoc_init_self directions]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
