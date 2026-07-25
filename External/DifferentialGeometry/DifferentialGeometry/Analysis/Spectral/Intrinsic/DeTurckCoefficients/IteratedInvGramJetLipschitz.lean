import DifferentialGeometry.Analysis.Calculus.IteratedFDerivSeminormCalculus
import DifferentialGeometry.Analysis.Calculus.PartialDerivIteratedFDerivOrderBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartRicciStructuralDifference


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set Matrix
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartGramJetDiffSeminormSum (N : ℕ) (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (s : Set E) (y : E) : ℝ :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    iteratedFDerivSeminorm N
      (fun z => chartGramOnE (I := I) g₁ α a b z - chartGramOnE (I := I) g₂ α a b z) s y

omit [NeZero (Module.finrank ℝ E)] in
lemma chartGramJetDiffSeminormSum_nonneg (N : ℕ)
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (s : Set E) (y : E) :
    0 ≤ chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α s y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    iteratedFDerivSeminorm_nonneg _ _ _ _

omit [NeZero (Module.finrank ℝ E)] in
lemma chartGramJetDiffSeminormSum_mono {N N' : ℕ} (hN : N ≤ N')
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (s : Set E) (y : E) :
    chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α s y ≤
      chartGramJetDiffSeminormSum (I := I) (M := M) N' g₁ g₂ α s y := by
  classical
  unfold chartGramJetDiffSeminormSum
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  exact iteratedFDerivSeminorm_mono hN _ _ _

omit [NeZero (Module.finrank ℝ E)] in
lemma iteratedFDerivSeminorm_gramDiff_le_sum (N : ℕ)
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (s : Set E) (y : E)
    (a b : Fin (Module.finrank ℝ E)) :
    iteratedFDerivSeminorm N
        (fun z => chartGramOnE (I := I) g₁ α a b z - chartGramOnE (I := I) g₂ α a b z) s y ≤
      chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α s y := by
  classical
  have hb : iteratedFDerivSeminorm N
        (fun z => chartGramOnE (I := I) g₁ α a b z - chartGramOnE (I := I) g₂ α a b z) s y ≤
      ∑ b' : Fin (Module.finrank ℝ E), iteratedFDerivSeminorm N
        (fun z => chartGramOnE (I := I) g₁ α a b' z - chartGramOnE (I := I) g₂ α a b' z) s y :=
    Finset.single_le_sum
      (f := fun b' => iteratedFDerivSeminorm N
        (fun z => chartGramOnE (I := I) g₁ α a b' z - chartGramOnE (I := I) g₂ α a b' z) s y)
      (fun _ _ => iteratedFDerivSeminorm_nonneg _ _ _ _) (Finset.mem_univ b)
  refine hb.trans ?_
  exact Finset.single_le_sum
    (f := fun a' => ∑ b' : Fin (Module.finrank ℝ E), iteratedFDerivSeminorm N
      (fun z => chartGramOnE (I := I) g₁ α a' b' z - chartGramOnE (I := I) g₂ α a' b' z) s y)
    (fun _ _ => Finset.sum_nonneg fun _ _ => iteratedFDerivSeminorm_nonneg _ _ _ _)
    (Finset.mem_univ a)

omit [NeZero (Module.finrank ℝ E)] in
lemma chartInvGramOnE_contDiffOn_int
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α k l)
      (interior (extChartAt I α).target) :=
  (chartInvGramOnE_contDiffOn (I := I) g α k l).mono interior_subset

omit [NeZero (Module.finrank ℝ E)] in
lemma chartGramOnE_contDiffOn_int
    (g : SmoothRiemannianMetric I M) (α : M)
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α a b)
      (interior (extChartAt I α).target) :=
  (chartGramOnE_contDiffOn (I := I) g α a b).mono interior_subset

theorem exists_chartInvGramOnE_iteratedFDeriv_lipschitz_on_compact
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ k l : Fin (Module.finrank ℝ E),
      ‖iteratedFDerivWithin ℝ N
          (fun z => chartInvGramOnE (I := I) g₁ α k l z -
            chartInvGramOnE (I := I) g₂ α k l z)
          (interior (extChartAt I α).target) y‖ ≤
        C * chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α
          (interior (extChartAt I α).target) y := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  have hs_open : IsOpen s := isOpen_interior
  have hbound_prod : ∀ (g₁' g₂' : SmoothRiemannianMetric I M)
      (k p q l : Fin (Module.finrank ℝ E)),
      ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ K, ∀ m : ℕ, m ≤ N →
        ‖iteratedFDerivWithin ℝ m
            (fun z => chartInvGramOnE (I := I) g₁' α k p z *
              chartInvGramOnE (I := I) g₂' α q l z) s y‖ ≤ B := by
    intro g₁' g₂' k p q l
    exact exists_uniform_iteratedFDerivWithin_bound_of_contDiffOn hs_open
      (ContDiffOn.mul (chartInvGramOnE_contDiffOn_int (I := I) g₁' α k p)
        (chartInvGramOnE_contDiffOn_int (I := I) g₂' α q l)) hK hKsub N
  choose Bprod hBprod_nn hBprod using hbound_prod
  set Bmax : ℝ := (Finset.univ : Finset
      (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E))).sup'
    (by exact Finset.univ_nonempty) (fun w => Bprod g₁ g₂ w.1 w.2.1 w.2.2.1 w.2.2.2) with hBmax_def
  have hBmax_nn : 0 ≤ Bmax := by
    obtain ⟨w₀⟩ := (inferInstance :
      Nonempty (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)))
    refine le_trans (hBprod_nn g₁ g₂ w₀.1 w₀.2.1 w₀.2.2.1 w₀.2.2.2) ?_
    exact Finset.le_sup' (fun w => Bprod g₁ g₂ w.1 w.2.1 w.2.2.1 w.2.2.2)
      (Finset.mem_univ w₀)
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * (2 ^ N * Bmax) + 1, ?_, ?_⟩
  · have h_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (2 ^ N * Bmax) := by positivity
    linarith
  intro y hy k l
  have hyS : y ∈ s := hKsub hy
  have hEqOn : EqOn
      (fun z => chartInvGramOnE (I := I) g₁ α k l z - chartInvGramOnE (I := I) g₂ α k l z)
      (fun z => ∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₁ α k p z *
          (chartGramOnE (I := I) g₂ α p q z - chartGramOnE (I := I) g₁ α p q z) *
          chartInvGramOnE (I := I) g₂ α q l z) s := by
    intro z hz
    exact invGramOnE_sub_eq (I := I) (M := M) g₁ g₂ α k l hz
  rw [iteratedFDerivWithin_congr hEqOn hyS N]
  have hcd_qp : ∀ q p : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun z => chartInvGramOnE (I := I) g₁ α k p z *
        (chartGramOnE (I := I) g₂ α p q z - chartGramOnE (I := I) g₁ α p q z) *
        chartInvGramOnE (I := I) g₂ α q l z) s := by
    intro q p
    refine ((chartInvGramOnE_contDiffOn_int (I := I) g₁ α k p).mul
      ((chartGramOnE_contDiffOn_int (I := I) g₂ α p q).sub
        (chartGramOnE_contDiffOn_int (I := I) g₁ α p q))).mul
      (chartInvGramOnE_contDiffOn_int (I := I) g₂ α q l)
  have hcd_q : ∀ q : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun z => ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₁ α k p z *
          (chartGramOnE (I := I) g₂ α p q z - chartGramOnE (I := I) g₁ α p q z) *
          chartInvGramOnE (I := I) g₂ α q l z) s := by
    intro q
    exact ContDiffOn.sum fun p _ => hcd_qp q p
  refine (norm_iteratedFDerivWithin_sum_le hs_open Finset.univ
    (fun q _ => hcd_q q) N hyS).trans ?_
  have hterm_q : ∀ q : Fin (Module.finrank ℝ E),
      ‖iteratedFDerivWithin ℝ N (fun z => ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g₁ α k p z *
            (chartGramOnE (I := I) g₂ α p q z - chartGramOnE (I := I) g₁ α p q z) *
            chartInvGramOnE (I := I) g₂ α q l z) s y‖ ≤
        ∑ p : Fin (Module.finrank ℝ E),
          2 ^ N * Bmax *
            chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α s y := by
    intro q
    refine (norm_iteratedFDerivWithin_sum_le hs_open Finset.univ
      (fun p _ => hcd_qp q p) N hyS).trans ?_
    refine Finset.sum_le_sum fun p _ => ?_
    have hassoc : (fun z => chartInvGramOnE (I := I) g₁ α k p z *
          (chartGramOnE (I := I) g₂ α p q z - chartGramOnE (I := I) g₁ α p q z) *
          chartInvGramOnE (I := I) g₂ α q l z) =
        (fun z => (chartGramOnE (I := I) g₂ α p q z - chartGramOnE (I := I) g₁ α p q z) *
          (chartInvGramOnE (I := I) g₁ α k p z * chartInvGramOnE (I := I) g₂ α q l z)) := by
      funext z; ring
    rw [hassoc]
    have hbnd := norm_iteratedFDerivWithin_mul_le_uniformBound (s := s) hs_open
      ((chartGramOnE_contDiffOn_int (I := I) g₂ α p q).sub
        (chartGramOnE_contDiffOn_int (I := I) g₁ α p q))
      ((chartInvGramOnE_contDiffOn_int (I := I) g₁ α k p).mul
        (chartInvGramOnE_contDiffOn_int (I := I) g₂ α q l))
      hKsub (hBmax_nn) N
      (fun y' hy' m hm => le_trans (hBprod g₁ g₂ k p q l y' hy' m hm)
        (Finset.le_sup' (fun w => Bprod g₁ g₂ w.1 w.2.1 w.2.2.1 w.2.2.2)
          (Finset.mem_univ ((k, p, q, l) :
            Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)))))
      hy
    refine hbnd.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [iteratedFDerivSeminorm_sub_comm hs_open.uniqueDiffOn hyS N]
    exact iteratedFDerivSeminorm_gramDiff_le_sum (I := I) (M := M) N g₁ g₂ α s y p q
  refine (Finset.sum_le_sum fun q _ => hterm_q q).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h_nn_sem : 0 ≤ chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α s y :=
    chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) N g₁ g₂ α s y
  calc (Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) *
            (2 ^ N * Bmax * chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α s y))
      = (Module.finrank ℝ E : ℝ) ^ 2 * (2 ^ N * Bmax) *
          chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α s y := by ring
    _ ≤ ((Module.finrank ℝ E : ℝ) ^ 2 * (2 ^ N * Bmax) + 1) *
          chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α s y := by
        refine mul_le_mul_of_nonneg_right ?_ h_nn_sem
        linarith

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
