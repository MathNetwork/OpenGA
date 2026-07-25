import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.ChartGramUniformContinuity
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorChartComponentSobolevBound
import DifferentialGeometry.Geometry.Metric.MetricBounds
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartTensor0SCovariantDerivative
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartMetric
import DifferentialGeometry.Analysis.Integration.Measure.Properties


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HebeyBlock

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma trivFromE_apply_eq_zero_of_notMem_baseSet
    (α : M) {b : M} (hb : b ∉ (trivializationAt E (TangentSpace I) α).baseSet)
    (w : E) :
    trivFromE (I := I) α b w = 0 := by
  classical
  change (trivializationAt E (TangentSpace I) α).symmL ℝ b w = 0
  rw [Bundle.Trivialization.symmL_apply]
  exact Bundle.Trivialization.symm_apply_of_notMem
    (trivializationAt E (TangentSpace I) α) hb w

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartLeviCivitaParallelCLM_apply_eq_zero_of_notMem_baseSet
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∉ (trivializationAt E (TangentSpace I) α).baseSet)
    (X : Π b' : M, TangentSpace I b') (v : TangentSpace I b) :
    chartLeviCivitaParallelCLM (I := I) g α b X v = 0 := by
  classical
  rw [chartLeviCivitaParallelCLM_apply]
  exact trivFromE_apply_eq_zero_of_notMem_baseSet (I := I) α hb _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma trivToE_chartBasisVecFiber_eq_chartModelBasis
    (α : M) (m : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    trivToE (I := I) α b (chartBasisVecFiber (I := I) α m b) =
      (chartModelBasis E) m := by
  classical
  change trivToE (I := I) α b
      (trivFromE (I := I) α b (chartModelBasis E m)) = _
  exact trivToE_trivFromE (I := I) α hb _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartLeviCivitaParallelCLM_chartBasisVec_apply_chartBasisVec_eq_sum
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (k m : Fin (Module.finrank ℝ E)) :
    chartLeviCivitaParallelCLM (I := I) g α b
        (chartBasisVecFiber (I := I) α m)
        (chartBasisVecFiber (I := I) α k b) =
      ∑ p : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α k m p (extChartAt I α b) •
          chartBasisVecFiber (I := I) α p b := by
  classical
  rw [chartLeviCivitaParallelCLM_apply]
  have hX_id :
      trivToE (I := I) α b (chartBasisVecFiber (I := I) α m b) =
        (chartModelBasis E) m :=
    trivToE_chartBasisVecFiber_eq_chartModelBasis (I := I) α m hb
  have hv_id :
      trivToE (I := I) α b (chartBasisVecFiber (I := I) α k b) =
        (chartModelBasis E) k :=
    trivToE_chartBasisVecFiber_eq_chartModelBasis (I := I) α k hb
  rw [christoffelCorrection_apply]
  rw [hv_id, hX_id]
  have hrepr_v : ∀ i : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr (chartModelBasis E k)) i =
        if i = k then (1 : ℝ) else 0 := by
    intro i
    rw [Module.Basis.repr_self]
    by_cases hi : i = k
    · subst hi; simp
    · simp [hi]
  have hrepr_Y : ∀ j : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr (chartModelBasis E m)) j =
        if j = m then (1 : ℝ) else 0 := by
    intro j
    rw [Module.Basis.repr_self]
    by_cases hj : j = m
    · subst hj; simp
    · simp [hj]
  rw [map_sum]
  have h_outer :
      ∀ i : Fin (Module.finrank ℝ E),
        trivFromE (I := I) α b
            (∑ j : Fin (Module.finrank ℝ E),
              ∑ p : Fin (Module.finrank ℝ E),
                (((chartModelBasis E).repr (chartModelBasis E k)) i *
                    ((chartModelBasis E).repr (chartModelBasis E m)) j *
                    chartChristoffel (I := I) g α i j p
                      (extChartAt I α b)) •
                  (chartModelBasis E) p) =
          (if i = k then
              ∑ p : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) g α k m p (extChartAt I α b) •
                  trivFromE (I := I) α b ((chartModelBasis E) p)
            else 0) := by
    intro i
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl]
      rw [map_sum]
      have hj_eq :
          ∀ j : Fin (Module.finrank ℝ E),
            trivFromE (I := I) α b
                (∑ p : Fin (Module.finrank ℝ E),
                  (((chartModelBasis E).repr (chartModelBasis E i)) i *
                      ((chartModelBasis E).repr (chartModelBasis E m)) j *
                      chartChristoffel (I := I) g α i j p
                        (extChartAt I α b)) •
                    (chartModelBasis E) p) =
              (if j = m then
                  ∑ p : Fin (Module.finrank ℝ E),
                    chartChristoffel (I := I) g α i m p
                        (extChartAt I α b) •
                      trivFromE (I := I) α b ((chartModelBasis E) p)
                else 0) := by
        intro j
        by_cases hjm : j = m
        · subst hjm
          rw [if_pos rfl]
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [map_smul]
          rw [hrepr_v i, hrepr_Y j]
          simp
        · rw [if_neg hjm]
          rw [map_sum]
          have h_sum_zero :
              (∑ p : Fin (Module.finrank ℝ E),
                  trivFromE (I := I) α b
                    ((((chartModelBasis E).repr (chartModelBasis E i)) i *
                        ((chartModelBasis E).repr (chartModelBasis E m)) j *
                        chartChristoffel (I := I) g α i j p
                          (extChartAt I α b)) •
                      (chartModelBasis E) p)) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro p _
            rw [map_smul]
            rw [hrepr_Y j, if_neg hjm]
            simp
          exact h_sum_zero
      rw [Finset.sum_congr rfl (fun j _ => hj_eq j)]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · rw [if_neg hik]
      rw [map_sum]
      refine Finset.sum_eq_zero ?_
      intro j _
      rw [map_sum]
      refine Finset.sum_eq_zero ?_
      intro p _
      rw [map_smul]
      rw [hrepr_v i, if_neg hik]
      simp
  rw [Finset.sum_congr rfl (fun i _ => h_outer i)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl ?_
  intro p _
  rfl

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma g_inner_sum_smul_chartBasisVec_self_eq_double_sum
    (g : SmoothRiemannianMetric I M) (α : M) (b : M)
    (a : Fin (Module.finrank ℝ E) → ℝ) :
    g.inner b (∑ p : Fin (Module.finrank ℝ E),
                  a p • chartBasisVecFiber (I := I) α p b)
            (∑ q : Fin (Module.finrank ℝ E),
                  a q • chartBasisVecFiber (I := I) α q b) =
      ∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
          a p * a q * chartGramMatrix (I := I) g α b p q := by
  classical
  have h_left :
      g.inner b (∑ p, a p • chartBasisVecFiber (I := I) α p b) =
        ∑ p, a p • g.inner b (chartBasisVecFiber (I := I) α p b) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [map_smul]
  rw [h_left]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  rw [map_smul, smul_eq_mul]
  rw [g_inner_eq_chartGramMatrix_basis (I := I) g α b p q]
  ring

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma g_inner_Phi_eq_double_sum
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (k : Fin (Module.finrank ℝ E)) :
    g.inner b
        (chartLeviCivitaParallelCLM (I := I) g α b
          (chartBasisVecFiber (I := I) α k)
          (chartBasisVecFiber (I := I) α k b))
        (chartLeviCivitaParallelCLM (I := I) g α b
          (chartBasisVecFiber (I := I) α k)
          (chartBasisVecFiber (I := I) α k b)) =
      ∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α k k p (extChartAt I α b) *
            chartChristoffel (I := I) g α k k q (extChartAt I α b) *
            chartGramMatrix (I := I) g α b p q := by
  classical
  rw [chartLeviCivitaParallelCLM_chartBasisVec_apply_chartBasisVec_eq_sum
      (I := I) (M := M) g α hb_base k k]
  exact g_inner_sum_smul_chartBasisVec_self_eq_double_sum (I := I) (M := M) g α b
    (fun p => chartChristoffel (I := I) g α k k p (extChartAt I α b))

private theorem g_inner_chartLeviCivitaParallelCLM_chartBasisVec_self_le_const_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ b : M,
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        g.inner b
            (chartLeviCivitaParallelCLM (I := I) g α b
              (chartBasisVecFiber (I := I) α k)
              (chartBasisVecFiber (I := I) α k b))
            (chartLeviCivitaParallelCLM (I := I) g α b
              (chartBasisVecFiber (I := I) α k)
              (chartBasisVecFiber (I := I) α k b)) ≤ K := by
  classical
  obtain ⟨CΓ, hCΓ_nn, hCΓ_le⟩ :=
    chartChristoffel_bdd_on_pou_tsupport (I := I) (M := M) g α
  set K_M : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_M_def
  have hK_M_compact : IsCompact K_M :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_isCompact
      (I := I) (M := M) α
  have hK_M_sub : K_M ⊆ (chartAt H α).source := by
    intro b hb
    exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α hb
  have h_gram_each : ∀ p q : Fin (Module.finrank ℝ E),
      ∃ Cpq : ℝ, 0 < Cpq ∧ ∀ b ∈ K_M,
        |chartGramMatrix (I := I) g α b p q| ≤ Cpq := by
    intro p q
    exact
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramMatrix_entry_isBounded_on_compact
        (I := I) (M := M) g α p q hK_M_compact hK_M_sub
  choose Cpq_fn hCpq_pos hCpq_le using h_gram_each
  set s : Finset (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) :=
    Finset.univ with hs_def
  have hs_ne : s.Nonempty := by
    refine Finset.univ_nonempty_iff.mpr ?_
    have : Nonempty (Fin (Module.finrank ℝ E)) :=
      ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
    exact ⟨⟨this.some, this.some⟩⟩
  set C_G : ℝ := s.sup' hs_ne (fun pq => Cpq_fn pq.1 pq.2) with hC_G_def
  have hC_G_nn : 0 ≤ C_G := by
    obtain ⟨pq₀, hpq₀_mem⟩ := hs_ne
    refine (hCpq_pos pq₀.1 pq₀.2).le.trans ?_
    exact Finset.le_sup' (fun pq => Cpq_fn pq.1 pq.2) hpq₀_mem
  have hC_G_bd : ∀ p q : Fin (Module.finrank ℝ E), ∀ b ∈ K_M,
      |chartGramMatrix (I := I) g α b p q| ≤ C_G := by
    intro p q b hb
    refine (hCpq_le p q b hb).trans ?_
    have hpq_mem : (p, q) ∈ s := Finset.mem_univ _
    exact Finset.le_sup' (fun pq => Cpq_fn pq.1 pq.2) hpq_mem
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * CΓ ^ 2 * C_G, by positivity, ?_⟩
  intro b hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
    exact hK_M_sub hb
  have hb_in_chartImage :
      extChartAt I α b ∈ (extChartAt I α) '' K_M := by
    exact ⟨b, hb, rfl⟩
  have hCΓ_at : ∀ i j p : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g α i j p (extChartAt I α b)| ≤ CΓ :=
    fun i j p => hCΓ_le (extChartAt I α b) hb_in_chartImage i j p
  rw [g_inner_Phi_eq_double_sum (I := I) (M := M) g α hb_base k]
  have h_tri :
      |∑ p : Fin (Module.finrank ℝ E),
          ∑ q : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k k p (extChartAt I α b) *
              chartChristoffel (I := I) g α k k q (extChartAt I α b) *
              chartGramMatrix (I := I) g α b p q| ≤
        ∑ p : Fin (Module.finrank ℝ E),
          ∑ q : Fin (Module.finrank ℝ E),
            |chartChristoffel (I := I) g α k k p (extChartAt I α b) *
              chartChristoffel (I := I) g α k k q (extChartAt I α b) *
              chartGramMatrix (I := I) g α b p q| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun p _ => Finset.abs_sum_le_sum_abs _ _))
  have h_per : ∀ p q : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g α k k p (extChartAt I α b) *
        chartChristoffel (I := I) g α k k q (extChartAt I α b) *
        chartGramMatrix (I := I) g α b p q| ≤ CΓ * CΓ * C_G := by
    intro p q
    have hΓp := hCΓ_at k k p
    have hΓq := hCΓ_at k k q
    have hG := hC_G_bd p q b hb
    have h_abs :
        |chartChristoffel (I := I) g α k k p (extChartAt I α b) *
          chartChristoffel (I := I) g α k k q (extChartAt I α b) *
          chartGramMatrix (I := I) g α b p q| =
        |chartChristoffel (I := I) g α k k p (extChartAt I α b)| *
          |chartChristoffel (I := I) g α k k q (extChartAt I α b)| *
          |chartGramMatrix (I := I) g α b p q| := by
      rw [abs_mul, abs_mul]
    rw [h_abs]
    have hΓq_nn : 0 ≤ |chartChristoffel (I := I) g α k k q (extChartAt I α b)| :=
      abs_nonneg _
    have hG_nn : 0 ≤ |chartGramMatrix (I := I) g α b p q| := abs_nonneg _
    have hΓp_nn : 0 ≤ |chartChristoffel (I := I) g α k k p (extChartAt I α b)| :=
      abs_nonneg _
    have h_step1 :
        |chartChristoffel (I := I) g α k k p (extChartAt I α b)| *
          |chartChristoffel (I := I) g α k k q (extChartAt I α b)| ≤
        CΓ * CΓ :=
      mul_le_mul hΓp hΓq hΓq_nn hCΓ_nn
    have h_step1_nn : 0 ≤ CΓ * CΓ := mul_nonneg hCΓ_nn hCΓ_nn
    have h_lhs_nn :
        0 ≤ |chartChristoffel (I := I) g α k k p (extChartAt I α b)| *
              |chartChristoffel (I := I) g α k k q (extChartAt I α b)| :=
      mul_nonneg hΓp_nn hΓq_nn
    have h_step2 :
        (|chartChristoffel (I := I) g α k k p (extChartAt I α b)| *
            |chartChristoffel (I := I) g α k k q (extChartAt I α b)|) *
          |chartGramMatrix (I := I) g α b p q| ≤
        (CΓ * CΓ) * C_G :=
      mul_le_mul h_step1 hG hG_nn h_step1_nn
    exact h_step2
  have h_dbl_sum_le :
      (∑ p : Fin (Module.finrank ℝ E),
          ∑ q : Fin (Module.finrank ℝ E),
            |chartChristoffel (I := I) g α k k p (extChartAt I α b) *
              chartChristoffel (I := I) g α k k q (extChartAt I α b) *
              chartGramMatrix (I := I) g α b p q|) ≤
        (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (CΓ * CΓ * C_G)) := by
    have h_inner_sum_le : ∀ p : Fin (Module.finrank ℝ E),
        (∑ q : Fin (Module.finrank ℝ E),
            |chartChristoffel (I := I) g α k k p (extChartAt I α b) *
              chartChristoffel (I := I) g α k k q (extChartAt I α b) *
              chartGramMatrix (I := I) g α b p q|) ≤
          (Module.finrank ℝ E : ℝ) * (CΓ * CΓ * C_G) := by
      intro p
      have h_le :=
        Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
          (f := fun q =>
            |chartChristoffel (I := I) g α k k p (extChartAt I α b) *
              chartChristoffel (I := I) g α k k q (extChartAt I α b) *
              chartGramMatrix (I := I) g α b p q|)
          (g := fun _ => CΓ * CΓ * C_G)
          (fun q _ => h_per p q)
      have h_const :
          (∑ _q : Fin (Module.finrank ℝ E), CΓ * CΓ * C_G) =
            (Module.finrank ℝ E : ℝ) * (CΓ * CΓ * C_G) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp [nsmul_eq_mul]
      linarith
    have h_outer_sum_le :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
        (f := fun p =>
          ∑ q : Fin (Module.finrank ℝ E),
            |chartChristoffel (I := I) g α k k p (extChartAt I α b) *
              chartChristoffel (I := I) g α k k q (extChartAt I α b) *
              chartGramMatrix (I := I) g α b p q|)
        (g := fun _ => (Module.finrank ℝ E : ℝ) * (CΓ * CΓ * C_G))
        (fun p _ => h_inner_sum_le p)
    have h_const_outer :
        (∑ _p : Fin (Module.finrank ℝ E), (Module.finrank ℝ E : ℝ) * (CΓ * CΓ * C_G)) =
          (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (CΓ * CΓ * C_G)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    linarith
  have h_abs_le_self :
      ∑ p : Fin (Module.finrank ℝ E),
          ∑ q : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k k p (extChartAt I α b) *
              chartChristoffel (I := I) g α k k q (extChartAt I α b) *
              chartGramMatrix (I := I) g α b p q ≤
        |∑ p : Fin (Module.finrank ℝ E),
            ∑ q : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g α k k p (extChartAt I α b) *
                chartChristoffel (I := I) g α k k q (extChartAt I α b) *
                chartGramMatrix (I := I) g α b p q| := le_abs_self _
  have h_chain := h_abs_le_self.trans (h_tri.trans h_dbl_sum_le)
  have h_arith :
      (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (CΓ * CΓ * C_G)) =
        (Module.finrank ℝ E : ℝ) ^ 2 * CΓ ^ 2 * C_G := by ring
  linarith

private theorem chartAtlasPOU_mul_sqrt_g_inner_Phi_le_sqrt_const_globally
    (g : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ b : M,
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            Real.sqrt
              (g.inner b
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α k)
                  (chartBasisVecFiber (I := I) α k b))
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α k)
                  (chartBasisVecFiber (I := I) α k b))) ≤ Real.sqrt K := by
  classical
  obtain ⟨K, hK_nn, h_pt⟩ :=
    g_inner_chartLeviCivitaParallelCLM_chartBasisVec_self_le_const_on_pouTsupport
      (I := I) (M := M) g α k
  refine ⟨K, hK_nn, ?_⟩
  intro b
  set ρ_b : ℝ := ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b with hρ_b_def
  set Φ_b : TangentSpace I b :=
    chartLeviCivitaParallelCLM (I := I) g α b
        (chartBasisVecFiber (I := I) α k)
        (chartBasisVecFiber (I := I) α k b) with hΦ_b_def
  set q_b : ℝ := g.inner b Φ_b Φ_b with hq_b_def
  have hq_b_nn : 0 ≤ q_b := by
    rw [hq_b_def]
    exact DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
      (I := I) (M := M) g b Φ_b
  have hρ_b_nn : 0 ≤ ρ_b := by
    rw [hρ_b_def]
    exact (chartAtlasPOU I M).nonneg α b
  by_cases hb : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  · have hρ_b_le_one : ρ_b ≤ 1 := by
      rw [hρ_b_def]
      exact (chartAtlasPOU I M).le_one α b
    have hq_b_le : q_b ≤ K := by
      rw [hq_b_def, hΦ_b_def]
      exact h_pt b hb
    have hsqrt_q_b : Real.sqrt q_b ≤ Real.sqrt K := Real.sqrt_le_sqrt hq_b_le
    have hsqrt_K_nn : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
    calc ρ_b * Real.sqrt q_b
        ≤ 1 * Real.sqrt K := by
          have h_factor : ρ_b * Real.sqrt q_b ≤ 1 * Real.sqrt q_b :=
            mul_le_mul_of_nonneg_right hρ_b_le_one (Real.sqrt_nonneg _)
          have h_inner : 1 * Real.sqrt q_b ≤ 1 * Real.sqrt K :=
            mul_le_mul_of_nonneg_left hsqrt_q_b zero_le_one
          linarith
      _ = Real.sqrt K := by ring
  · have hρ_b_zero : ρ_b = 0 := by
      rw [hρ_b_def]
      exact image_eq_zero_of_notMem_tsupport hb
    rw [hρ_b_zero]
    have : (0 : ℝ) * Real.sqrt q_b = 0 := by ring
    rw [this]
    exact Real.sqrt_nonneg _

theorem chartAtlasPOU_mul_sqrt_g_inner_chartLeviCivitaParallelCLM_chartBasisVec_self_eLpNorm_le_uniform_intrinsic
    (g : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm
        (fun b : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            Real.sqrt
              (g.inner b
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α k)
                  (chartBasisVecFiber (I := I) α k b))
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α k)
                  (chartBasisVecFiber (I := I) α k b)))) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal C := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  obtain ⟨K, hK_nn, h_pt⟩ :=
    chartAtlasPOU_mul_sqrt_g_inner_Phi_le_sqrt_const_globally
      (I := I) (M := M) g α k
  set f : M → ℝ := fun b =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
      Real.sqrt
        (g.inner b
          (chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α k)
            (chartBasisVecFiber (I := I) α k b))
          (chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α k)
            (chartBasisVecFiber (I := I) α k b))) with hf_def
  have hf_nn : ∀ b : M, 0 ≤ f b := by
    intro b
    rw [hf_def]
    exact mul_nonneg ((chartAtlasPOU I M).nonneg α b) (Real.sqrt_nonneg _)
  have h_norm_eq : ∀ b : M, ‖f b‖ = f b := by
    intro b
    rw [Real.norm_eq_abs, abs_of_nonneg (hf_nn b)]
  have h_pt' : ∀ b : M, ‖f b‖ ≤ Real.sqrt K := by
    intro b
    rw [h_norm_eq b, hf_def]
    exact h_pt b
  have h_eLpNorm_bound :
      eLpNorm f 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        (riemannianVolumeMeasure (I := I) (M := M) g
            (Set.univ : Set M)) ^ ((2 : ℝ≥0∞).toReal⁻¹) *
          ENNReal.ofReal (Real.sqrt K) :=
    MeasureTheory.eLpNorm_le_of_ae_bound
      (μ := riemannianVolumeMeasure (I := I) (M := M) g) (f := f)
      (C := Real.sqrt K) (Filter.Eventually.of_forall h_pt')
  set μM_univ : ℝ≥0∞ := riemannianVolumeMeasure (I := I) (M := M) g Set.univ
    with hμM_univ_def
  have hμM_univ_lt_top : μM_univ < ⊤ := by
    rw [hμM_univ_def]
    exact (measure_lt_top (riemannianVolumeMeasure (I := I) (M := M) g) Set.univ)
  set μM_real : ℝ := μM_univ.toReal with hμM_real_def
  have hμM_real_nn : 0 ≤ μM_real := by
    rw [hμM_real_def]; exact ENNReal.toReal_nonneg
  have h_two_toReal : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  have h_inv : (2 : ℝ≥0∞).toReal⁻¹ = (1 / 2 : ℝ) := by rw [h_two_toReal]; norm_num
  have hμM_univ_rpow_eq :
      μM_univ ^ ((2 : ℝ≥0∞).toReal⁻¹) = ENNReal.ofReal (μM_real ^ ((1 / 2 : ℝ))) := by
    rw [h_inv]
    have h_ofReal_back : μM_univ = ENNReal.ofReal μM_real := by
      rw [hμM_real_def]
      exact (ENNReal.ofReal_toReal hμM_univ_lt_top.ne).symm
    rw [h_ofReal_back]
    rw [ENNReal.ofReal_rpow_of_nonneg hμM_real_nn (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  set C : ℝ := μM_real ^ ((1 / 2 : ℝ)) * Real.sqrt K with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    exact mul_nonneg (Real.rpow_nonneg hμM_real_nn _) (Real.sqrt_nonneg _)
  refine ⟨C, hC_nn, ?_⟩
  refine h_eLpNorm_bound.trans ?_
  rw [hμM_univ_rpow_eq]
  rw [hC_def]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hμM_real_nn _)]

theorem g3_christoffel_atom_eLpNorm_le_uniform_intrinsic_pou
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (_S : SmoothCcTensorH1 g r s) (α : M)
        (k : Fin (Module.finrank ℝ E)),
        eLpNorm
          (fun b : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
              Real.sqrt
                (g.inner b
                  (chartLeviCivitaParallelCLM (I := I) g α b
                    (chartBasisVecFiber (I := I) α k)
                    (chartBasisVecFiber (I := I) α k b))
                  (chartLeviCivitaParallelCLM (I := I) g α b
                    (chartBasisVecFiber (I := I) α k)
                    (chartBasisVecFiber (I := I) α k b)))) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C := by
  classical
  set S_act : Finset M :=
    chartAtlasPOU_activeFinset (I := I) (M := M) with hS_act_def
  have hper : ∀ α : M, ∀ k : Fin (Module.finrank ℝ E),
      ∃ C : ℝ, 0 ≤ C ∧
        eLpNorm
          (fun b : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
              Real.sqrt
                (g.inner b
                  (chartLeviCivitaParallelCLM (I := I) g α b
                    (chartBasisVecFiber (I := I) α k)
                    (chartBasisVecFiber (I := I) α k b))
                  (chartLeviCivitaParallelCLM (I := I) g α b
                    (chartBasisVecFiber (I := I) α k)
                    (chartBasisVecFiber (I := I) α k b)))) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C := by
    intro α k
    exact
      chartAtlasPOU_mul_sqrt_g_inner_chartLeviCivitaParallelCLM_chartBasisVec_self_eLpNorm_le_uniform_intrinsic
        (I := I) (M := M) g α k
  set Cα_k : M → Fin (Module.finrank ℝ E) → ℝ :=
    fun α k => Classical.choose (hper α k) with hCα_k_def
  have hCα_k_nn : ∀ α : M, ∀ k : Fin (Module.finrank ℝ E), 0 ≤ Cα_k α k :=
    fun α k => (Classical.choose_spec (hper α k)).1
  have hCα_k_bd : ∀ α : M, ∀ k : Fin (Module.finrank ℝ E),
      eLpNorm
        (fun b : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            Real.sqrt
              (g.inner b
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α k)
                  (chartBasisVecFiber (I := I) α k b))
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α k)
                  (chartBasisVecFiber (I := I) α k b)))) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal (Cα_k α k) :=
    fun α k => (Classical.choose_spec (hper α k)).2
  set C_total : ℝ := ∑ α ∈ S_act, ∑ k : Fin (Module.finrank ℝ E), Cα_k α k
    with hC_total_def
  have hC_total_nn : 0 ≤ C_total :=
    Finset.sum_nonneg (fun α _ =>
      Finset.sum_nonneg (fun k _ => hCα_k_nn α k))
  refine ⟨C_total, hC_total_nn, ?_⟩
  intro _S α k
  by_cases hα : α ∈ S_act
  · have h_in_sum : Cα_k α k ≤ C_total := by
      rw [hC_total_def]
      have h1 : Cα_k α k ≤ ∑ j : Fin (Module.finrank ℝ E), Cα_k α j := by
        have h_split :
            ∑ j : Fin (Module.finrank ℝ E), Cα_k α j =
              Cα_k α k +
                ∑ j ∈ Finset.univ.erase k, Cα_k α j := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), add_comm]
        rw [h_split]
        have h_rest_nn : 0 ≤ ∑ j ∈ Finset.univ.erase k, Cα_k α j :=
          Finset.sum_nonneg (fun j _ => hCα_k_nn α j)
        linarith
      have h2 :
          ∑ j : Fin (Module.finrank ℝ E), Cα_k α j ≤
            ∑ β ∈ S_act, ∑ j : Fin (Module.finrank ℝ E), Cα_k β j := by
        have h_split :
            ∑ β ∈ S_act, ∑ j : Fin (Module.finrank ℝ E), Cα_k β j =
              (∑ j : Fin (Module.finrank ℝ E), Cα_k α j) +
                ∑ β ∈ S_act.erase α, ∑ j : Fin (Module.finrank ℝ E), Cα_k β j := by
          rw [← Finset.sum_erase_add _ _ hα, add_comm]
        rw [h_split]
        have h_rest_nn :
            0 ≤ ∑ β ∈ S_act.erase α, ∑ j : Fin (Module.finrank ℝ E), Cα_k β j :=
          Finset.sum_nonneg (fun β _ =>
            Finset.sum_nonneg (fun j _ => hCα_k_nn β j))
        linarith
      linarith
    have hofReal_le : ENNReal.ofReal (Cα_k α k) ≤ ENNReal.ofReal C_total :=
      ENNReal.ofReal_le_ofReal h_in_sum
    exact (hCα_k_bd α k).trans hofReal_le
  · have h_zero : ∀ b : M, ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b = 0 :=
      chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
    have h_integrand_zero :
        (fun b : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            Real.sqrt
              (g.inner b
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α k)
                  (chartBasisVecFiber (I := I) α k b))
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α k)
                  (chartBasisVecFiber (I := I) α k b)))) =
        (fun _ : M => (0 : ℝ)) := by
      funext b
      rw [h_zero b]; ring
    rw [h_integrand_zero]
    rw [eLpNorm_zero']
    exact zero_le _

end HebeyBlock
end RicciFlow
end PDE
end DifferentialGeometry

end
