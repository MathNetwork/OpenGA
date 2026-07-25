import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Equivalence
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lp
import DifferentialGeometry.Analysis.Sobolev.Approximation.ContMDiffDense
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Sobolev.Manifold.EmbeddingSubcritical
import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifold
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.IntegrationByParts
import DifferentialGeometry.Geometry.Operator.Laplacian
import DifferentialGeometry.Analysis.Integration.Measure.Family
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceForwardSmoothMemW1pIntrinsic
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceForwardELpNormWkpNormChartBound
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceForwardChartSmoothExtFderivWkpNorm
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceForwardGradNormPartitionSum
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace EquivalenceFull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Intrinsic
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

private noncomputable def chartInvGramMatrix_l1Sum
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) (x : M) : ℝ :=
  ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
    |DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix
      (I := I) g α x ij.1 ij.2|

private lemma chartInvGramMatrix_l1Sum_nonneg
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) (x : M) :
    0 ≤ chartInvGramMatrix_l1Sum (I := I) (M := M) g α x := by
  unfold chartInvGramMatrix_l1Sum
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

private lemma chartInvGramMatrix_l1Sum_continuousOn
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) :
    ContinuousOn (chartInvGramMatrix_l1Sum (I := I) (M := M) g α)
      (chartAt H α).source := by
  classical
  unfold chartInvGramMatrix_l1Sum
  refine continuousOn_finset_sum _ (fun ij _ => ?_)
  have h1 :
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun x : M =>
          DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix
            (I := I) g α x ij.1 ij.2)
        (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix_entry_contMDiffOn
      (I := I) g α ij.1 ij.2
  have h_cont : ContinuousOn
      (fun x : M =>
        DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix
          (I := I) g α x ij.1 ij.2)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    h1.continuousOn
  have h_cont_src : ContinuousOn
      (fun x : M =>
        DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix
          (I := I) g α x ij.1 ij.2)
      (chartAt H α).source := by
    intro x hx
    have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
      exact hx
    exact (h_cont x hbase).mono (by
      intro y hy
      rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
      exact hy)
  exact h_cont_src.abs

private lemma sq_norm_gradFun_le_chartInvGramMatrix_l1Sum_mul
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) :
    g.inner x
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
          (I := I) g f x)
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
          (I := I) g f x)
      ≤ chartInvGramMatrix_l1Sum (I := I) (M := M) g α x *
          ∑ k : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
              (E := E) k
              (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                (I := I) α f)
              (extChartAt I α x))^2 := by
  classical
  have hgrad_eq :
      DifferentialGeometry.Integral.DivergenceTheorem.gradFun
          (I := I) g f x =
        DifferentialGeometry.Integral.DivergenceTheorem.gradChartLocal
          (I := I) g α f x :=
    (DifferentialGeometry.Integral.DivergenceTheorem.gradChartLocal_eq_gradFun
      (I := I) g α hf hx hx_int).symm
  rw [hgrad_eq]
  set c : Fin (Module.finrank ℝ E) → ℝ := fun i =>
    DifferentialGeometry.Integral.DivergenceTheorem.gradChartCoeff
      (I := I) g α f i x with hc_def
  have hgcl_eq :
      DifferentialGeometry.Integral.DivergenceTheorem.gradChartLocal
        (I := I) g α f x =
        ∑ i, c i •
          DifferentialGeometry.Integral.Measure.chartBasisVecFiber
            (I := I) α i x := by
    unfold DifferentialGeometry.Integral.DivergenceTheorem.gradChartLocal
    rfl
  rw [hgcl_eq]
  set Gmat : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g α x with hGmat_def
  have hG_form : g.inner x
        (∑ i, c i •
          DifferentialGeometry.Integral.Measure.chartBasisVecFiber
            (I := I) α i x)
        (∑ j, c j •
          DifferentialGeometry.Integral.Measure.chartBasisVecFiber
            (I := I) α j x)
      = dotProduct (star c) (Matrix.mulVec Gmat c) :=
    (DifferentialGeometry.Integral.Measure.chartGramMatrix_dotProduct_mulVec
      (I := I) g α x c).symm
  rw [hG_form]
  set d : Fin (Module.finrank ℝ E) → ℝ := fun j =>
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
      (E := E) j
      (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I) α f)
      (extChartAt I α x) with hd_def
  set Ginv : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix
      (I := I) g α x with hGinv_def
  have hc_eq : ∀ i, c i = ∑ j, Ginv i j * d j := by
    intro i
    rfl
  have hcGc_expand :
      dotProduct (star c) (Matrix.mulVec Gmat c) =
        ∑ i, ∑ j, c i * c j * Gmat i j := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    have h_dot : dotProduct (Gmat i) c =
        ∑ j', Gmat i j' * c j' := rfl
    ring
  rw [hcGc_expand]
  have h_cGc_eq_dGd :
      (∑ i, ∑ j, c i * c j * Gmat i j) =
        ∑ j, ∑ k, Ginv j k * d j * d k := by
    have hstep1 :
        (∑ i, ∑ j, c i * c j * Gmat i j) =
          ∑ j, c j * (∑ i, c i * Gmat i j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [hstep1]
    have h_dot_sum : ∀ j, (∑ i, c i * Gmat i j) = d j := by
      intro j
      have hsym : ∀ i, Gmat i j = Gmat j i := fun i => g.symm x _ _
      have h_step :
          (∑ i, c i * Gmat i j) =
            (∑ i, ∑ k, Ginv i k * d k * Gmat j i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hc_eq i]
        rw [hsym i]
        rw [Finset.sum_mul]
      rw [h_step]
      have h_swap : (∑ i, ∑ k, Ginv i k * d k * Gmat j i) =
          ∑ k, d k * (∑ i, Gmat j i * Ginv i k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      rw [h_swap]
      have h_id : ∀ k, (∑ i, Gmat j i * Ginv i k) =
          (Gmat * Ginv) j k := by
        intro k
        rfl
      have h_id_eq_one : ∀ k, (∑ i, Gmat j i * Ginv i k) =
          if j = k then (1 : ℝ) else 0 := by
        intro k
        rw [h_id k, hGmat_def, hGinv_def]
        rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramMatrix_mul_chartInvGramMatrix
          (I := I) g α hx]
        rw [Matrix.one_apply]
      rw [show (∑ k, d k * (∑ i, Gmat j i * Ginv i k)) =
            ∑ k, d k * (if j = k then (1 : ℝ) else 0) from
        Finset.sum_congr rfl (fun k _ => by rw [h_id_eq_one k])]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hjk
        rw [if_neg (Ne.symm hjk), mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ j) hk
    have hstep2 :
        (∑ j, c j * (∑ i, c i * Gmat i j)) =
          ∑ j, c j * d j := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [h_dot_sum j]
    rw [hstep2]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hc_eq j]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [h_cGc_eq_dGd]
  set D : ℝ := ∑ k, (d k)^2 with hD_def
  have hD_nn : 0 ≤ D := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hd_sq_le : ∀ j, (d j)^2 ≤ D := by
    intro j
    rw [hD_def]
    refine Finset.single_le_sum (f := fun k => (d k)^2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have hd_abs_le_sqrtD : ∀ j, |d j| ≤ Real.sqrt D := by
    intro j
    rw [show |d j| = Real.sqrt ((d j)^2) by rw [Real.sqrt_sq_eq_abs]]
    exact Real.sqrt_le_sqrt (hd_sq_le j)
  have h_dj_dk_le_D : ∀ j k, |d j * d k| ≤ D := by
    intro j k
    rw [abs_mul]
    have h := mul_le_mul (hd_abs_le_sqrtD j) (hd_abs_le_sqrtD k)
      (abs_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt hD_nn] at h
    exact h
  have h_main_le :
      (∑ j, ∑ k, Ginv j k * d j * d k) ≤
        chartInvGramMatrix_l1Sum (I := I) (M := M) g α x * D := by
    unfold chartInvGramMatrix_l1Sum
    rw [Finset.sum_mul]
    rw [show (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            |DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix
              (I := I) g α x ij.1 ij.2| * D) =
          ∑ j, ∑ k, |Ginv j k| * D from ?_]
    swap
    · rw [← Finset.sum_product']
      rfl
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine Finset.sum_le_sum (fun k _ => ?_)
    have h1 : Ginv j k * d j * d k ≤ |Ginv j k * (d j * d k)| := by
      have h := le_abs_self (Ginv j k * (d j * d k))
      have heq : Ginv j k * d j * d k = Ginv j k * (d j * d k) := by ring
      rw [heq]
      exact h
    refine h1.trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h_dj_dk_le_D j k) (abs_nonneg _)
  exact h_main_le

private lemma norm_gradFun_le_sqrt_chartInvGramMatrix_l1Sum_mul
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) :
    Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g f x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g f x))
      ≤ Real.sqrt (chartInvGramMatrix_l1Sum (I := I) (M := M) g α x) *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
                (E := E) k
                (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                  (I := I) α f)
                (extChartAt I α x))^2) := by
  have h_sq := sq_norm_gradFun_le_chartInvGramMatrix_l1Sum_mul
    (I := I) (M := M) g α hf hx hx_int
  have h_M_nn := chartInvGramMatrix_l1Sum_nonneg (I := I) (M := M) g α x
  have h_D_nn : (0 : ℝ) ≤ ∑ k : Fin (Module.finrank ℝ E),
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
        (E := E) k
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
          (I := I) α f)
        (extChartAt I α x))^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_sqrt_le := Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_mul h_M_nn] at h_sqrt_le
  exact h_sqrt_le

local notation "EuclN_E" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private noncomputable def gramInvL1SumSupOnPouTsupport
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) : ℝ := by
  classical
  set Kα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  by_cases hKα_ne : Kα.Nonempty
  · have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
    have hKα_sub : Kα ⊆ (chartAt H α).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
    have h_cont : ContinuousOn
        (chartInvGramMatrix_l1Sum (I := I) (M := M) g α) Kα :=
      (chartInvGramMatrix_l1Sum_continuousOn (I := I) (M := M) g α).mono hKα_sub
    exact (hKα_compact.image_of_continuousOn h_cont).bddAbove.choose
  · exact 0

private lemma gramInvL1SumSupOnPouTsupport_nonneg
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) :
    0 ≤ gramInvL1SumSupOnPouTsupport (I := I) (M := M) g α := by
  classical
  unfold gramInvL1SumSupOnPouTsupport
  set Kα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  by_cases hKα_ne : Kα.Nonempty
  · rw [dif_pos hKα_ne]
    have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
    have hKα_sub : Kα ⊆ (chartAt H α).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
    have h_cont : ContinuousOn
        (chartInvGramMatrix_l1Sum (I := I) (M := M) g α) Kα :=
      (chartInvGramMatrix_l1Sum_continuousOn (I := I) (M := M) g α).mono hKα_sub
    set hImg :=
      (hKα_compact.image_of_continuousOn h_cont).bddAbove
    obtain ⟨x₀, hx₀⟩ := hKα_ne
    have hx₀_val :
        chartInvGramMatrix_l1Sum (I := I) (M := M) g α x₀ ∈
        (chartInvGramMatrix_l1Sum (I := I) (M := M) g α) '' Kα :=
      ⟨x₀, hx₀, rfl⟩
    have h_le := hImg.choose_spec hx₀_val
    have h_val_nn :
        (0 : ℝ) ≤ chartInvGramMatrix_l1Sum (I := I) (M := M) g α x₀ :=
      chartInvGramMatrix_l1Sum_nonneg (I := I) (M := M) g α x₀
    exact le_trans h_val_nn h_le
  · rw [dif_neg hKα_ne]

private lemma chartInvGramMatrix_l1Sum_le_sup
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {x : M}
    (hx : x ∈ tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    chartInvGramMatrix_l1Sum (I := I) (M := M) g α x ≤
      gramInvL1SumSupOnPouTsupport (I := I) (M := M) g α := by
  classical
  unfold gramInvL1SumSupOnPouTsupport
  set Kα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_ne : Kα.Nonempty := ⟨x, hx⟩
  rw [dif_pos hKα_ne]
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  have h_cont : ContinuousOn
      (chartInvGramMatrix_l1Sum (I := I) (M := M) g α) Kα :=
    (chartInvGramMatrix_l1Sum_continuousOn (I := I) (M := M) g α).mono hKα_sub
  set hImg :=
    (hKα_compact.image_of_continuousOn h_cont).bddAbove
  exact hImg.choose_spec ⟨x, hx, rfl⟩

private lemma contDiff_chartSmoothExt_local
    [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source)
    (hf_compact : IsCompact (tsupport f)) :
    ContDiff ℝ ∞
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  set form : EuclN_E → ℝ := fun z =>
    f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) with hform_def
  have h_target_open :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) (α := α)
  have h_form_contDiffOn : ContDiffOn ℝ ∞ form
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
    have hscalar : ContDiffOn ℝ ∞
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
          (I := I) α f) (extChartAt I α).target :=
      DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
        (I := I) α hf
    have htoEuc_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
      ContinuousLinearEquiv.contDiff _
    have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm)
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)
        (extChartAt I α).target := by
      intro y' hy'
      obtain ⟨z, hz_target, rfl⟩ := hy'
      have h_eq : (toEuclidean (E := E)).symm
          ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) z) = z :=
        (toEuclidean (E := E)).symm_apply_apply z
      rw [h_eq]
      exact hz_target
    have h_eq_form : form = (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I) α f) ∘ (fun z : EuclN_E => (toEuclidean (E := E)).symm z) := by
      funext z
      rfl
    rw [h_eq_form]
    exact hscalar.comp htoEuc_symm_smooth.contDiffOn hmaps
  by_cases hy_target : y ∈
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
  · have h_at : ContDiffAt ℝ ∞ form y :=
      (h_form_contDiffOn.contDiffWithinAt hy_target).contDiffAt
        (h_target_open.mem_nhds hy_target)
    apply h_at.congr_of_eventuallyEq
    filter_upwards [h_target_open.mem_nhds hy_target] with z hz
    obtain ⟨w, hw_target, hw_eq⟩ := hz
    have hsymm_eq : (toEuclidean (E := E)).symm z = w := by
      rw [← hw_eq]
      exact (toEuclidean (E := E)).symm_apply_apply w
    have htarget_at_z : (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target := by
      rw [hsymm_eq]; exact hw_target
    change DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f z =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    change (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
        f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
      else (0 : ℝ)) =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    rw [if_pos htarget_at_z]
  · set K : Set EuclN_E := (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f))
      with hK_def
    have hK_compact : IsCompact K := by
      have h_extChart_cont : ContinuousOn (extChartAt I α) (tsupport f) :=
        (continuousOn_extChartAt α).mono (by
          intro x hx
          rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact hf_supp hx)
      have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
        hf_compact.image_of_continuousOn h_extChart_cont
      exact h1.image (toEuclidean (E := E)).continuous
    have hK_subset : K ⊆
        DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α := by
      rintro y' ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      have hxsource : x ∈ (extChartAt I α).source := by
        rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hf_supp hx
      exact ⟨extChartAt I α x, (extChartAt I α).map_source hxsource, rfl⟩
    have hy_off_K : y ∉ K := by
      intro hy_in
      exact hy_target (hK_subset hy_in)
    have hK_closed : IsClosed K := hK_compact.isClosed
    have hK_compl_open : IsOpen Kᶜ := hK_closed.isOpen_compl
    apply ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuclN_E => (0 : ℝ)) contDiffAt_const
    filter_upwards [hK_compl_open.mem_nhds hy_off_K] with z hz
    exact chartSmoothExt_eq_zero_off_image_tsupport_local
      (I := I) (M := M) α (f := f) hz

private lemma contDiff_chartSmoothExt_pou_mul_local
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContDiff ℝ ∞
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y)) := by
  classical
  set f : M → ℝ := fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯) y * u y with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.mul hu
  have hf_supp : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      have h_eq : f = (fun y : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) y • u y) := by funext y; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun y : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) (g := u)
    exact h1.trans
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  exact contDiff_chartSmoothExt_local (I := I) (M := M) α hf_smooth hf_supp hf_compact

private lemma gNormGrad_pou_mul_le_sqrt_partial_sum
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) {x : M}
    (hx : x ∈ tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    gNormGrad (I := I) (M := M) g
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y) x ≤
      Real.sqrt
        (gramInvL1SumSupOnPouTsupport (I := I) (M := M) g α) *
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
              (E := E) k
              (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                (I := I) α
                (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) y * u y))
              (extChartAt I α x))^2) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α with hρ_def
  set f : M → ℝ := fun y : M => (ρ : M → ℝ) y * u y with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := ρ.contMDiff.mul hu
  have hxchart : x ∈ (chartAt H α).source := by
    have hsubord : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).IsSubordinate
        (fun β : M => (chartAt H β).source) :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M
    exact hsubord α hx
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
    exact hxchart
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I)]
    exact hxchart
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source hxsrc
  have hf_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
    hf_smooth.mdifferentiable (by simp) x
  have h_pointwise :=
    norm_gradFun_le_sqrt_chartInvGramMatrix_l1Sum_mul
      (I := I) (M := M) g α (f := f) (x := x) hf_diff hxbase hx_int
  refine le_trans h_pointwise ?_
  have h_M_le : chartInvGramMatrix_l1Sum (I := I) (M := M) g α x ≤
      gramInvL1SumSupOnPouTsupport (I := I) (M := M) g α :=
    chartInvGramMatrix_l1Sum_le_sup (I := I) (M := M) g α (x := x) hx
  have h_M_nn : 0 ≤ chartInvGramMatrix_l1Sum (I := I) (M := M) g α x :=
    chartInvGramMatrix_l1Sum_nonneg (I := I) (M := M) g α x
  have h_sqrt_M_le : Real.sqrt (chartInvGramMatrix_l1Sum (I := I) (M := M) g α x) ≤
      Real.sqrt (gramInvL1SumSupOnPouTsupport (I := I) (M := M) g α) :=
    Real.sqrt_le_sqrt h_M_le
  have h_partial_sum_nn : (0 : ℝ) ≤ ∑ k : Fin (Module.finrank ℝ E),
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
        (E := E) k
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
          (I := I) α f)
        (extChartAt I α x))^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact mul_le_mul_of_nonneg_right h_sqrt_M_le (Real.sqrt_nonneg _)

private lemma gNormGrad_pou_mul_le_indicator_sqrt
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (x : M) :
    gNormGrad (I := I) (M := M) g
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y) x ≤
      Real.sqrt
        (gramInvL1SumSupOnPouTsupport (I := I) (M := M) g α) *
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
              (E := E) k
              (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                (I := I) α
                (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) y * u y))
              (extChartAt I α x))^2) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α with hρ_def
  set f : M → ℝ := fun y : M => (ρ : M → ℝ) y * u y with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := ρ.contMDiff.mul hu
  by_cases hx_pou : x ∈ tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  · exact gNormGrad_pou_mul_le_sqrt_partial_sum (I := I) (M := M) g α hu hx_pou
  · have hx_supp_f : x ∉ tsupport f := by
      intro hx_in
      apply hx_pou
      have h_subset : tsupport f ⊆ tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
        have h_eq : f = (fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y • u y) := by
          funext y; rfl
        rw [h_eq]
        exact tsupport_smul_subset_left
          (f := fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) (g := u)
      exact h_subset hx_in
    rw [gNormGrad_eq_zero_of_notMem_tsupport (I := I) (M := M) g hf_smooth hx_supp_f]
    have h1 : (0 : ℝ) ≤ Real.sqrt
        (gramInvL1SumSupOnPouTsupport (I := I) (M := M) g α) :=
      Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ Real.sqrt
        (∑ k : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) k
            (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
              (I := I) α f)
            (extChartAt I α x))^2) := Real.sqrt_nonneg _
    exact mul_nonneg h1 h2

private lemma eLpNorm_gNormGrad_pou_mul_le_const_mul_wkpNormChart_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        eLpNorm (gNormGrad (I := I) (M := M) g
            (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x)) p
            (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
          ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) g 1 p u := by
  classical
  set Kα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  obtain ⟨Cbridge, hCbridge_pos, hCbridge_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
  set M_g_α : ℝ := gramInvL1SumSupOnPouTsupport (I := I) (M := M) g α
  have hM_nn : 0 ≤ M_g_α := gramInvL1SumSupOnPouTsupport_nonneg (I := I) (M := M) g α
  set B : ℝ := toEuclideanBasisSqSum (E := E)
  have hB_nn : 0 ≤ B := toEuclideanBasisSqSum_nonneg
  set d_dim : ℕ := Module.finrank ℝ E
  set C : ℝ := Cbridge * Real.sqrt M_g_α * Real.sqrt B * (d_dim : ℝ) with hC_def
  have hC_nn : 0 ≤ C := by
    refine mul_nonneg (mul_nonneg (mul_nonneg hCbridge_pos.le ?_) ?_) ?_
    · exact Real.sqrt_nonneg _
    · exact Real.sqrt_nonneg _
    · exact Nat.cast_nonneg _
  refine ⟨C, hC_nn, ?_⟩
  intro u hu
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α with hρ_def
  set f : M → ℝ := fun y : M => (ρ : M → ℝ) y * u y with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := ρ.contMDiff.mul hu
  have hf_supp : tsupport f ⊆ Kα := by
    have h_eq : f = (fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y • u y) := by
      funext y; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) (g := u)
  have hf_supp_chart : tsupport f ⊆ (chartAt H α).source :=
    hf_supp.trans hKα_sub
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have h_gNormGrad_meas : Measurable (gNormGrad (I := I) (M := M) g f) := by
    have h_cont := continuous_g_norm_gradFun (I := I) (M := M) g hf_smooth
    exact h_cont.measurable
  have h_gNormGrad_supp : tsupport (gNormGrad (I := I) (M := M) g f) ⊆ Kα := by
    refine subset_trans ?_ hf_supp
    apply closure_minimal _ (isClosed_tsupport _)
    intro y hy
    by_contra hy_off
    apply hy
    have : gNormGrad (I := I) (M := M) g f y = 0 :=
      gNormGrad_eq_zero_of_notMem_tsupport (I := I) (M := M) g hf_smooth hy_off
    exact this
  have h_step1 := hCbridge_bound h_gNormGrad_meas h_gNormGrad_supp
  refine h_step1.trans ?_
  have h_chartSmoothExt_smooth : ContDiff ℝ ∞
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f) :=
    contDiff_chartSmoothExt_local (I := I) (M := M) α hf_smooth hf_supp_chart hf_compact
  have h_pt_bound : ∀ y : EuclN_E,
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
        (gNormGrad (I := I) (M := M) g f) y ≤
        Real.sqrt M_g_α * Real.sqrt B *
          ‖fderiv ℝ
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f) y‖ := by
    intro y
    by_cases hy_in : y ∈
        DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α
    · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
        (I := I) α (gNormGrad (I := I) (M := M) g f) hy_in]
      set z : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hz_def
      have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
        rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
          (I := I) (M := M)] at hy_in
        exact hy_in
      have hz_source : z ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hsymm_target
      have hz_chart_source : z ∈ (chartAt H α).source := by
        rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)] at hz_source
        exact hz_source
      have hz_base : z ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
        exact hz_chart_source
      have hz_int : extChartAt I α z ∈ interior (extChartAt I α).target := by
        rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
        exact (extChartAt I α).map_source hz_source
      have h_pt := norm_gradFun_le_sqrt_chartInvGramMatrix_l1Sum_mul
        (I := I) (M := M) g α (f := f) (x := z)
        (hf_smooth.mdifferentiable (by simp) z) hz_base hz_int
      have hzy : extChartAt I α z = (toEuclidean (E := E)).symm y := by
        change extChartAt I α ((extChartAt I α).symm
            ((toEuclidean (E := E)).symm y)) = (toEuclidean (E := E)).symm y
        exact (extChartAt I α).right_inv hsymm_target
      by_cases hz_pou : z ∈ Kα
      · have h_M_le := chartInvGramMatrix_l1Sum_le_sup
          (I := I) (M := M) g α (x := z) hz_pou
        have h_M_z_nn := chartInvGramMatrix_l1Sum_nonneg
          (I := I) (M := M) g α z
        have h_combined : gNormGrad (I := I) (M := M) g f z ≤
            Real.sqrt M_g_α *
              Real.sqrt
                (∑ k : Fin (Module.finrank ℝ E),
                  (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
                    (E := E) k
                    (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                      (I := I) α f)
                    (extChartAt I α z))^2) := by
          unfold gNormGrad
          refine h_pt.trans ?_
          have h_sqrt_M_le : Real.sqrt
              (chartInvGramMatrix_l1Sum (I := I) (M := M) g α z) ≤
              Real.sqrt M_g_α := Real.sqrt_le_sqrt h_M_le
          have h_partial_sum_nn : (0 : ℝ) ≤ Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
                  (E := E) k
                  (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                    (I := I) α f)
                  (extChartAt I α z))^2) := Real.sqrt_nonneg _
          exact mul_le_mul_of_nonneg_right h_sqrt_M_le h_partial_sum_nn
        rw [hzy] at h_combined
        have h_sq_le := sq_partials_scalarOnE_le_chartSmoothExt_fderiv
          (I := I) (M := M) α (f := f) h_chartSmoothExt_smooth (y := (toEuclidean (E := E)).symm y)
          hsymm_target
        have h_TE_apply : (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
            ((toEuclidean (E := E)).symm y) = y :=
          (toEuclidean (E := E)).apply_symm_apply y
        rw [h_TE_apply] at h_sq_le
        have h_sqrt_partial_le : Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
                (E := E) k
                (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                  (I := I) α f)
                ((toEuclidean (E := E)).symm y))^2) ≤
            Real.sqrt B *
              ‖fderiv ℝ
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
                  (I := I) (M := M) α f) y‖ := by
          have h_sqrt_le := Real.sqrt_le_sqrt h_sq_le
          rw [Real.sqrt_mul hB_nn] at h_sqrt_le
          rw [Real.sqrt_sq (norm_nonneg _)] at h_sqrt_le
          exact h_sqrt_le
        refine h_combined.trans ?_
        have h_sqrt_M_nn : 0 ≤ Real.sqrt M_g_α := Real.sqrt_nonneg _
        calc Real.sqrt M_g_α *
              Real.sqrt
                (∑ k : Fin (Module.finrank ℝ E),
                  (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
                    (E := E) k
                    (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                      (I := I) α f)
                    ((toEuclidean (E := E)).symm y))^2)
            ≤ Real.sqrt M_g_α *
              (Real.sqrt B *
                ‖fderiv ℝ
                  (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
                    (I := I) (M := M) α f) y‖) :=
              mul_le_mul_of_nonneg_left h_sqrt_partial_le h_sqrt_M_nn
          _ = Real.sqrt M_g_α * Real.sqrt B *
              ‖fderiv ℝ
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
                  (I := I) (M := M) α f) y‖ := by ring
      · have hz_off_f : z ∉ tsupport f := fun hin => hz_pou (hf_supp hin)
        rw [gNormGrad_eq_zero_of_notMem_tsupport (I := I) (M := M) g hf_smooth hz_off_f]
        positivity
    · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
        (I := I) α (gNormGrad (I := I) (M := M) g f) hy_in]
      positivity
  have h_eLpNorm_le :
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
          (gNormGrad (I := I) (M := M) g f)) p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) ≤
      eLpNorm
        (fun y : EuclN_E => Real.sqrt M_g_α * Real.sqrt B *
          ‖fderiv ℝ
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f) y‖) p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) := by
    apply eLpNorm_mono_real
    intro y
    have h := h_pt_bound y
    have h_norm : ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
        (gNormGrad (I := I) (M := M) g f) y‖ =
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
          (gNormGrad (I := I) (M := M) g f) y := by
      rw [Real.norm_eq_abs]
      apply abs_of_nonneg
      by_cases hy_in : y ∈
          DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α
      · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
          (I := I) α (gNormGrad (I := I) (M := M) g f) hy_in]
        exact gNormGrad_nonneg _ _ _
      · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
          (I := I) α (gNormGrad (I := I) (M := M) g f) hy_in]
    rw [h_norm]
    exact h
  set Csqrt : ℝ := Real.sqrt M_g_α * Real.sqrt B
  have h_csqrt_nn : 0 ≤ Csqrt := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_eq_fun : (fun y : EuclN_E => Real.sqrt M_g_α * Real.sqrt B *
        ‖fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y‖) =
      (fun y : EuclN_E => Csqrt *
        ‖fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y‖) := by
    funext y
    show Real.sqrt M_g_α * Real.sqrt B *
        ‖fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y‖ =
      Csqrt *
        ‖fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y‖
    rw [show Csqrt = Real.sqrt M_g_α * Real.sqrt B from rfl]
  rw [h_eq_fun] at h_eLpNorm_le
  have h_eLp_const :
      eLpNorm
        (fun y : EuclN_E => Csqrt *
          ‖fderiv ℝ
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f) y‖) p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) =
      ‖Csqrt‖ₑ *
      eLpNorm
        (fun y : EuclN_E =>
          ‖fderiv ℝ
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f) y‖) p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) := by
    have h := eLpNorm_const_smul (𝕜 := ℝ) (p := p)
      (μ := (volume : Measure EuclN_E).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
      (c := Csqrt)
      (f := fun y : EuclN_E =>
        ‖fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y‖)
    exact h
  rw [h_eLp_const] at h_eLpNorm_le
  have hChartTarget_open :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) (α := α)
  have h_supp_smooth_ext : tsupport
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f) ⊆
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α := by
    have hK_compact : IsCompact ((toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) := by
      have h_cont : ContinuousOn (extChartAt I α) (tsupport f) := by
        apply (continuousOn_extChartAt α).mono
        intro x hx
        rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hf_supp_chart hx
      have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
        hf_compact.image_of_continuousOn h_cont
      exact h1.image (toEuclidean (E := E)).continuous
    have h_sub_image : tsupport
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) ⊆
        (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) := by
      apply closure_minimal _ hK_compact.isClosed
      intro y hy
      by_contra hy_off
      apply hy
      exact chartSmoothExt_eq_zero_off_image_tsupport_local
        (I := I) (M := M) α (f := f) hy_off
    refine h_sub_image.trans ?_
    rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    have hxsource : x ∈ (extChartAt I α).source := by
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hf_supp_chart hx
    exact ⟨extChartAt I α x, (extChartAt I α).map_source hxsource, rfl⟩
  have h_compact_smooth_ext : HasCompactSupport
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f) := by
    have hK_compact : IsCompact ((toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) := by
      have h_cont : ContinuousOn (extChartAt I α) (tsupport f) := by
        apply (continuousOn_extChartAt α).mono
        intro x hx
        rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hf_supp_chart hx
      have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
        hf_compact.image_of_continuousOn h_cont
      exact h1.image (toEuclidean (E := E)).continuous
    have h_sub_image : tsupport
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) ⊆
        (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) := by
      apply closure_minimal _ hK_compact.isClosed
      intro y hy
      by_contra hy_off
      apply hy
      exact chartSmoothExt_eq_zero_off_image_tsupport_local
        (I := I) (M := M) α (f := f) hy_off
    exact hK_compact.of_isClosed_subset (isClosed_tsupport _) h_sub_image
  have h_fderiv_le := eLpNorm_norm_fderiv_le_d_mul_wkpNorm_local
    (q := p) hp_one (Ω :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
    hChartTarget_open
    (h_chartSmoothExt_smooth)
    h_compact_smooth_ext h_supp_smooth_ext
  have h_wkpNorm_le := wkpNorm_chartSmoothExt_pou_mul_le_wkpNormChart
    (I := I) (M := M) g α hp_one u
  have h_chain : ENNReal.ofReal Cbridge *
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
          (gNormGrad (I := I) (M := M) g f)) p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) ≤
      ENNReal.ofReal Cbridge *
      (‖Csqrt‖ₑ *
        (((Module.finrank ℝ E : ℕ) : ℝ≥0∞) *
          wkpNormChart (I := I) (M := M) g 1 p u)) := by
    gcongr
    apply h_eLpNorm_le.trans
    gcongr
    apply h_fderiv_le.trans
    gcongr
  refine h_chain.trans ?_
  have h_csqrt_enorm : ‖Csqrt‖ₑ = ENNReal.ofReal Csqrt :=
    Real.enorm_eq_ofReal h_csqrt_nn
  rw [h_csqrt_enorm]
  have h_d_eq : ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) = ENNReal.ofReal (d_dim : ℝ) := by
    change ((d_dim : ℕ) : ℝ≥0∞) = ENNReal.ofReal (d_dim : ℝ)
    rw [ENNReal.ofReal_natCast]
  rw [h_d_eq]
  rw [show ENNReal.ofReal Cbridge *
        (ENNReal.ofReal Csqrt *
          (ENNReal.ofReal (d_dim : ℝ) * wkpNormChart (I := I) (M := M) g 1 p u)) =
      (ENNReal.ofReal Cbridge * ENNReal.ofReal Csqrt * ENNReal.ofReal (d_dim : ℝ)) *
        wkpNormChart (I := I) (M := M) g 1 p u from by ring]
  have h_const_eq : ENNReal.ofReal Cbridge * ENNReal.ofReal Csqrt *
      ENNReal.ofReal (d_dim : ℝ) =
      ENNReal.ofReal C := by
    rw [hC_def]
    rw [show Cbridge * Real.sqrt M_g_α * Real.sqrt B * (d_dim : ℝ) =
      Cbridge * Csqrt * (d_dim : ℝ) from by
      change Cbridge * Real.sqrt M_g_α * Real.sqrt B * (d_dim : ℝ) =
        Cbridge * (Real.sqrt M_g_α * Real.sqrt B) * (d_dim : ℝ)
      ring]
    have hCC_nn : 0 ≤ Cbridge * Csqrt :=
      mul_nonneg hCbridge_pos.le h_csqrt_nn
    rw [ENNReal.ofReal_mul hCC_nn]
    rw [ENNReal.ofReal_mul hCbridge_pos.le]
  rw [h_const_eq]

theorem eLpNorm_g_norm_gradFun_le_const_mul_wkpNormChart_smooth_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        eLpNorm (fun x : M => Real.sqrt
            (g.inner x
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                (I := I) g u x)
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                (I := I) g u x))) p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)
          ≤ ENNReal.ofReal C *
              wkpNormChart (I := I) (M := M) g 1 p u := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have h_per_α : ∀ α : M, ∃ C_α : ℝ, 0 ≤ C_α ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        eLpNorm (gNormGrad (I := I) (M := M) g
            (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x)) p
            (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
          ENNReal.ofReal C_α *
            wkpNormChart (I := I) (M := M) g 1 p u :=
    fun α =>
      eLpNorm_gNormGrad_pou_mul_le_const_mul_wkpNormChart_smooth
        (I := I) (M := M) g hp_one hp_top α
  set Cα : M → ℝ := fun α => Classical.choose (h_per_α α) with hCα_def
  have hCα_nn : ∀ α : M, 0 ≤ Cα α := fun α => (Classical.choose_spec (h_per_α α)).1
  have hCα_bound : ∀ α : M, ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      eLpNorm (gNormGrad (I := I) (M := M) g
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)) p
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
        ENNReal.ofReal (Cα α) *
          wkpNormChart (I := I) (M := M) g 1 p u :=
    fun α => (Classical.choose_spec (h_per_α α)).2
  refine ⟨∑ α ∈ S, Cα α,
    Finset.sum_nonneg (fun α _ => hCα_nn α), ?_⟩
  intro u hu_smooth
  rw [DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_def
    (I := I) (M := M) g]
  change eLpNorm (gNormGrad (I := I) (M := M) g u) p
      (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
      ENNReal.ofReal (∑ α ∈ S, Cα α) *
        wkpNormChart (I := I) (M := M) g 1 p u
  have h_pointwise : ∀ x : M, gNormGrad (I := I) (M := M) g u x ≤
      ∑ α ∈ S, gNormGrad (I := I) (M := M) g
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y) x :=
    fun x => gNormGrad_le_finset_sum_pou_mul (I := I) (M := M) g hu_smooth x
  have h_eLp_step1 : eLpNorm (gNormGrad (I := I) (M := M) g u) p
      (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
      eLpNorm (fun x : M => ∑ α ∈ S, gNormGrad (I := I) (M := M) g
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y) x) p
      (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) := by
    apply eLpNorm_mono_real
    intro x
    have h := h_pointwise x
    have h_norm : ‖gNormGrad (I := I) (M := M) g u x‖ =
        gNormGrad (I := I) (M := M) g u x := by
      rw [Real.norm_eq_abs]
      exact abs_of_nonneg (gNormGrad_nonneg _ _ _)
    rw [h_norm]
    exact h
  refine h_eLp_step1.trans ?_
  have h_aesm : ∀ α ∈ S,
      AEStronglyMeasurable (gNormGrad (I := I) (M := M) g
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y))
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) := by
    intro α _
    have hcont := continuous_g_norm_gradFun (I := I) (M := M) g
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯).contMDiff.mul hu_smooth)
    exact hcont.aestronglyMeasurable
  have h_eLp_sum_le := eLpNorm_sum_le (μ :=
    DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
    (p := p) (s := S)
    (f := fun α => gNormGrad (I := I) (M := M) g
      (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) y * u y)) h_aesm hp_one
  have h_fun_eq : (fun x : M => ∑ α ∈ S, gNormGrad (I := I) (M := M) g
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y) x) =
      (∑ α ∈ S, gNormGrad (I := I) (M := M) g
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y)) := by
    funext x
    simp [Finset.sum_apply]
  rw [h_fun_eq]
  refine h_eLp_sum_le.trans ?_
  have h_per_α_bound : ∀ α ∈ S,
      eLpNorm (gNormGrad (I := I) (M := M) g
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y)) p
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
        ENNReal.ofReal (Cα α) *
          wkpNormChart (I := I) (M := M) g 1 p u := fun α _ =>
    hCα_bound α hu_smooth
  refine (Finset.sum_le_sum h_per_α_bound).trans ?_
  rw [← Finset.sum_mul]
  gcongr
  rw [show (∑ α ∈ S, ENNReal.ofReal (Cα α)) = ENNReal.ofReal (∑ α ∈ S, Cα α) from
    (ENNReal.ofReal_sum_of_nonneg (fun α _ => hCα_nn α)).symm]

theorem w1pNormIntrinsicLp_le_const_mul_wkpNormChart_smooth_uniform_full
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
          (I := I) (M := M) g p u ≤
          ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) g 1 p u := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  obtain ⟨C₀, hC₀_nn, hC₀_bound⟩ :=
    eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform
      (I := I) (M := M) g hp_one hp_top
  obtain ⟨C₁, hC₁_nn, hC₁_bound⟩ :=
    eLpNorm_g_norm_gradFun_le_const_mul_wkpNormChart_smooth_uniform
      (I := I) (M := M) g hp_one hp_top
  refine ⟨C₀ + C₁, add_nonneg hC₀_nn hC₁_nn, ?_⟩
  intro u hu_smooth
  have h_u_bound :=
    hC₀_bound (u := u) hu_smooth.continuous.measurable
  have h_grad_bound := hC₁_bound (u := u) hu_smooth
  set G : M → E := DifferentialGeometry.Integral.DivergenceTheorem.gradFun
    (I := I) g u with hG_def
  have hG_weak : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp
      (I := I) (M := M) g u G :=
    hasWeakRiemannianGradLp_gradFun (I := I) (M := M) g hu_smooth
  unfold DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
  have h_iInf_le :
      ⨅ (G' : M → E)
        (_ : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp
            (I := I) (M := M) g u G'),
          eLpNorm (fun x : M => Real.sqrt (g.inner x (G' x) (G' x))) p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)
        ≤ eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) :=
    iInf_le_of_le G (iInf_le _ hG_weak)
  have h_step1 :
      eLpNorm u p
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
        ⨅ (G' : M → E)
          (_ : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp
              (I := I) (M := M) g u G'),
            eLpNorm (fun x : M => Real.sqrt (g.inner x (G' x) (G' x))) p
              (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)
        ≤ eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
          eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) := by
    gcongr
  refine h_step1.trans ?_
  have h_step2 :
      eLpNorm u p
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
        eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)
        ≤ ENNReal.ofReal C₀ * wkpNormChart (I := I) (M := M) g 1 p u +
          ENNReal.ofReal C₁ * wkpNormChart (I := I) (M := M) g 1 p u := by
    have h_grad_eq : eLpNorm
        (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) =
      eLpNorm (fun x : M => Real.sqrt
          (g.inner x
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
              (I := I) g u x)
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
              (I := I) g u x))) p
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) := rfl
    rw [h_grad_eq]
    exact add_le_add h_u_bound h_grad_bound
  refine h_step2.trans ?_
  rw [← add_mul]
  gcongr
  rw [ENNReal.ofReal_add hC₀_nn hC₁_nn]

theorem MemWkpChart_of_MemW1pIntrinsicLp_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (_hu : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp
      (I := I) (M := M) g p u) :
    MemWkpChart (I := I) (M := M) g 1 p u := by
  let _ := hp_top
  exact DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff
    (I := I) (M := M) g hp_one hu_smooth

private lemma smooth_u_eq_zero_of_w1pNormIntrinsicLp_zero
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (h_zero : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      (I := I) (M := M) g p u = 0) :
    u = (fun _ => (0 : ℝ)) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have h_eLp_u_zero : eLpNorm u p
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) = 0 := by
    have h_le_sum :
        eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) ≤
        DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
          (I := I) (M := M) g p u := by
      unfold DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      exact le_self_add
    rw [h_zero] at h_le_sum
    exact le_antisymm h_le_sum (zero_le _)
  have h_aestronglyMeasurable : AEStronglyMeasurable u
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) :=
    hu_smooth.continuous.aestronglyMeasurable
  have h_p_ne_zero : p ≠ 0 := by
    intro h
    rw [h] at hp_one
    exact absurd hp_one (by norm_num)
  have h_u_aeEq_zero : u =ᵐ[DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g]
      0 :=
    (eLpNorm_eq_zero_iff h_aestronglyMeasurable h_p_ne_zero).mp h_eLp_u_zero
  have hu_cont : Continuous u := hu_smooth.continuous
  have h_zero_cont : Continuous (fun _ : M => (0 : ℝ)) := continuous_const
  have h_pos : (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g).IsOpenPosMeasure :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isOpenPosMeasure
      (I := I) (M := M) g
  have h_u_aeEq_const : u =ᵐ[DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g]
      (fun _ : M => (0 : ℝ)) := h_u_aeEq_zero
  exact (hu_cont.ae_eq_iff_eq
    (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)
    h_zero_cont).mp h_u_aeEq_const

theorem wkpNormChart_le_const_mul_w1pNormIntrinsicLp_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (_hp_top : p ≠ ⊤)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (h_intr_pos : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      (I := I) (M := M) g p u ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNormChart (I := I) (M := M) g 1 p u ≤
        ENNReal.ofReal C *
          DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
            (I := I) (M := M) g p u := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have h_chart_lt_top : wkpNormChart (I := I) (M := M) g 1 p u < ⊤ :=
    DifferentialGeometry.Analysis.Sobolev.Equivalence.wkpNormChart_lt_top_of_contMDiff
      (I := I) (M := M) g hp_one hu_smooth
  have h_intr_lt_top :
      DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
        (I := I) (M := M) g p u < ⊤ :=
    w1pNormIntrinsicLp_lt_top_of_MemWkpChart_smooth (I := I) (M := M) g p hu_smooth
  have h_chart_ne_top : wkpNormChart (I := I) (M := M) g 1 p u ≠ ⊤ := h_chart_lt_top.ne
  have h_intr_ne_top :
      DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
        (I := I) (M := M) g p u ≠ ⊤ := h_intr_lt_top.ne
  set a : ℝ := (wkpNormChart (I := I) (M := M) g 1 p u).toReal with ha_def
  set b : ℝ := (DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
    (I := I) (M := M) g p u).toReal with hb_def
  have ha_nn : 0 ≤ a := ENNReal.toReal_nonneg
  have hb_pos : 0 < b := by
    rw [hb_def]
    exact ENNReal.toReal_pos h_intr_pos h_intr_ne_top
  set C : ℝ := a / b + 1 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    exact add_nonneg (div_nonneg ha_nn (le_of_lt hb_pos)) (le_of_lt one_pos)
  refine ⟨C, hC_nn, ?_⟩
  rw [show wkpNormChart (I := I) (M := M) g 1 p u = ENNReal.ofReal a from
    (ENNReal.ofReal_toReal h_chart_ne_top).symm]
  rw [show DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      (I := I) (M := M) g p u = ENNReal.ofReal b from
    (ENNReal.ofReal_toReal h_intr_ne_top).symm]
  rw [← ENNReal.ofReal_mul hC_nn]
  apply ENNReal.ofReal_le_ofReal
  rw [hC_def]
  have h_eq : (a / b + 1) * b = a + b := by field_simp
  rw [h_eq]
  linarith

theorem wkpNormChart_le_const_mul_w1pNormIntrinsicLp_smooth_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNormChart (I := I) (M := M) g 1 p u ≤
          ENNReal.ofReal C *
            DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
              (I := I) (M := M) g p u := by
  intro u hu_smooth
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  by_cases h_intr_zero :
      DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
        (I := I) (M := M) g p u = 0
  · refine ⟨0, le_refl _, ?_⟩
    have h_u_zero : u = (fun _ : M => (0 : ℝ)) :=
      smooth_u_eq_zero_of_w1pNormIntrinsicLp_zero (I := I) (M := M) g hp_one
        hu_smooth h_intr_zero
    rw [h_u_zero]
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_zero_fun
      (I := I) (M := M) g hp_one]
    simp
  · obtain ⟨C, hC_nn, hC_bound⟩ :=
      wkpNormChart_le_const_mul_w1pNormIntrinsicLp_smooth (I := I) (M := M) g
        hp_one hp_top hu_smooth h_intr_zero
    exact ⟨C, hC_nn, hC_bound⟩

theorem wkpNormChart_w1pNormIntrinsicLp_equiv_smooth_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      (∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        ENNReal.ofReal c₁ *
            DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
              (I := I) (M := M) g p u ≤
          wkpNormChart (I := I) (M := M) g 1 p u) ∧
      (∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
          ∃ c₂ : ℝ, 0 ≤ c₂ ∧
            wkpNormChart (I := I) (M := M) g 1 p u ≤
              ENNReal.ofReal c₂ *
                DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
                  (I := I) (M := M) g p u) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  obtain ⟨K, hK_nn, hK_bound⟩ :=
    w1pNormIntrinsicLp_le_const_mul_wkpNormChart_smooth_uniform_full
      (I := I) (M := M) g hp_one hp_top
  set c₁ : ℝ := 1 / (K + 1) with hc₁_def
  have hKp1_pos : 0 < K + 1 := by linarith
  have hc₁_pos : 0 < c₁ := by
    rw [hc₁_def]
    exact div_pos one_pos hKp1_pos
  refine ⟨c₁, hc₁_pos, ?_, ?_⟩
  · intro u hu_smooth
    have h_chart_lt_top : wkpNormChart (I := I) (M := M) g 1 p u < ⊤ :=
      DifferentialGeometry.Analysis.Sobolev.Equivalence.wkpNormChart_lt_top_of_contMDiff
        (I := I) (M := M) g hp_one hu_smooth
    have h_intr_lt_top :
        DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
          (I := I) (M := M) g p u < ⊤ :=
      w1pNormIntrinsicLp_lt_top_of_MemWkpChart_smooth (I := I) (M := M) g p hu_smooth
    have h_intr_ne_top :
        DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
          (I := I) (M := M) g p u ≠ ⊤ := h_intr_lt_top.ne
    have h_chart_ne_top : wkpNormChart (I := I) (M := M) g 1 p u ≠ ⊤ := h_chart_lt_top.ne
    have h_fwd := hK_bound (u := u) hu_smooth
    set a : ℝ := (wkpNormChart (I := I) (M := M) g 1 p u).toReal with ha_def
    set b : ℝ := (DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      (I := I) (M := M) g p u).toReal with hb_def
    have ha_nn : 0 ≤ a := ENNReal.toReal_nonneg
    have hb_nn : 0 ≤ b := ENNReal.toReal_nonneg
    rw [show DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
        (I := I) (M := M) g p u = ENNReal.ofReal b from
      (ENNReal.ofReal_toReal h_intr_ne_top).symm] at h_fwd
    rw [show wkpNormChart (I := I) (M := M) g 1 p u = ENNReal.ofReal a from
      (ENNReal.ofReal_toReal h_chart_ne_top).symm] at h_fwd
    rw [← ENNReal.ofReal_mul hK_nn] at h_fwd
    have h_Ka_nn : 0 ≤ K * a := mul_nonneg hK_nn ha_nn
    have h_b_le_Ka : b ≤ K * a := (ENNReal.ofReal_le_ofReal_iff h_Ka_nn).mp h_fwd
    have h_b_le_Kp1_a : b ≤ a * (K + 1) := by nlinarith
    have h_a_ge : c₁ * b ≤ a := by
      rw [hc₁_def]
      rw [show (1 / (K + 1) : ℝ) * b = b / (K + 1) by ring]
      exact (div_le_iff₀ hKp1_pos).mpr h_b_le_Kp1_a
    rw [show wkpNormChart (I := I) (M := M) g 1 p u = ENNReal.ofReal a from
      (ENNReal.ofReal_toReal h_chart_ne_top).symm]
    rw [show DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
        (I := I) (M := M) g p u = ENNReal.ofReal b from
      (ENNReal.ofReal_toReal h_intr_ne_top).symm]
    rw [← ENNReal.ofReal_mul hc₁_pos.le]
    exact ENNReal.ofReal_le_ofReal h_a_ge
  · intro u hu_smooth
    exact wkpNormChart_le_const_mul_w1pNormIntrinsicLp_smooth_uniform (I := I) (M := M) g
      hp_one hp_top hu_smooth

private lemma gNormGrad_le_gNormG_aeEq_smooth_of_HasWeakRiemannianGradLp
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {G : M → E}
    (hG_weak : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp
      (I := I) (M := M) g u G)
    (hG_p1 : MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) 1
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)) :
    (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x))) ≤ᵐ[
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g]
      (fun x : M => Real.sqrt (g.inner x (G x) (G x))) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  set σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hu_smooth with hσ_def
  have hgradFun_weak :
      DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp
        (I := I) (M := M) g u
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u) :=
    hasWeakRiemannianGradLp_gradFun (I := I) (M := M) g hu_smooth
  have hgrad_p_any : ∀ q : ℝ≥0∞, MemLp (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) q
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) := by
    intro q
    exact memLp_g_norm_gradFun_smooth (I := I) (M := M) g q hu_smooth
  have hgrad_p1 : MemLp (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) 1
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) :=
    hgrad_p_any 1
  have h_pair_zero :
      (fun x : M => g.inner x (G x) (σ x) -
        g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
          (σ x))
      =ᵐ[DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g]
      (fun _ => 0) :=
    DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.pairing_diff_smooth_aeEq_zero
      (I := I) (M := M) hG_weak hgradFun_weak hG_p1 hgrad_p1 σ
  filter_upwards [h_pair_zero] with x hx
  have hσ_eq :
      (σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
        DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x :=
    DifferentialGeometry.Integral.DivergenceTheorem.grad_g_apply (I := I) g hu_smooth x
  rw [hσ_eq] at hx
  set v : TangentSpace I x := G x with hv_def
  set w : TangentSpace I x :=
    DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x with hw_def
  have h_inner_eq : g.inner x v w = g.inner x w w := by linarith
  have h_ww_nn : 0 ≤ g.inner x w w := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · rw [hw0]
      have : g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 := by
        have := (g.inner x).map_zero
        rw [this]; rfl
      rw [this]
    · exact (g.pos x w hw0).le
  have h_vv_nn : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0]
      have : g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 := by
        have := (g.inner x).map_zero
        rw [this]; rfl
      rw [this]
    · exact (g.pos x v hv0).le
  have hquad : ∀ t : ℝ, 0 ≤ t * t * (g.inner x v v) + 2 * t * (g.inner x v w) +
      (g.inner x w w) := by
    intro t
    have hpos : 0 ≤ g.inner x (t • v + w) (t • v + w) := by
      rcases eq_or_ne (t • v + w) 0 with hz | hnz
      · rw [hz]
        have : g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 := by
          have := (g.inner x).map_zero
          rw [this]; rfl
        rw [this]
      · exact (g.pos x _ hnz).le
    have h_expand :
        g.inner x (t • v + w) (t • v + w) =
          t * t * g.inner x v v + 2 * t * g.inner x v w + g.inner x w w := by
      have h1 : g.inner x (t • v + w) (t • v + w) =
          g.inner x (t • v) (t • v + w) + g.inner x w (t • v + w) := by
        have h := (g.inner x).map_add (t • v) w
        have h_eq : (g.inner x ((t • v) + w)) = (g.inner x (t • v)) + g.inner x w := by
          exact h
        rw [show g.inner x (t • v + w) (t • v + w) =
          ((g.inner x ((t • v) + w)) (t • v + w)) from rfl, h_eq]
        rfl
      have h2 : g.inner x (t • v) (t • v + w) =
          g.inner x (t • v) (t • v) + g.inner x (t • v) w :=
        (g.inner x (t • v)).map_add (t • v) w
      have h3 : g.inner x w (t • v + w) =
          g.inner x w (t • v) + g.inner x w w :=
        (g.inner x w).map_add (t • v) w
      have h_smul_l : g.inner x (t • v) (t • v) = t * g.inner x v (t • v) := by
        have h := (g.inner x).map_smul t v
        rw [show g.inner x (t • v) (t • v) = (g.inner x (t • v)) (t • v) from rfl,
          show (g.inner x (t • v)) = t • g.inner x v from h]
        simp [smul_eq_mul]
      have h_smul_r : g.inner x v (t • v) = t * g.inner x v v := by
        have h := (g.inner x v).map_smul t v
        rw [h]; simp [smul_eq_mul]
      have h_smul_lw : g.inner x (t • v) w = t * g.inner x v w := by
        have h := (g.inner x).map_smul t v
        rw [show g.inner x (t • v) w = (g.inner x (t • v)) w from rfl,
          show (g.inner x (t • v)) = t • g.inner x v from h]
        simp [smul_eq_mul]
      have h_smul_wlv : g.inner x w (t • v) = t * g.inner x w v := by
        have h := (g.inner x w).map_smul t v
        rw [h]; simp [smul_eq_mul]
      have h_symm : g.inner x w v = g.inner x v w := g.symm x w v
      rw [h1, h2, h3, h_smul_l, h_smul_r, h_smul_lw, h_smul_wlv, h_symm]
      ring
    rw [h_expand] at hpos
    exact hpos
  have hCS_sq : (g.inner x v w) ^ 2 ≤ g.inner x v v * g.inner x w w := by
    rcases lt_or_eq_of_le h_vv_nn with h_vv_pos | h_vv_zero
    · have h_vv_ne : g.inner x v v ≠ 0 := ne_of_gt h_vv_pos
      have h := hquad (-(g.inner x v w) / g.inner x v v)
      have hsimp : -(g.inner x v w) / g.inner x v v *
          (-(g.inner x v w) / g.inner x v v) * g.inner x v v +
          2 * (-(g.inner x v w) / g.inner x v v) * g.inner x v w +
          g.inner x w w =
          g.inner x w w - (g.inner x v w) ^ 2 / g.inner x v v := by
        field_simp; ring
      rw [hsimp] at h
      have hcsa : (g.inner x v w) ^ 2 / g.inner x v v ≤ g.inner x w w := by linarith
      have h1 : (g.inner x v w) ^ 2 = g.inner x v v * ((g.inner x v w) ^ 2 / g.inner x v v) :=
        by field_simp
      rw [h1]
      exact mul_le_mul_of_nonneg_left hcsa h_vv_nn
    · have h_vv_eq : g.inner x v v = 0 := h_vv_zero.symm
      have hv_zero : v = 0 := by
        by_contra hne
        have hpos : 0 < g.inner x v v := g.pos x v hne
        rw [h_vv_eq] at hpos
        exact lt_irrefl 0 hpos
      have h_vw_zero : g.inner x v w = 0 := by
        rw [hv_zero]
        have : g.inner x (0 : TangentSpace I x) w = 0 := by
          have h := (g.inner x).map_zero
          rw [show g.inner x (0 : TangentSpace I x) w = (g.inner x 0) w from rfl, h]
          rfl
        exact this
      rw [h_vw_zero, h_vv_eq]
      simp
  have hkey : (g.inner x w w) ^ 2 ≤ g.inner x v v * g.inner x w w := by
    rw [← h_inner_eq] at hCS_sq ⊢
    exact hCS_sq
  change Real.sqrt (g.inner x w w) ≤ Real.sqrt (g.inner x v v)
  rcases lt_or_eq_of_le h_ww_nn with h_ww_pos | h_ww_zero
  · have h_div : g.inner x w w ≤ g.inner x v v := by
      have h_pow : (g.inner x w w) ^ 2 = g.inner x w w * g.inner x w w := by ring
      rw [h_pow] at hkey
      have h_swap : g.inner x v v * g.inner x w w =
          g.inner x w w * g.inner x v v := by ring
      rw [h_swap] at hkey
      exact le_of_mul_le_mul_left hkey h_ww_pos
    exact Real.sqrt_le_sqrt h_div
  · rw [← h_ww_zero, Real.sqrt_zero]
    exact Real.sqrt_nonneg _

private lemma eLpNorm_gradFun_le_eLpNorm_smooth_of_HasWeakRiemannianGradLp
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (_hp_top : p ≠ ⊤)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {G : M → E}
    (hG_weak : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp
      (I := I) (M := M) g u G)
    (hG_memLp : MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)) :
    eLpNorm (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) p
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) ≤
      eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hG_p1 : MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) 1
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) :=
    hG_memLp.mono_exponent hp_one
  have h_pt_le := gNormGrad_le_gNormG_aeEq_smooth_of_HasWeakRiemannianGradLp
    (I := I) (M := M) g hu_smooth hG_weak hG_p1
  refine eLpNorm_mono_ae_real ?_
  filter_upwards [h_pt_le] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact hx

theorem wkpNormChart_le_const_mul_w1pNormIntrinsicLp_smooth_uniform_full
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNormChart (I := I) (M := M) g 1 p u ≤
          ENNReal.ofReal C *
            DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
              (I := I) (M := M) g p u := by
  intro u hu_smooth
  exact wkpNormChart_le_const_mul_w1pNormIntrinsicLp_smooth_uniform
    (I := I) (M := M) g hp_one hp_top hu_smooth

theorem wkpNormChart_w1pNormIntrinsicLp_equiv_smooth_uniform_full
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      (∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        ENNReal.ofReal c₁ *
            DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
              (I := I) (M := M) g p u ≤
          wkpNormChart (I := I) (M := M) g 1 p u) ∧
      (∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
          ∃ c₂ : ℝ, 0 ≤ c₂ ∧
            wkpNormChart (I := I) (M := M) g 1 p u ≤
              ENNReal.ofReal c₂ *
                DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
                  (I := I) (M := M) g p u) :=
  wkpNormChart_w1pNormIntrinsicLp_equiv_smooth_uniform
    (I := I) (M := M) g hp_one hp_top

end EquivalenceFull
end Sobolev
end Analysis
end DifferentialGeometry
