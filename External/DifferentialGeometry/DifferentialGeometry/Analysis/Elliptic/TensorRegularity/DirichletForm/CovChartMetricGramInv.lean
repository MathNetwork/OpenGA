import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartFormLowerOrder


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators Matrix
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

abbrev CompIdx (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (r s : ℕ) : Type _ :=
  (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E))

noncomputable def covChartMetricGramMatrix
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    Matrix (CompIdx E r s) (CompIdx E r s) ℝ :=
  Matrix.of (fun P Q => covChartMetricGram (I := I) (M := M) g r s α P Q y)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma covChartMetricGramMatrix_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    (P Q : CompIdx E r s) :
    covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q =
      covChartMetricGram (I := I) (M := M) g r s α P Q y := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem covChartMetricGramMatrix_isSymm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    (covChartMetricGramMatrix (I := I) (M := M) g r s α y).IsSymm := by
  refine Matrix.IsSymm.ext (fun P Q => ?_)
  rw [covChartMetricGramMatrix_apply, covChartMetricGramMatrix_apply]
  exact covChartMetricGram_symm (I := I) (M := M) g r s α Q P y

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartInner_eq_gramMatrix_quadratic
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (X Y : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) X Y =
      ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
        covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q *
          (tensorChartComponentProjection (E := E) r s P.1 P.2 X *
            tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y) := by
  classical
  have hX : X = ∑ P : CompIdx E r s,
      tensorChartComponentProjection (E := E) r s P.1 P.2 X •
        tensorChartBasisElement (E := E) r s P.1 P.2 := by
    rw [Fintype.sum_prod_type
      (f := fun P : CompIdx E r s =>
        tensorChartComponentProjection (E := E) r s P.1 P.2 X •
          tensorChartBasisElement (E := E) r s P.1 P.2)]
    exact tensorRSModel_eq_sum_basis (E := E) r s X
  have hY : Y = ∑ Q : CompIdx E r s,
      tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y •
        tensorChartBasisElement (E := E) r s Q.1 Q.2 := by
    rw [Fintype.sum_prod_type
      (f := fun Q : CompIdx E r s =>
        tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y •
          tensorChartBasisElement (E := E) r s Q.1 Q.2)]
    exact tensorRSModel_eq_sum_basis (E := E) r s Y
  conv_lhs => rw [hX]
  rw [show chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (∑ P : CompIdx E r s,
          tensorChartComponentProjection (E := E) r s P.1 P.2 X •
            tensorChartBasisElement (E := E) r s P.1 P.2) Y =
      ∑ P : CompIdx E r s,
        tensorChartComponentProjection (E := E) r s P.1 P.2 X *
          chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            (tensorChartBasisElement (E := E) r s P.1 P.2) Y from ?_]
  · refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [show chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (tensorChartBasisElement (E := E) r s P.1 P.2) Y =
        chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (tensorChartBasisElement (E := E) r s P.1 P.2)
          (∑ Q : CompIdx E r s,
            tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y •
              tensorChartBasisElement (E := E) r s Q.1 Q.2) from by rw [← hY]]
    rw [show chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (tensorChartBasisElement (E := E) r s P.1 P.2)
          (∑ Q : CompIdx E r s,
            tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y •
              tensorChartBasisElement (E := E) r s Q.1 Q.2) =
        ∑ Q : CompIdx E r s,
          tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y *
            chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              (tensorChartBasisElement (E := E) r s P.1 P.2)
              (tensorChartBasisElement (E := E) r s Q.1 Q.2) from ?_]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      rw [covChartMetricGramMatrix_apply, covChartMetricGram_def]
      ring
    · induction (Finset.univ : Finset (CompIdx E r s)) using Finset.induction with
      | empty =>
          rw [Finset.sum_empty, Finset.sum_empty]
          rw [show (0 : TensorRSModel r s ℝ E) =
              (0 : ℝ) • tensorChartBasisElement (E := E) r s P.1 P.2 from
            (zero_smul ℝ _).symm]
          rw [chartTensorInnerPointwise_rs_model_smul_right, zero_mul]
      | insert Q A hQ ih =>
          rw [Finset.sum_insert hQ, Finset.sum_insert hQ]
          rw [chartTensorInnerPointwise_rs_model_add_right,
            chartTensorInnerPointwise_rs_model_smul_right, ih]
  · induction (Finset.univ : Finset (CompIdx E r s)) using Finset.induction with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : TensorRSModel r s ℝ E) =
            (0 : ℝ) • (0 : TensorRSModel r s ℝ E) from
          (smul_zero (0 : ℝ)).symm]
        rw [chartTensorInnerPointwise_rs_model_smul_left, zero_mul]
    | insert P A hP ih =>
        rw [Finset.sum_insert hP, Finset.sum_insert hP]
        rw [chartTensorInnerPointwise_rs_model_add_left,
          chartTensorInnerPointwise_rs_model_smul_left, ih]

private noncomputable def gramCoeffTensor (r s : ℕ) (v : CompIdx E r s → ℝ) :
    TensorRSModel r s ℝ E :=
  ∑ P : CompIdx E r s, v P • tensorChartBasisElement (E := E) r s P.1 P.2

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma tensorChartComponentProjection_gramCoeffTensor (r s : ℕ)
    (v : CompIdx E r s → ℝ) (P₀ : CompIdx E r s) :
    tensorChartComponentProjection (E := E) r s P₀.1 P₀.2
        (gramCoeffTensor (E := E) r s v) = v P₀ := by
  classical
  rw [gramCoeffTensor, map_sum]
  rw [Finset.sum_eq_single P₀]
  · rw [map_smul, smul_eq_mul,
      tensorChartComponentProjection_basisElement (E := E) r s P₀.1 P₀.1 P₀.2 P₀.2]
    simp
  · intro P _ hP
    rw [map_smul, smul_eq_mul,
      tensorChartComponentProjection_basisElement (E := E) r s P₀.1 P.1 P₀.2 P.2]
    by_cases h1 : P₀.1 = P.1
    · by_cases h2 : P.2 = P₀.2
      · have hPP₀ : P = P₀ := Prod.ext h1.symm h2
        exact absurd hPP₀ hP
      · rw [if_neg h2, mul_zero, mul_zero]
    · rw [if_neg h1, zero_mul, mul_zero]
  · intro hP₀
    exact absurd (Finset.mem_univ P₀) hP₀

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma gramCoeffTensor_ne_zero (r s : ℕ) {v : CompIdx E r s → ℝ}
    (hv : v ≠ 0) :
    gramCoeffTensor (E := E) r s v ≠ 0 := by
  intro hzero
  apply hv
  funext P₀
  have hproj := tensorChartComponentProjection_gramCoeffTensor (E := E) r s v P₀
  rw [hzero, map_zero] at hproj
  exact hproj.symm

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma gramMatrix_star_dotProduct_mulVec
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    (v : CompIdx E r s → ℝ) :
    star v ⬝ᵥ (covChartMetricGramMatrix (I := I) (M := M) g r s α y *ᵥ v) =
      ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
        v P * covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q *
          v Q := by
  classical
  change (∑ P : CompIdx E r s,
      star v P * (covChartMetricGramMatrix (I := I) (M := M) g r s α y *ᵥ v) P) =
    ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
      v P * covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q * v Q
  refine Finset.sum_congr rfl (fun P _ => ?_)
  change star (v P) *
      (∑ Q : CompIdx E r s,
        covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q * v Q) =
    ∑ Q : CompIdx E r s,
      v P * covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q * v Q
  rw [Finset.mul_sum, star_trivial]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  ring

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covChartMetricGramMatrix_posDef
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (covChartMetricGramMatrix (I := I) (M := M) g r s α y).PosDef := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hb_chart
  have hSymm : (covChartMetricGramMatrix (I := I) (M := M) g r s α y).IsSymm :=
    covChartMetricGramMatrix_isSymm (I := I) (M := M) g r s α y
  have hHerm :
      (covChartMetricGramMatrix (I := I) (M := M) g r s α y).IsHermitian := by
    refine Matrix.IsHermitian.ext (fun P Q => ?_)
    rw [star_trivial]
    exact hSymm.apply P Q
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hHerm (fun v hv => ?_)
  rw [gramMatrix_star_dotProduct_mulVec (I := I) (M := M) g r s α y v]
  have hquad := chartInner_eq_gramMatrix_quadratic (I := I) (M := M) g r s α
    (y := y) (gramCoeffTensor (E := E) r s v) (gramCoeffTensor (E := E) r s v)
  have hsum_eq :
      (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q *
            (tensorChartComponentProjection (E := E) r s P.1 P.2
                (gramCoeffTensor (E := E) r s v) *
              tensorChartComponentProjection (E := E) r s Q.1 Q.2
                (gramCoeffTensor (E := E) r s v))) =
        ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          v P * covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q *
            v Q := by
    refine Finset.sum_congr rfl (fun P _ => ?_)
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [tensorChartComponentProjection_gramCoeffTensor (E := E) r s v P,
      tensorChartComponentProjection_gramCoeffTensor (E := E) r s v Q]
    ring
  rw [hsum_eq] at hquad
  rw [← hquad, ← hb_def]
  exact chartTensorInnerPointwise_rs_model_pos_of_ne_zero (I := I) (M := M)
    g r s α hb_base (gramCoeffTensor_ne_zero (E := E) r s hv)

noncomputable def covChartMetricGramInv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    Matrix (CompIdx E r s) (CompIdx E r s) ℝ :=
  (covChartMetricGramMatrix (I := I) (M := M) g r s α y)⁻¹

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covChartMetricGramMatrix_det_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    0 < (covChartMetricGramMatrix (I := I) (M := M) g r s α y).det :=
  (covChartMetricGramMatrix_posDef (I := I) (M := M) g r s α hy).det_pos

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covChartMetricGramInv_mul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covChartMetricGramInv (I := I) (M := M) g r s α y *
        covChartMetricGramMatrix (I := I) (M := M) g r s α y = 1 := by
  rw [covChartMetricGramInv]
  exact Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr
      (ne_of_gt (covChartMetricGramMatrix_det_pos (I := I) (M := M) g r s α hy)))

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem mul_covChartMetricGramInv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covChartMetricGramMatrix (I := I) (M := M) g r s α y *
        covChartMetricGramInv (I := I) (M := M) g r s α y = 1 := by
  rw [covChartMetricGramInv]
  exact Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr
      (ne_of_gt (covChartMetricGramMatrix_det_pos (I := I) (M := M) g r s α hy)))

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covChartMetricGramMatrix_entry_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P Q : CompIdx E r s) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q)
      (chartTargetEuclid (I := I) (M := M) α) :=
  covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covChartMetricGramMatrix_det_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        (covChartMetricGramMatrix (I := I) (M := M) g r s α y).det)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hexp :
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (covChartMetricGramMatrix (I := I) (M := M) g r s α y).det)
        = fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            ∑ σ : Equiv.Perm (CompIdx E r s),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ P : CompIdx E r s,
                  covChartMetricGramMatrix (I := I) (M := M) g r s α y (σ P) P := by
    funext y
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine ContDiffOn.sum (fun σ _ => ?_)
  refine ContDiffOn.mul contDiffOn_const ?_
  refine contDiffOn_prod (fun P _ => ?_)
  exact covChartMetricGramMatrix_entry_contDiffOn (I := I) (M := M) g r s α
    (σ P) P

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covChartMetricGramMatrix_adjugate_entry_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P Q : CompIdx E r s) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        (covChartMetricGramMatrix (I := I) (M := M) g r s α y).adjugate P Q)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hexp :
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (covChartMetricGramMatrix (I := I) (M := M) g r s α y).adjugate P Q)
        = fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            ∑ σ : Equiv.Perm (CompIdx E r s),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ K : CompIdx E r s,
                  (covChartMetricGramMatrix (I := I) (M := M) g r s α y).updateRow Q
                    (Pi.single P (1 : ℝ)) (σ K) K := by
    funext y
    rw [Matrix.adjugate_apply, Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine ContDiffOn.sum (fun σ _ => ?_)
  refine ContDiffOn.mul contDiffOn_const ?_
  refine contDiffOn_prod (fun K _ => ?_)
  by_cases hσK : σ K = Q
  · have heq :
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            (covChartMetricGramMatrix (I := I) (M := M) g r s α y).updateRow Q
              (Pi.single P (1 : ℝ)) (σ K) K)
          = fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
              (Pi.single (M := fun _ : CompIdx E r s => ℝ) P (1 : ℝ)) K := by
      funext y
      rw [hσK, Matrix.updateRow_self]
    rw [heq]
    exact contDiffOn_const
  · have heq :
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            (covChartMetricGramMatrix (I := I) (M := M) g r s α y).updateRow Q
              (Pi.single P (1 : ℝ)) (σ K) K)
          = fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
              covChartMetricGramMatrix (I := I) (M := M) g r s α y (σ K) K := by
      funext y
      rw [Matrix.updateRow_ne hσK]
    rw [heq]
    exact covChartMetricGramMatrix_entry_contDiffOn (I := I) (M := M) g r s α
      (σ K) K

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covChartMetricGramInv_entry_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P Q : CompIdx E r s) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        covChartMetricGramInv (I := I) (M := M) g r s α y P Q)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hcongr : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      covChartMetricGramInv (I := I) (M := M) g r s α y P Q =
        ((covChartMetricGramMatrix (I := I) (M := M) g r s α y).det)⁻¹ *
          (covChartMetricGramMatrix (I := I) (M := M) g r s α y).adjugate P Q := by
    intro y hy
    rw [covChartMetricGramInv, Matrix.inv_def]
    rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    exact Ring.inverse_eq_inv _
  refine ContDiffOn.congr ?_ hcongr
  refine ContDiffOn.mul ?_
    (covChartMetricGramMatrix_adjugate_entry_contDiffOn (I := I) (M := M)
      g r s α P Q)
  intro y hy
  have hdet_pos := covChartMetricGramMatrix_det_pos (I := I) (M := M) g r s α hy
  have hdet_ne :
      (covChartMetricGramMatrix (I := I) (M := M) g r s α y).det ≠ 0 :=
    ne_of_gt hdet_pos
  have hsmooth_inv : ContDiffAt ℝ ∞ (fun u : ℝ => u⁻¹)
      (covChartMetricGramMatrix (I := I) (M := M) g r s α y).det :=
    contDiffAt_inv _ hdet_ne
  have h_at := covChartMetricGramMatrix_det_contDiffOn (I := I) (M := M)
    g r s α y hy
  exact hsmooth_inv.comp_contDiffWithinAt y h_at

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem covChartMetricGramInv_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    (P Q : CompIdx E r s) :
    covChartMetricGramInv (I := I) (M := M) g r s α y P Q =
      covChartMetricGramInv (I := I) (M := M) g r s α y Q P := by
  classical
  have hSymm : (covChartMetricGramMatrix (I := I) (M := M) g r s α y).IsSymm :=
    covChartMetricGramMatrix_isSymm (I := I) (M := M) g r s α y
  have hInvSymm : (covChartMetricGramInv (I := I) (M := M) g r s α y).IsSymm := by
    unfold Matrix.IsSymm
    rw [covChartMetricGramInv, Matrix.transpose_nonsing_inv, hSymm.eq]
  exact hInvSymm.apply Q P

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
