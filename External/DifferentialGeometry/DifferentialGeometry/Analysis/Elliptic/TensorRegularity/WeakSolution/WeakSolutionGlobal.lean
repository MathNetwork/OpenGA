import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.ChartWeakIdentity
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.SourcePairing
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.ChartIntegrationByParts


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter MeasureTheory
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
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

noncomputable def lowerOrderRotationLOCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) (Q : CompIdx E r s) :
    EuclN → ℝ :=
  fun y =>
    ∑ p : CompIdx E r s,
      covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Q.1 p.1 Q.2 p.2 y *
        covChartMetricGramInv (I := I) (M := M) g r s α y p P₀

noncomputable def covLowerOrderRotationGradCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    ∑ P : CompIdx E r s,
      ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          ∑ k : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
              covDerivLowerOrderTerm (I := I) (M := M) g r s T α k P.1 P.2 y *
              covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma covLowerOrderRotationGradCoeff_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) (y : EuclN) :
    covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y =
      ∑ P : CompIdx E r s,
        ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                covDerivLowerOrderTerm (I := I) (M := M) g r s T α k P.1 P.2 y *
                covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ := rfl

noncomputable def covLowerOrderRotationValueCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) : EuclN → ℝ :=
  fun y =>
    ∑ P : CompIdx E r s,
      ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                (euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s T α P.1 P.2)) y *
                    lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y
                  + covDerivLowerOrderTerm (I := I) (M := M)
                        g r s T α k P.1 P.2 y *
                      euclidPartial (E := E) l
                        (gramInvEntry (I := I) (M := M) g r s α Q P₀) y
                  + covDerivLowerOrderTerm (I := I) (M := M)
                        g r s T α k P.1 P.2 y *
                      lowerOrderRotationLOCoeff (I := I) (M := M)
                        g r s α P₀ l Q y)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma covLowerOrderRotationValueCoeff_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) (y : EuclN) :
    covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y =
      ∑ P : CompIdx E r s,
        ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                  (euclidPartial (E := E) k
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s T α P.1 P.2)) y *
                      lowerOrderRotationLOCoeff (I := I) (M := M)
                        g r s α P₀ l Q y
                    + covDerivLowerOrderTerm (I := I) (M := M)
                          g r s T α k P.1 P.2 y *
                        euclidPartial (E := E) l
                          (gramInvEntry (I := I) (M := M) g r s α Q P₀) y
                    + covDerivLowerOrderTerm (I := I) (M := M)
                          g r s T α k P.1 P.2 y *
                        lowerOrderRotationLOCoeff (I := I) (M := M)
                          g r s α P₀ l Q y) := rfl

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivLowerOrderTerm_rotatedTestSection_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (l : Fin (Module.finrank ℝ E)) (Q : CompIdx E r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
        α l Q.1 Q.2 y =
      lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y *
        chartPushedRaw I α χ y := by
  classical
  rw [covDerivLowerOrderTerm_def, lowerOrderRotationLOCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [rotatedTestSection_chartComp (I := I) (M := M) g r s α P₀ hχs hχt p hy]
  ring

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covLowerOrderIntegrand_rotated_collapse
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covLowerOrderIntegrand (I := I) (M := M) g r s T
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α y =
      covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
          chartPushedRaw I α χ y +
        ∑ l : Fin (Module.finrank ℝ E),
          covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
            euclidPartial (E := E) l (chartPushedRaw I α χ) y := by
  classical
  rw [covLowerOrderIntegrand_def, covLowerOrderRotationValueCoeff_def]
  unfold covLowerOrderRotationGradCoeff
  have hleibniz : ∀ Q : CompIdx E r s, ∀ l : Fin (Module.finrank ℝ E),
      euclidPartial (E := E) l
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s
              (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
              α Q.1 Q.2)) y =
        euclidPartial (E := E) l
            (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
          chartPushedRaw I α χ y +
        covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ *
          euclidPartial (E := E) l (chartPushedRaw I α χ) y := fun Q l =>
    euclidPartial_chartPushedRaw_rotatedTestSection_eqOn (I := I) (M := M)
      g r s α P₀ hχs hχt Q l hy
  have hsummand : ∀ P Q : CompIdx E r s, ∀ k l : Fin (Module.finrank ℝ E),
      chartInvGramEuclid (I := I) g α k l y *
          (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s T α P.1 P.2)) y *
              covDerivLowerOrderTerm (I := I) (M := M) g r s
                (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
                α l Q.1 Q.2 y
            + covDerivLowerOrderTerm (I := I) (M := M) g r s T α k P.1 P.2 y *
                euclidPartial (E := E) l
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s
                      (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
                      α Q.1 Q.2)) y
            + covDerivLowerOrderTerm (I := I) (M := M) g r s T α k P.1 P.2 y *
                covDerivLowerOrderTerm (I := I) (M := M) g r s
                  (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
                  α l Q.1 Q.2 y) =
        chartInvGramEuclid (I := I) g α k l y *
            (euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M)
                      g r s T α P.1 P.2)) y *
                lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y
              + covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α k P.1 P.2 y *
                  euclidPartial (E := E) l
                    (gramInvEntry (I := I) (M := M) g r s α Q P₀) y
              + covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α k P.1 P.2 y *
                  lowerOrderRotationLOCoeff (I := I) (M := M)
                    g r s α P₀ l Q y) * chartPushedRaw I α χ y +
          chartInvGramEuclid (I := I) g α k l y *
              covDerivLowerOrderTerm (I := I) (M := M) g r s T α k P.1 P.2 y *
              covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ *
            euclidPartial (E := E) l (chartPushedRaw I α χ) y := by
    intro P Q k l
    rw [covDerivLowerOrderTerm_rotatedTestSection_eq (I := I) (M := M)
      g r s α P₀ hχs hχt l Q hy, hleibniz Q l]
    ring
  rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => by
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl
      (fun l _ => hsummand P Q k l))]))]
  have hsplit : ∀ P Q : CompIdx E r s,
      (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          (chartInvGramEuclid (I := I) g α k l y *
              (euclidPartial (E := E) k
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M)
                        g r s T α P.1 P.2)) y *
                  lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y
                + covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α k P.1 P.2 y *
                    euclidPartial (E := E) l
                      (gramInvEntry (I := I) (M := M) g r s α Q P₀) y
                + covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α k P.1 P.2 y *
                    lowerOrderRotationLOCoeff (I := I) (M := M)
                      g r s α P₀ l Q y) * chartPushedRaw I α χ y +
            chartInvGramEuclid (I := I) g α k l y *
                covDerivLowerOrderTerm (I := I) (M := M) g r s T α k P.1 P.2 y *
                covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ *
              euclidPartial (E := E) l (chartPushedRaw I α χ) y)) =
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
              (euclidPartial (E := E) k
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M)
                        g r s T α P.1 P.2)) y *
                  lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y
                + covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α k P.1 P.2 y *
                    euclidPartial (E := E) l
                      (gramInvEntry (I := I) (M := M) g r s α Q P₀) y
                + covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α k P.1 P.2 y *
                    lowerOrderRotationLOCoeff (I := I) (M := M)
                      g r s α P₀ l Q y)) * chartPushedRaw I α χ y +
          ∑ l : Fin (Module.finrank ℝ E),
            (∑ k : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                covDerivLowerOrderTerm (I := I) (M := M) g r s T α k P.1 P.2 y *
                covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀) *
              euclidPartial (E := E) l (chartPushedRaw I α χ) y := by
    intro P Q
    simp only [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_mul]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => by
    rw [hsplit P Q, mul_add]))]
  simp only [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [mul_assoc]
  · have hLHS :
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ l : Fin (Module.finrank ℝ E),
              (∑ k : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                  covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α k P.1 P.2 y *
                  covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀) *
                euclidPartial (E := E) l (chartPushedRaw I α χ) y) =
          ∑ l : Fin (Module.finrank ℝ E), ∑ P : CompIdx E r s,
            ∑ Q : CompIdx E r s, ∑ k : Fin (Module.finrank ℝ E),
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                (chartInvGramEuclid (I := I) g α k l y *
                  covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α k P.1 P.2 y *
                  covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀) *
                euclidPartial (E := E) l (chartPushedRaw I α χ) y := by
      have h1 : ∀ P Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ∑ l : Fin (Module.finrank ℝ E),
                (∑ k : Fin (Module.finrank ℝ E),
                  chartInvGramEuclid (I := I) g α k l y *
                    covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α k P.1 P.2 y *
                    covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀) *
                  euclidPartial (E := E) l (chartPushedRaw I α χ) y =
            ∑ l : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                (chartInvGramEuclid (I := I) g α k l y *
                  covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α k P.1 P.2 y *
                  covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀) *
                euclidPartial (E := E) l (chartPushedRaw I α χ) y := by
        intro P Q
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [← mul_assoc, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl
        (fun Q _ => h1 P Q))]
      rw [Finset.sum_congr rfl (fun P (_ : P ∈ (Finset.univ : Finset (CompIdx E r s))) =>
        Finset.sum_comm (s := (Finset.univ : Finset (CompIdx E r s)))
          (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))))]
      rw [Finset.sum_comm]
    have hRHS :
        (∑ l : Fin (Module.finrank ℝ E),
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ∑ k : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                  covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α k P.1 P.2 y *
                  covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀) *
            euclidPartial (E := E) l (chartPushedRaw I α χ) y) =
          ∑ l : Fin (Module.finrank ℝ E), ∑ P : CompIdx E r s,
            ∑ Q : CompIdx E r s, ∑ k : Fin (Module.finrank ℝ E),
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                (chartInvGramEuclid (I := I) g α k l y *
                  covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α k P.1 P.2 y *
                  covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀) *
                euclidPartial (E := E) l (chartPushedRaw I α χ) y := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun P _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [hLHS, hRHS]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma euclidPartial_contDiffOn_target
    (α : M) (l : Fin (Module.finrank ℝ E))
    {u : EuclN → ℝ}
    (hu : ContDiffOn ℝ ∞ u (chartTargetEuclid (I := I) (M := M) α)) :
    ContDiffOn ℝ ∞ (euclidPartial (E := E) l u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hfderiv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ u z)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have hsucc : ContDiffOn ℝ ((∞ : WithTop ℕ∞) + 1) u
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]; exact hu
    have hfw : ContDiffOn ℝ ∞ (fderivWithin ℝ u
        (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_succ_iff_fderivWithin hopen.uniqueDiffOn).mp hsucc).2.2
    refine hfw.congr (fun z hz => ?_)
    exact (fderivWithin_of_isOpen (f := u) (𝕜 := ℝ) hopen hz).symm
  have hcomp : ContDiffOn ℝ ∞
      ((fun L : EuclN →L[ℝ] ℝ => L (EuclideanSpace.single l 1)) ∘
        (fun z => fderiv ℝ u z))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single l 1)).contDiff.comp_contDiffOn hfderiv
  refine hcomp.congr (fun z _ => ?_)
  rfl

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lowerOrderRotationLOCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) (Q : CompIdx E r s) :
    ContDiffOn ℝ ∞ (lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ContDiffOn.sum (fun p _ => ?_)
  exact (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
      g r s α l Q.1 p.1 Q.2 p.2).mul
    (covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α p P₀)

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivLowerOrderTerm_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (covDerivLowerOrderTerm (I := I) (M := M) g r s T α k Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g r s T α k Idx Jdx
    (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
      (I := I) (M := M) g r s T α Idx' Jdx')

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covLowerOrderRotationGradCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold covLowerOrderRotationGradCoeff
  refine ContDiffOn.sum (fun P _ => ContDiffOn.sum (fun Q _ => ?_))
  refine (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul ?_
  refine ContDiffOn.sum (fun k _ => ?_)
  exact ((chartInvGramEuclid_contDiffOn (I := I) g α k l).mul
      (covDerivLowerOrderTerm_contDiffOn (I := I) (M := M) g r s T α k P.1 P.2)).mul
    (covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α Q P₀)

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covLowerOrderRotationValueCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) :
    ContDiffOn ℝ ∞
      (covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold covLowerOrderRotationValueCoeff
  refine ContDiffOn.sum (fun P _ => ContDiffOn.sum (fun Q _ => ?_))
  refine (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul ?_
  refine ContDiffOn.sum (fun k _ => ContDiffOn.sum (fun l _ => ?_))
  refine (chartInvGramEuclid_contDiffOn (I := I) g α k l).mul ?_
  have hloT : ContDiffOn ℝ ∞
      (covDerivLowerOrderTerm (I := I) (M := M) g r s T α k P.1 P.2)
      (chartTargetEuclid (I := I) (M := M) α) :=
    covDerivLowerOrderTerm_contDiffOn (I := I) (M := M) g r s T α k P.1 P.2
  have hloVc : ContDiffOn ℝ ∞
      (lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q)
      (chartTargetEuclid (I := I) (M := M) α) :=
    lowerOrderRotationLOCoeff_contDiffOn (I := I) (M := M) g r s α P₀ l Q
  have hdkT : ContDiffOn ℝ ∞
      (euclidPartial (E := E) k
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α P.1 P.2)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g r s T α k P.1 P.2
  have hdlGinv : ContDiffOn ℝ ∞
      (euclidPartial (E := E) l
        (gramInvEntry (I := I) (M := M) g r s α Q P₀))
      (chartTargetEuclid (I := I) (M := M) α) :=
    euclidPartial_contDiffOn_target (I := I) (M := M) α l
      (covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α Q P₀)
  exact ((hdkT.mul hloVc).add (hloT.mul hdlGinv)).add (hloT.mul hloVc)

noncomputable def covPrincipalRotationCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) : EuclN → ℝ :=
  fun y =>
    ∑ P : CompIdx E r s,
      ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                  euclidPartial (E := E) k
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M)
                        g r s T α P.1 P.2)) y *
                euclidPartial (E := E) l
                  (gramInvEntry (I := I) (M := M) g r s α Q P₀) y

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma covPrincipalRotationCoeff_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) (y : EuclN) :
    covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y =
      ∑ P : CompIdx E r s,
        ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                    euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s T α P.1 P.2)) y *
                  euclidPartial (E := E) l
                    (gramInvEntry (I := I) (M := M) g r s α Q P₀) y := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma covPrincipalRotationRemainder_eq_coeff_mul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) (y : EuclN) :
    covPrincipalRotationRemainder (I := I) (M := M) g r s T α P₀ χ hχs hχt y =
      covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y *
        chartPushedRaw I α χ y := by
  classical
  rw [covPrincipalRotationRemainder_def, covPrincipalRotationCoeff_def,
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  have hinner :
      (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramEuclid (I := I) g α k l y *
              euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s T α P.1 P.2)) y *
            (euclidPartial (E := E) l
                (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
              chartPushedRaw I α χ y)) =
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
                euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M)
                      g r s T α P.1 P.2)) y *
              euclidPartial (E := E) l
                (gramInvEntry (I := I) (M := M) g r s α Q P₀) y) * chartPushedRaw I α χ y := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [hinner, ← mul_assoc]

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covPrincipalRotationCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) :
    ContDiffOn ℝ ∞ (covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold covPrincipalRotationCoeff
  refine ContDiffOn.sum (fun P _ => ContDiffOn.sum (fun Q _ => ?_))
  refine (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul ?_
  refine ContDiffOn.sum (fun k _ => ContDiffOn.sum (fun l _ => ?_))
  refine ((chartInvGramEuclid_contDiffOn (I := I) g α k l).mul ?_).mul ?_
  · exact euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M)
      g r s T α k P.1 P.2
  · exact euclidPartial_contDiffOn_target (I := I) (M := M) α l
      (covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α Q P₀)

noncomputable def weightedGradCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y => densityOnEuclid (I := I) g α y *
    covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma weightedGradCoeff_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) :
    weightedGradCoeff (I := I) (M := M) g r s T α P₀ l =
      (fun y => densityOnEuclid (I := I) g α y *
        covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y) :=
  rfl

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem weightedGradCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  rw [weightedGradCoeff_eq]
  exact (densityOnEuclid_contDiffOn (I := I) g α).mul
    (covLowerOrderRotationGradCoeff_contDiffOn (I := I) (M := M) g r s T α P₀ l)

noncomputable def tensorComponentWeakRHS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (_hK : IsCompact K)
    (_hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s) : EuclN → ℝ := by
  classical
  exact fun y =>
    if y ∈ chartTargetEuclid (I := I) (M := M) α then
      densityOnEuclid (I := I) g α y *
          sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y -
        densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y -
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y +
        ∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y
    else 0

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tensorComponentWeakRHS_apply_of_mem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀ y =
      densityOnEuclid (I := I) g α y *
          sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y -
        densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y -
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y +
        ∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y := by
  unfold tensorComponentWeakRHS
  rw [if_pos hy]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tensorComponentWeakRHS_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    {y : EuclN} (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀ y = 0 := by
  unfold tensorComponentWeakRHS
  rw [if_neg hy]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma contDiff_of_contDiffOn_zero_off_closed_local
    {P : EuclN → ℝ} {U C : Set EuclN}
    (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hP : ContDiffOn ℝ ∞ P U) (hzero : ∀ y, y ∉ C → P y = 0) :
    ContDiff ℝ ∞ P := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact hP.contDiffAt (hU.mem_nhds hy)
  · have hyC : y ∉ C := fun hyC => hy (hCU hyC)
    have hy_nhds : Cᶜ ∈ 𝓝 y := hC.isOpen_compl.mem_nhds hyC
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hy_nhds] with z hz using hzero z hz

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_eq_zero_off_closed
    {u : EuclN → ℝ} {C : Set EuclN} (hC : IsClosed C)
    (hu : ∀ z, z ∉ C → u z = 0)
    (l : Fin (Module.finrank ℝ E)) {y : EuclN} (hy : y ∉ C) :
    euclidPartial (E := E) l u y = 0 := by
  classical
  have hy_nhds : Cᶜ ∈ 𝓝 y := hC.isOpen_compl.mem_nhds hy
  have hu_evt : u =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
    Filter.eventually_of_mem hy_nhds (fun z hz => hu z hz)
  rw [euclidPartial_def, Filter.EventuallyEq.fderiv_eq hu_evt,
    fderiv_const_apply, ContinuousLinearMap.zero_apply]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_eq_zero_of_open_zero
    {u : EuclN → ℝ} {U : Set EuclN} (hU : IsOpen U) {y : EuclN} (hy : y ∈ U)
    (hu : ∀ z ∈ U, u z = 0) (l : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) l u y = 0 := by
  classical
  have hu_evt : u =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
    Filter.eventually_of_mem (hU.mem_nhds hy) (fun z hz => hu z hz)
  rw [euclidPartial_def, Filter.EventuallyEq.fderiv_eq hu_evt,
    fderiv_const_apply, ContinuousLinearMap.zero_apply]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorComponentEuclid_eq_zero_off_image
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P : CompIdx E r s)
    {y : EuclN}
    (hy : y ∉ toEuclidean '' ((extChartAt I α) '' tsupport S.toFun)) :
    tensorComponentEuclid (I := I) (M := M) g r s S α P y = 0 := by
  classical
  by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [tensorComponentEuclid_def]
    refine chartPushedRaw_eq_zero_off_image_tsupport (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s S α P.1 P.2)
      α hyT (fun hmem => hy ?_)
    have hsub := tensorChartComponentRaw_tsupport_subset (I := I) (M := M)
      g r s S α P.1 P.2
    exact (Set.image_mono (Set.image_mono hsub)) hmem
  · exact tensorComponentEuclid_apply_of_notMem (I := I) (M := M) g r s S α P hyT

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma image_tsupport_isCompact
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (hS_supp : tsupport S.toFun ⊆ (chartAt H α).source) :
    IsCompact (toEuclidean '' ((extChartAt I α) '' tsupport S.toFun)) := by
  have hcontOn : ContinuousOn (extChartAt I α) (tsupport S.toFun) := by
    refine (continuousOn_extChartAt (I := I) α).mono ?_
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hS_supp hx
  have hTcompact : IsCompact (tsupport S.toFun) := S.hasCompactSupport
  have himg1 : IsCompact ((extChartAt I α) '' tsupport S.toFun) :=
    hTcompact.image_of_continuousOn hcontOn
  exact himg1.image (toEuclidean (E := E)).continuous

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma image_tsupport_subset_target
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (hS_supp : tsupport S.toFun ⊆ (chartAt H α).source) :
    toEuclidean '' ((extChartAt I α) '' tsupport S.toFun) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  rintro y ⟨w, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨(extChartAt I α) x, ?_, rfl⟩
  have hx_src : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hS_supp hx
  exact (extChartAt I α).map_source hx_src

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorComponentWeakRHS_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_supp : tsupport F.toFun ⊆ (chartAt H α).source) :
    ContDiff ℝ ∞
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  set CT : Set EuclN := toEuclidean '' ((extChartAt I α) '' tsupport T.toFun)
    with hCT_def
  set CF : Set EuclN := toEuclidean '' ((extChartAt I α) '' tsupport F.toFun)
    with hCF_def
  have hCT_compact : IsCompact CT :=
    image_tsupport_isCompact (I := I) (M := M) g r s T α hT_supp
  have hCF_compact : IsCompact CF :=
    image_tsupport_isCompact (I := I) (M := M) g r s F α hF_supp
  have hCT_target : CT ⊆ chartTargetEuclid (I := I) (M := M) α :=
    image_tsupport_subset_target (I := I) (M := M) g r s T α hT_supp
  have hCF_target : CF ⊆ chartTargetEuclid (I := I) (M := M) α :=
    image_tsupport_subset_target (I := I) (M := M) g r s F α hF_supp
  have hK'_compact : IsCompact (CT ∪ CF) := hCT_compact.union hCF_compact
  have hK'_target : CT ∪ CF ⊆ chartTargetEuclid (I := I) (M := M) α :=
    Set.union_subset hCT_target hCF_target
  have hdensity : ContDiffOn ℝ ∞ (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
    densityOnEuclid_contDiffOn (I := I) g α
  have hbody : ContDiffOn ℝ ∞
      (fun y : EuclN =>
        densityOnEuclid (I := I) g α y *
            sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y -
          densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y -
          densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y +
          ∑ l : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) l
              (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have hgrad : ∀ l : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞
          (euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l))
          (chartTargetEuclid (I := I) (M := M) α) := by
      intro l
      refine euclidPartial_contDiffOn_target (I := I) (M := M) α l ?_
      exact hdensity.mul (covLowerOrderRotationGradCoeff_contDiffOn
        (I := I) (M := M) g r s T α P₀ l)
    refine (((hdensity.mul (sourcePairingCoeff_contDiffOn
      (I := I) (M := M) g r s F α P₀)).sub
      (hdensity.mul (covPrincipalRotationCoeff_contDiffOn
        (I := I) (M := M) g r s T α P₀))).sub
      (hdensity.mul (covLowerOrderRotationValueCoeff_contDiffOn
        (I := I) (M := M) g r s T α P₀))).add ?_
    exact ContDiffOn.sum (fun l _ => hgrad l)
  have hcontDiffOn : ContDiffOn ℝ ∞
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine hbody.congr (fun y hy => ?_)
    exact (tensorComponentWeakRHS_apply_of_mem (I := I) (M := M)
      g r s T F α hK hK_target P₀ hy)
  have hzero : ∀ y, y ∉ CT ∪ CF →
      tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀ y = 0 := by
    intro y hy
    have hyCT : y ∉ CT := fun h => hy (Or.inl h)
    have hyCF : y ∉ CF := fun h => hy (Or.inr h)
    by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [tensorComponentWeakRHS_apply_of_mem (I := I) (M := M)
        g r s T F α hK hK_target P₀ hyT]
      have hS0 : sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y = 0 := by
        rw [sourcePairingCoeff_def]
        refine Finset.sum_eq_zero (fun Q _ => ?_)
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun P _ => ?_))
        rw [tensorComponentEuclid_eq_zero_off_image (I := I) (M := M)
          g r s F α P (by rw [← hCF_def]; exact hyCF), mul_zero]
      have hpush_zero : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          ∀ z, z ∉ CT →
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx) z = 0 := by
        intro Idx Jdx z hz
        by_cases hzT : z ∈ chartTargetEuclid (I := I) (M := M) α
        · refine chartPushedRaw_eq_zero_off_image_tsupport (I := I) (M := M)
            (u := tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)
            α hzT (fun hmem => hz ?_)
          have hsub := tensorChartComponentRaw_tsupport_subset (I := I) (M := M)
            g r s T α Idx Jdx
          rw [hCT_def]
          exact (Set.image_mono (Set.image_mono hsub)) hmem
        · exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hzT
      have hClosedCT : IsClosed CT := hCT_compact.isClosed
      have hdkT_zero : ∀ (k : Fin (Module.finrank ℝ E))
          (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)) y = 0 :=
        fun k Idx Jdx => euclidPartial_eq_zero_off_closed (E := E) hClosedCT
          (hpush_zero Idx Jdx) k hyCT
      have hloT_zero : ∀ (k : Fin (Module.finrank ℝ E))
          (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          covDerivLowerOrderTerm (I := I) (M := M) g r s T α k Idx Jdx y = 0 := by
        intro k Idx Jdx
        rw [covDerivLowerOrderTerm_def]
        refine Finset.sum_eq_zero (fun p _ => ?_)
        have hraw0 : tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
          have := hpush_zero p.1 p.2 y hyCT
          by_cases hyT' : y ∈ chartTargetEuclid (I := I) (M := M) α
          · rwa [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hyT'] at this
          · exact absurd hyT hyT'
        rw [hraw0, mul_zero]
      have hP0 : covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y = 0 := by
        rw [covPrincipalRotationCoeff_def]
        refine Finset.sum_eq_zero (fun P _ => ?_)
        refine Finset.sum_eq_zero (fun Q _ => ?_)
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun k _ => ?_))
        refine Finset.sum_eq_zero (fun l _ => ?_)
        rw [hdkT_zero k P.1 P.2]; ring
      have hV0 : covLowerOrderRotationValueCoeff (I := I) (M := M)
          g r s T α P₀ y = 0 := by
        rw [covLowerOrderRotationValueCoeff_def]
        refine Finset.sum_eq_zero (fun P _ => ?_)
        refine Finset.sum_eq_zero (fun Q _ => ?_)
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun k _ => ?_))
        refine Finset.sum_eq_zero (fun l _ => ?_)
        rw [hdkT_zero k P.1 P.2, hloT_zero k P.1 P.2]; ring
      have hGrad0 : ∀ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y = 0 := by
        intro l
        have hUopen : IsOpen
            (chartTargetEuclid (I := I) (M := M) α \ CT) :=
          hopen.sdiff hClosedCT
        have hyU : y ∈ chartTargetEuclid (I := I) (M := M) α \ CT :=
          ⟨hyT, hyCT⟩
        refine euclidPartial_eq_zero_of_open_zero (E := E) hUopen hyU
          (fun z hz => ?_) l
        unfold weightedGradCoeff
        refine mul_eq_zero_of_right _ ?_
        rw [covLowerOrderRotationGradCoeff_def]
        refine Finset.sum_eq_zero (fun P _ => ?_)
        refine Finset.sum_eq_zero (fun Q _ => ?_)
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun k _ => ?_))
        have hloT_z : covDerivLowerOrderTerm (I := I) (M := M)
            g r s T α k P.1 P.2 z = 0 := by
          rw [covDerivLowerOrderTerm_def]
          refine Finset.sum_eq_zero (fun p _ => ?_)
          have hraw0 : tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) = 0 := by
            have hpz := hpush_zero p.1 p.2 z hz.2
            rwa [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hz.1] at hpz
          rw [hraw0, mul_zero]
        rw [hloT_z]; ring
      rw [hS0, hP0, hV0]
      simp only [mul_zero, sub_zero, zero_add]
      exact Finset.sum_eq_zero (fun l _ => hGrad0 l)
    · exact tensorComponentWeakRHS_apply_of_notMem (I := I) (M := M)
        g r s T F α hK hK_target P₀ hyT
  exact contDiff_of_contDiffOn_zero_off_closed_local (E := E) hopen
    hK'_compact.isClosed hK'_target hcontDiffOn hzero

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
