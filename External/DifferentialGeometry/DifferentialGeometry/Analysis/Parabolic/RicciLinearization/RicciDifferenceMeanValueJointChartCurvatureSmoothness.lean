import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.MetricFamilyChartLinearization
import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1600000

open Set Function MeasureTheory intervalIntegral Bundle Tensor0SBundle
open scoped Topology Manifold BigOperators ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
lemma gen_joint_partialDeriv
    (Ψ : ℝ → E → ℝ) (q : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E}
    (hΨ : ContDiffAt ℝ ∞ (fun r : ℝ × E => Ψ r.1 r.2) (s₀, y₀)) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × E => partialDeriv (E := E) q (fun y => Ψ p.1 y) p.2) (s₀, y₀) := by
  have hf : ContDiffAt ℝ ∞
      (Function.uncurry (fun (p : ℝ × E) (y : E) => Ψ p.1 y))
      ((s₀, y₀), (fun p : ℝ × E => p.2) (s₀, y₀)) := by
    have huncurry : (Function.uncurry (fun (p : ℝ × E) (y : E) => Ψ p.1 y)) =
        (fun r : ℝ × E => Ψ r.1 r.2) ∘ (fun z : (ℝ × E) × E => (z.1.1, z.2)) := by
      funext z; rfl
    rw [huncurry]
    refine hΨ.comp ((s₀, y₀), y₀) ?_
    exact (contDiffAt_fst.comp ((s₀, y₀), y₀) contDiffAt_fst).prodMk contDiffAt_snd
  have hg : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (s₀, y₀) := contDiffAt_snd
  have hfd := ContDiffAt.fderiv hf hg (le_refl _)
  exact (ContinuousLinearMap.apply ℝ ℝ (chartModelBasis E q)).contDiff.contDiffAt.comp (s₀, y₀) hfd

variable (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)

def ChartGramFamilyJointSmoothNondegenerate (S : Set ℝ) : Prop :=
  (∀ (i j : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E}, s₀ ∈ S →
      y₀ ∈ interior (extChartAt I α).target →
      ContDiffAt ℝ ∞ (fun p : ℝ × E => chartGramOnE (I := I) (gfam p.1) α i j p.2) (s₀, y₀)) ∧
  (∀ {s₀ : ℝ}, s₀ ∈ S →
      ∀ {x : M}, x ∈ (trivializationAt E (TangentSpace I) α).baseSet →
      0 < (chartGramMatrix (I := I) (gfam s₀) α x).det)

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartInvGramOnE_contDiffAt_joint {S : Set ℝ} (hG : ChartGramFamilyJointSmoothNondegenerate (I := I) gfam α S)
    (k l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × E => chartInvGramOnE (I := I) (gfam p.1) α k l p.2) (s₀, y₀) := by
  classical
  have hGentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2) a b) (s₀, y₀) := by
    intro a b
    have := hG.1 a b hs hy
    simpa only [chartGramOnE_def] using this
  have hdet : ContDiffAt ℝ ∞
      (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
        ((extChartAt I α).symm p.2)).det) (s₀, y₀) := by
    have hdet_eq : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).det) =
        (fun p : ℝ × E => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ kk, chartGramMatrix (I := I) (gfam p.1) α
              ((extChartAt I α).symm p.2) (σ kk) kk) := by
      funext p; rw [Matrix.det_apply]; simp [Units.smul_def]
    rw [hdet_eq]
    refine ContDiffAt.sum (fun σ _ => ?_)
    refine contDiffAt_const.mul ?_
    exact contDiffAt_prod (fun kk _ => hGentry (σ kk) kk)
  have hx_base : (extChartAt I α).symm y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    have hy_t : y₀ ∈ (extChartAt I α).target := interior_subset hy
    have hsource : (extChartAt I α).symm y₀ ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy_t
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    exact hsource
  have hdet_ne : (chartGramMatrix (I := I) (gfam (s₀, y₀).1) α
      ((extChartAt I α).symm (s₀, y₀).2)).det ≠ 0 := ne_of_gt (hG.2 hs hx_base)
  have hadj : ∀ kk ll : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).adjugate kk ll) (s₀, y₀) := by
    intro kk ll
    have hexp : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).adjugate kk ll) =
        (fun p : ℝ × E => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ m, (chartGramMatrix (I := I) (gfam p.1) α
                ((extChartAt I α).symm p.2)).updateRow ll
                (Pi.single kk (1 : ℝ)) (σ m) m) := by
      funext p; rw [Matrix.adjugate_apply, Matrix.det_apply]; simp [Units.smul_def]
    rw [hexp]
    refine ContDiffAt.sum (fun σ _ => ?_)
    refine contDiffAt_const.mul ?_
    refine contDiffAt_prod (fun m _ => ?_)
    by_cases hσm : σ m = ll
    · have heq : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).updateRow ll (Pi.single kk (1 : ℝ)) (σ m) m) =
          (fun _ : ℝ × E => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) kk
            (1 : ℝ)) m) := by
        funext p; rw [hσm, Matrix.updateRow_self]
      rw [heq]; exact contDiffAt_const
    · have heq : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).updateRow ll (Pi.single kk (1 : ℝ)) (σ m) m) =
          (fun p : ℝ × E => chartGramMatrix (I := I) (gfam p.1) α
            ((extChartAt I α).symm p.2) (σ m) m) := by
        funext p; rw [Matrix.updateRow_ne hσm]
      rw [heq]; exact hGentry (σ m) m
  have hcongr : (fun p : ℝ × E => chartInvGramOnE (I := I) (gfam p.1) α k l p.2) =
      (fun p : ℝ × E => ((chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).det)⁻¹ *
        (chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2)).adjugate k l) := by
    funext p
    rw [chartInvGramOnE_def]
    change (chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2))⁻¹ k l = _
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) (gfam p.1) α
            ((extChartAt I α).symm p.2)).det •
            (chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2)).adjugate) k l = _
    rw [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [hcongr]
  exact ((contDiffAt_inv _ hdet_ne).comp (s₀, y₀) hdet).mul (hadj k l)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma gen_joint_gramBracket {S : Set ℝ} (hG : ChartGramFamilyJointSmoothNondegenerate (I := I) gfam α S)
    (i j l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => gramBracket (I := I) (gfam r.1) α i j l r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => gramBracket (I := I) (gfam r.1) α i j l r.2) =
      (fun r : ℝ × E =>
        partialDeriv (E := E) i (fun y => chartGramOnE (I := I) (gfam r.1) α l j y) r.2 +
          partialDeriv (E := E) j (fun y => chartGramOnE (I := I) (gfam r.1) α l i y) r.2 -
          partialDeriv (E := E) l (fun y => chartGramOnE (I := I) (gfam r.1) α i j y) r.2) := by
    funext r; rw [gramBracket]
  rw [heq]
  exact ((gen_joint_partialDeriv (fun s y => chartGramOnE (I := I) (gfam s) α l j y) i
      (hG.1 l j hs hy)).add
    (gen_joint_partialDeriv (fun s y => chartGramOnE (I := I) (gfam s) α l i y) j
      (hG.1 l i hs hy))).sub
    (gen_joint_partialDeriv (fun s y => chartGramOnE (I := I) (gfam s) α i j y) l
      (hG.1 i j hs hy))

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gen_joint_christoffel {S : Set ℝ} (hG : ChartGramFamilyJointSmoothNondegenerate (I := I) gfam α S)
    (i j k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartChristoffel (I := I) (gfam r.1) α i j k r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartChristoffel (I := I) (gfam r.1) α i j k r.2) =
      (fun r : ℝ × E => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (gfam r.1) α k l r.2 *
          gramBracket (I := I) (gfam r.1) α i j l r.2) := by
    funext r; rw [chartChristoffel_eq_sum_invGramOnE_bracket]
  rw [heq]
  refine contDiffAt_const.mul (ContDiffAt.sum (fun l _ => ?_))
  exact (chartInvGramOnE_contDiffAt_joint (I := I) gfam α hG k l hs hy).mul
    (gen_joint_gramBracket (I := I) gfam α hG i j l hs hy)

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gen_joint_partial_christoffel {S : Set ℝ} (hG : ChartGramFamilyJointSmoothNondegenerate (I := I) gfam α S)
    (m i j k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E =>
        partialDeriv (E := E) m (fun y => chartChristoffel (I := I) (gfam r.1) α i j k y) r.2)
      (s₀, y₀) :=
  gen_joint_partialDeriv (fun s y => chartChristoffel (I := I) (gfam s) α i j k y) m
    (gen_joint_christoffel (I := I) gfam α hG i j k hs hy)

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gen_joint_riemann {S : Set ℝ} (hG : ChartGramFamilyJointSmoothNondegenerate (I := I) gfam α S)
    (i j k l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartRiemannTensor (I := I) (gfam r.1) α i j k l r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartRiemannTensor (I := I) (gfam r.1) α i j k l r.2) =
      (fun r : ℝ × E =>
        partialDeriv (E := E) j (fun y => chartChristoffel (I := I) (gfam r.1) α i k l y) r.2 -
          partialDeriv (E := E) k (fun y => chartChristoffel (I := I) (gfam r.1) α i j l y) r.2 +
          (∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) (gfam r.1) α j m l r.2 *
                chartChristoffel (I := I) (gfam r.1) α i k m r.2 -
              chartChristoffel (I := I) (gfam r.1) α k m l r.2 *
                chartChristoffel (I := I) (gfam r.1) α i j m r.2))) := by
    funext r; rw [chartRiemannTensor_def]
  rw [heq]
  refine ((gen_joint_partial_christoffel (I := I) gfam α hG j i k l hs hy).sub
    (gen_joint_partial_christoffel (I := I) gfam α hG k i j l hs hy)).add ?_
  refine ContDiffAt.sum (fun m _ => ?_)
  exact ((gen_joint_christoffel (I := I) gfam α hG j m l hs hy).mul
      (gen_joint_christoffel (I := I) gfam α hG i k m hs hy)).sub
    ((gen_joint_christoffel (I := I) gfam α hG k m l hs hy).mul
      (gen_joint_christoffel (I := I) gfam α hG i j m hs hy))

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gen_joint_ricci {S : Set ℝ} (hG : ChartGramFamilyJointSmoothNondegenerate (I := I) gfam α S)
    (i k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartRicciTensor (I := I) (gfam r.1) α i k r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartRicciTensor (I := I) (gfam r.1) α i k r.2) =
      (fun r : ℝ × E => ∑ j : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) (gfam r.1) α i j k j r.2) := by
    funext r; rw [chartRicciTensor_def]
  rw [heq]
  exact ContDiffAt.sum (fun j _ => gen_joint_riemann (I := I) gfam α hG i j k j hs hy)

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gen_joint_chartDeTurckVFComp {S : Set ℝ} (hG : ChartGramFamilyJointSmoothNondegenerate (I := I) gfam α S)
    (g_bg : SmoothRiemannianMetric I M) (k : Fin (Module.finrank ℝ E))
    {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k r.2) (s₀, y₀) := by
  have hbg : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞
        (fun r : ℝ × E => chartChristoffel (I := I) g_bg α a b k r.2) (s₀, y₀) := by
    intro a b
    have hbase : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g_bg α a b k) y₀ :=
      (chartChristoffel_contDiffOn_interior (I := I) g_bg α a b k).contDiffAt
        (isOpen_interior.mem_nhds hy)
    have hcomp : (fun r : ℝ × E => chartChristoffel (I := I) g_bg α a b k r.2) =
        (chartChristoffel (I := I) g_bg α a b k) ∘ (fun r : ℝ × E => r.2) := rfl
    rw [hcomp]
    exact ContDiffAt.comp (s₀, y₀) hbase contDiffAt_snd
  have heq : (fun r : ℝ × E => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k r.2) =
      (fun r : ℝ × E => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (gfam r.1) α a b r.2 *
          (chartChristoffel (I := I) (gfam r.1) α a b k r.2 -
            chartChristoffel (I := I) g_bg α a b k r.2)) := by
    funext r; rw [chartDeTurckVFComp_def]
  rw [heq]
  refine ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ => ?_))
  exact (chartInvGramOnE_contDiffAt_joint (I := I) gfam α hG a b hs hy).mul
    ((gen_joint_christoffel (I := I) gfam α hG a b k hs hy).sub (hbg a b))

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gen_joint_partial_chartDeTurckVFComp {S : Set ℝ} (hG : ChartGramFamilyJointSmoothNondegenerate (I := I) gfam α S)
    (g_bg : SmoothRiemannianMetric I M) (m k : Fin (Module.finrank ℝ E))
    {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E =>
        partialDeriv (E := E) m (fun y => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k y) r.2)
      (s₀, y₀) :=
  gen_joint_partialDeriv (fun s y => chartDeTurckVFComp (I := I) (gfam s) g_bg α k y) m
    (gen_joint_chartDeTurckVFComp (I := I) gfam α hG g_bg k hs hy)

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gen_joint_chartLieDeTurckComp {S : Set ℝ} (hG : ChartGramFamilyJointSmoothNondegenerate (I := I) gfam α S)
    (g_bg : SmoothRiemannianMetric I M) (i j : Fin (Module.finrank ℝ E))
    {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartLieDeTurckComp (I := I) (gfam r.1) g_bg α i j r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartLieDeTurckComp (I := I) (gfam r.1) g_bg α i j r.2) =
      (fun r : ℝ × E =>
        (∑ k : Fin (Module.finrank ℝ E),
            chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k r.2 *
              partialDeriv (E := E) k (fun y => chartGramOnE (I := I) (gfam r.1) α i j y) r.2)
        + (∑ k : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) (gfam r.1) α k j r.2 *
              partialDeriv (E := E) i
                (fun y => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k y) r.2)
        + (∑ k : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) (gfam r.1) α i k r.2 *
              partialDeriv (E := E) j
                (fun y => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k y) r.2)) := by
    funext r; rw [chartLieDeTurckComp_def]
  rw [heq]
  refine ((ContDiffAt.sum (fun k _ => ?_)).add (ContDiffAt.sum (fun k _ => ?_))).add
    (ContDiffAt.sum (fun k _ => ?_))
  · exact (gen_joint_chartDeTurckVFComp (I := I) gfam α hG g_bg k hs hy).mul
      (gen_joint_partialDeriv (fun s y => chartGramOnE (I := I) (gfam s) α i j y) k
        (hG.1 i j hs hy))
  · exact (hG.1 k j hs hy).mul
      (gen_joint_partial_chartDeTurckVFComp (I := I) gfam α hG g_bg i k hs hy)
  · exact (hG.1 i k hs hy).mul
      (gen_joint_partial_chartDeTurckVFComp (I := I) gfam α hG g_bg j k hs hy)

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gen_joint_chartDeTurckRicciRHS {S : Set ℝ} (hG : ChartGramFamilyJointSmoothNondegenerate (I := I) gfam α S)
    (g_bg : SmoothRiemannianMetric I M) (i k : Fin (Module.finrank ℝ E))
    {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartDeTurckRicciRHS (I := I) (gfam r.1) g_bg α i k r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartDeTurckRicciRHS (I := I) (gfam r.1) g_bg α i k r.2) =
      (fun r : ℝ × E => -2 * chartRicciTensor (I := I) (gfam r.1) α i k r.2 +
        chartLieDeTurckComp (I := I) (gfam r.1) g_bg α i k r.2) := by
    funext r; rw [chartDeTurckRicciRHS_def]
  rw [heq]
  exact (contDiffAt_const.mul (gen_joint_ricci (I := I) gfam α hG i k hs hy)).add
    (gen_joint_chartLieDeTurckComp (I := I) gfam α hG g_bg i k hs hy)

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
