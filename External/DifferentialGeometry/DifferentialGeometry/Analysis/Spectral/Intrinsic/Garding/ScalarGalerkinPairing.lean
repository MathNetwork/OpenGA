import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarNonautTame
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.DirichletSpectralBochnerGap
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.FiniteSpectralPairing









noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E





theorem cc_finite_diss
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    (hsmall :
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.metricCauchySchwarzBound
        (I := I) q k ((1 : ℝ) / 4)) (n : ℕ) :
    ∃ Cmid : ℝ, 0 ≤ Cmid ∧
      ∀ (T : tensorHs (I := I) (M := M) q 0 0 0)
        (hT : (Function.support T.coeff).Finite),
        2 * ∑ i ∈ hT.toFinset,
            tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
              (T.coeff i *
                tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) q 0 0)
                  (SmoothCcTensor.toL2
                    (scalarLapDiffCc (I := I) q h
                      (tensorHsSmoothRepr (I := I) (M := M) T hT))) i) ≤
          ((5 : ℝ) / 3) *
              (∑ i ∈ hT.toFinset,
                tensorSobolevWeight (I := I) (M := M) i ((n + 1 : ℕ) : ℝ) *
                  (T.coeff i) ^ 2) +
            Cmid *
              (∑ i ∈ hT.toFinset,
                tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
                  (T.coeff i) ^ 2) := by
  classical
  obtain ⟨Clap, hClap_nn, hlap⟩ :=
    cc_lap_pair (I := I) (M := M) q h k htie
      (by norm_num : ((1 : ℝ) / 4) < 1)
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4) hsmall n
  obtain ⟨Cgap, hCgap_nn, hgap⟩ :=
    cc_dirichlet_gap (I := I) (M := M) q 0 n
  obtain ⟨Clo, hClo_nn, hlo⟩ := hsJet_le (I := I) (M := M) q 0 n
  obtain ⟨Chi, hChi_nn, hhi⟩ := hsJet_le (I := I) (M := M) q 0 (n + 1)
  let P : ℝ := Clap * Clo * Chi
  refine ⟨((2 : ℝ) / 3) * Cgap + P ^ 2, by positivity, ?_⟩
  intro T hT
  let U : SmoothCcTensor q 0 0 :=
    tensorHsSmoothRepr (I := I) (M := M) T hT
  let A : SmoothCcTensor q 0 0 := scalarLapDiffCc (I := I) q h U
  let Jlo : ℝ :=
    ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) q 0 0 j U‖
  let Jhi : ℝ :=
    ∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) q 0 0 j U‖
  let Hlo : ℝ := ‖ccTensorToHs (I := I) (M := M) q 0 (n : ℝ) U‖
  let Hhi : ℝ := ‖ccTensorToHs (I := I) (M := M) q 0 ((n + 1 : ℕ) : ℝ) U‖
  have hcastNorm :
      ‖SmoothCcTensor.toL2
          (castCcTensorRank (I := I) (M := M) q 0
            (by omega : 0 + (n + 1) = 1 + n)
            (iteratedCovGrad (I := I) q 0 0 (n + 1) U))‖ =
        ‖SmoothCcTensor.toL2
          (iteratedCovGrad (I := I) q 0 0 (n + 1) U)‖ := by
    rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_toL2,
      DiffBilinOp.norm_castCcTensorRank]
  have hlapU :
      tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun A.toFun ≤
        ((1 : ℝ) / 3) *
            ‖SmoothCcTensor.toL2
              (iteratedCovGrad (I := I) q 0 0 (n + 1) U)‖ ^ 2 +
          Clap * (Jlo * Jhi) := by
    have h := hlap U
    rw [show (((1 : ℝ) / 4) / (1 - (1 : ℝ) / 4)) = (1 : ℝ) / 3 by
      norm_num, hcastNorm] at h
    simpa only [A, Jlo, Jhi] using h
  have hgapU :
      ‖SmoothCcTensor.toL2
          (iteratedCovGrad (I := I) q 0 0 (n + 1) U)‖ ^ 2 ≤
        Hhi ^ 2 + Cgap * Hlo ^ 2 := by
    have hn : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
    dsimp only [Hhi, Hlo]
    rw [hn]
    exact hgap U
  have hloU : Jlo ≤ Clo * Hlo := by
    simpa only [Jlo, Hlo] using hlo U
  have hhiU : Jhi ≤ Chi * Hhi := by
    have h := hhi U
    simpa only [Jhi, Hhi, show n + 1 + 1 = n + 2 by omega] using h
  have hJlo_nn : 0 ≤ Jlo := by
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hJhi_nn : 0 ≤ Jhi := by
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hHlo_nn : 0 ≤ Hlo := norm_nonneg _
  have hHhi_nn : 0 ≤ Hhi := norm_nonneg _
  have hprod : Jlo * Jhi ≤ (Clo * Hlo) * (Chi * Hhi) :=
    mul_le_mul hloU hhiU hJhi_nn (mul_nonneg hClo_nn hHlo_nn)
  have hrem : Clap * (Jlo * Jhi) ≤ P * Hlo * Hhi := by
    calc
      Clap * (Jlo * Jhi) ≤ Clap * ((Clo * Hlo) * (Chi * Hhi)) :=
        mul_le_mul_of_nonneg_left hprod hClap_nn
      _ = P * Hlo * Hhi := by simp only [P]; ring
  have hyoung :
      2 * (Clap * (Jlo * Jhi)) ≤ Hhi ^ 2 + P ^ 2 * Hlo ^ 2 := by
    have hsquare : 0 ≤ (Hhi - P * Hlo) ^ 2 := sq_nonneg _
    nlinarith [hrem]
  have hmain :
      2 * tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun A.toFun ≤
        ((5 : ℝ) / 3) * Hhi ^ 2 +
          (((2 : ℝ) / 3) * Cgap + P ^ 2) * Hlo ^ 2 := by
    nlinarith [hlapU, hgapU, hyoung]
  let hc := tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0
  have hrepr
      (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) q 0 0) :
      tensorL2Coeff (I := I) (M := M) hc (SmoothCcTensor.toL2 U) i =
        T.coeff i := by
    dsimp only [U]
    rw [SmoothCcTensor.toL2_apply,
      tensorHsSmoothRepr_toL2 (I := I) (M := M) (le_refl (0 : ℝ)) T hT,
      tensorHsToL2_tensorL2Coeff (I := I) (M := M) (le_refl (0 : ℝ))]
  have hhs (m : ℕ) :
      ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) U =
        tensorHsOfFiniteSupport (I := I) (M := M) (m : ℝ) T.coeff hT := by
    apply tensorHs.ext
    funext i
    rw [ccTensorToHs_coeff, tensorHsOfFiniteSupport_coeff]
    exact hrepr i
  have henergy (m : ℕ) :
      ‖tensorHsOfFiniteSupport (I := I) (M := M) (m : ℝ) T.coeff hT‖ ^ 2 =
        ∑ i ∈ hT.toFinset,
          tensorSobolevWeight (I := I) (M := M) i (m : ℝ) * (T.coeff i) ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum]
    simp only [tensorHsOfFiniteSupport_coeff]
    rw [tsum_eq_sum (s := hT.toFinset)]
    intro i hi
    have hcoeff : T.coeff i = 0 := by
      by_contra hne
      exact hi (hT.mem_toFinset.mpr (Function.mem_support.mpr hne))
    norm_num [hcoeff]
  have hmain' :
      2 * tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun A.toFun ≤
        ((5 : ℝ) / 3) *
            (∑ i ∈ hT.toFinset,
              tensorSobolevWeight (I := I) (M := M) i ((n + 1 : ℕ) : ℝ) *
                (T.coeff i) ^ 2) +
          (((2 : ℝ) / 3) * Cgap + P ^ 2) *
            (∑ i ∈ hT.toFinset,
              tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
                (T.coeff i) ^ 2) := by
    dsimp only [Hhi, Hlo] at hmain
    rw [hhs (n + 1), hhs n, henergy (n + 1), henergy n] at hmain
    exact hmain
  have hpair := finite_cc_pair (I := I) (M := M) q 0 n T hT A
  rw [hpair]
  simpa only [U, A] using hmain'





theorem cc_a2_closure
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    (hsmall :
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.metricCauchySchwarzBound
        (I := I) q k ((1 : ℝ) / 4)) (n : ℕ) :
    ∃ Cmid : ℝ, 0 ≤ Cmid ∧
      ∀ (S : Finset
          (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) q 0 0))
        (T : tensorHs (I := I) (M := M) q 0 0 0)
        (hT : (Function.support T.coeff).Finite),
        hT.toFinset ⊆ S →
          2 * ∑ i ∈ S,
              tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
                (T.coeff i *
                  tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator
                      (I := I) (M := M) q 0 0)
                    (SmoothCcTensor.toL2
                      (scalarLapDiffCc (I := I) q h
                        (tensorHsSmoothRepr (I := I) (M := M) T hT))) i) ≤
            ((5 : ℝ) / 3) *
                (∑ i ∈ S,
                  tensorSobolevWeight (I := I) (M := M) i ((n + 1 : ℕ) : ℝ) *
                    (T.coeff i) ^ 2) +
              Cmid *
                (∑ i ∈ S,
                  tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
                    (T.coeff i) ^ 2) := by
  classical
  obtain ⟨Cmid, hCmid, hcore⟩ :=
    cc_finite_diss (I := I) (M := M) q h k htie hsmall n
  refine ⟨Cmid, hCmid, ?_⟩
  intro S T hT hsub
  let A : SmoothCcTensor q 0 0 :=
    scalarLapDiffCc (I := I) q h
      (tensorHsSmoothRepr (I := I) (M := M) T hT)
  have hcoeff {i} (hi : i ∉ hT.toFinset) : T.coeff i = 0 := by
    by_contra hne
    exact hi (hT.mem_toFinset.mpr (Function.mem_support.mpr hne))
  have hlhs :
      (∑ i ∈ hT.toFinset,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (T.coeff i * tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
              (SmoothCcTensor.toL2 A) i)) =
        ∑ i ∈ S,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (T.coeff i * tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
              (SmoothCcTensor.toL2 A) i) := by
    apply Finset.sum_subset hsub
    intro i _ hi
    rw [hcoeff hi, zero_mul, mul_zero]
  have hhi :
      (∑ i ∈ hT.toFinset,
          tensorSobolevWeight (I := I) (M := M) i ((n + 1 : ℕ) : ℝ) *
            (T.coeff i) ^ 2) =
        ∑ i ∈ S,
          tensorSobolevWeight (I := I) (M := M) i ((n + 1 : ℕ) : ℝ) *
            (T.coeff i) ^ 2 := by
    apply Finset.sum_subset hsub
    intro i _ hi
    norm_num [hcoeff hi]
  have hlo :
      (∑ i ∈ hT.toFinset,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (T.coeff i) ^ 2) =
        ∑ i ∈ S,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (T.coeff i) ^ 2 := by
    apply Finset.sum_subset hsub
    intro i _ hi
    norm_num [hcoeff hi]
  have h := hcore T hT
  rw [← hlhs, ← hhi, ← hlo]
  exact h

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
