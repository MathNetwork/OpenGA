import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevPointwise
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.WeakPartial.ComponentSobolevBoundDerivBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.IntrinsicL2Bridge

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma le_sum_of_mem_finset_nonneg
    {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf_nn : ∀ i, 0 ≤ f i) (i : ι) :
    f i ≤ ∑ j, f j := by
  classical
  have hmem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ _
  have h_split :
      ∑ j, f j = f i + ∑ j ∈ Finset.univ.erase i, f j := by
    rw [← Finset.sum_erase_add _ _ hmem, add_comm]
  have h_rest_nn :
      0 ≤ ∑ j ∈ Finset.univ.erase i, f j :=
    Finset.sum_nonneg (fun j _ => hf_nn j)
  linarith

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_const_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α β : M)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) β)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := by
  classical
  have hper : ∀ (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                      (Fin s → Fin (Module.finrank ℝ E))),
      ∃ C : ℝ, 0 ≤ C ∧
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α IJ.1 IJ.2))
              (chartTargetEuclid (I := I) (M := M) β)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := fun IJ =>
    eLpNorm_chosenWeakPartial'_chartPushed_tensorChartComponentScalar_le_per_section
      (I := I) (M := M) g r s S α β IJ.1 IJ.2 k
  choose CIJ hCIJ_nn hCIJ_le using hper
  set Csum : ℝ := ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                          (Fin s → Fin (Module.finrank ℝ E)),
    CIJ IJ with hCsum_def
  refine ⟨Csum, Finset.sum_nonneg (fun IJ _ => hCIJ_nn IJ), ?_⟩
  intro Idx Jdx
  have hsmd : CIJ (Idx, Jdx) ≤ Csum :=
    le_sum_of_mem_finset_nonneg
      (f := fun IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                    (Fin s → Fin (Module.finrank ℝ E)) => CIJ IJ)
      (fun IJ => hCIJ_nn IJ) (Idx, Jdx)
  have h_ofReal_le : ENNReal.ofReal (CIJ (Idx, Jdx)) ≤
      ENNReal.ofReal Csum := ENNReal.ofReal_le_ofReal hsmd
  have h_envelope_le :
      ENNReal.ofReal (CIJ (Idx, Jdx)) * (‖S‖₊ + 1) ≤
        ENNReal.ofReal Csum * (‖S‖₊ + 1) :=
    mul_le_mul_of_nonneg_right h_ofReal_le (by exact zero_le _)
  exact (hCIJ_le (Idx, Jdx)).trans h_envelope_le

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_const_sum_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α β : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∑ k : Fin (Module.finrank ℝ E),
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 k
                (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                  (tensorChartComponentScalar (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx))
                (chartTargetEuclid (I := I) (M := M) β)) 2
              (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := by
  classical
  have hper : ∀ k : Fin (Module.finrank ℝ E),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 k
                (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                  (tensorChartComponentScalar (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx))
                (chartTargetEuclid (I := I) (M := M) β)) 2
              (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
            ENNReal.ofReal C * (‖S‖₊ + 1) := fun k =>
    exists_const_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices
      (I := I) (M := M) g r s S α β k
  choose Ck hCk_nn hCk_le using hper
  set Ctot : ℝ := ∑ k : Fin (Module.finrank ℝ E), Ck k with hCtot_def
  refine ⟨Ctot, Finset.sum_nonneg (fun k _ => hCk_nn k), ?_⟩
  intro Idx Jdx
  have h_sum_le :
      ∑ k : Fin (Module.finrank ℝ E),
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) β)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
        ∑ k : Fin (Module.finrank ℝ E),
          ENNReal.ofReal (Ck k) * (‖S‖₊ + 1) :=
    Finset.sum_le_sum (fun k _ => hCk_le k Idx Jdx)
  refine h_sum_le.trans ?_
  rw [show
        ∑ k : Fin (Module.finrank ℝ E),
          ENNReal.ofReal (Ck k) * (‖S‖₊ + 1) =
        (∑ k : Fin (Module.finrank ℝ E), ENNReal.ofReal (Ck k)) *
          (‖S‖₊ + 1) from
      (Finset.sum_mul (s := Finset.univ)
        (f := fun k : Fin (Module.finrank ℝ E) => ENNReal.ofReal (Ck k))
        (a := (‖S‖₊ + 1))).symm]
  have h_ofReal_sum :
      ∑ k : Fin (Module.finrank ℝ E), ENNReal.ofReal (Ck k) ≤
        ENNReal.ofReal (∑ k : Fin (Module.finrank ℝ E), Ck k) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hCk_nn k)]
  exact mul_le_mul_of_nonneg_right h_ofReal_sum (by exact zero_le _)

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_const_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices_S
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α β : M)
    (k : Fin (Module.finrank ℝ E)) :
    ∀ S : SmoothCcTensorH1 g r s,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 k
                (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                  (tensorChartComponentScalar (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx))
                (chartTargetEuclid (I := I) (M := M) β)) 2
              (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
            ENNReal.ofReal C * (‖S‖₊ + 1) := fun S =>
  exists_const_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices
    (I := I) (M := M) g r s S α β k

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_const_sum_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices_S
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α β : M) :
    ∀ S : SmoothCcTensorH1 g r s,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          ∑ k : Fin (Module.finrank ℝ E),
            eLpNorm
                (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                  (d := Module.finrank ℝ E) 2 k
                  (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                    (tensorChartComponentScalar (I := I) (M := M)
                      g r s S.toCcTensor α Idx Jdx))
                  (chartTargetEuclid (I := I) (M := M) β)) 2
                (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
            ENNReal.ofReal C * (‖S‖₊ + 1) := fun S =>
  exists_const_sum_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices
    (I := I) (M := M) g r s S α β

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_const_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices_single_chart
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) α)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) :=
  exists_const_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices
    (I := I) (M := M) g r s S α α k

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_const_sum_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices_single_chart
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∑ k : Fin (Module.finrank ℝ E),
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 k
                (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
                  (tensorChartComponentScalar (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx))
                (chartTargetEuclid (I := I) (M := M) α)) 2
              (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) :=
  exists_const_sum_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices
    (I := I) (M := M) g r s S α α

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
