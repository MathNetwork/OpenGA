import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SubcriticalSmallTime
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeOperator


















noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : Nat}
variable {a T : Real}




def nonautMap (a : Real) {T : Real} (hT : 0 < T) (hT1 : T ≤ 1)
    (u0 : tensorHs (I := I) (M := M) g r s (a + 2))
    (A2 : Real → tensorHs (I := I) (M := M) g r s (a + 2) →L[Real]
      tensorHs (I := I) (M := M) g r s a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : NNReal) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ (C2 : Real))
    (A1 : Real → tensorHs (I := I) (M := M) g r s (a + 1) →L[Real]
      tensorHs (I := I) (M := M) g r s a)
    (hA1 : AEStronglyMeasurable A1 (timeMeasure T))
    (C1 : NNReal) (hC1 : ∀ᵐ t ∂timeMeasure T, ‖A1 t‖ ≤ (C1 : Real)) :
    timeL2 (tensorHs (I := I) (M := M) g r s a) T ->
      timeL2 (tensorHs (I := I) (M := M) g r s a) T :=
  fun force =>
    timeOp A2 hA2 C2 hC2
        (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) +
      timeOp A1 hA1 C1 hC1
        (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force)


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nonautMap_apply (hT : 0 < T) (hT1 : T ≤ 1)
    (u0 : tensorHs (I := I) (M := M) g r s (a + 2))
    (A2 : Real → tensorHs (I := I) (M := M) g r s (a + 2) →L[Real]
      tensorHs (I := I) (M := M) g r s a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : NNReal) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ (C2 : Real))
    (A1 : Real → tensorHs (I := I) (M := M) g r s (a + 1) →L[Real]
      tensorHs (I := I) (M := M) g r s a)
    (hA1 : AEStronglyMeasurable A1 (timeMeasure T))
    (C1 : NNReal) (hC1 : ∀ᵐ t ∂timeMeasure T, ‖A1 t‖ ≤ (C1 : Real))
    (force : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    nonautMap (I := I) (M := M) a hT hT1 u0
        A2 hA2 C2 hC2 A1 hA1 C1 hC1 force =
      timeOp A2 hA2 C2 hC2
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) +
        timeOp A1 hA1 C1 hC1
          (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force) :=
  rfl



omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nonautMap_dist_le
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u0 : tensorHs (I := I) (M := M) g r s (a + 2))
    (A2 : Real → tensorHs (I := I) (M := M) g r s (a + 2) →L[Real]
      tensorHs (I := I) (M := M) g r s a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : NNReal) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ (C2 : Real))
    (A1 : Real → tensorHs (I := I) (M := M) g r s (a + 1) →L[Real]
      tensorHs (I := I) (M := M) g r s a)
    (hA1 : AEStronglyMeasurable A1 (timeMeasure T))
    (C1 : NNReal) (hC1 : ∀ᵐ t ∂timeMeasure T, ‖A1 t‖ ≤ (C1 : Real))
    (force force' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    dist (nonautMap (I := I) (M := M) a hT hT1 u0
        A2 hA2 C2 hC2 A1 hA1 C1 hC1 force)
      (nonautMap (I := I) (M := M) a hT hT1 u0
        A2 hA2 C2 hC2 A1 hA1 C1 hC1 force') ≤
      ((C2 : Real) * (1 + T) + (C1 : Real) * (2 * Real.sqrt T)) *
        dist force force' := by
  have hfield2 := maxRegDuhamelSolField_dist_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u0 force force'
  have hfield1 := maxRegDuhamelSolFieldHa1_dist_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u0 force force'
  have h2 :
      ‖timeOp A2 hA2 C2 hC2
            (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) -
          timeOp A2 hA2 C2 hC2
            (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force')‖ ≤
        (C2 : Real) * (1 + T) * ‖force - force'‖ := by
    rw [← map_sub]
    calc
      ‖timeOp A2 hA2 C2 hC2
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force -
            maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force')‖
          ≤ ‖timeOp A2 hA2 C2 hC2‖ *
              ‖maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force -
                maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force'‖ :=
            (timeOp A2 hA2 C2 hC2).le_opNorm _
      _ ≤ (C2 : Real) *
              ‖maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force -
                maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force'‖ :=
          mul_le_mul_of_nonneg_right (timeOp_norm_le A2 hA2 C2 hC2)
            (norm_nonneg _)
      _ ≤ (C2 : Real) * ((1 + T) * ‖force - force'‖) :=
          mul_le_mul_of_nonneg_left hfield2 C2.coe_nonneg
      _ = (C2 : Real) * (1 + T) * ‖force - force'‖ := by ring
  have h1 :
      ‖timeOp A1 hA1 C1 hC1
            (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force) -
          timeOp A1 hA1 C1 hC1
            (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force')‖ ≤
        (C1 : Real) * (2 * Real.sqrt T) * ‖force - force'‖ := by
    rw [← map_sub]
    calc
      ‖timeOp A1 hA1 C1 hC1
          (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force -
            maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force')‖
          ≤ ‖timeOp A1 hA1 C1 hC1‖ *
              ‖maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force -
                maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force'‖ :=
            (timeOp A1 hA1 C1 hC1).le_opNorm _
      _ ≤ (C1 : Real) *
              ‖maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force -
                maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force'‖ :=
          mul_le_mul_of_nonneg_right (timeOp_norm_le A1 hA1 C1 hC1)
            (norm_nonneg _)
      _ ≤ (C1 : Real) * ((2 * Real.sqrt T) * ‖force - force'‖) :=
          mul_le_mul_of_nonneg_left hfield1 C1.coe_nonneg
      _ = (C1 : Real) * (2 * Real.sqrt T) * ‖force - force'‖ := by ring
  rw [dist_eq_norm, dist_eq_norm]
  unfold nonautMap
  have hsplit :
      (timeOp A2 hA2 C2 hC2
            (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) +
          timeOp A1 hA1 C1 hC1
            (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force)) -
        (timeOp A2 hA2 C2 hC2
            (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force') +
          timeOp A1 hA1 C1 hC1
            (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force')) =
      (timeOp A2 hA2 C2 hC2
            (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) -
          timeOp A2 hA2 C2 hC2
            (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force')) +
        (timeOp A1 hA1 C1 hC1
            (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force) -
          timeOp A1 hA1 C1 hC1
            (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force')) := by
    abel
  rw [hsplit]
  calc
    ‖(timeOp A2 hA2 C2 hC2
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) -
        timeOp A2 hA2 C2 hC2
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force')) +
      (timeOp A1 hA1 C1 hC1
          (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force) -
        timeOp A1 hA1 C1 hC1
          (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force'))‖
        ≤ ‖timeOp A2 hA2 C2 hC2
            (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) -
            timeOp A2 hA2 C2 hC2
              (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force')‖ +
          ‖timeOp A1 hA1 C1 hC1
            (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force) -
            timeOp A1 hA1 C1 hC1
              (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force')‖ :=
          norm_add_le _ _
    _ ≤ (C2 : Real) * (1 + T) * ‖force - force'‖ +
          (C1 : Real) * (2 * Real.sqrt T) * ‖force - force'‖ :=
        add_le_add h2 h1
    _ = ((C2 : Real) * (1 + T) + (C1 : Real) * (2 * Real.sqrt T)) *
          ‖force - force'‖ := by ring



omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nonautMap_contract
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u0 : tensorHs (I := I) (M := M) g r s (a + 2))
    (A2 : Real → tensorHs (I := I) (M := M) g r s (a + 2) →L[Real]
      tensorHs (I := I) (M := M) g r s a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : NNReal) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ (C2 : Real))
    (A1 : Real → tensorHs (I := I) (M := M) g r s (a + 1) →L[Real]
      tensorHs (I := I) (M := M) g r s a)
    (hA1 : AEStronglyMeasurable A1 (timeMeasure T))
    (C1 : NNReal) (hC1 : ∀ᵐ t ∂timeMeasure T, ‖A1 t‖ ≤ (C1 : Real))
    (hsmall :
      (C2 : Real) * (1 + T) + (C1 : Real) * (2 * Real.sqrt T) < 1) :
    ContractingWith
      ⟨(C2 : Real) * (1 + T) + (C1 : Real) * (2 * Real.sqrt T),
        add_nonneg
          (mul_nonneg C2.coe_nonneg (by linarith [hT.le]))
          (mul_nonneg C1.coe_nonneg (by positivity))⟩
      (nonautMap (I := I) (M := M) a hT hT1 u0
        A2 hA2 C2 hC2 A1 hA1 C1 hC1) := by
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_lt_coe]
    simpa only [NNReal.coe_mk] using hsmall
  · refine LipschitzWith.of_dist_le_mul (fun force force' => ?_)
    have h := nonautMap_dist_le (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 u0
      A2 hA2 C2 hC2 A1 hA1 C1 hC1 force force'
    simpa only [NNReal.coe_mk] using h




omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nonaut_strong_exists
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u0 : tensorHs (I := I) (M := M) g r s (a + 2))
    (A2 : Real → tensorHs (I := I) (M := M) g r s (a + 2) →L[Real]
      tensorHs (I := I) (M := M) g r s a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : NNReal) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ (C2 : Real))
    (A1 : Real → tensorHs (I := I) (M := M) g r s (a + 1) →L[Real]
      tensorHs (I := I) (M := M) g r s a)
    (hA1 : AEStronglyMeasurable A1 (timeMeasure T))
    (C1 : NNReal) (hC1 : ∀ᵐ t ∂timeMeasure T, ‖A1 t‖ ≤ (C1 : Real))
    (hsmall :
      (C2 : Real) * (1 + T) + (C1 : Real) * (2 * Real.sqrt T) < 1) :
    ∃ (u : MaxRegSolutionSpace (I := I) (M := M) a T)
      (force : timeL2 (tensorHs (I := I) (M := M) g r s a) T),
      u = maxRegDuhamelMap (I := I) (M := M) a hT hT1 u0 force ∧
        force =
          timeOp A2 hA2 C2 hC2
              (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) +
            timeOp A1 hA1 C1 hC1
              (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0
                force) ∧
        TimeSobolev.timeH1.trace0 _ T u =
            tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
              (show a ≤ a + 2 by linarith) u0 ∧
        TimeSobolev.timeH1.timeDeriv _ T u =
          timeScaleLaplacian (I := I) (M := M) a
              (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) +
            (timeOp A2 hA2 C2 hC2
                (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) +
              timeOp A1 hA1 C1 hC1
                (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0
                  force)) := by
  have hcontr := nonautMap_contract (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u0
    A2 hA2 C2 hC2 A1 hA1 C1 hC1 hsmall
  set forceStar := ContractingWith.fixedPoint
    (nonautMap (I := I) (M := M) a hT hT1 u0
      A2 hA2 C2 hC2 A1 hA1 C1 hC1) hcontr with hforceStar_def
  have hforceStar_fix :
      nonautMap (I := I) (M := M) a hT hT1 u0
          A2 hA2 C2 hC2 A1 hA1 C1 hC1 forceStar = forceStar :=
    ContractingWith.fixedPoint_isFixedPt hcontr
  have hforceStar_eq : forceStar =
      timeOp A2 hA2 C2 hC2
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 forceStar) +
        timeOp A1 hA1 C1 hC1
          (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0
            forceStar) := by
    rw [← nonautMap_apply (I := I) (M := M) (a := a) hT hT1 u0
      A2 hA2 C2 hC2 A1 hA1 C1 hC1 forceStar, hforceStar_fix]
  refine ⟨maxRegDuhamelMap (I := I) (M := M) a hT hT1 u0 forceStar,
    forceStar, rfl, hforceStar_eq, ?_, ?_⟩
  · exact maxRegDuhamelMap_trace0 (I := I) (M := M) (a := a) (T := T)
      hT hT1 u0 forceStar
  · rw [maxRegDuhamelMap_timeDeriv_eq (I := I) (M := M)
      (h_compact := h_compact) (a := a) (T := T) hT hT1 u0 forceStar]
    exact congrArg₂ (fun x y => x + y) rfl hforceStar_eq

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
