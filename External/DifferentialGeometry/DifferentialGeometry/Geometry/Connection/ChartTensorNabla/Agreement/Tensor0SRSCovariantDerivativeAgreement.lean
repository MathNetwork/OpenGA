import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradParallelNaturality


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorRSCovariantDerivative_zeroS_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
          (fun y : M => σ y) x v)
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from σ y)
            (unitZeroSec (I := I) (M := M) y))
        x v := by
  classical
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) 0 s
    (LeviCivita (I := I) g) σ (unitZeroSec (I := I) (M := M)) x v]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitZeroSec (I := I) (M := M) y) x v) = 0 from
    tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]

noncomputable def unitScalarRSLift {s : ℕ} (x : M) (T : Tensor0SSpace s I x) :
    TensorRSSpace 0 s I x :=
  TensorRSSpace.ofCLM
    (ContinuousLinearMap.smulRight
      (tensor0Iso (I := I) M x).toContinuousLinearMap T)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem unitScalarRSLift_apply {s : ℕ} (x : M) (T : Tensor0SSpace s I x)
    (D : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        unitScalarRSLift (I := I) (M := M) x T) D =
      (tensor0Iso (I := I) M x D) • T := by
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem unitScalarRSLift_apply_unit {s : ℕ} (x : M) (T : Tensor0SSpace s I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        unitScalarRSLift (I := I) (M := M) x T)
        (unitZeroSec (I := I) (M := M) x) = T := by
  rw [unitScalarRSLift_apply]
  have hscalar : tensor0Iso (I := I) M x (unitZeroSec (I := I) (M := M) x) = (1 : ℝ) := by
    have h := scalarFn_unitZero (I := I) (M := M)
    have := congrFun h x
    simpa [scalarFn_apply, unitZeroSec_apply] using this
  rw [hscalar, one_smul]

noncomputable def unitScalarRSLiftSection {s : ℕ} (S : Π y : M, Tensor0SSpace s I y) :
    Π y : M, TensorRSSpace 0 s I y :=
  fun y => unitScalarRSLift (I := I) (M := M) y (S y)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem unitScalarRSLiftSection_apply {s : ℕ}
    (S : Π y : M, Tensor0SSpace s I y) (y : M) :
    unitScalarRSLiftSection (I := I) (M := M) S y =
      unitScalarRSLift (I := I) (M := M) y (S y) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem unitScalarRSLiftSection_apply_unit {s : ℕ}
    (S : Π y : M, Tensor0SSpace s I y) (y : M) :
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
        unitScalarRSLiftSection (I := I) (M := M) S y)
        (unitZeroSec (I := I) (M := M) y) = S y := by
  rw [unitScalarRSLiftSection_apply, unitScalarRSLift_apply_unit]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem unitScalarRSLiftSection_apply_at_section {s : ℕ}
    (S : Π y : M, Tensor0SSpace s I y)
    (Y : Π y : M, Tensor0SSpace 0 I y) (y : M) :
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
        unitScalarRSLiftSection (I := I) (M := M) S y) (Y y) =
      scalarFn (I := I) (M := M) Y y • S y := by
  rw [unitScalarRSLiftSection_apply, unitScalarRSLift_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem contMDiff_unitScalarRSLiftSection {s : ℕ}
    (S : Π y : M, Tensor0SSpace s I y)
    (hS : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y (S y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (unitScalarRSLiftSection (I := I) (M := M) S y)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun y : M => Tensor0SSpace 0 I y)
    (V₂ := fun y : M => Tensor0SSpace s I y)
    (φ := fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
      unitScalarRSLiftSection (I := I) (M := M) S y))
  intro Y
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞ (scalarFn (I := I) (M := M) (fun y => Y y)) :=
    (contMDiff_scalarFn_iff_section (I := I) (M := M) (fun y => Y y)).mpr Y.contMDiff
  have hsmul : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y
        (scalarFn (I := I) (M := M) (fun y => Y y) y • S y)) :=
    ContMDiff.smul_section hscalar hS
  have hpt : (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          unitScalarRSLiftSection (I := I) (M := M) S y) (Y y))) =
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y
        (scalarFn (I := I) (M := M) (fun y => Y y) y • S y)) := by
    funext y
    rw [unitScalarRSLiftSection_apply_at_section (I := I) (M := M) S (fun y => Y y) y]
  rw [hpt]
  exact hsmul

noncomputable def unitScalarRSLiftCₛ {s : ℕ}
    (S : Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun y : M => Tensor0SSpace s I y)⟯) :
    Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯ :=
  ⟨fun y : M => unitScalarRSLiftSection (I := I) (M := M) (fun z => S z) y,
   contMDiff_unitScalarRSLiftSection (I := I) (M := M) (fun z => S z) S.contMDiff⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] theorem unitScalarRSLiftCₛ_apply {s : ℕ}
    (S : Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun y : M => Tensor0SSpace s I y)⟯) (y : M) :
    unitScalarRSLiftCₛ (I := I) (M := M) S y =
      unitScalarRSLiftSection (I := I) (M := M) (fun z => S z) y := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensor0SCovariantDerivative_eq_tensorRSCovariantDerivative
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun y : M => Tensor0SSpace s I y)⟯)
    (x : M) (v : TangentSpace I x) :
    Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (fun y : M => S y) x v =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
          (fun y : M => unitScalarRSLiftCₛ (I := I) (M := M) S y) x v)
        (unitZeroSec (I := I) (M := M) x) := by
  classical
  rw [tensorRSCovariantDerivative_zeroS_unit_eval (I := I) (M := M) g s
    (unitScalarRSLiftCₛ (I := I) (M := M) S) x v]
  have hsec : (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          unitScalarRSLiftCₛ (I := I) (M := M) S y)
          (unitZeroSec (I := I) (M := M) y)) =
      (fun y : M => S y) := by
    funext y
    rw [unitScalarRSLiftCₛ_apply]
    exact unitScalarRSLiftSection_apply_unit (I := I) (M := M) (fun z => S z) y
  rw [hsec]

end Connection
end Integral
end DifferentialGeometry

end
