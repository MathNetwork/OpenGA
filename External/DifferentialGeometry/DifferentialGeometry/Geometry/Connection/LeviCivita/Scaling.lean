import DifferentialGeometry.Geometry.Connection.LeviCivita.KoszulFormula
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase

set_option autoImplicit false
set_option linter.style.longLine false









namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle
open DifferentialGeometry.Integral.Connection
open scoped Bundle Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private theorem mfderiv_const_smul_ne
    {f : M -> Real} {x : M} {c : Real} (hc : c ≠ 0) :
    mfderiv I 𝓘(Real, Real) (c • f) x =
      c • mfderiv I 𝓘(Real, Real) f x := by
  by_cases hf : MDifferentiableAt I 𝓘(Real, Real) f x
  · simpa using
      (const_smul_mfderiv (I := I) (f := f) (z := x) hf c)
  · have hcf : ¬ MDifferentiableAt I 𝓘(Real, Real) (c • f) x := by
      intro h
      have hinv : MDifferentiableAt I 𝓘(Real, Real) (c⁻¹ • (c • f)) x :=
        h.const_smul c⁻¹
      have heq : (c⁻¹ • (c • f) : M -> Real) = f := by
        funext y
        simp [Pi.smul_apply, smul_eq_mul, hc]
      exact hf (by simpa [heq] using hinv)
    rw [mfderiv_zero_of_not_mdifferentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt hcf]
    rw [smul_zero]
    rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private theorem directionalDeriv_const_mul_ne
    (X : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M)
    {c : Real} (hc : c ≠ 0) :
    directionalDerivAlong (I := I) X (fun y : M => c * f y) x =
      c * directionalDerivAlong (I := I) X f x := by
  change directionalDerivAlong (I := I) X (c • f) x =
    c * directionalDerivAlong (I := I) X f x
  unfold directionalDerivAlong
  rw [DifferentialGeometry.extDerivFun_real_eq_mfderiv I (c • f) x (X x),
    DifferentialGeometry.extDerivFun_real_eq_mfderiv I f x (X x)]
  rw [mfderiv_const_smul_ne (I := I) (f := f) (x := x) hc]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M) :
    koszulScalar (I := I) (scaleMetric (I := I) c hc g) X Y Z x =
      c * koszulScalar (I := I) g X Y Z x := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hYZ :
      directionalDerivAlong (I := I) X
          (fun y : M => c * g.inner y (Y y) (Z y)) x =
        c * directionalDerivAlong (I := I) X
          (fun y : M => g.inner y (Y y) (Z y)) x :=
    directionalDeriv_const_mul_ne (I := I) X
      (fun y : M => g.inner y (Y y) (Z y)) x hcne
  have hZX :
      directionalDerivAlong (I := I) Y
          (fun y : M => c * g.inner y (Z y) (X y)) x =
        c * directionalDerivAlong (I := I) Y
          (fun y : M => g.inner y (Z y) (X y)) x :=
    directionalDeriv_const_mul_ne (I := I) Y
      (fun y : M => g.inner y (Z y) (X y)) x hcne
  have hXY :
      directionalDerivAlong (I := I) Z
          (fun y : M => c * g.inner y (X y) (Y y)) x =
        c * directionalDerivAlong (I := I) Z
          (fun y : M => g.inner y (X y) (Y y)) x :=
    directionalDeriv_const_mul_ne (I := I) Z
      (fun y : M => g.inner y (X y) (Y y)) x hcne
  unfold koszulScalar
  simp only [scaleMetric_inner]
  rw [hYZ, hZX, hXY]
  ring

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulCovectorField_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M) :
    koszulCovectorField (I := I) (scaleMetric (I := I) c hc g) X Y x =
      c • koszulCovectorField (I := I) g X Y x := by
  classical
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  change
    (∑ i ∈ (Finset.univ : Finset (Fin (Module.finrank Real (TangentSpace I x)))),
      ((1 / 2 : Real) *
        koszulScalar (I := I) (scaleMetric (I := I) c hc g) X Y
          (tangentConstAt (I := I) x (B i)) x) • (B.coord i)) =
      c • ∑ i ∈ (Finset.univ : Finset (Fin (Module.finrank Real (TangentSpace I x)))),
        ((1 / 2 : Real) *
          koszulScalar (I := I) g X Y
            (tangentConstAt (I := I) x (B i)) x) • (B.coord i)
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ext v
  simp [koszulScalar_scaleMetric (I := I) c hc g, smul_eq_mul]
  ring

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem metricSharp_scaleMetric_smul
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M)
    (alpha : Module.Dual Real (TangentSpace I x)) :
    metricSharp (I := I) (scaleMetric (I := I) c hc g) x (c • alpha) =
      metricSharp (I := I) g x alpha := by
  apply metricFlatLinear_injective (I := I) g x
  ext w
  simp only [metricFlatLinear_apply]
  have hraw := inner_metricSharp (I := I)
    (scaleMetric (I := I) c hc g) x (c • alpha) w
  have hscaled :
      c * g.inner x
          (metricSharp (I := I) (scaleMetric (I := I) c hc g) x (c • alpha)) w =
        c * alpha w := by
    simpa [scaleMetric_inner, smul_eq_mul] using hraw
  have hcancel :
      g.inner x
          (metricSharp (I := I) (scaleMetric (I := I) c hc g) x (c • alpha)) w =
        alpha w :=
    mul_left_cancel₀ (ne_of_gt hc) hscaled
  calc
    g.inner x
        (metricSharp (I := I) (scaleMetric (I := I) c hc g) x (c • alpha)) w =
        alpha w := hcancel
    _ = g.inner x (metricSharp (I := I) g x alpha) w :=
        (inner_metricSharp (I := I) g x alpha w).symm

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulNablaField_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M) :
    koszulNablaField (I := I) (scaleMetric (I := I) c hc g) X Y x =
      koszulNablaField (I := I) g X Y x := by
  unfold koszulNablaField
  rw [koszulCovectorField_scaleMetric (I := I) c hc g X Y x]
  exact metricSharp_scaleMetric_smul (I := I) c hc g x
    (koszulCovectorField (I := I) g X Y x)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem leviCivitaConnectionCandidateAt_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M) :
    leviCivitaConnectionCandidateAt (I := I) (scaleMetric (I := I) c hc g) Y x =
      leviCivitaConnectionCandidateAt (I := I) g Y x := by
  classical
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  change
    LinearMap.toContinuousLinearMap
        (B.constr Real
          (fun i : Fin (Module.finrank Real (TangentSpace I x)) =>
            koszulNablaField (I := I) (scaleMetric (I := I) c hc g)
              (tangentConstAt (I := I) x (B i)) Y x)) =
      LinearMap.toContinuousLinearMap
        (B.constr Real
          (fun i : Fin (Module.finrank Real (TangentSpace I x)) =>
            koszulNablaField (I := I) g
              (tangentConstAt (I := I) x (B i)) Y x))
  congr 1
  apply B.ext
  intro i
  simp [koszulNablaField_scaleMetric (I := I) c hc g]



omit [SigmaCompactSpace M] [T2Space M] in
theorem lcConn_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) :
    leviCivitaConnectionOfMetric (I := I) (scaleMetric (I := I) c hc g) =
      leviCivitaConnectionOfMetric (I := I) g := by
  ext Y x v
  simp [leviCivitaConnectionOfMetric,
    leviCivitaConnectionCandidateAt_scaleMetric (I := I) c hc g Y x]

end

end DifferentialGeometry.Integral.Connection
