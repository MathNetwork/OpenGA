import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.TfHeatCore

set_option autoImplicit false
set_option linter.style.longLine false







noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped Manifold ContDiff BigOperators
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]







def quotField
    (phi psi : Real -> M -> Real) (alpha beta : Real) :
    Real -> M -> Real :=
  fun t x => phi t x ^ alpha * psi t x ^ (-beta)


def quotLap
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi : Real -> M -> Real) (alpha beta : Real) :
    Real -> M -> Real :=
  fun t x =>
    DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t
      (quotField (M := M) phi psi alpha beta t) x






def quotHeatRHS
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real) : Real -> M -> Real :=
  fun t x =>
    alpha * phi t x ^ (alpha - 1) * psi t x ^ (-beta) *
        phiHeat t x -
      beta * phi t x ^ alpha * psi t x ^ (-beta - 1) *
        psiHeat t x -
      alpha * (alpha - 1) * phi t x ^ (alpha - 2) *
        psi t x ^ (-beta) *
          (G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (phi t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (phi t) x) -
      ((-beta) * ((-beta) - 1)) * phi t x ^ alpha *
        psi t x ^ (-beta - 2) *
          (G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (psi t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (psi t) x) +
      2 * alpha * beta * phi t x ^ (alpha - 1) *
        psi t x ^ (-beta - 1) *
          (G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (phi t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (psi t) x)





def quotHeatRHSDiv
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real) : Real -> M -> Real :=
  fun t x =>
    alpha * phi t x ^ (alpha - 1) / psi t x ^ beta *
        phiHeat t x -
      beta * phi t x ^ alpha / psi t x ^ (beta + 1) *
        psiHeat t x -
      alpha * (alpha - 1) * phi t x ^ (alpha - 2) /
        psi t x ^ beta *
          (G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (phi t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (phi t) x) -
      beta * (beta + 1) * phi t x ^ alpha /
        psi t x ^ (beta + 2) *
          (G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (psi t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (psi t) x) +
      2 * alpha * beta * phi t x ^ (alpha - 1) /
        psi t x ^ (beta + 1) *
          (G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (phi t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (psi t) x)



omit [Module.Finite ℝ E] [IsManifold I 1 M] in
theorem quotHeatRHSDiv_eq
    [FiniteDimensional Real E]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real) {t : Real} {x : M}
    (hpsi : 0 < psi t x) :
    quotHeatRHSDiv (I := I) G phi psi phiHeat psiHeat alpha beta t x =
      quotHeatRHS (I := I) G phi psi phiHeat psiHeat alpha beta t x := by
  have h0 :
      psi t x ^ (-beta) = (psi t x ^ beta)⁻¹ := by
    simpa using Real.rpow_neg hpsi.le beta
  have h1 :
      psi t x ^ (-beta - 1) = (psi t x ^ (beta + 1))⁻¹ := by
    rw [show -beta - 1 = -(beta + 1) by ring]
    simpa using Real.rpow_neg hpsi.le (beta + 1)
  have h2 :
      psi t x ^ (-beta - 2) = (psi t x ^ (beta + 2))⁻¹ := by
    rw [show -beta - 2 = -(beta + 2) by ring]
    simpa using Real.rpow_neg hpsi.le (beta + 2)
  unfold quotHeatRHSDiv quotHeatRHS
  rw [h0, h1, h2]
  simp [div_eq_mul_inv]
  ring_nf


def QuotientEvolutionOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => quotField (M := M) phi psi alpha beta s x)
      (quotLap (I := I) G phi psi alpha beta (t : Real) x +
        quotHeatRHS (I := I) G phi psi phiHeat psiHeat alpha beta
          (t : Real) x)
      D.carrier
      (t : Real)



def QuotEvolDivOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => quotField (M := M) phi psi alpha beta s x)
      (quotLap (I := I) G phi psi alpha beta (t : Real) x +
        quotHeatRHSDiv (I := I) G phi psi phiHeat psiHeat alpha beta
          (t : Real) x)
      D.carrier
      (t : Real)







omit [Module.Finite ℝ E] in
theorem quotHeat_at
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiLap psiLap phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (hphiDt :
      HasDerivWithinAt (fun s : Real => phi s x)
        (phiLap (t : Real) x + phiHeat (t : Real) x)
        D.carrier (t : Real))
    (hpsiDt :
      HasDerivWithinAt (fun s : Real => psi s x)
        (psiLap (t : Real) x + psiHeat (t : Real) x)
        D.carrier (t : Real))
    (hphiLap :
      phiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (phi (t : Real)) x)
    (hpsiLap :
      psiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (psi (t : Real)) x)
    (hphiDiff :
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (phi (t : Real)) y)
    (hpsiDiff :
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (psi (t : Real)) y)
    (hphiPos : forall y : M, 0 < phi (t : Real) y)
    (hpsiPos : forall y : M, 0 < psi (t : Real) y)
    (hgradPhi :
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (phi (t : Real)) y) x)
    (hgradPsi :
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (psi (t : Real)) y) x)
    (hgradPhiPow :
      forall y : M, MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => phi (t : Real) w ^ alpha) z) y)
    (hgradPsiPow :
      forall y : M, MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => psi (t : Real) w ^ (-beta)) z) y) :
    HasDerivWithinAt
      (fun s : Real => quotField (M := M) phi psi alpha beta s x)
      (quotLap (I := I) G phi psi alpha beta (t : Real) x +
        quotHeatRHS (I := I) G phi psi phiHeat psiHeat alpha beta
          (t : Real) x)
      D.carrier
      (t : Real) := by
  let tt : Real := (t : Real)
  let A : M -> Real := fun y => phi tt y ^ alpha
  let B : M -> Real := fun y => psi tt y ^ (-beta)
  have hA_diff : forall y : M, MDifferentiableAt I 𝓘(Real, Real) A y := by
    intro y
    exact DifferentialGeometry.Integral.Connection.mdifferentiableAt_rpow
      (I := I) alpha (hphiDiff y) (hphiPos y)
  have hB_diff : forall y : M, MDifferentiableAt I 𝓘(Real, Real) B y := by
    intro y
    exact DifferentialGeometry.Integral.Connection.mdifferentiableAt_rpow
      (I := I) (-beta) (hpsiDiff y) (hpsiPos y)
  have hA_lap :=
    DifferentialGeometry.Integral.Connection.laplacianAt_rpow (I := I) G tt
      (f := phi tt) (x := x) alpha hphiDiff hphiPos hgradPhi
  have hB_lap :=
    DifferentialGeometry.Integral.Connection.laplacianAt_rpow (I := I) G tt
      (f := psi tt) (x := x) (-beta) hpsiDiff hpsiPos hgradPsi
  have hAB_lap :=
    DifferentialGeometry.Integral.Connection.laplacianAt_mul_of_scalarRegular (I := I) G tt
      (f := A) (h := B) (x := x)
      hA_diff hB_diff hgradPhiPow hgradPsiPow
  have hgradA :=
    DifferentialGeometry.Integral.Connection.gradientAt_rpow (I := I) G tt
      (f := phi tt) (x := x) alpha (hphiDiff x) (hphiPos x)
  have hgradB :=
    DifferentialGeometry.Integral.Connection.gradientAt_rpow (I := I) G tt
      (f := psi tt) (x := x) (-beta) (hpsiDiff x) (hpsiPos x)
  have hphiPowDt :=
    hphiDt.rpow_const (p := alpha) (Or.inl (hphiPos x).ne')
  have hpsiPowDt :=
    hpsiDt.rpow_const (p := -beta) (Or.inl (hpsiPos x).ne')
  have hdt := hphiPowDt.mul hpsiPowDt
  convert hdt using 1
  · unfold quotLap quotHeatRHS quotField
    simp only [tt] at hA_lap hB_lap hAB_lap hgradA hgradB hphiLap hpsiLap
    rw [hAB_lap, hA_lap, hB_lap, hgradA, hgradB, hphiLap, hpsiLap]
    simp [A, B, tt, smul_eq_mul]
    ring_nf


omit [Module.Finite ℝ E] in
theorem quotHeat
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiLap psiLap phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real)
    (hphiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => phi s x)
        (phiLap (t : Real) x + phiHeat (t : Real) x)
        D.carrier (t : Real))
    (hpsiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => psi s x)
        (psiLap (t : Real) x + psiHeat (t : Real) x)
        D.carrier (t : Real))
    (hphiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      phiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (phi (t : Real)) x)
    (hpsiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      psiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (psi (t : Real)) x)
    (hphiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (phi (t : Real)) y)
    (hpsiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (psi (t : Real)) y)
    (hphiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < phi (t : Real) y)
    (hpsiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < psi (t : Real) y)
    (hgradPhi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (phi (t : Real)) y) x)
    (hgradPsi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (psi (t : Real)) y) x)
    (hgradPhiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => phi (t : Real) w ^ alpha) z) y)
    (hgradPsiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => psi (t : Real) w ^ (-beta)) z) y) :
    QuotientEvolutionOn (I := I) (D := D) G
      phi psi phiHeat psiHeat alpha beta := by
  intro t x
  exact quotHeat_at (I := I) G phi psi phiLap psiLap phiHeat psiHeat
    alpha beta t x
    (hphiDt t x) (hpsiDt t x) (hphiLap t x) (hpsiLap t x)
    (hphiDiff t) (hpsiDiff t) (hphiPos t) (hpsiPos t)
    (hgradPhi t x) (hgradPsi t x) (hgradPhiPow t) (hgradPsiPow t)





omit [Module.Finite ℝ E] in
theorem quotHeat_one
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiLap psiLap phiHeat psiHeat : Real -> M -> Real)
    (beta : Real)
    (hphiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => phi s x)
        (phiLap (t : Real) x + phiHeat (t : Real) x)
        D.carrier (t : Real))
    (hpsiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => psi s x)
        (psiLap (t : Real) x + psiHeat (t : Real) x)
        D.carrier (t : Real))
    (hphiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      phiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (phi (t : Real)) x)
    (hpsiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      psiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (psi (t : Real)) x)
    (hphiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (phi (t : Real)) y)
    (hpsiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (psi (t : Real)) y)
    (hphiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < phi (t : Real) y)
    (hpsiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < psi (t : Real) y)
    (hgradPhi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (phi (t : Real)) y) x)
    (hgradPsi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (psi (t : Real)) y) x)
    (hgradPhiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => phi (t : Real) w ^ (1 : Real)) z) y)
    (hgradPsiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => psi (t : Real) w ^ (-beta)) z) y) :
    QuotientEvolutionOn (I := I) (D := D) G
      phi psi phiHeat psiHeat (1 : Real) beta := by
  exact quotHeat (I := I) (D := D) G
    phi psi phiLap psiLap phiHeat psiHeat (1 : Real) beta
    hphiDt hpsiDt hphiLap hpsiLap hphiDiff hpsiDiff
    hphiPos hpsiPos hgradPhi hgradPsi hgradPhiPow hgradPsiPow








omit [Module.Finite ℝ E] in
theorem quotHeat1_of_nonneg
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiLap psiLap phiHeat psiHeat : Real -> M -> Real)
    (beta : Real)
    (hphiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => phi s x)
        (phiLap (t : Real) x + phiHeat (t : Real) x)
        D.carrier (t : Real))
    (hpsiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => psi s x)
        (psiLap (t : Real) x + psiHeat (t : Real) x)
        D.carrier (t : Real))
    (hphiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      phiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (phi (t : Real)) x)
    (hpsiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      psiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (psi (t : Real)) x)
    (hphiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (phi (t : Real)) y)
    (hpsiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (psi (t : Real)) y)
    (_hphiNonneg : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 <= phi (t : Real) y)
    (hpsiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < psi (t : Real) y)
    (hgradPhi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (phi (t : Real)) y) x)
    (hgradPsi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (psi (t : Real)) y) x)
    (hgradPsiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => psi (t : Real) w ^ (-beta)) z) y) :
    QuotientEvolutionOn (I := I) (D := D) G
      phi psi phiHeat psiHeat (1 : Real) beta := by
  intro t x
  let tt : Real := (t : Real)
  let B : M -> Real := fun y => psi tt y ^ (-beta)
  have hB_diff : forall y : M, MDifferentiableAt I 𝓘(Real, Real) B y := by
    intro y
    exact DifferentialGeometry.Integral.Connection.mdifferentiableAt_rpow
      (I := I) (-beta) (hpsiDiff t y) (hpsiPos t y)
  have hB_lap :=
    DifferentialGeometry.Integral.Connection.laplacianAt_rpow (I := I) G tt
      (f := psi tt) (x := x) (-beta) (hpsiDiff t) (hpsiPos t)
      (hgradPsi t x)
  have hphiB_lap :=
    DifferentialGeometry.Integral.Connection.laplacianAt_mul_of_scalarRegular (I := I) G tt
      (f := phi tt) (h := B) (x := x)
      (hphiDiff t) hB_diff (hgradPhi t) (hgradPsiPow t)
  have hgradB :=
    DifferentialGeometry.Integral.Connection.gradientAt_rpow (I := I) G tt
      (f := psi tt) (x := x) (-beta) (hpsiDiff t x) (hpsiPos t x)
  have hpsiPowDt :=
    (hpsiDt t x).rpow_const (p := -beta) (Or.inl (hpsiPos t x).ne')
  have hdt := (hphiDt t x).mul hpsiPowDt
  have hfield_lap :
      DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G tt
          (fun y : M => phi tt y ^ (1 : Real) * psi tt y ^ (-beta)) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G tt
          (fun y : M => phi tt y * B y) x := by
    congr 1
    funext y
    simp [B]
  convert hdt using 1
  · funext s
    simp [quotField]
  · unfold quotLap quotHeatRHS quotField
    simp only [tt] at hB_lap hphiB_lap hgradB hphiLap hpsiLap hfield_lap
    rw [hfield_lap, hphiB_lap, hB_lap, hgradB, hphiLap t x, hpsiLap t x]
    simp [B, tt, smul_eq_mul]
    ring_nf







omit [Module.Finite ℝ E] in
theorem quotHeat_book
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiLap psiLap phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real)
    (hphiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => phi s x)
        (phiLap (t : Real) x + phiHeat (t : Real) x)
        D.carrier (t : Real))
    (hpsiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => psi s x)
        (psiLap (t : Real) x + psiHeat (t : Real) x)
        D.carrier (t : Real))
    (hphiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      phiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (phi (t : Real)) x)
    (hpsiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      psiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (psi (t : Real)) x)
    (hphiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (phi (t : Real)) y)
    (hpsiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (psi (t : Real)) y)
    (hphiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < phi (t : Real) y)
    (hpsiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < psi (t : Real) y)
    (hgradPhi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (phi (t : Real)) y) x)
    (hgradPsi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (psi (t : Real)) y) x)
    (hgradPhiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => phi (t : Real) w ^ alpha) z) y)
    (hgradPsiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => psi (t : Real) w ^ (-beta)) z) y) :
    QuotientEvolutionOn (I := I) (D := D) G
      phi psi phiHeat psiHeat alpha beta :=
  quotHeat (I := I) (D := D) G
    phi psi phiLap psiLap phiHeat psiHeat alpha beta
    hphiDt hpsiDt hphiLap hpsiLap hphiDiff hpsiDiff
    hphiPos hpsiPos hgradPhi hgradPsi hgradPhiPow hgradPsiPow





omit [Module.Finite ℝ E] in
theorem quotHeat1_book
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiLap psiLap phiHeat psiHeat : Real -> M -> Real)
    (beta : Real)
    (hphiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => phi s x)
        (phiLap (t : Real) x + phiHeat (t : Real) x)
        D.carrier (t : Real))
    (hpsiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => psi s x)
        (psiLap (t : Real) x + psiHeat (t : Real) x)
        D.carrier (t : Real))
    (hphiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      phiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (phi (t : Real)) x)
    (hpsiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      psiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (psi (t : Real)) x)
    (hphiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (phi (t : Real)) y)
    (hpsiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (psi (t : Real)) y)
    (hphiNonneg : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 <= phi (t : Real) y)
    (hpsiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < psi (t : Real) y)
    (hgradPhi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (phi (t : Real)) y) x)
    (hgradPsi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (psi (t : Real)) y) x)
    (hgradPsiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => psi (t : Real) w ^ (-beta)) z) y) :
    QuotientEvolutionOn (I := I) (D := D) G
      phi psi phiHeat psiHeat (1 : Real) beta :=
  quotHeat1_of_nonneg (I := I) (D := D) G
    phi psi phiLap psiLap phiHeat psiHeat beta
    hphiDt hpsiDt hphiLap hpsiLap hphiDiff hpsiDiff
    hphiNonneg hpsiPos hgradPhi hgradPsi hgradPsiPow


omit [Module.Finite ℝ E] in
theorem quotHeatDiv
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiLap psiLap phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real)
    (hphiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => phi s x)
        (phiLap (t : Real) x + phiHeat (t : Real) x)
        D.carrier (t : Real))
    (hpsiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => psi s x)
        (psiLap (t : Real) x + psiHeat (t : Real) x)
        D.carrier (t : Real))
    (hphiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      phiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (phi (t : Real)) x)
    (hpsiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      psiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (psi (t : Real)) x)
    (hphiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (phi (t : Real)) y)
    (hpsiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (psi (t : Real)) y)
    (hphiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < phi (t : Real) y)
    (hpsiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < psi (t : Real) y)
    (hgradPhi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (phi (t : Real)) y) x)
    (hgradPsi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (psi (t : Real)) y) x)
    (hgradPhiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => phi (t : Real) w ^ alpha) z) y)
    (hgradPsiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => psi (t : Real) w ^ (-beta)) z) y) :
    QuotEvolDivOn (I := I) (D := D) G
      phi psi phiHeat psiHeat alpha beta := by
  have hstable :=
    quotHeat_book (I := I) (D := D) G
      phi psi phiLap psiLap phiHeat psiHeat alpha beta
      hphiDt hpsiDt hphiLap hpsiLap hphiDiff hpsiDiff
      hphiPos hpsiPos hgradPhi hgradPsi hgradPhiPow hgradPsiPow
  intro t x
  have h := hstable t x
  convert h using 1
  · rw [quotHeatRHSDiv_eq (I := I) G phi psi phiHeat psiHeat alpha beta
      (hpsiPos t x)]

end DifferentialGeometry.PDE.RicciFlow
