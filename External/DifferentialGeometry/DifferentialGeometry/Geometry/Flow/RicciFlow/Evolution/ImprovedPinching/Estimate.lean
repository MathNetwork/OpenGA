import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.Wrappers
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.EigenBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RicciPreservation
import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.ScalarWeak

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


def pinchWeight (scalar : Real -> M -> Real) (epsilon : Real) :
    Real -> M -> Real :=
  fun t x => scalar t x ^ (-epsilon)


def PinchEstimateOn
    (tracefreeRicciNormSq scalar weight : Real -> M -> Real)
    (C : Real) (U : Set Real) : Prop :=
  ∀ t : Real, t ∈ U -> ∀ x : M,
    tracefreeRicciNormSq t x / scalar t x ^ 2 ≤ C * weight t x




def pinchQuotient
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (epsilon : Real) :
    Real -> M -> Real :=
  quotField (M := M)
    (tfRicNormSq S.scalar (ricciNorm (I := I) S))
    S.scalar (1 : Real) (2 - epsilon)


def pinchDriftVector
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar : Real -> M -> Real) (epsilon : Real) :
    Real -> (x : M) -> TangentSpace I x :=
  fun t x =>
    (2 * (1 - epsilon) / scalar t x) •
      DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x


omit [Module.Finite ℝ E] [IsManifold I 1 M] in
theorem pinchDriftTerm_eq_inner_drift
    [Module.Finite ℝ E]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar ricciNormSq : Real -> M -> Real)
    (epsilon t : Real) (x : M) :
    pinchDriftTerm (I := I) G scalar ricciNormSq epsilon t x =
      (G.metric t).inner x
        (pinchDriftVector (I := I) G scalar epsilon t x)
        (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t
          (quotField (M := M) (tfRicNormSq scalar ricciNormSq)
            scalar (1 : Real) (2 - epsilon) t) x) := by
  simp [pinchDriftTerm, pinchDriftVector]



omit [TopologicalSpace M] in
theorem pinchEstimateOn_of_pinchQuotient_bound
    {tracefreeRicciNormSq scalar : Real -> M -> Real}
    {epsilon C : Real} {U : Set Real}
    (hscalar : ∀ t : Real, t ∈ U -> ∀ x : M, 0 < scalar t x)
    (hP : ∀ t : Real, t ∈ U -> ∀ x : M,
      quotField (M := M) tracefreeRicciNormSq scalar
        (1 : Real) (2 - epsilon) t x ≤ C) :
    PinchEstimateOn (M := M) tracefreeRicciNormSq scalar
      (pinchWeight (M := M) scalar epsilon) C U := by
  intro t ht x
  have hR : 0 < scalar t x := hscalar t ht x
  have hweight_nonneg : 0 <= scalar t x ^ (-epsilon) :=
    le_of_lt (Real.rpow_pos_of_pos hR (-epsilon))
  have hmul :=
    mul_le_mul_of_nonneg_right (hP t ht x) hweight_nonneg
  have hpow :
      scalar t x ^ (-(2 - epsilon)) * scalar t x ^ (-epsilon) =
        scalar t x ^ (-(2 : Real)) := by
    rw [← Real.rpow_add hR]
    ring_nf
  have hneg2 :
      scalar t x ^ (-(2 : Real)) =
        (scalar t x ^ (2 : Real))⁻¹ := by
    simpa using Real.rpow_neg hR.le (2 : Real)
  have hquot :
      quotField (M := M) tracefreeRicciNormSq scalar
          (1 : Real) (2 - epsilon) t x *
          scalar t x ^ (-epsilon) =
        tracefreeRicciNormSq t x / scalar t x ^ 2 := by
    unfold quotField
    rw [Real.rpow_one, mul_assoc, hpow, hneg2]
    simp [div_eq_mul_inv]
  simpa [PinchEstimateOn, pinchWeight, hquot] using hmul


omit [TopologicalSpace M] in
theorem pinchSquareTerm_nonpos
    (scalar coupleSq : Real -> M -> Real) (epsilon t : Real) (x : M)
    (hR : 0 < scalar t x) (hcouple : 0 <= coupleSq t x) :
    pinchSquareTerm scalar coupleSq epsilon t x <= 0 := by
  have hden : 0 <= scalar t x ^ (4 - epsilon) :=
    le_of_lt (Real.rpow_pos_of_pos hR (4 - epsilon))
  have hcoef : -2 / scalar t x ^ (4 - epsilon) <= 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) hden
  simpa [pinchSquareTerm] using
    mul_nonpos_of_nonpos_of_nonneg hcoef hcouple



omit [TopologicalSpace M] in
theorem pinchGradTerm_nonpos
    (scalar ricciNormSq gradScalarNormSq : Real -> M -> Real)
    (epsilon t : Real) (x : M)
    (hR : 0 < scalar t x) (heps0 : 0 < epsilon) (heps1 : epsilon < 1)
    (htf : 0 <= tfRicNormSq scalar ricciNormSq t x)
    (hgrad : 0 <= gradScalarNormSq t x) :
    pinchGradTerm scalar ricciNormSq gradScalarNormSq epsilon t x <= 0 := by
  have hden : 0 <= scalar t x ^ (4 - epsilon) :=
    le_of_lt (Real.rpow_pos_of_pos hR (4 - epsilon))
  have heps_prod : 0 <= epsilon * (1 - epsilon) :=
    mul_nonneg (le_of_lt heps0) (by linarith)
  have hcoef :
      -epsilon * (1 - epsilon) / scalar t x ^ (4 - epsilon) <= 0 := by
    have hneg : -epsilon * (1 - epsilon) <= 0 := by
      nlinarith
    exact div_nonpos_of_nonpos_of_nonneg hneg hden
  have htfgrad :
      0 <= tfRicNormSq scalar ricciNormSq t x * gradScalarNormSq t x :=
    mul_nonneg htf hgrad
  have hmain :
      (-epsilon * (1 - epsilon) / scalar t x ^ (4 - epsilon)) *
          (tfRicNormSq scalar ricciNormSq t x * gradScalarNormSq t x) <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcoef htfgrad
  have hterm :
      pinchGradTerm scalar ricciNormSq gradScalarNormSq epsilon t x =
        (-epsilon * (1 - epsilon) / scalar t x ^ (4 - epsilon)) *
          (tfRicNormSq scalar ricciNormSq t x * gradScalarNormSq t x) := by
    simp [pinchGradTerm, mul_assoc]
  rw [hterm]
  exact hmain



omit [TopologicalSpace M] in
theorem pinchReactTerm_nonpos
    (scalar ricciNormSq Q : Real -> M -> Real)
    (epsilon t : Real) (x : M)
    (hR : 0 < scalar t x)
    (hreact :
      0 <= Q t x -
        epsilon * ricciNormSq t x * tfRicNormSq scalar ricciNormSq t x) :
    pinchReactTerm scalar ricciNormSq Q epsilon t x <= 0 := by
  have hden : 0 <= scalar t x ^ (3 - epsilon) :=
    le_of_lt (Real.rpow_pos_of_pos hR (3 - epsilon))
  have hcoef : -2 / scalar t x ^ (3 - epsilon) <= 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) hden
  simpa [pinchReactTerm] using
    mul_nonpos_of_nonpos_of_nonneg hcoef hreact



omit [Module.Finite ℝ E] in
theorem cubicQ_sub_nonneg_of_section9
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {T delta epsilon t : Real} {x : M}
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hscalar : 0 < S.scalar t x)
    (hdelta0 : 0 < delta)
    (hepsilon : epsilon <= 2 * delta ^ 2)
    (ht : t ∈ Set.Icc 0 T)
    (hric :
      DifferentialGeometry.Integral.Connection.TwoTensorFamilyNonnegativeOn (I := I) (M := M)
        (DifferentialGeometry.Integral.Connection.twoTensorSecToFamily (I := I) (M := M) S.ricci)
        (Set.Icc 0 T))
    (hpinch :
      PinchPres (I := I) (M := M)
        (fun t : Real => S.base.metric t)
        (DifferentialGeometry.Integral.Connection.twoTensorSecToFamily (I := I) (M := M) S.ricci)
        S.scalar T delta) :
    0 <=
      cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S) t x
        - epsilon * ricciNorm (I := I) S t x *
          tfRicNormSq S.scalar (ricciNorm (I := I) S) t x := by
  exact cubicQ_sub_nonneg_of_section9_point (I := I) S
    (hdim x) hscalar (le_of_lt hdelta0) hepsilon
    (hric t ht x) (hpinch t ht x)


omit [Module.Finite ℝ E] in
theorem scalGradSq_nonneg
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) :
    0 <= scalGradSq (I := I) S t x := by
  let v :=
    DifferentialGeometry.Integral.Connection.gradientAt (I := I) (flowG (I := I) S) t (S.scalar t) x
  change 0 <= (S.family.metric t).inner x v v
  by_cases hv : v = 0
  · simp [hv]
  · exact le_of_lt ((S.family.metric t).pos x v hv)


omit [Module.Finite ℝ E] in
theorem pinchCoupleSol_nonneg
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) :
    0 <= pinchCoupleSol (I := I) S t x := by
  simpa [pinchCoupleSol, ricciGradCoupleSq, normSq0S, inner0S] using
    (tensor0SMetricData (I := I) (S.family.metric t) x 3).inner_nonneg
      (ricciGradCoupleAt (I := I)
        (S.scalar t x) (S.ricci t x)
        (ricciNablaSec (I := I) S t x)
        (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (S.scalar t) x))



omit [Module.Finite ℝ E] [IsManifold I 1 M] in
theorem pinchBookRHS_le_drift
    [Module.Finite ℝ E]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar ricciNormSq gradScalarNormSq coupleSq Q : Real -> M -> Real)
    (epsilon t : Real) (x : M)
    (hR : 0 < scalar t x) (heps0 : 0 < epsilon) (heps1 : epsilon < 1)
    (hcouple : 0 <= coupleSq t x)
    (hgrad : 0 <= gradScalarNormSq t x)
    (htf : 0 <= tfRicNormSq scalar ricciNormSq t x)
    (hreact :
      0 <= Q t x -
        epsilon * ricciNormSq t x * tfRicNormSq scalar ricciNormSq t x) :
    pinchBookRHS (I := I) G scalar ricciNormSq gradScalarNormSq
        coupleSq Q epsilon t x <=
      pinchDriftTerm (I := I) G scalar ricciNormSq epsilon t x := by
  have hsquare :=
    pinchSquareTerm_nonpos (M := M) scalar coupleSq epsilon t x hR hcouple
  have hgradTerm :=
    pinchGradTerm_nonpos (M := M) scalar ricciNormSq gradScalarNormSq
      epsilon t x hR heps0 heps1 htf hgrad
  have hreactTerm :=
    pinchReactTerm_nonpos (M := M) scalar ricciNormSq Q epsilon t x hR hreact
  unfold pinchBookRHS
  nlinarith




omit [Module.Finite ℝ E] in
theorem pinchBookRHS_le_drift_sol
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    {T delta epsilon t : Real} {x : M}
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hR : 0 < S.scalar t x)
    (hdelta0 : 0 < delta)
    (heps0 : 0 < epsilon) (heps1 : epsilon < 1)
    (hepsilon : epsilon <= 2 * delta ^ 2)
    (ht : t ∈ Set.Icc 0 T)
    (hric :
      DifferentialGeometry.Integral.Connection.TwoTensorFamilyNonnegativeOn (I := I) (M := M)
        (DifferentialGeometry.Integral.Connection.twoTensorSecToFamily (I := I) (M := M) S.ricci)
        (Set.Icc 0 T))
    (hpinch :
      PinchPres (I := I) (M := M)
        (fun t : Real => S.base.metric t)
        (DifferentialGeometry.Integral.Connection.twoTensorSecToFamily (I := I) (M := M) S.ricci)
        S.scalar T delta) :
    pinchBookRHS (I := I) (flowG (I := I) S)
        S.scalar (ricciNorm (I := I) S) (scalGradSq (I := I) S)
        (pinchCoupleSol (I := I) S)
        (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
        epsilon t x <=
      pinchDriftTerm (I := I) (flowG (I := I) S)
        S.scalar (ricciNorm (I := I) S) epsilon t x := by
  exact pinchBookRHS_le_drift (I := I) (M := M)
    (flowG (I := I) S) S.scalar (ricciNorm (I := I) S)
    (scalGradSq (I := I) S) (pinchCoupleSol (I := I) S)
    (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
    epsilon t x hR heps0 heps1
    (pinchCoupleSol_nonneg (I := I) S t x)
    (scalGradSq_nonneg (I := I) S t x)
    (tfNonneg_sol (I := I) S (fun tt y => hdim y) t x)
    (cubicQ_sub_nonneg_of_section9 (I := I) S hdim hR hdelta0
      hepsilon ht hric hpinch)



omit [Module.Finite ℝ E] in
theorem pinchQuotient_parabolic_nonpos
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {omega T delta epsilon : Real} (h0ω : 0 < omega)
    (hD : D = DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω)
    (_hT : 0 <= T) (hTω : T < omega)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hscalar : ∀ t : Real, t ∈ D.carrier -> ∀ x : M, 0 < S.scalar t x)
    (hdelta0 : 0 < delta)
    (heps0 : 0 < epsilon) (heps1 : epsilon < 1)
    (hepsilon : epsilon <= 2 * delta ^ 2)
    (hric :
      DifferentialGeometry.Integral.Connection.TwoTensorFamilyNonnegativeOn (I := I) (M := M)
        (DifferentialGeometry.Integral.Connection.twoTensorSecToFamily (I := I) (M := M) S.ricci)
        (Set.Icc 0 T))
    (hpinch :
      PinchPres (I := I) (M := M)
        (fun t : Real => S.base.metric t)
        (DifferentialGeometry.Integral.Connection.twoTensorSecToFamily (I := I) (M := M) S.ricci)
        S.scalar T delta) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
        (pinchDriftVector (I := I) (flowG (I := I) S) S.scalar epsilon)
        (pinchQuotient (I := I) S epsilon) t x <= 0 := by
  intro t ht htpos x
  have hTpos : 0 < T := lt_of_lt_of_le htpos ht.2
  have htreg : t ∈ D.regular := by
    rw [hD]
    exact ⟨htpos, lt_of_le_of_lt ht.2 hTω⟩
  let τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D := ⟨t, htreg⟩
  have hIcc_subset : Set.Icc 0 T ⊆ D.carrier := by
    intro s hs
    rw [hD]
    exact ⟨hs.1, lt_of_le_of_lt hs.2 hTω⟩
  have hderivD :=
    pinchEvol_book (I := I) (M := M) S hS.isSolution
      (fun _ x => hdim x) heps0 heps1
      (fun τ y => hscalar (τ : Real) (D.regular_subset τ.2) y) τ x
  have hderivIcc := hderivD.mono hIcc_subset
  have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
    (uniqueDiffOn_Icc hTpos).uniqueDiffWithinAt ht
  have hderiv :
      derivWithin (fun s : Real => pinchQuotient (I := I) S epsilon s x)
          (Set.Icc 0 T) t =
        quotLap (I := I) (flowG (I := I) S)
          (tfRicNormSq S.scalar (ricciNorm (I := I) S))
          S.scalar (1 : Real) (2 - epsilon) t x +
        pinchBookRHS (I := I) (flowG (I := I) S)
          S.scalar (ricciNorm (I := I) S) (scalGradSq (I := I) S)
          (pinchCoupleSol (I := I) S)
          (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
          epsilon t x := by
    simpa [pinchQuotient, τ] using hderivIcc.derivWithin huniq
  have hheat :
      DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) (flowG (I := I) S) t
          (pinchDriftVector (I := I) (flowG (I := I) S) S.scalar epsilon t)
          (pinchQuotient (I := I) S epsilon t) x =
        quotLap (I := I) (flowG (I := I) S)
          (tfRicNormSq S.scalar (ricciNorm (I := I) S))
          S.scalar (1 : Real) (2 - epsilon) t x +
        pinchDriftTerm (I := I) (flowG (I := I) S)
          S.scalar (ricciNorm (I := I) S) epsilon t x := by
    unfold DifferentialGeometry.Integral.Connection.heatOperatorWithDrift DifferentialGeometry.Integral.Connection.driftTerm
      pinchQuotient quotLap
    rw [← pinchDriftTerm_eq_inner_drift (I := I) (M := M)
      (flowG (I := I) S) S.scalar (ricciNorm (I := I) S) epsilon t x]
  have hbook :=
    pinchBookRHS_le_drift_sol (I := I) (M := M) S hdim
      (hscalar t (hIcc_subset ht) x) hdelta0 heps0 heps1 hepsilon
      ht hric hpinch
  unfold DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift
  rw [hderiv, hheat]
  linarith


omit [Module.Finite ℝ E] in
theorem pinchQuotient_initial_continuous
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (epsilon : Real)
    (h0D : (0 : Real) ∈ D.carrier)
    (hscalar0 : ∀ x : M, 0 < S.scalar 0 x) :
    Continuous (fun x : M => pinchQuotient (I := I) S epsilon 0 x) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hnorm : ContinuousAt (fun y : M => ricciNorm (I := I) S 0 y) x :=
    (hS.ricciRegular.ricci_norm_space 0 h0D x).continuousAt
  have hscalarAt : ContinuousAt (fun y : M => S.scalar 0 y) x :=
    (hS.scalarRegular.scalar_space 0 h0D x).continuousAt
  have htf : ContinuousAt
      (fun y : M => tfRicNormSq S.scalar (ricciNorm (I := I) S) 0 y) x := by
    simpa [tfRicNormSq, tracefreeRicciNormSqOf, tracefreeRicciNormSqAtOf,
      div_eq_mul_inv] using
      hnorm.sub ((hscalarAt.pow 2).mul continuousAt_const)
  have hpow : ContinuousAt (fun y : M => S.scalar 0 y ^ (-(2 - epsilon))) x :=
    hscalarAt.rpow_const (Or.inl (ne_of_gt (hscalar0 x)))
  simpa [pinchQuotient, quotField] using htf.mul hpow


theorem compact_nonneg_upper_bound
    [CompactSpace M] (f : M -> Real) (hf : Continuous f) :
    ∃ C : Real, 0 <= C ∧ ∀ x : M, f x <= C := by
  classical
  by_cases hne : Nonempty M
  · have hcompact : IsCompact (Set.univ : Set M) := isCompact_univ
    rcases hcompact.exists_isMaxOn
        (show (Set.univ : Set M).Nonempty from ⟨Classical.choice hne, trivial⟩)
        hf.continuousOn with
      ⟨x0, _hx0, hmax⟩
    refine ⟨max 0 (f x0), le_max_left _ _, ?_⟩
    intro x
    exact le_trans (hmax trivial) (le_max_right _ _)
  · refine ⟨0, le_rfl, ?_⟩
    intro x
    exact False.elim (hne ⟨x⟩)


omit [Module.Finite ℝ E] in
theorem pinchQuotient_initial_bound
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (epsilon : Real)
    (h0D : (0 : Real) ∈ D.carrier)
    (hscalar0 : ∀ x : M, 0 < S.scalar 0 x) :
    ∃ C : Real,
      0 <= C ∧ ∀ x : M,
        pinchQuotient (I := I) S epsilon 0 x <= C :=
  compact_nonneg_upper_bound (M := M)
    (fun x : M => pinchQuotient (I := I) S epsilon 0 x)
    (pinchQuotient_initial_continuous (I := I) S hS epsilon h0D hscalar0)

private theorem continuousOn_of_restrict
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {s : Set α} {f : α -> β}
    (h : Continuous (s.restrict f)) :
    ContinuousOn f s := by
  intro x hx
  exact (continuousWithinAt_iff_continuousAt_restrict f hx).mpr h.continuousAt

omit [Module.Finite ℝ E] in
private theorem ricciComp_coordCont
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (x0 : M) (i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    ContinuousOn
      (fun p : Real × M =>
        ricciCompInFrame (I := I) S
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0) p.1 p.2 i j)
      (D.carrier ×ˢ DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x0) := by
  classical
  let K : Set Real := D.carrier
  let u : Set M := DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x0
  let frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0
  let P := {p : Real × M // p ∈ K ×ˢ u}
  have hcomp : Continuous (fun q : P =>
      ricciCompInFrame (I := I) S frame q.1.1 q.1.2 i j) := by
    have hframe_i : Continuous (fun q : P =>
        (⟨q.1.2, frame i q.1.2⟩ : TangentBundle I M)) := by
      have hlocal : ContinuousOn (fun y : M =>
          (⟨y, frame i y⟩ : TangentBundle I M)) u := by
        simpa [frame, u] using
          ((DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame (I := I) x0).contMDiffOn i).continuousOn
      exact hlocal.comp_continuous
        (continuous_snd.comp continuous_subtype_val) (fun q => q.2.2)
    have hframe_j : Continuous (fun q : P =>
        (⟨q.1.2, frame j q.1.2⟩ : TangentBundle I M)) := by
      have hlocal : ContinuousOn (fun y : M =>
          (⟨y, frame j y⟩ : TangentBundle I M)) u := by
        simpa [frame, u] using
          ((DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame (I := I) x0).contMDiffOn j).continuousOn
      exact hlocal.comp_continuous
        (continuous_snd.comp continuous_subtype_val) (fun q => q.2.2)
    have hA := hS.ricciRegular.ricciTensorFamilyContinuousOnSet
    have heval := DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.eval_continuous
      (I := I) (M := M) (s := 2) (K := K)
      (A := fun t x => S.ricci t x) hA
      (P := P)
      (τ := fun q : P => q.1.1)
      (b := fun q : P => q.1.2)
      (continuous_fst.comp continuous_subtype_val)
      (fun q : P => q.2.1)
      (continuous_snd.comp continuous_subtype_val)
      (v := fun a : Fin 2 => fun q : P =>
        if a = 0 then frame i q.1.2 else frame j q.1.2)
      (by
        intro a
        fin_cases a
        · simpa using hframe_i
        · simpa using hframe_j)
    simpa [ricciCompInFrame, frame, DifferentialGeometry.Integral.Connection.vec2] using heval
  simpa [K, u, P, frame] using
    continuousOn_of_restrict (s := D.carrier ×ˢ DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x0)
      (f := fun p : Real × M =>
        ricciCompInFrame (I := I) S
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0) p.1 p.2 i j)
      hcomp

omit [Module.Finite ℝ E] in
private theorem ricciNorm_coordCont
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (x0 : M) :
    ContinuousOn (fun p : Real × M => ricciNorm (I := I) S p.1 p.2)
      (D.carrier ×ˢ DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x0) := by
  classical
  let Idx := DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E
  let frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0
  let gInv := coordInv (I := I) S x0
  let U := D.carrier ×ˢ DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x0
  have hInv : ∀ i j : Idx,
      ContinuousOn (fun p : Real × M => gInv p.1 p.2 i j) U := by
    intro i j
    simpa [gInv, U] using
      coordInvContOn (I := I) S hS.isSolution x0 i j
  have hRic : ∀ i j : Idx,
      ContinuousOn (fun p : Real × M =>
        ricciCompInFrame (I := I) S frame p.1 p.2 i j) U := by
    intro i j
    simpa [frame, U] using
      ricciComp_coordCont (I := I) S hS x0 i j
  have hRaised : ∀ i j : Idx,
      ContinuousOn (fun p : Real × M =>
        raisedRicciCompInFrame (I := I) S gInv frame p.1 p.2 i j) U := by
    intro i j
    simp only [raisedRicciCompInFrame_apply]
    refine continuousOn_finset_sum _ (fun a _ => ?_)
    refine continuousOn_finset_sum _ (fun b _ => ?_)
    exact ((hInv i a).mul (hInv j b)).mul (hRic a b)
  have hFrameNorm : ContinuousOn (fun p : Real × M =>
      ricciNormSqInFrame (I := I) S gInv frame p.1 p.2) U := by
    simp only [ricciNormSqInFrame_apply]
    refine continuousOn_finset_sum _ (fun i _ => ?_)
    refine continuousOn_finset_sum _ (fun j _ => ?_)
    exact (hRic i j).mul (hRaised i j)
  refine hFrameNorm.congr ?_
  intro p hp
  have hbasis :
      ∀ i : Idx,
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x0 hp.2) i =
          frame i p.2 := by
    intro i
    simp [frame, DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply]
  have hnorm :=
    ricciNormSq_basis (I := I) S gInv frame
      (t := p.1) (x := p.2)
      (basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x0 hp.2)
      (hinv := by
        simpa [gInv, coordInv] using
          DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) (S.family.metric p.1) x0 hp.2)
      hbasis
  simpa [ricciNorm, U] using hnorm.symm

omit [Module.Finite ℝ E] in
private theorem ricciNorm_slabCont
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {omega T : Real} (h0ω : 0 < omega)
    (hD : D = DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω)
    (hTω : T < omega) :
    ContinuousOn (fun p : Real × M => ricciNorm (I := I) S p.1 p.2)
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T) := by
  classical
  refine continuousOn_of_locally_continuousOn ?_
  intro p hp
  let u : Set (Real × M) :=
    Set.univ ×ˢ DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) p.2
  refine ⟨u, ?_, ?_, ?_⟩
  · exact isOpen_univ.prod (DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open (I := I) p.2)
  · exact ⟨trivial, DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) p.2⟩
  · have hlocal := ricciNorm_coordCont (I := I) S hS p.2
    refine hlocal.mono ?_
    intro q hq
    rcases hq with ⟨hslab, _hu_time, hu_space⟩
    have hslab' : q.1 ∈ Set.Icc 0 T ∧ q.2 ∈ (Set.univ : Set M) := by
      simpa [DifferentialGeometry.Integral.Connection.spacetimeSlab] using hslab
    constructor
    · rw [hD]
      exact ⟨hslab'.1.1, lt_of_le_of_lt hslab'.1.2 hTω⟩
    · exact hu_space



omit [Module.Finite ℝ E] in
theorem pinchQuotient_slab_continuous_of_ricciNorm
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {omega T epsilon C : Real} (h0ω : 0 < omega)
    (hD : D = DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω)
    (hTω : T < omega)
    (hscalar : ∀ t : Real, t ∈ D.carrier -> ∀ x : M, 0 < S.scalar t x)
    (hricciNorm_cont :
      ContinuousOn (fun p : Real × M => ricciNorm (I := I) S p.1 p.2)
        (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T)) :
    ContinuousOn
      (fun p : Real × M => C - pinchQuotient (I := I) S epsilon p.1 p.2)
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T) := by
  have hscalar_cont : ContinuousOn (fun p : Real × M => S.scalar p.1 p.2)
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T) := by
    simpa [DifferentialGeometry.Integral.Connection.spacetimeSlab] using
      (SolutionOn.scalar_continuousOn (I := I) (M := M) S
        hS.isSolution hS.scalarSTCont T
        (by
          intro t ht
          rw [hD]
          exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩))
  have hscalar_ne : ∀ p : Real × M, p ∈ DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T ->
      S.scalar p.1 p.2 ≠ 0 ∨ 0 ≤ -(2 - epsilon) := by
    intro p hp
    have hp' : p.1 ∈ Set.Icc 0 T ∧ p.2 ∈ (Set.univ : Set M) := by
      simpa [DifferentialGeometry.Integral.Connection.spacetimeSlab] using hp
    have hpD : p.1 ∈ D.carrier := by
      rw [hD]
      exact ⟨hp'.1.1, lt_of_le_of_lt hp'.1.2 hTω⟩
    exact Or.inl (ne_of_gt (hscalar p.1 hpD p.2))
  have htf_cont : ContinuousOn
      (fun p : Real × M =>
        tfRicNormSq S.scalar (ricciNorm (I := I) S) p.1 p.2)
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T) := by
    simpa [tfRicNormSq, tracefreeRicciNormSqOf,
      tracefreeRicciNormSqAtOf, div_eq_mul_inv] using
      hricciNorm_cont.sub ((hscalar_cont.pow 2).mul continuousOn_const)
  have hpow_cont : ContinuousOn
      (fun p : Real × M => S.scalar p.1 p.2 ^ (-(2 - epsilon)))
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T) :=
    hscalar_cont.rpow_const hscalar_ne
  have hquot_cont : ContinuousOn
      (fun p : Real × M => pinchQuotient (I := I) S epsilon p.1 p.2)
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T) := by
    simpa [pinchQuotient, quotField] using htf_cont.mul hpow_cont
  exact continuousOn_const.sub hquot_cont


omit [Module.Finite ℝ E] in
theorem pinchQuotient_space_pos
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (epsilon : Real)
    (hscalar : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      0 < S.scalar (t : Real) x) :
    ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDifferentiableAt I 𝓘(Real, Real)
        (pinchQuotient (I := I) S epsilon (t : Real)) x := by
  intro t x
  let p : Real := -(2 - epsilon)
  have htf := tfDiff_sol (I := I) S hS.isSolution t x
  have ht : (t : Real) ∈ D.carrier := D.regular_subset t.2
  have hscalarDiff :
      MDifferentiableAt I 𝓘(Real, Real) (S.scalar (t : Real)) x :=
    hS.scalarRegular.scalar_space (t : Real) ht x
  have hpow :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => S.scalar (t : Real) y ^ p) x :=
    DifferentialGeometry.Integral.Connection.mdifferentiableAt_rpow (I := I) p hscalarDiff (hscalar t x)
  have hprod :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => tfRicNormSq S.scalar (ricciNorm (I := I) S) (t : Real) y *
          S.scalar (t : Real) y ^ p) x :=
    htf.mul hpow
  convert hprod using 1
  funext y
  simp [pinchQuotient, quotField, p]


omit [Module.Finite ℝ E] in
theorem pinchQuotient_grad_pos
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (epsilon : Real)
    (hscalar : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      0 < S.scalar (t : Real) x) :
    ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (pinchQuotient (I := I) S epsilon (t : Real)) y) x := by
  intro t x
  let f : M -> Real := tfRicNormSq S.scalar (ricciNorm (I := I) S) (t : Real)
  let h : M -> Real := fun y : M => S.scalar (t : Real) y ^ (-(2 - epsilon))
  have hfDiff : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) f y := by
    intro y
    simpa [f] using tfDiff_sol (I := I) S hS.isSolution t y
  have hhDiff : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) h y := by
    intro y
    have ht : (t : Real) ∈ D.carrier := D.regular_subset t.2
    exact DifferentialGeometry.Integral.Connection.mdifferentiableAt_rpow (I := I) (-(2 - epsilon))
      (hS.scalarRegular.scalar_space (t : Real) ht y) (hscalar t y)
  have hgradf : MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) f y) x := by
    simpa [f] using tfGrad_sol (I := I) S hS.isSolution t x
  have hgradh : MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) h y) x := by
    simpa [h] using scalarPowGrad_sol (I := I) S hS.isSolution epsilon hscalar t x
  have hterm1 : MDiffAt (T% (f • fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) h y)) x :=
    (hfDiff x).smul_section hgradh
  have hterm2 : MDiffAt (T% (h • fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) f y)) x :=
    (hhDiff x).smul_section hgradf
  have hsum : MDiffAt (T% fun y : M =>
      f y • DifferentialGeometry.Integral.Connection.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) h y +
      h y • DifferentialGeometry.Integral.Connection.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) f y) x :=
    by simpa using mdifferentiableAt_add_section hterm1 hterm2
  have hgrad_eq :
      (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (pinchQuotient (I := I) S epsilon (t : Real)) y) =
      (T% fun y : M =>
        f y • DifferentialGeometry.Integral.Connection.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real)) h y +
        h y • DifferentialGeometry.Integral.Connection.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real)) f y) := by
    have hfun_eq :
        pinchQuotient (I := I) S epsilon (t : Real) =
          fun y : M => f y * h y := by
      funext y
      simp [pinchQuotient, quotField, f, h]
    funext y
    rw [hfun_eq]
    simpa [f, h] using
      DifferentialGeometry.Integral.Connection.gradientFun_mul (I := I)
        ((flowG (I := I) S).metric (t : Real))
        (hfDiff y) (hhDiff y)
  rw [hgrad_eq]
  exact hsum








omit [Module.Finite ℝ E] in
theorem pinchQuot_slab_bound
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {omega T delta epsilon C : Real} (h0ω : 0 < omega)
    (hD : D = DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω)
    (hT : 0 <= T) (hTω : T < omega)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hscalar : ∀ t : Real, t ∈ D.carrier -> ∀ x : M, 0 < S.scalar t x)
    (hdelta0 : 0 < delta)
    (heps0 : 0 < epsilon) (heps1 : epsilon < 1)
    (hepsilon : epsilon <= 2 * delta ^ 2)
    (hric :
      DifferentialGeometry.Integral.Connection.TwoTensorFamilyNonnegativeOn (I := I) (M := M)
        (DifferentialGeometry.Integral.Connection.twoTensorSecToFamily (I := I) (M := M) S.ricci)
        (Set.Icc 0 T))
    (hpinch :
      PinchPres (I := I) (M := M)
        (fun t : Real => S.base.metric t)
        (DifferentialGeometry.Integral.Connection.twoTensorSecToFamily (I := I) (M := M) S.ricci)
        S.scalar T delta)
    (hinit : ∀ x : M, pinchQuotient (I := I) S epsilon 0 x <= C)
    (hw_cont : ContinuousOn
      (fun p : Real × M => C - pinchQuotient (I := I) S epsilon p.1 p.2)
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T)) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      pinchQuotient (I := I) S epsilon t x <= C := by
  classical
  have hsub :
      ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
        DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
          (pinchDriftVector (I := I) (flowG (I := I) S) S.scalar epsilon)
          (pinchQuotient (I := I) S epsilon) t x <= 0 :=
    pinchQuotient_parabolic_nonpos (I := I) (M := M) S hS h0ω hD
      hT hTω hdim hscalar hdelta0 heps0 heps1 hepsilon hric hpinch
  have hw_time : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      ∀ x : M, DifferentiableWithinAt Real
        (fun s : Real => C - pinchQuotient (I := I) S epsilon s x)
        (Set.Icc 0 T) t := by
    intro t ht htpos x
    have hIcc_subset : Set.Icc 0 T ⊆ D.carrier := by
      intro s hs
      rw [hD]
      exact ⟨hs.1, lt_of_le_of_lt hs.2 hTω⟩
    have hTpos : 0 < T := lt_of_lt_of_le htpos ht.2
    have htreg : t ∈ D.regular := by
      rw [hD]
      exact ⟨htpos, lt_of_le_of_lt ht.2 hTω⟩
    let τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D := ⟨t, htreg⟩
    have hderivD :=
      pinchEvol_book (I := I) (M := M) S hS.isSolution
        (fun _ x => hdim x) heps0 heps1
        (fun τ y => hscalar (τ : Real) (D.regular_subset τ.2) y) τ x
    have hderivIcc := hderivD.mono hIcc_subset
    have hu :
        DifferentiableWithinAt Real
          (fun s : Real => pinchQuotient (I := I) S epsilon s x)
          (Set.Icc 0 T) t := by
      simpa [pinchQuotient, τ] using hderivIcc.differentiableWithinAt
    exact (differentiableWithinAt_const C).sub hu
  have hw_mdiff : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      ∀ x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => C - pinchQuotient (I := I) S epsilon t y) x := by
    intro t ht htpos x
    have htreg : t ∈ D.regular := by
      rw [hD]
      exact ⟨htpos, lt_of_le_of_lt ht.2 hTω⟩
    let τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D := ⟨t, htreg⟩
    have hP :=
      pinchQuotient_space_pos (I := I) S hS epsilon
        (fun τ y => hscalar (τ : Real) (D.regular_subset τ.2) y) τ x
    simpa [τ] using mdifferentiableAt_const.sub hP
  have hw_grad : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) ((flowG (I := I) S).metric t)
          (fun z : M => C - pinchQuotient (I := I) S epsilon t z) y) x := by
    intro t ht htpos x
    have htreg : t ∈ D.regular := by
      rw [hD]
      exact ⟨htpos, lt_of_le_of_lt ht.2 hTω⟩
    let τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D := ⟨t, htreg⟩
    have hPgrad :=
      pinchQuotient_grad_pos (I := I) S hS epsilon
        (fun τ y => hscalar (τ : Real) (D.regular_subset τ.2) y) τ x
    have hPdiff : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real)
        (pinchQuotient (I := I) S epsilon t) y := by
      intro y
      simpa [τ] using
        pinchQuotient_space_pos (I := I) S hS epsilon
          (fun τ y => hscalar (τ : Real) (D.regular_subset τ.2) y) τ y
    have hgrad_plain :
        (fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) ((flowG (I := I) S).metric t)
            (fun z : M => C - pinchQuotient (I := I) S epsilon t z) y) =
        (fun y : M =>
          - DifferentialGeometry.Integral.Connection.gradientFun (I := I) ((flowG (I := I) S).metric t)
            (pinchQuotient (I := I) S epsilon t) y) := by
      funext y
      calc
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) ((flowG (I := I) S).metric t)
            (fun z : M => C - pinchQuotient (I := I) S epsilon t z) y =
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) ((flowG (I := I) S).metric t)
              (fun _ : M => C) y -
            DifferentialGeometry.Integral.Connection.gradientFun (I := I) ((flowG (I := I) S).metric t)
              (pinchQuotient (I := I) S epsilon t) y := by
            exact DifferentialGeometry.Integral.Connection.gradientFun_sub (I := I)
              ((flowG (I := I) S).metric t)
              mdifferentiableAt_const (hPdiff y)
        _ = - DifferentialGeometry.Integral.Connection.gradientFun (I := I) ((flowG (I := I) S).metric t)
              (pinchQuotient (I := I) S epsilon t) y := by
            rw [DifferentialGeometry.Integral.Connection.gradientFun_const]
            simp
    have hgrad_eq :
        (T% fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) ((flowG (I := I) S).metric t)
            (fun z : M => C - pinchQuotient (I := I) S epsilon t z) y) =
        (T% fun y : M =>
          - DifferentialGeometry.Integral.Connection.gradientFun (I := I) ((flowG (I := I) S).metric t)
            (pinchQuotient (I := I) S epsilon t) y) := by
      funext y
      simpa using congrFun hgrad_plain y
    rw [hgrad_eq]
    simpa [τ] using mdifferentiableAt_neg_section hPgrad
  have hoperator_neg : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      ∀ x : M,
        DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
          (pinchDriftVector (I := I) (flowG (I := I) S) S.scalar epsilon)
          (fun s y => C - pinchQuotient (I := I) S epsilon s y) t x =
        - DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
          (pinchDriftVector (I := I) (flowG (I := I) S) S.scalar epsilon)
          (pinchQuotient (I := I) S epsilon) t x := by
    intro t ht htpos x
    have hTpos : 0 < T := lt_of_lt_of_le htpos ht.2
    have hIcc_subset : Set.Icc 0 T ⊆ D.carrier := by
      intro s hs
      rw [hD]
      exact ⟨hs.1, lt_of_le_of_lt hs.2 hTω⟩
    have htreg : t ∈ D.regular := by
      rw [hD]
      exact ⟨htpos, lt_of_le_of_lt ht.2 hTω⟩
    let τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D := ⟨t, htreg⟩
    have hderivD :=
      pinchEvol_book (I := I) (M := M) S hS.isSolution
        (fun _ x => hdim x) heps0 heps1
        (fun τ y => hscalar (τ : Real) (D.regular_subset τ.2) y) τ x
    have hu_time :
        DifferentiableWithinAt Real
          (fun s : Real => pinchQuotient (I := I) S epsilon s x)
          (Set.Icc 0 T) t := by
      simpa [pinchQuotient, τ] using
        (hderivD.mono hIcc_subset).differentiableWithinAt
    have hu_space : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real)
        (pinchQuotient (I := I) S epsilon t) y := by
      intro y
      simpa [τ] using
        pinchQuotient_space_pos (I := I) S hS epsilon
          (fun τ y => hscalar (τ : Real) (D.regular_subset τ.2) y) τ y
    have hu_grad : MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) ((flowG (I := I) S).metric t)
          (pinchQuotient (I := I) S epsilon t) y) x := by
      simpa [τ] using
        pinchQuotient_grad_pos (I := I) S hS epsilon
          (fun τ y => hscalar (τ : Real) (D.regular_subset τ.2) y) τ x
    exact DifferentialGeometry.Integral.Connection.parabolic_const_sub (I := I) (flowG (I := I) S) T
      (pinchDriftVector (I := I) (flowG (I := I) S) S.scalar epsilon)
      (pinchQuotient (I := I) S epsilon) C t x
      ((uniqueDiffOn_Icc hTpos).uniqueDiffWithinAt ht)
      hu_time hu_space hu_grad
  exact DifferentialGeometry.Integral.Connection.scalar_sub_const_posReg (I := I)
    (flowG (I := I) S) T hT
    (pinchDriftVector (I := I) (flowG (I := I) S) S.scalar epsilon)
    (pinchQuotient (I := I) S epsilon) C
    hw_cont hw_time hw_mdiff hw_grad hinit hsub hoperator_neg


def carrierZeroExt
    (D : DifferentialGeometry.Integral.Connection.RealTimeInterval) (f : Real -> M -> Real) :
    Real -> M -> Real := by
  classical
  exact fun t x => if t ∈ D.carrier then f t x else 0



def carrierScalarExt
    (D : DifferentialGeometry.Integral.Connection.RealTimeInterval) (scalar : Real -> M -> Real) :
    Real -> M -> Real := by
  classical
  exact fun t x => if t ∈ D.carrier then scalar t x else 1


def carrierWeightExt
    (D : DifferentialGeometry.Integral.Connection.RealTimeInterval) (scalar : Real -> M -> Real)
    (epsilon : Real) : Real -> M -> Real := by
  classical
  exact fun t x =>
    if t ∈ D.carrier then pinchWeight (M := M) scalar epsilon t x else 0



omit [TopologicalSpace M] in
theorem pinchEstimate_ext
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {tracefreeRicciNormSq scalar : Real -> M -> Real}
    {epsilon C : Real}
    (h : PinchEstimateOn (M := M) tracefreeRicciNormSq scalar
      (pinchWeight (M := M) scalar epsilon) C D.carrier) :
    PinchEstimateOn (M := M)
      (carrierZeroExt (M := M) D tracefreeRicciNormSq)
      (carrierScalarExt (M := M) D scalar)
      (carrierWeightExt (M := M) D scalar epsilon) C Set.univ := by
  intro t _ht x
  by_cases htD : t ∈ D.carrier
  · simpa [carrierZeroExt, carrierScalarExt, carrierWeightExt, htD] using
      h t htD x
  · simp [carrierZeroExt, carrierScalarExt, carrierWeightExt, htD]








omit [Module.Finite ℝ E] in
theorem pinchEstimate_sol
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E
      (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E
      (TangentSpace I : M -> Type _) I]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {omega : Real} (h0ω : 0 < omega)
    (hD : D = DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hscalar : ∀ t : Real, t ∈ D.carrier -> ∀ x : M, 0 < S.scalar t x)
    (hpinch :
      ∃ delta : Real,
        0 < delta ∧ delta < (1 : Real) / 3 ∧
          ∀ T : Real, 0 ≤ T -> T < omega ->
            PinchPres (I := I) (M := M)
              (fun t : Real => S.base.metric t)
              (DifferentialGeometry.Integral.Connection.twoTensorSecToFamily (I := I) (M := M) S.ricci)
              S.scalar T delta)
    (hric :
      ∀ T : Real, 0 ≤ T -> T < omega ->
        DifferentialGeometry.Integral.Connection.TwoTensorFamilyNonnegativeOn (I := I) (M := M)
          (DifferentialGeometry.Integral.Connection.twoTensorSecToFamily (I := I) (M := M) S.ricci)
          (Set.Icc 0 T)) :
    ∃ epsilon C : Real,
      0 < epsilon ∧ epsilon < 1 ∧ 0 ≤ C ∧
        PinchEstimateOn (M := M)
          (tfRicNormSq S.scalar (ricciNorm (I := I) S))
          S.scalar (pinchWeight (M := M) S.scalar epsilon) C D.carrier := by
  classical
  rcases hpinch with ⟨delta, hdelta0, _hdelta13, hpinchAll⟩
  let epsilon : Real := min ((1 : Real) / 2) (delta ^ 2)
  have hdelta_sq_pos : 0 < delta ^ 2 := sq_pos_of_ne_zero hdelta0.ne'
  have heps0 : 0 < epsilon := by
    dsimp [epsilon]
    exact lt_min (by norm_num) hdelta_sq_pos
  have heps1 : epsilon < 1 := by
    dsimp [epsilon]
    exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hepsilon : epsilon <= 2 * delta ^ 2 := by
    dsimp [epsilon]
    have hsq_nonneg : 0 <= delta ^ 2 := sq_nonneg delta
    nlinarith [min_le_right ((1 : Real) / 2) (delta ^ 2)]
  have h0D : (0 : Real) ∈ D.carrier := by
    rw [hD]
    exact ⟨le_rfl, h0ω⟩
  obtain ⟨C, hC0, hCinit⟩ :=
    pinchQuotient_initial_bound (I := I) (M := M) S hS epsilon h0D
      (hscalar 0 h0D)
  refine ⟨epsilon, C, heps0, heps1, hC0, ?_⟩
  apply pinchEstimateOn_of_pinchQuotient_bound (M := M)
    (tracefreeRicciNormSq := tfRicNormSq S.scalar (ricciNorm (I := I) S))
    (scalar := S.scalar) (epsilon := epsilon) (C := C)
    (U := D.carrier) hscalar
  intro t htD x
  have htD' : t ∈ (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω).carrier := by
    simpa [hD] using htD
  have ht0 : 0 <= t := htD'.1
  have htω : t < omega := htD'.2
  by_cases htpos : 0 < t
  · have hricT := hric t ht0 htω
    have hpinchT := hpinchAll t ht0 htω
    have hricciNorm_cont : ContinuousOn
        (fun p : Real × M => ricciNorm (I := I) S p.1 p.2)
        (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) t) :=
      ricciNorm_slabCont (I := I) (M := M) S hS h0ω hD htω
    have hw_cont : ContinuousOn
        (fun p : Real × M =>
          C - pinchQuotient (I := I) S epsilon p.1 p.2)
        (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) t) :=
      pinchQuotient_slab_continuous_of_ricciNorm (I := I) (M := M)
        S hS h0ω hD htω hscalar hricciNorm_cont
    have hbound :=
      pinchQuot_slab_bound (I := I) (M := M) S hS h0ω hD ht0 htω
        hdim hscalar hdelta0 heps0 heps1 hepsilon hricT hpinchT
        hCinit hw_cont
    simpa [pinchQuotient] using hbound t ⟨ht0, le_rfl⟩ x
  · have ht_le0 : t <= 0 := not_lt.mp htpos
    have ht_eq : t = 0 := le_antisymm ht_le0 ht0
    subst t
    simpa [pinchQuotient] using hCinit x



omit [Module.Finite ℝ E] in
theorem pinchEstimate_display_sol
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E
      (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E
      (TangentSpace I : M -> Type _) I]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {omega : Real} (h0ω : 0 < omega)
    (hD : D = DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hscalar : ∀ t : Real, t ∈ D.carrier -> ∀ x : M, 0 < S.scalar t x)
    (hpinch :
      ∃ delta : Real,
        0 < delta ∧ delta < (1 : Real) / 3 ∧
          ∀ T : Real, 0 ≤ T -> T < omega ->
            PinchPres (I := I) (M := M)
              (fun t : Real => S.base.metric t)
              (DifferentialGeometry.Integral.Connection.twoTensorSecToFamily (I := I) (M := M) S.ricci)
              S.scalar T delta)
    (hric :
      ∀ T : Real, 0 ≤ T -> T < omega ->
        DifferentialGeometry.Integral.Connection.TwoTensorFamilyNonnegativeOn (I := I) (M := M)
          (DifferentialGeometry.Integral.Connection.twoTensorSecToFamily (I := I) (M := M) S.ricci)
          (Set.Icc 0 T)) :
    ∃ tracefreeRicciNormSq scalar weight : Real -> M -> Real, ∃ C : Real,
      PinchEstimateOn (M := M) tracefreeRicciNormSq scalar weight C Set.univ := by
  classical
  rcases pinchEstimate_sol (I := I) (M := M) S hS h0ω hD hdim hscalar
      hpinch hric with
    ⟨epsilon, C, _heps0, _heps1, _hC, hest⟩
  refine ⟨
    carrierZeroExt (M := M) D (tfRicNormSq S.scalar (ricciNorm (I := I) S)),
    carrierScalarExt (M := M) D S.scalar,
    carrierWeightExt (M := M) D S.scalar epsilon,
    C, ?_⟩
  intro t _ht x
  by_cases htD : t ∈ D.carrier
  · simpa [carrierZeroExt, carrierScalarExt, carrierWeightExt, htD] using
      hest t htD x
  · simp [carrierZeroExt, carrierScalarExt, carrierWeightExt, htD]

end DifferentialGeometry.PDE.RicciFlow
