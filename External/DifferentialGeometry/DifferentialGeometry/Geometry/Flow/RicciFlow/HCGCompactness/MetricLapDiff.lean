import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBoundsFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivContinuity
import DifferentialGeometry.Geometry.Connection.ChartBridge.HessFrobenius
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.ConnectionDifferenceNorm

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [CompactSpace M] [NeZero (Module.finrank Real E)]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [NeZero (Module.finrank ℝ E)] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem mtf_eq_mt0S
    (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.metricTensorField (I := I) g x =
      metricTensor0S (I := I) g x := by
  ext v
  rw [Tensor0SBundle.metricTensorField_apply, metricTensor0S_apply]

omit [I.Boundaryless] [CompactSpace M] [NeZero (Module.finrank ℝ E)] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
private theorem diffZero_eq
    (h g gRef : SmoothRiemannianMetric I M) (x : M) :
    metricDiffCovDerivAt (I := I) 0 h g gRef x =
      metricTensor0S (I := I) h x - metricTensor0S (I := I) g x := by
  unfold metricDiffCovDerivAt
  change Tensor0SBundle.metricTensorField (I := I) h x -
      Tensor0SBundle.metricTensorField (I := I) g x = _
  rw [mtf_eq_mt0S, mtf_eq_mt0S]

omit [I.Boundaryless] [CompactSpace M] [NeZero (Module.finrank ℝ E)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
private theorem covSelfOneAt
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricCovDeriv (I := I) g g 1 x = 0 := by
  apply ContinuousMultilinearMap.ext
  intro slots
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at_gen
    (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x (slots 0)
  have hcons : Fin.cons (X x) (Fin.tail slots) = slots := by
    rw [hX]
    exact Fin.cons_self_tail slots
  have hstep := metricCovDeriv_one_apply_section
    (I := I) g g X x (Fin.tail slots)
  have hzero :
      Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2
        (leviCivitaConnectionOfMetric (I := I) g) X
        (metricCovDeriv (I := I) g g 0) x = 0 := by
    have hbase : metricCovDeriv (I := I) g g 0 =
        Tensor0SBundle.metricTensorField (I := I) g := rfl
    rw [hbase]
    exact Tensor0SBundle.nabla_metric_zero (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) g
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g) X x
  calc
    metricCovDeriv (I := I) g g 1 x slots =
        metricCovDeriv (I := I) g g 1 x
          (Fin.cons (X x) (Fin.tail slots)) := by rw [hcons]
    _ = Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2
          (leviCivitaConnectionOfMetric (I := I) g) X
          (metricCovDeriv (I := I) g g 0) x (Fin.tail slots) := hstep
    _ = 0 := by rw [hzero]; rfl
    _ = (0 : Tensor0SBundle.Tensor0SSpace 3 I x) slots := rfl

omit [I.Boundaryless] [CompactSpace M] [NeZero (Module.finrank ℝ E)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
private theorem covOne_eq_deriv
    (h g : SmoothRiemannianMetric I M) (x : M) :
    metricCovDerivNorm (I := I) 1 h g x =
      metricDerivNorm (I := I) 1 h g g x := by
  unfold metricCovDerivNorm metricDerivNorm metricDiffCovDerivAt
  rw [covSelfOneAt (I := I) g x]
  exact (congrArg
    (fun A : Tensor0SBundle.Tensor0SSpace (1 + 2) I x =>
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (1 + 2) A))
    (sub_zero (metricCovDeriv (I := I) h g 1 x))).symm

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [NeZero (Module.finrank ℝ E)] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem normSq0S_nonneg'
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A : Tensor0SBundle.Tensor0SSpace s I x) :
    0 <= Tensor0SBundle.normSq0S (I := I) g x s A := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) g x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j
    constructor <;> simp [Tensor0SBundle.identityInvMetric,
      Tensor0SBundle.diagonalInvMetric, hON]
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq
    (I := I) g x s basis hinv A]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [NeZero (Module.finrank ℝ E)] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem normSqRS_nonneg'
    (g : SmoothRiemannianMetric I M) (x : M) (r s : Nat)
    (A : Tensor0SBundle.TensorRSSpace r s I x) :
    0 <= Tensor0SBundle.normSqRS (I := I) (g := g) (x := x) r s A := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) g x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j
    constructor <;> simp [Tensor0SBundle.identityInvMetric,
      Tensor0SBundle.diagonalInvMetric, hON]
  rw [Tensor0SBundle.normSqRS_identity_eq_componentL2SqRS
    (I := I) g x r s basis hinv A]
  unfold Tensor0SBundle.componentL2SqRS
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [NeZero (Module.finrank ℝ E)] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem trace_sq_le
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SBundle.Tensor0SSpace 2 I x) :
    (metricTracePair0SAt (I := I) g A) ^ 2 <=
      (Module.finrank Real (TangentSpace I x) : Real) *
        Tensor0SBundle.normSq0S (I := I) g x 2 A := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) g x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j
    constructor <;> simp [Tensor0SBundle.identityInvMetric,
      Tensor0SBundle.diagonalInvMetric, hON]
  simpa using metricTracePair0SAt_sq_le_card_mul_normSq0S
    (I := I) g basis
    (Tensor0SBundle.identityInvMetric
      (Idx := Fin (Module.finrank Real (TangentSpace I x))))
    hinv A




omit [I.Boundaryless] [CompactSpace M] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lcDiff_norm_le
    {K : Set M} (g h : SmoothRiemannianMetric I M) {C : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K g h C)
    {x : M} (hx : x ∈ K) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (leviCivitaConnectionOfMetric (I := I) h)
            (leviCivitaConnectionOfMetric (I := I) g) x)) <=
      (3 / 2 : Real) *
        (Real.sqrt (C ^ 3) *
          metricDerivNorm (I := I) 1 h g g x) := by
  classical
  obtain ⟨_, basis, hhinv, _, _, _⟩ :=
    exists_diagInv_of_metricUniformEquivalentOn
      (I := I) (metricUniformEquivalentOn_symm (I := I) hEq) hx
  have hdiff := diff_le_covOne_basis_ref_lc
    (I := I) h g hx C hEq basis hhinv
  simpa only [covOne_eq_deriv] using hdiff

omit [NeZero (Module.finrank ℝ E)] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
private theorem delta_eq_lap
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f) (x : M) :
    Δ_g (I := I) g hf x =
      laplacian (I := I) (leviCivitaConnectionOfMetric (I := I) g) g f x := by
  exact (laplacian_levi_eq (E := E) (H := H) (I := I) (M := M)
    (g := g) (f := f) hf x).symm

omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem lapDiff_sq_core
    (g h : SmoothRiemannianMetric I M)
    {f : M -> Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (x : M) (rho : Real) (hrho : 0 <= rho)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ g h 2)
    (hzero :
      Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) g x 2
          (metricTensor0S (I := I) h x - metricTensor0S (I := I) g x)) <= rho)
    (hone : metricDerivNorm (I := I) 1 h g g x <= rho) :
    (Δ_g (I := I) h hf x - Δ_g (I := I) g hf x) ^ 2 <=
      8 * (Module.finrank Real E : Real) ^ 2 * rho ^ 2 *
          Tensor0SBundle.normSq0S (I := I) g x 2
            (leviHessSec (I := I) g f hf x) +
        72 * (Module.finrank Real E : Real) * rho ^ 2 *
          Tensor0SBundle.normSq0S (I := I) g x 1
            (duSec (I := I) f hf x) := by
  classical
  let covH := leviCivitaConnectionOfMetric (I := I) h
  let covG := leviCivitaConnectionOfMetric (I := I) g
  let Hess := leviHessSec (I := I) g f hf x
  let du := duSec (I := I) f hf x
  let D := Tensor0SBundle.connectionDifferenceTensorAt (I := I) covH covG x
  let B := Tensor0SBundle.connectionDifferenceOutput (I := I)
    (CovariantDerivative.difference covH covG x) du
  let a := metricTracePair0SAt (I := I) h Hess -
    metricTracePair0SAt (I := I) g Hess
  let b := metricTracePair0SAt (I := I) h B
  have hEqx := hEq.2 x (Set.mem_univ x)
  have ha0 :
      |a| <= (Module.finrank Real (TangentSpace I x) : Real) * 2 *
        Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) g x 2
            (metricTensor0S (I := I) h x - metricTensor0S (I := I) g x)) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 Hess) := by
    simpa only [a] using
      trace_sub_le_c0 (I := I) g h x (C := (2 : Real)) (by norm_num) hEqx Hess
  have ha :
      |a| <= 2 * (Module.finrank Real E : Real) * rho *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 Hess) := by
    calc
      |a| <= (Module.finrank Real (TangentSpace I x) : Real) * 2 *
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) g x 2
              (metricTensor0S (I := I) h x - metricTensor0S (I := I) g x)) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 Hess) := ha0
      _ <= (Module.finrank Real (TangentSpace I x) : Real) * 2 * rho *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 Hess) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hzero (by positivity))
          (Real.sqrt_nonneg _)
      _ = 2 * (Module.finrank Real E : Real) * rho *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 Hess) := by
        have hfr : Module.finrank Real (TangentSpace I x) =
            Module.finrank Real E := rfl
        rw [hfr]
        ring
  have hHess0 : 0 <= Tensor0SBundle.normSq0S (I := I) g x 2 Hess :=
    normSq0S_nonneg' (I := I) g x 2 Hess
  have ha_sq :
      a ^ 2 <= 4 * (Module.finrank Real E : Real) ^ 2 * rho ^ 2 *
        Tensor0SBundle.normSq0S (I := I) g x 2 Hess := by
    have hR : 0 <= 2 * (Module.finrank Real E : Real) * rho *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 Hess) := by
      positivity
    have hsquare := (sq_le_sq₀ (abs_nonneg a) hR).2 ha
    calc
      a ^ 2 = |a| ^ 2 := by rw [sq_abs]
      _ <= (2 * (Module.finrank Real E : Real) * rho *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 Hess)) ^ 2 := hsquare
      _ = 4 * (Module.finrank Real E : Real) ^ 2 * rho ^ 2 *
          Tensor0SBundle.normSq0S (I := I) g x 2 Hess := by
        calc
          (2 * (Module.finrank Real E : Real) * rho *
              Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 Hess)) ^ 2 =
            4 * (Module.finrank Real E : Real) ^ 2 * rho ^ 2 *
              (Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 Hess)) ^ 2 := by ring
          _ = 4 * (Module.finrank Real E : Real) ^ 2 * rho ^ 2 *
              Tensor0SBundle.normSq0S (I := I) g x 2 Hess := by
            rw [Real.sq_sqrt hHess0]
  have hconn0 :
      Real.sqrt (Tensor0SBundle.normSqRS
        (I := I) (g := h) (x := x) 1 2 D) <=
        (3 / 2 : Real) * (Real.sqrt ((2 : Real) ^ 3) *
          metricDerivNorm (I := I) 1 h g g x) := by
    simpa only [D, covH, covG] using
      lcDiff_norm_le (I := I) (K := Set.univ) g h hEq
        (x := x) (Set.mem_univ x)
  have hconn :
      Real.sqrt (Tensor0SBundle.normSqRS
        (I := I) (g := h) (x := x) 1 2 D) <=
        (3 / 2 : Real) * (Real.sqrt ((2 : Real) ^ 3) * rho) :=
    hconn0.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hone (Real.sqrt_nonneg _)) (by norm_num))
  have hD0 : 0 <= Tensor0SBundle.normSqRS
      (I := I) (g := h) (x := x) 1 2 D :=
    normSqRS_nonneg' (I := I) h x 1 2 D
  have hconn_sq :
      Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2 D <=
        18 * rho ^ 2 := by
    have hR : 0 <= (3 / 2 : Real) *
        (Real.sqrt ((2 : Real) ^ 3) * rho) := by positivity
    have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) hR).2 hconn
    calc
      Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2 D =
          (Real.sqrt (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) 1 2 D)) ^ 2 := by
        rw [Real.sq_sqrt hD0]
      _ <= ((3 / 2 : Real) *
          (Real.sqrt ((2 : Real) ^ 3) * rho)) ^ 2 := hsquare
      _ = 18 * rho ^ 2 := by
        have hsqrt : (Real.sqrt ((2 : Real) ^ 3)) ^ 2 = 8 := by norm_num
        rw [mul_pow, mul_pow, hsqrt]
        ring
  have hdu0 : 0 <= Tensor0SBundle.normSq0S (I := I) h x 1 du :=
    normSq0S_nonneg' (I := I) h x 1 du
  have hdug0 : 0 <= Tensor0SBundle.normSq0S (I := I) g x 1 du :=
    normSq0S_nonneg' (I := I) g x 1 du
  have hdu : Tensor0SBundle.normSq0S (I := I) h x 1 du <=
      2 * Tensor0SBundle.normSq0S (I := I) g x 1 du := by
    simpa using Tensor0SBundle.normSq0S_upper_le_of_equiv
      (I := I) g h x 1 (C := (2 : Real)) (by norm_num) hEqx du
  have hB0 : 0 <= Tensor0SBundle.normSq0S (I := I) h x 2 B :=
    normSq0S_nonneg' (I := I) h x 2 B
  have hout0 :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 2 B) <=
        Real.sqrt (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) 1 2 D) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 1 du) := by
    simpa only [B, D, covH, covG] using
      Tensor0SBundle.connOut_norm_le (I := I) h covH covG du
  have hout : Tensor0SBundle.normSq0S (I := I) h x 2 B <=
      Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2 D *
        Tensor0SBundle.normSq0S (I := I) h x 1 du := by
    have hR : 0 <= Real.sqrt (Tensor0SBundle.normSqRS
        (I := I) (g := h) (x := x) 1 2 D) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 1 du) := by positivity
    have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) hR).2 hout0
    calc
      Tensor0SBundle.normSq0S (I := I) h x 2 B =
          (Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 2 B)) ^ 2 := by
        rw [Real.sq_sqrt hB0]
      _ <= (Real.sqrt (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) 1 2 D) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 1 du)) ^ 2 := hsquare
      _ = Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) 1 2 D *
            Tensor0SBundle.normSq0S (I := I) h x 1 du := by
        rw [mul_pow, Real.sq_sqrt hD0, Real.sq_sqrt hdu0]
  have hout' : Tensor0SBundle.normSq0S (I := I) h x 2 B <=
      36 * rho ^ 2 * Tensor0SBundle.normSq0S (I := I) g x 1 du := by
    calc
      Tensor0SBundle.normSq0S (I := I) h x 2 B <=
          Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2 D *
            Tensor0SBundle.normSq0S (I := I) h x 1 du := hout
      _ <= (18 * rho ^ 2) *
          Tensor0SBundle.normSq0S (I := I) h x 1 du :=
        mul_le_mul_of_nonneg_right hconn_sq hdu0
      _ <= (18 * rho ^ 2) *
          (2 * Tensor0SBundle.normSq0S (I := I) g x 1 du) :=
        mul_le_mul_of_nonneg_left hdu (by positivity)
      _ = 36 * rho ^ 2 *
          Tensor0SBundle.normSq0S (I := I) g x 1 du := by ring
  have hb_sq : b ^ 2 <= 36 * (Module.finrank Real E : Real) * rho ^ 2 *
      Tensor0SBundle.normSq0S (I := I) g x 1 du := by
    calc
      b ^ 2 <= (Module.finrank Real (TangentSpace I x) : Real) *
          Tensor0SBundle.normSq0S (I := I) h x 2 B := by
        simpa only [b] using trace_sq_le (I := I) h x B
      _ <= (Module.finrank Real (TangentSpace I x) : Real) *
          (36 * rho ^ 2 *
            Tensor0SBundle.normSq0S (I := I) g x 1 du) :=
        mul_le_mul_of_nonneg_left hout' (by positivity)
      _ = 36 * (Module.finrank Real E : Real) * rho ^ 2 *
          Tensor0SBundle.normSq0S (I := I) g x 1 du := by
        have hfr : Module.finrank Real (TangentSpace I x) =
            Module.finrank Real E := rfl
        rw [hfr]
        ring
  have hlap0 := lap_sub_conn (I := I) covH covG
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) h)
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g)
    h g
    (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) h)
    (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
    f hf x
  have hlap : Δ_g (I := I) h hf x - Δ_g (I := I) g hf x = a - b := by
    have hh := delta_eq_lap (I := I) h hf x
    have hg := delta_eq_lap (I := I) g hf x
    rw [hh, hg]
    simpa only [a, b, Hess, B, du, covH, covG, leviHessSec, LeviCivita] using hlap0
  rw [hlap]
  have hsub : (a - b) ^ 2 <= 2 * a ^ 2 + 2 * b ^ 2 := by
    nlinarith [sq_nonneg (a + b)]
  calc
    (a - b) ^ 2 <= 2 * a ^ 2 + 2 * b ^ 2 := hsub
    _ <= 2 * (4 * (Module.finrank Real E : Real) ^ 2 * rho ^ 2 *
          Tensor0SBundle.normSq0S (I := I) g x 2 Hess) +
        2 * (36 * (Module.finrank Real E : Real) * rho ^ 2 *
          Tensor0SBundle.normSq0S (I := I) g x 1 du) :=
      add_le_add
        (mul_le_mul_of_nonneg_left ha_sq (by norm_num))
        (mul_le_mul_of_nonneg_left hb_sq (by norm_num))
    _ = 8 * (Module.finrank Real E : Real) ^ 2 * rho ^ 2 *
          Tensor0SBundle.normSq0S (I := I) g x 2
            (leviHessSec (I := I) g f hf x) +
        72 * (Module.finrank Real E : Real) * rho ^ 2 *
          Tensor0SBundle.normSq0S (I := I) g x 1
            (duSec (I := I) f hf x) := by
      simp only [Hess, du]
      ring





omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lapDiff_sq_le
    (g h : SmoothRiemannianMetric I M)
    {f : M -> Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (x : M)
    (hsmall :
      (Module.finrank Real E : Real) *
        metricDerivNormSupOn (I := I) Set.univ 1 h g g <= (1 / 2 : Real)) :
    (Δ_g (I := I) h hf x - Δ_g (I := I) g hf x) ^ 2 <=
      8 * (Module.finrank Real E : Real) ^ 2 *
          (metricDerivNormSupOn (I := I) Set.univ 1 h g g) ^ 2 *
          Tensor0SBundle.normSq0S (I := I) g x 2
            (leviHessSec (I := I) g f hf x) +
        72 * (Module.finrank Real E : Real) *
          (metricDerivNormSupOn (I := I) Set.univ 1 h g g) ^ 2 *
          Tensor0SBundle.normSq0S (I := I) g x 1
            (duSec (I := I) f hf x) := by
  let rho := metricDerivNormSupOn (I := I) Set.univ 1 h g g
  have hzero0 : metricDerivNorm (I := I) 0 h g g x <= rho :=
    derivNorm_le_sup (I := I) (K := Set.univ) isCompact_univ
      (a := 0) (p := 1) (by omega) h g g (Set.mem_univ x)
  have hrho : 0 <= rho :=
    (Real.sqrt_nonneg _).trans hzero0
  have hpoint : forall y : M, y ∈ (Set.univ : Set M) ->
      (Module.finrank Real (TangentSpace I y) : Real) *
        metricDerivNorm (I := I) 0 h g g y <= (1 / 2 : Real) := by
    intro y _
    have hy : metricDerivNorm (I := I) 0 h g g y <= rho :=
      derivNorm_le_sup (I := I) (K := Set.univ) isCompact_univ
        (a := 0) (p := 1) (by omega) h g g (Set.mem_univ y)
    have hfr : Module.finrank Real (TangentSpace I y) =
        Module.finrank Real E := rfl
    calc
      (Module.finrank Real (TangentSpace I y) : Real) *
          metricDerivNorm (I := I) 0 h g g y =
        (Module.finrank Real E : Real) *
          metricDerivNorm (I := I) 0 h g g y := by rw [hfr]
      _ <= (Module.finrank Real E : Real) * rho :=
        mul_le_mul_of_nonneg_left hy (by positivity)
      _ <= (1 / 2 : Real) := by simpa only [rho] using hsmall
  have hEq0 := metricUniformEquivalentOn_of_metricDerivNorm
    (I := I) (K := Set.univ) h g
    (δ := (1 / 2 : Real)) (by norm_num) (by norm_num) hpoint
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ g h 2 := by
    simpa only [show (1 - (1 / 2 : Real))⁻¹ = 2 by norm_num] using hEq0
  have hzero :
      Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) g x 2
          (metricTensor0S (I := I) h x - metricTensor0S (I := I) g x)) <= rho := by
    simpa only [metricDerivNorm, diffZero_eq] using hzero0
  have hone : metricDerivNorm (I := I) 1 h g g x <= rho :=
    derivNorm_le_sup (I := I) (K := Set.univ) isCompact_univ
      (a := 1) (p := 1) le_rfl h g g (Set.mem_univ x)
  simpa only [rho] using
    lapDiff_sq_core (I := I) g h hf x rho hrho hEq hzero hone

end HCGCompactness
end DifferentialGeometry

end
