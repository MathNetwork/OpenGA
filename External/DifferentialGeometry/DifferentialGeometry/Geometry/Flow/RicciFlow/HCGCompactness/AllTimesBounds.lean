import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.BoundedGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedConvergence
import DifferentialGeometry.Geometry.Connection.LeviCivita.Variation.Connection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Christoffel
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivFrame

set_option autoImplicit false
set_option linter.style.longLine false














noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology

section ScalarLogDerivative



theorem exp_bounds_of_abs_log_sub_le
    {fa fb R : Real}
    (hfa : 0 < fa) (hfb : 0 < fb)
    (hlog : |Real.log fb - Real.log fa| <= R) :
    Real.exp (-R) * fa <= fb /\ fb <= Real.exp R * fa := by
  have hlow : -R <= Real.log fb - Real.log fa := (abs_le.mp hlog).1
  have hhigh : Real.log fb - Real.log fa <= R := (abs_le.mp hlog).2
  have hratio_pos : 0 < fb / fa := div_pos hfb hfa
  constructor
  · have hlog_ratio : -R <= Real.log (fb / fa) := by
      simpa [Real.log_div hfb.ne' hfa.ne'] using hlow
    have hratio_lower : Real.exp (-R) <= fb / fa :=
      (Real.le_log_iff_exp_le hratio_pos).mp hlog_ratio
    calc
      Real.exp (-R) * fa <= (fb / fa) * fa :=
        mul_le_mul_of_nonneg_right hratio_lower (le_of_lt hfa)
      _ = fb := by
        field_simp [hfa.ne']
  · have hlog_ratio : Real.log (fb / fa) <= R := by
      simpa [Real.log_div hfb.ne' hfa.ne'] using hhigh
    have hratio_upper : fb / fa <= Real.exp R :=
      (Real.log_le_iff_le_exp hratio_pos).mp hlog_ratio
    calc
      fb = (fb / fa) * fa := by
        field_simp [hfa.ne']
      _ <= Real.exp R * fa :=
        mul_le_mul_of_nonneg_right hratio_upper (le_of_lt hfa)





theorem exp_bounds_of_log_deriv_bound
    (f f' : Real -> Real) {a b Lambda : Real}
    (hf_pos : forall s : Real, s ∈ Set.uIcc a b -> 0 < f s)
    (hf_deriv :
      forall s : Real, s ∈ Set.uIcc a b -> HasDerivAt f (f' s) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b -> |f' s / f s| <= Lambda) :
    Real.exp (-Lambda * |b - a|) * f a <= f b /\
      f b <= Real.exp (Lambda * |b - a|) * f a := by
  have hlog_deriv :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivWithinAt (fun y : Real => Real.log (f y)) (f' s / f s)
          (Set.uIcc a b) s := by
    intro s hs
    exact ((hf_deriv s hs).log (ne_of_gt (hf_pos s hs))).hasDerivWithinAt
  have hnorm_bound :
      forall s : Real, s ∈ Set.uIcc a b -> ‖f' s / f s‖ <= Lambda := by
    intro s hs
    simpa only [Real.norm_eq_abs] using hbound s hs
  have hdist :=
    (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      hlog_deriv hnorm_bound Set.left_mem_uIcc Set.right_mem_uIcc
  have hlog :
      |Real.log (f b) - Real.log (f a)| <= Lambda * |b - a| := by
    simpa [Real.norm_eq_abs] using hdist
  simpa [neg_mul] using
    exp_bounds_of_abs_log_sub_le (hf_pos a Set.left_mem_uIcc)
      (hf_pos b Set.right_mem_uIcc) hlog










theorem affineGronwall_of_abs_deriv_le
    (U U' : Real -> Real) {t0 t alpha beta : Real}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hU_nonneg : forall s : Real, s ∈ Set.uIcc t0 t -> 0 <= U s)
    (hU_deriv :
      forall s : Real, s ∈ Set.uIcc t0 t -> HasDerivAt U (U' s) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc t0 t -> |U' s| <= alpha * U s + beta) :
    U t <= Real.exp (alpha * |t - t0|) * (U t0 + beta / alpha) := by
  have ha0 : alpha ≠ 0 := ne_of_gt halpha
  have hbpos : 0 < beta / alpha := div_pos hbeta halpha
  have hcancel : alpha * (beta / alpha) = beta := by field_simp
  set W : Real -> Real := fun s => U s + beta / alpha with hW
  have hW_pos : forall s : Real, s ∈ Set.uIcc t0 t -> 0 < W s := by
    intro s hs
    have h1 := hU_nonneg s hs
    have h2 : (0 : Real) < U s + beta / alpha := by linarith
    simpa [hW] using h2
  have hW_deriv :
      forall s : Real, s ∈ Set.uIcc t0 t -> HasDerivAt W (U' s) s := by
    intro s hs
    simpa [hW] using (hU_deriv s hs).add_const (beta / alpha)
  have hW_bound :
      forall s : Real, s ∈ Set.uIcc t0 t -> |U' s / W s| <= alpha := by
    intro s hs
    have hWs : 0 < W s := hW_pos s hs
    rw [abs_div, abs_of_pos hWs, div_le_iff₀ hWs]
    calc |U' s| <= alpha * U s + beta := hbound s hs
      _ = alpha * (U s + beta / alpha) := by rw [mul_add, hcancel]
      _ = alpha * W s := by rw [hW]
  have hmain :=
    (exp_bounds_of_log_deriv_bound W U' hW_pos hW_deriv hW_bound).2
  simp only [hW] at hmain
  linarith [hbpos]

open scoped RealInnerProductSpace in










theorem hasDerivAt_normSq_abs_deriv_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    {c : Real -> F} {c' : F} {t : Real}
    (hc : HasDerivAt c c' t) :
    exists d : Real,
      HasDerivAt (fun s : Real => ‖c s‖ ^ 2) d t ∧
        |d| <= ‖c t‖ ^ 2 + ‖c'‖ ^ 2 := by
  have hbnd : |2 * ⟪c t, c'⟫| <= ‖c t‖ ^ 2 + ‖c'‖ ^ 2 := by
    have hCS : |⟪c t, c'⟫| <= ‖c t‖ * ‖c'‖ := abs_real_inner_le_norm (c t) c'
    have hyoung : 2 * ‖c t‖ * ‖c'‖ <= ‖c t‖ ^ 2 + ‖c'‖ ^ 2 :=
      two_mul_le_add_sq _ _
    calc |2 * ⟪c t, c'⟫|
        = 2 * |⟪c t, c'⟫| := by rw [abs_mul, abs_two]
      _ <= 2 * (‖c t‖ * ‖c'‖) :=
            mul_le_mul_of_nonneg_left hCS (by norm_num)
      _ = 2 * ‖c t‖ * ‖c'‖ := by ring
      _ <= ‖c t‖ ^ 2 + ‖c'‖ ^ 2 := hyoung
  exact ⟨_, hc.norm_sq, hbnd⟩




theorem norm_le_initial_add_deriv_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (f f' : Real -> F) {a b L : Real}
    (hf_deriv :
      forall s : Real, s ∈ Set.uIcc a b -> HasDerivAt f (f' s) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b -> ‖f' s‖ <= L) :
    ‖f b‖ <= L * |b - a| + ‖f a‖ := by
  have hderivWithin :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivWithinAt f (f' s) (Set.uIcc a b) s := by
    intro s hs
    exact (hf_deriv s hs).hasDerivWithinAt
  have hdist :=
    (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderivWithin hbound Set.left_mem_uIcc Set.right_mem_uIcc
  have hsub : ‖f b - f a‖ <= L * |b - a| := by
    simpa [Real.norm_eq_abs] using hdist
  calc
    ‖f b‖ = ‖(f b - f a) + f a‖ := by rw [sub_add_cancel]
    _ <= ‖f b - f a‖ + ‖f a‖ := norm_add_le _ _
    _ <= L * |b - a| + ‖f a‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hsub ‖f a‖






theorem norm_le_initial_add_derivWithin_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (f f' : Real -> F) {a b L : Real}
    (hf_deriv :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivWithinAt f (f' s) (Set.uIcc a b) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b -> ‖f' s‖ <= L) :
    ‖f b‖ <= L * |b - a| + ‖f a‖ := by
  have hdist :=
    (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      hf_deriv hbound Set.left_mem_uIcc Set.right_mem_uIcc
  have hsub : ‖f b - f a‖ <= L * |b - a| := by
    simpa [Real.norm_eq_abs] using hdist
  calc
    ‖f b‖ = ‖(f b - f a) + f a‖ := by rw [sub_add_cancel]
    _ <= ‖f b - f a‖ + ‖f a‖ := norm_add_le _ _
    _ <= L * |b - a| + ‖f a‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hsub ‖f a‖

end ScalarLogDerivative

section ComponentL2

variable {Idx : Type*} [Fintype Idx]






noncomputable def componentVec3
    (A : Idx -> Idx -> Idx -> Real) :
    EuclideanSpace Real (Idx × Idx × Idx) :=
  WithLp.toLp 2 (fun p : Idx × Idx × Idx => A p.1 p.2.1 p.2.2)

omit [Fintype Idx] in
@[simp]
theorem componentVec3_apply
    (A : Idx -> Idx -> Idx -> Real)
    (p : Idx × Idx × Idx) :
    componentVec3 A p = A p.1 p.2.1 p.2.2 := by
  simp [componentVec3, PiLp.toLp_apply]



theorem norm_componentVec3
    (A : Idx -> Idx -> Idx -> Real) :
    ‖componentVec3 A‖ = Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 A) := by
  rw [EuclideanSpace.norm_eq]
  simp [componentVec3, DifferentialGeometry.Integral.Connection.componentL2Sq3, Real.norm_eq_abs, sq_abs]



theorem hasDerivAt_componentVec3
    (A A' : Real -> Idx -> Idx -> Idx -> Real) {t : Real}
    (hderiv :
      forall p : Idx × Idx × Idx,
        HasDerivAt (fun s : Real => A s p.1 p.2.1 p.2.2)
          (A' t p.1 p.2.1 p.2.2) t) :
    HasDerivAt (fun s : Real => componentVec3 (A s))
      (componentVec3 (A' t)) t := by
  classical
  let L :
      (((Idx × Idx × Idx) → Real) →L[Real]
        EuclideanSpace Real (Idx × Idx × Idx)) :=
    (PiLp.continuousLinearEquiv 2 Real
      (fun _ : Idx × Idx × Idx => Real)).symm.toContinuousLinearMap
  have hpi :
      HasDerivAt
        (fun s : Real => fun p : Idx × Idx × Idx => A s p.1 p.2.1 p.2.2)
        (fun p : Idx × Idx × Idx => A' t p.1 p.2.1 p.2.2) t := by
    rw [hasDerivAt_pi]
    intro p
    exact hderiv p
  have hL :
      HasDerivAt
        (fun s : Real =>
          L (fun p : Idx × Idx × Idx => A s p.1 p.2.1 p.2.2))
        (L (fun p : Idx × Idx × Idx => A' t p.1 p.2.1 p.2.2)) t := by
    have hconst :
        HasDerivAt (fun _s : Real => L)
          (0 : ((Idx × Idx × Idx) → Real) →L[Real]
            EuclideanSpace Real (Idx × Idx × Idx)) t := by
      simpa using hasDerivAt_const (x := t) (c := L)
    simpa using hconst.clm_apply hpi
  simpa [componentVec3, L, PiLp.coe_symm_continuousLinearEquiv] using hL


theorem hasDerivWithinAt_componentVec3
    (A A' : Real -> Idx -> Idx -> Idx -> Real) {s : Set Real} {t : Real}
    (hderiv :
      forall p : Idx × Idx × Idx,
        HasDerivWithinAt (fun r : Real => A r p.1 p.2.1 p.2.2)
          (A' t p.1 p.2.1 p.2.2) s t) :
    HasDerivWithinAt (fun r : Real => componentVec3 (A r))
      (componentVec3 (A' t)) s t := by
  classical
  let L :
      (((Idx × Idx × Idx) -> Real) →L[Real]
        EuclideanSpace Real (Idx × Idx × Idx)) :=
    (PiLp.continuousLinearEquiv 2 Real
      (fun _ : Idx × Idx × Idx => Real)).symm.toContinuousLinearMap
  have hpi :
      HasDerivWithinAt
        (fun r : Real => fun p : Idx × Idx × Idx => A r p.1 p.2.1 p.2.2)
        (fun p : Idx × Idx × Idx => A' t p.1 p.2.1 p.2.2) s t := by
    rw [hasDerivWithinAt_pi]
    intro p
    exact hderiv p
  have hL :
      HasDerivWithinAt
        (fun r : Real =>
          L (fun p : Idx × Idx × Idx => A r p.1 p.2.1 p.2.2))
        (L (fun p : Idx × Idx × Idx => A' t p.1 p.2.1 p.2.2)) s t := by
    have hconst :
        HasDerivWithinAt (fun _r : Real => L)
          (0 : ((Idx × Idx × Idx) -> Real) →L[Real]
            EuclideanSpace Real (Idx × Idx × Idx)) s t := by
      simpa using (hasDerivAt_const (x := t) (c := L)).hasDerivWithinAt
    simpa using hconst.clm_apply hpi
  simpa [componentVec3, L, PiLp.coe_symm_continuousLinearEquiv] using hL







theorem componentL2_le_initial_add
    (A A' : Real -> Idx -> Idx -> Idx -> Real) {a b L : Real}
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivAt (fun r : Real => A r p.1 p.2.1 p.2.2)
            (A' s p.1 p.2.1 p.2.2) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (A' s)) <= L) :
    Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (A b)) <=
      L * |b - a| + Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (A a)) := by
  have hvecDeriv :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivAt (fun r : Real => componentVec3 (A r))
          (componentVec3 (A' s)) s := by
    intro s hs
    exact hasDerivAt_componentVec3 (A := A) (A' := A') (t := s)
      (hderiv s hs)
  have hvecBound :
      forall s : Real, s ∈ Set.uIcc a b ->
        ‖componentVec3 (A' s)‖ <= L := by
    intro s hs
    simpa [norm_componentVec3] using hbound s hs
  have h :=
    norm_le_initial_add_deriv_bound
      (fun s : Real => componentVec3 (A s))
      (fun s : Real => componentVec3 (A' s))
      (a := a) (b := b) (L := L) hvecDeriv hvecBound
  simpa [norm_componentVec3] using h



theorem componentL2_le_initial_add_within
    (A A' : Real -> Idx -> Idx -> Idx -> Real) {a b L : Real}
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivWithinAt (fun r : Real => A r p.1 p.2.1 p.2.2)
            (A' s p.1 p.2.1 p.2.2) (Set.uIcc a b) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (A' s)) <= L) :
    Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (A b)) <=
      L * |b - a| + Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (A a)) := by
  have hvecDeriv :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivWithinAt (fun r : Real => componentVec3 (A r))
          (componentVec3 (A' s)) (Set.uIcc a b) s := by
    intro s hs
    exact hasDerivWithinAt_componentVec3 (A := A) (A' := A') (t := s)
      (s := Set.uIcc a b) (hderiv s hs)
  have hvecBound :
      forall s : Real, s ∈ Set.uIcc a b ->
        ‖componentVec3 (A' s)‖ <= L := by
    intro s hs
    simpa [norm_componentVec3] using hbound s hs
  have h :=
    norm_le_initial_add_derivWithin_bound
      (fun s : Real => componentVec3 (A s))
      (fun s : Real => componentVec3 (A' s))
      (a := a) (b := b) (L := L) hvecDeriv hvecBound
  simpa [norm_componentVec3] using h





theorem componentL2_le_initial_add_on_subset
    (A A' : Real -> Idx -> Idx -> Idx -> Real) {S : Set Real} {a b L : Real}
    (hsub : Set.uIcc a b ⊆ S)
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivWithinAt (fun r : Real => A r p.1 p.2.1 p.2.2)
            (A' s p.1 p.2.1 p.2.2) S s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (A' s)) <= L) :
    Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (A b)) <=
      L * |b - a| + Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (A a)) := by
  refine componentL2_le_initial_add_within
    (A := A) (A' := A') (a := a) (b := b) (L := L) ?_ hbound
  intro s hs p
  exact (hderiv s hs p).mono hsub








theorem gammaL2_le_initial_add
    (Gamma dGamma nablaRic : Real -> Idx -> Idx -> Idx -> Real)
    {a b R : Real}
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivAt
            (fun r : Real => Gamma r p.1 p.2.1 p.2.2)
            (dGamma s p.1 p.2.1 p.2.2) s)
    (hcombo :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall i j k : Idx,
          dGamma s i j k =
            -nablaRic s i j k - nablaRic s j i k + nablaRic s k i j)
    (hRic :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (nablaRic s)) <= R) :
    Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (Gamma b)) <=
      3 * R * |b - a| +
        Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (Gamma a)) := by
  refine componentL2_le_initial_add
    (A := Gamma) (A' := dGamma) (a := a) (b := b) (L := 3 * R)
    hderiv ?_
  intro s hs
  exact le_trans
    (DifferentialGeometry.Integral.Connection.gammaEvol_l2_le (Idx := Idx) (nablaRic s) (dGamma s)
      (hcombo s hs))
    (mul_le_mul_of_nonneg_left (hRic s hs) (by norm_num : (0 : Real) <= 3))


theorem gammaL2_le_initial_add_within
    (Gamma dGamma nablaRic : Real -> Idx -> Idx -> Idx -> Real)
    {a b R : Real}
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivWithinAt
            (fun r : Real => Gamma r p.1 p.2.1 p.2.2)
            (dGamma s p.1 p.2.1 p.2.2) (Set.uIcc a b) s)
    (hcombo :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall i j k : Idx,
          dGamma s i j k =
            -nablaRic s i j k - nablaRic s j i k + nablaRic s k i j)
    (hRic :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (nablaRic s)) <= R) :
    Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (Gamma b)) <=
      3 * R * |b - a| +
        Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (Gamma a)) := by
  refine componentL2_le_initial_add_within
    (A := Gamma) (A' := dGamma) (a := a) (b := b) (L := 3 * R)
    hderiv ?_
  intro s hs
  exact le_trans
    (DifferentialGeometry.Integral.Connection.gammaEvol_l2_le (Idx := Idx) (nablaRic s) (dGamma s)
      (hcombo s hs))
    (mul_le_mul_of_nonneg_left (hRic s hs) (by norm_num : (0 : Real) <= 3))


theorem gammaL2_le_initial_add_on_subset
    (Gamma dGamma nablaRic : Real -> Idx -> Idx -> Idx -> Real)
    {S : Set Real} {a b R : Real}
    (hsub : Set.uIcc a b ⊆ S)
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivWithinAt
            (fun r : Real => Gamma r p.1 p.2.1 p.2.2)
            (dGamma s p.1 p.2.1 p.2.2) S s)
    (hcombo :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall i j k : Idx,
          dGamma s i j k =
            -nablaRic s i j k - nablaRic s j i k + nablaRic s k i j)
    (hRic :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (nablaRic s)) <= R) :
    Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (Gamma b)) <=
      3 * R * |b - a| +
        Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (Gamma a)) := by
  refine componentL2_le_initial_add_on_subset
    (A := Gamma) (A' := dGamma) (S := S) (a := a) (b := b)
    (L := 3 * R) hsub hderiv ?_
  intro s hs
  exact le_trans
    (DifferentialGeometry.Integral.Connection.gammaEvol_l2_le (Idx := Idx) (nablaRic s) (dGamma s)
      (hcombo s hs))
    (mul_le_mul_of_nonneg_left (hRic s hs) (by norm_num : (0 : Real) <= 3))







theorem gammaL2_le_initial_add_regular
    (Gamma dGamma nablaRic : Real -> Idx -> Idx -> Idx -> Real)
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval} {a b R : Real}
    (hsub : Set.uIcc a b ⊆ D.carrier)
    (hregular : forall s : Real, s ∈ Set.uIcc a b -> s ∈ D.regular)
    (hderiv :
      forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        forall p : Idx × Idx × Idx,
          HasDerivWithinAt
            (fun r : Real => Gamma r p.1 p.2.1 p.2.2)
            (dGamma (t : Real) p.1 p.2.1 p.2.2) D.carrier (t : Real))
    (hcombo :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall i j k : Idx,
          dGamma s i j k =
            -nablaRic s i j k - nablaRic s j i k + nablaRic s k i j)
    (hRic :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (nablaRic s)) <= R) :
    Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (Gamma b)) <=
      3 * R * |b - a| +
        Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 (Gamma a)) := by
  refine gammaL2_le_initial_add_on_subset
    (Gamma := Gamma) (dGamma := dGamma) (nablaRic := nablaRic)
    (S := D.carrier) (a := a) (b := b) (R := R) hsub ?_ hcombo hRic
  intro s hs p
  simpa using hderiv ⟨s, hregular s hs⟩ p

end ComponentL2

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedDomain

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)




omit [CompleteSpace E] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] in
private theorem componentRS_eq_gen
    [IsManifold I 1 M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r s : Nat} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (T : Tensor0SBundle.TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    Tensor0SBundle.componentRS (I := I) basis T upper lower =
      Tensor0SBundle.componentRS_gen (I := I) basis T upper lower := rfl


def localFrameOneOfInf
    {Idx : Type*} {u : Set M}
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) :
    IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u where
  linearIndependent := hframe.linearIndependent
  generating := hframe.generating
  contMDiffOn := fun i =>
    (hframe.contMDiffOn i).of_le (by decide : (1 : WithTop ℕ∞) <= ∞)






def MetricUniformEquivalentOn
    (K : Set M)
    (gRef h : SmoothRiemannianMetric I M)
    (C : Real) : Prop :=
  1 <= C /\
    forall x : M, x ∈ K ->
      forall v : TangentSpace I x,
        C⁻¹ * gRef.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * gRef.inner x v v


def MetricUniformEquivalentOnWindow
    (K : Set M) (β ψ : Real)
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (B : Real -> Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    MetricUniformEquivalentOn (I := I) K gRef (gSeq i t) (B t)


omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem metricUniformEquivalentOn_of_le
    {K : Set M} {gRef h : SmoothRiemannianMetric I M} {C C' : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K gRef h C)
    (hCC' : C <= C') :
    MetricUniformEquivalentOn (I := I) K gRef h C' := by
  constructor
  · exact le_trans hEq.1 hCC'
  · intro x hx v
    have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hEq.1
    have hgin_nonneg : 0 <= gRef.inner x v v := by
      by_cases hv : v = 0
      · subst v
        simp
      · exact le_of_lt (gRef.pos x v hv)
    have hinv_le : C'⁻¹ <= C⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hC_pos hCC'
    constructor
    · exact le_trans
        (mul_le_mul_of_nonneg_right hinv_le hgin_nonneg)
        (hEq.2 x hx v).1
    · exact le_trans (hEq.2 x hx v).2
        (mul_le_mul_of_nonneg_right hCC' hgin_nonneg)


omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem metricUniformEquivalentOnWindow_mono
    {K K' : Set M} {β ψ : Real} {gRef : SmoothRiemannianMetric I M}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M} {B : Real -> Real}
    (hKK : K' ⊆ K)
    (h : MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B) :
    MetricUniformEquivalentOnWindow (I := I) K' β ψ gRef gSeq B :=
  fun i t ht => ⟨(h i t ht).1, fun x hx v => (h i t ht).2 x (hKK hx) v⟩



def metricEquivalenceFactor (C A t t0 : Real) : Real :=
  C * Real.exp (2 * A * |t - t0|)




noncomputable def metricCovDerivNorm
    (a : Nat) (h gRef : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) gRef x (a + 2)
      (metricCovDeriv (I := I) h gRef a x))






noncomputable def metricCovDerivNormSupOn
    (K : Set M) (p : Nat)
    (h gRef : SmoothRiemannianMetric I M) : Real :=
  sSup {r : Real |
    exists a : Nat, a <= p ∧
      exists x : M, x ∈ K ∧
        metricCovDerivNorm (I := I) a h gRef x = r}



def MetricCovDerivBoundOn
    (K : Set M) (p : Nat)
    (h gRef : SmoothRiemannianMetric I M)
    (C : Real) : Prop :=
  metricCovDerivNormSupOn (I := I) K p h gRef <= C




def MetricCovDerivOrderBoundOn
    (K : Set M) (a : Nat)
    (h gRef : SmoothRiemannianMetric I M)
    (C : Real) : Prop :=
  forall x : M, x ∈ K -> metricCovDerivNorm (I := I) a h gRef x <= C





omit [SigmaCompactSpace M] in
theorem metricCovBound_of_pointwise
    (K : Set M) (p : Nat)
    (h gRef : SmoothRiemannianMetric I M) (C : Real)
    (hC : 0 <= C)
    (hpoint :
      forall a : Nat, a <= p ->
        forall x : M, x ∈ K ->
          metricCovDerivNorm (I := I) a h gRef x <= C) :
    MetricCovDerivBoundOn (I := I) K p h gRef C := by
  unfold MetricCovDerivBoundOn metricCovDerivNormSupOn
  refine Real.sSup_le ?_ hC
  intro r hr
  rcases hr with ⟨a, ha, x, hx, hr⟩
  simpa [← hr] using hpoint a ha x hx




omit [SigmaCompactSpace M] in
theorem metricCovBoundOne_of_orders
    (K : Set M) (h gRef : SmoothRiemannianMetric I M) (C : Real)
    (hC : 0 <= C)
    (h0 : MetricCovDerivOrderBoundOn (I := I) K 0 h gRef C)
    (h1 : MetricCovDerivOrderBoundOn (I := I) K 1 h gRef C) :
    MetricCovDerivBoundOn (I := I) K 1 h gRef C := by
  refine metricCovBound_of_pointwise (I := I) K 1 h gRef C hC ?_
  intro a ha x hx
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
  · exact h0 x hx
  · exact h1 x hx




def MetricCovDerivBoundsAtTimeOn
    (K : Set M) (t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Real) : Prop :=
  forall i p : Nat, 0 < p ->
    MetricCovDerivBoundOn (I := I) K p (gSeq i t0) gRef (C p)



omit [SigmaCompactSpace M] in
theorem metricCovAtTime_of_pointwise
    (K : Set M) (t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Real)
    (hC : forall p : Nat, 0 <= C p)
    (hpoint :
      forall i p : Nat, 0 < p ->
        forall a : Nat, a <= p ->
          forall x : M, x ∈ K ->
            metricCovDerivNorm (I := I) a (gSeq i t0) gRef x <= C p) :
    MetricCovDerivBoundsAtTimeOn (I := I) K t0 gSeq gRef C := by
  intro i p hp
  exact
    metricCovBound_of_pointwise (I := I) K p (gSeq i t0) gRef (C p)
      (hC p) (hpoint i p hp)



def MetricCovDerivBoundsOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    forall p : Nat, MetricCovDerivBoundOn (I := I) K p (gSeq i t) gRef (C p)



def MetricCovDerivOrderBoundOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (a : Nat) (C : Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    MetricCovDerivOrderBoundOn (I := I) K a (gSeq i t) gRef C


omit [SigmaCompactSpace M] in
theorem metricCovOrderWindow_mono
    {K K' : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {a : Nat} {C : Real}
    (hKK : K' ⊆ K)
    (h : MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef a C) :
    MetricCovDerivOrderBoundOnWindow (I := I) K' β ψ gSeq gRef a C :=
  fun i t ht x hx => h i t ht x (hKK hx)



omit [SigmaCompactSpace M] in
theorem metricCovOrderWindow_of_pointwise
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (a : Nat) (C : Real)
    (hpoint :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall x : M, x ∈ K ->
          metricCovDerivNorm (I := I) a (gSeq i t) gRef x <= C) :
    MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef a C := by
  intro i t ht x hx
  exact hpoint i t ht x hx



omit [SigmaCompactSpace M] in
theorem metricCovBoundOneWindow_of_orders
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (C : Real)
    (hC : 0 <= C)
    (h0 :
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef 0 C)
    (h1 :
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef 1 C) :
    forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
      MetricCovDerivBoundOn (I := I) K 1 (gSeq i t) gRef C := by
  intro i t ht
  exact metricCovBoundOne_of_orders (I := I) K (gSeq i t) gRef C hC
    (h0 i t ht) (h1 i t ht)



omit [SigmaCompactSpace M] in
theorem metricCovWindow_of_pointwise
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Real)
    (hC : forall p : Nat, 0 <= C p)
    (hpoint :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall p : Nat,
          forall a : Nat, a <= p ->
            forall x : M, x ∈ K ->
              metricCovDerivNorm (I := I) a (gSeq i t) gRef x <= C p) :
    MetricCovDerivBoundsOnWindow (I := I) K β ψ gSeq gRef C := by
  intro i t ht p
  exact
    metricCovBound_of_pointwise (I := I) K p (gSeq i t) gRef (C p)
      (hC p) (hpoint i t ht p)



noncomputable def metricCovCumulativeConstant
    (C : Nat -> Real) (p : Nat) : Real :=
  (Finset.range (p + 1)).sup' (by
    refine ⟨0, ?_⟩
    simp) C




omit [SigmaCompactSpace M] in
theorem metricCovBoundsWindow_of_orderBounds
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Real)
    (hC : forall a : Nat, 0 <= C a)
    (horder :
      forall a : Nat,
        MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef a
          (C a)) :
    MetricCovDerivBoundsOnWindow (I := I) K β ψ gSeq gRef
      (metricCovCumulativeConstant C) := by
  refine
    metricCovWindow_of_pointwise (I := I) K β ψ gSeq gRef
      (metricCovCumulativeConstant C) ?_ ?_
  · intro p
    have h0mem : 0 ∈ Finset.range (p + 1) := by
      simp
    exact le_trans (hC 0) (Finset.le_sup' C h0mem)
  · intro i t ht p a ha x hx
    have hamem : a ∈ Finset.range (p + 1) := by
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le ha)
    exact le_trans (horder a i t ht x hx) (Finset.le_sup' C hamem)







omit [T2Space M] [SigmaCompactSpace M] in
theorem gammaL2_le_of_christoffel
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    {x : M} (hx : x ∈ u)
    (baseGamma : Idx -> Idx -> Idx -> Real)
    {a b R : Real}
    (hsub : Set.uIcc a b ⊆ D.carrier)
    (hregular : forall s : Real, s ∈ Set.uIcc a b -> s ∈ D.regular)
    (hinv_id :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall e l : Idx, gInv s x e l = if e = l then 1 else 0)
    (hevol :
      DifferentialGeometry.PDE.RicciFlow.ChristoffelEvolutionEquationInFrameOn
        (I := I) S gInv frame hframe nablaRic)
    (hRic :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt
          (DifferentialGeometry.Integral.Connection.componentL2Sq3
            (fun i j k : Idx => nablaRic s x i j k)) <= R) :
    Real.sqrt
        (DifferentialGeometry.Integral.Connection.componentL2Sq3
          (fun i j k : Idx =>
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (S.family.connection b) frame hframe x i j k -
              baseGamma i j k)) <=
      3 * R * |b - a| +
        Real.sqrt
          (DifferentialGeometry.Integral.Connection.componentL2Sq3
            (fun i j k : Idx =>
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                  (S.family.connection a) frame hframe x i j k -
                baseGamma i j k)) := by
  let Gamma : Real -> Idx -> Idx -> Idx -> Real :=
    fun s i j k =>
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (S.family.connection s) frame hframe x i j k -
        baseGamma i j k
  let dGamma : Real -> Idx -> Idx -> Idx -> Real :=
    fun s i j k =>
      DifferentialGeometry.PDE.RicciFlow.christoffelEvolutionRHSInFrame
        (M := M) gInv nablaRic s x i j k
  refine gammaL2_le_initial_add_regular
    (Gamma := Gamma) (dGamma := dGamma)
    (nablaRic := fun s i j k => nablaRic s x i j k)
    (D := D) (a := a) (b := b) (R := R)
    hsub hregular ?_ ?_ hRic
  · intro t p
    have h :=
      hevol t x hx p.1 p.2.1 p.2.2
    simpa [Gamma, dGamma] using
      h.sub_const (baseGamma p.1 p.2.1 p.2.2)
  · intro s hs i j k
    exact DifferentialGeometry.PDE.RicciFlow.christoffelRHS_id
      (M := M) gInv nablaRic (hinv_id s hs) i j k

set_option linter.unusedDecidableInType false in


omit [SigmaCompactSpace M] in
theorem metricCov1_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g h : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (d a b : Idx) :
    Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hx)
        (metricCovDeriv (I := I) g h 1 x)
        (Fin.cons d (fun q : Fin 2 => if q = 0 then a else b) :
          Fin 3 -> Idx) =
      DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
        (I := I) g
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
        frame (localFrameOneOfInf (I := I) frame hframe) x d a b := by
  let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h
  let hframe1 : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u :=
    localFrameOneOfInf (I := I) frame hframe
  rw [metricCovDeriv_one_component_localFrame
    (I := I) (h := g) (gRef := h) frame hframe hu hx d a b]
  unfold DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
    DifferentialGeometry.Tensor.Coordinates.metricCompForMetricInFrame
  have ha :
      (cov (frame a) x) (frame d x) =
        ∑ p : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d a p •
            frame p x :=
    DifferentialGeometry.Tensor.Coordinates.covariantDerivative_eq_sum_christoffel
      (I := I) cov frame hframe1 hx d a
  have hb :
      (cov (frame b) x) (frame d x) =
        ∑ p : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d b p •
            frame p x :=
    DifferentialGeometry.Tensor.Coordinates.covariantDerivative_eq_sum_christoffel
      (I := I) cov frame hframe1 hx d b
  rw [ha, hb]
  simp [map_sum, map_smul, cov]
  ring




omit [SigmaCompactSpace M] in
theorem metricCovDeriv_two_eval_smooth_slots
    (h gRef : SmoothRiemannianMetric I M)
    (X :
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (V : Fin 3 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) :
    metricCovDeriv (I := I) h gRef 2 x
        (Fin.cons (X x) (fun a : Fin 3 => V a x)) =
      extDerivFun (I := I)
          (fun p : M =>
            metricCovDeriv (I := I) h gRef 1 p
              (fun a : Fin 3 => V a p)) x (X x) -
        ∑ a : Fin 3,
          metricCovDeriv (I := I) h gRef 1 x
            (Function.update (fun b : Fin 3 => V b x) a
              (((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun p : M => V a p) x) (X x))) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef
  let A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 3 :=
    metricCovDeriv (I := I) h gRef 1
  let hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (∞ : WithTop ℕ∞) := by
    simpa [cov] using
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) gRef
  let hreg :=
    Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
      (I := I) (M := M) 3 cov hcov A
  have hreal :
      Tensor0SBundle.TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 cov A
        (Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 3 cov A hreg) := by
    exact Tensor0SBundle.totalNabla0S_realizes
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 cov A hreg
  have hmain :=
    Tensor0SBundle.TotalNabla0SRealizes.eval_smooth_slots
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      hreal X V x
  change
    (Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 cov A hreg x)
        (Fin.cons (X x) (fun a : Fin 3 => V a x)) =
      extDerivFun (I := I) (fun p : M => A p (fun a : Fin 3 => V a p))
        x (X x) -
        ∑ a : Fin 3,
          A x
            (Function.update (fun b : Fin 3 => V b x) a
              ((cov (fun p : M => V a p) x) (X x)))
  exact hmain




omit [SigmaCompactSpace M] in
theorem metricCovDeriv_three_eval_smooth_slots
    (h gRef : SmoothRiemannianMetric I M)
    (X :
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (V : Fin 4 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) :
    metricCovDeriv (I := I) h gRef 3 x
        (Fin.cons (X x) (fun a : Fin 4 => V a x)) =
      extDerivFun (I := I)
          (fun p : M =>
            metricCovDeriv (I := I) h gRef 2 p
              (fun a : Fin 4 => V a p)) x (X x) -
        ∑ a : Fin 4,
          metricCovDeriv (I := I) h gRef 2 x
            (Function.update (fun b : Fin 4 => V b x) a
              (((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun p : M => V a p) x) (X x))) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef
  let A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 4 :=
    metricCovDeriv (I := I) h gRef 2
  let hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (∞ : WithTop ℕ∞) := by
    simpa [cov] using
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) gRef
  let hreg :=
    Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
      (I := I) (M := M) 4 cov hcov A
  have hreal :
      Tensor0SBundle.TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 cov A
        (Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 4 cov A hreg) := by
    exact Tensor0SBundle.totalNabla0S_realizes
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 cov A hreg
  have hmain :=
    Tensor0SBundle.TotalNabla0SRealizes.eval_smooth_slots
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      hreal X V x
  change
    (Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 cov A hreg x)
        (Fin.cons (X x) (fun a : Fin 4 => V a x)) =
      extDerivFun (I := I) (fun p : M => A p (fun a : Fin 4 => V a p))
        x (X x) -
        ∑ a : Fin 4,
          A x
            (Function.update (fun b : Fin 4 => V b x) a
              ((cov (fun p : M => V a p) x) (X x)))
  exact hmain

set_option linter.unusedDecidableInType false in


omit [SigmaCompactSpace M] in
theorem metricCov2_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g h : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (d a b c : Idx) :
    Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hx)
        (metricCovDeriv (I := I) g h 2 x)
        (Fin.cons d (DifferentialGeometry.Tensor.Coordinates.slots3 a b c) : Fin 4 -> Idx) =
      DifferentialGeometry.Tensor.Coordinates.metricCovDeriv2ForMetricCompInFrame
        (I := I) g
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
        frame (localFrameOneOfInf (I := I) frame hframe) x d a b c := by
  classical
  let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h
  let hframe1 : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u :=
    localFrameOneOfInf (I := I) frame hframe
  obtain ⟨sec, hsec⟩ :=
    hframe.exists_contMDiffSection_eqOn_nhd hu hx
  let X :
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) := sec d
  let V : Fin 3 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) :=
    fun q => sec (DifferentialGeometry.Tensor.Coordinates.slots3 a b c q)
  have hsec_ev (i : Idx) :
      (fun y : M => sec i y) =ᶠ[𝓝 x] frame i :=
    hsec.mono fun y hy => hy i
  have hsec_x (i : Idx) : sec i x = frame i x :=
    (hsec_ev i).self_of_nhds
  have hXx : X x = frame d x := hsec_x d
  have hVx (q : Fin 3) : V q x = frame (DifferentialGeometry.Tensor.Coordinates.slots3 a b c q) x :=
    hsec_x (DifferentialGeometry.Tensor.Coordinates.slots3 a b c q)
  have slots3_cons (i j k : Idx) :
      (Fin.cons i (fun q : Fin 2 => if q = 0 then j else k) :
        Fin 3 -> Idx) =
        DifferentialGeometry.Tensor.Coordinates.slots3 i j k := by
    funext q
    cases q using Fin.cases with
    | zero =>
        simp [DifferentialGeometry.Tensor.Coordinates.slots3]
    | succ q =>
        rw [Fin.cons_succ]
        fin_cases q <;> simp [DifferentialGeometry.Tensor.Coordinates.slots3]
  have hslots :
      (fun q : Fin 4 =>
          hframe.toBasisAt hx
            ((Fin.cons d (DifferentialGeometry.Tensor.Coordinates.slots3 a b c) : Fin 4 -> Idx) q)) =
        Fin.cons (X x) (fun q : Fin 3 => V q x) := by
    funext q
    cases q using Fin.cases with
    | zero =>
        simpa [X, IsLocalFrameOn.toBasisAt_coe] using hXx.symm
    | succ q =>
        simpa [V, IsLocalFrameOn.toBasisAt_coe] using (hVx q).symm
  rw [Tensor0SBundle.component0S_apply]
  rw [hslots]
  have hmain :=
    metricCovDeriv_two_eval_smooth_slots (I := I) g h X V x
  rw [hmain]
  have hscalar :
      (fun y : M =>
          metricCovDeriv (I := I) g h 1 y
            (fun q : Fin 3 => V q y)) =ᶠ[𝓝 x]
        (fun y : M =>
          DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
            (I := I) g cov frame hframe1 y a b c) := by
    filter_upwards [hsec_ev a, hsec_ev b, hsec_ev c, hu.mem_nhds hx]
      with y hsa hsb hsc hy
    have hVy :
        (fun q : Fin 3 => V q y) =
          fun q : Fin 3 => frame (DifferentialGeometry.Tensor.Coordinates.slots3 a b c q) y := by
      funext q
      fin_cases q <;> simp [V, DifferentialGeometry.Tensor.Coordinates.slots3, hsa, hsb, hsc]
    have hslot3 :
        (Fin.cons a (fun q : Fin 2 => if q = 0 then b else c) :
          Fin 3 -> Idx) =
          DifferentialGeometry.Tensor.Coordinates.slots3 a b c := by
      exact slots3_cons a b c
    have hcomp :=
      metricCov1_coord (I := I) g h frame hframe hu hy a b c
    rw [Tensor0SBundle.component0S_apply] at hcomp
    simpa [hVy, hslot3, IsLocalFrameOn.toBasisAt_coe, cov, hframe1] using hcomp
  have hext :
      extDerivFun (I := I)
          (fun p : M =>
            metricCovDeriv (I := I) g h 1 p
              (fun q : Fin 3 => V q p)) x (X x) =
        extDerivFun (I := I)
          (fun y : M =>
            DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g cov frame hframe1 y a b c) x (frame d x) := by
    calc
      extDerivFun (I := I)
          (fun p : M =>
            metricCovDeriv (I := I) g h 1 p
              (fun q : Fin 3 => V q p)) x (X x)
          =
        extDerivFun (I := I)
          (fun y : M =>
            DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g cov frame hframe1 y a b c) x (X x) := by
          exact DifferentialGeometry.Tensor.Coordinates.extDerivFun_congr_eventually
            (I := I) (X x) hscalar
      _ =
        extDerivFun (I := I)
          (fun y : M =>
            DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g cov frame hframe1 y a b c) x (frame d x) := by
          rw [hXx]
  have hcov_slot (i : Idx) :
      (cov (frame i) x) (frame d x) =
        ∑ p : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d i p •
            frame p x :=
    DifferentialGeometry.Tensor.Coordinates.covariantDerivative_eq_sum_christoffel
      (I := I) cov frame hframe1 hx d i
  have hcorr0 :
      metricCovDeriv (I := I) g h 1 x
        (Function.update (fun q : Fin 3 => V q x) 0
          ((cov (fun y : M => V 0 y) x) (X x))) =
        ∑ p : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d a p *
            DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g cov frame hframe1 x p b c := by
    have hcov0 :
        (cov (fun y : M => V 0 y) x) (X x) =
          ∑ p : Idx,
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d a p •
              frame p x := by
      have hV0 : MDiffAt (T% (fun y : M => V 0 y)) x :=
        (V 0).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
      have hframea : MDiffAt (T% (frame a)) x :=
        (hframe.contMDiffAt hu hx a).mdifferentiableAt (by simp)
      have hcov_eq :
          (cov (fun y : M => V 0 y) x) (X x) =
            (cov (frame a) x) (frame d x) := by
        have hV0_ev : (fun y : M => V 0 y) =ᶠ[𝓝 x] frame a := by
          simpa [V, DifferentialGeometry.Tensor.Coordinates.slots3] using hsec_ev a
        have hcov_congr :=
          cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
            hV0 hframea (by simp) hV0_ev
        rw [hXx]
        rw [hcov_congr]
      rw [hcov_eq, hcov_slot a]
    let A := metricCovDeriv (I := I) g h 1 x
    let slots : Fin 3 -> TangentSpace I x := fun q => V q x
    calc
      A
          (Function.update slots 0
            ((cov (fun y : M => V 0 y) x) (X x)))
          =
        A
          (Function.update slots 0
            (∑ p : Idx,
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d a p •
                frame p x)) := by
          rw [hcov0]
      _ =
        ∑ p : Idx,
          A
            (Function.update slots 0
              (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d a p •
                frame p x)) := by
          have hsum :=
            A.toMultilinearMap.map_update_sum
              (Finset.univ : Finset Idx) (0 : Fin 3)
              (fun p : Idx =>
                DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d a p •
                  frame p x) slots
          simpa [A, slots, ContinuousMultilinearMap.map_update_smul,
            Tensor0SBundle.Tensor0SSpace.map_update_smul, smul_eq_mul] using hsum
      _ =
        ∑ p : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d a p *
            DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g cov frame hframe1 x p b c := by
          refine Finset.sum_congr rfl ?_
          intro p _
          have hcomp :=
            metricCov1_coord (I := I) g h frame hframe hu hx p b c
          rw [Tensor0SBundle.component0S_apply] at hcomp
          have hsmul :=
            A.map_update_smul slots (0 : Fin 3)
              (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d a p)
              (frame p x)
          have hslots0 :
              Function.update slots 0 (frame p x) =
                fun q : Fin 3 =>
                  frame
                    ((Fin.cons p (fun q : Fin 2 => if q = 0 then b else c) :
                      Fin 3 -> Idx) q) x := by
            rw [slots3_cons p b c]
            funext q
            fin_cases q <;>
              simp [slots, V, DifferentialGeometry.Tensor.Coordinates.slots3, Function.update, hsec_x b, hsec_x c]
          have hframeComp :
              A (Function.update slots 0 (frame p x)) =
                DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
                  (I := I) g cov frame hframe1 x p b c := by
            rw [hslots0]
            simpa [A, cov, hframe1, IsLocalFrameOn.toBasisAt_coe] using hcomp
          calc
            A
                (Function.update slots 0
                  (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d a p •
                    frame p x))
                =
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d a p *
                A (Function.update slots 0 (frame p x)) := by
                rw [hsmul]
                simp [smul_eq_mul]
            _ =
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d a p *
                DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
                  (I := I) g cov frame hframe1 x p b c := by
                rw [hframeComp]
  have hcorr1 :
      metricCovDeriv (I := I) g h 1 x
        (Function.update (fun q : Fin 3 => V q x) 1
          ((cov (fun y : M => V 1 y) x) (X x))) =
        ∑ p : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d b p *
            DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g cov frame hframe1 x a p c := by
    have hcov1 :
        (cov (fun y : M => V 1 y) x) (X x) =
          ∑ p : Idx,
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d b p •
              frame p x := by
      have hV1 : MDiffAt (T% (fun y : M => V 1 y)) x :=
        (V 1).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
      have hframeb : MDiffAt (T% (frame b)) x :=
        (hframe.contMDiffAt hu hx b).mdifferentiableAt (by simp)
      have hcov_eq :
          (cov (fun y : M => V 1 y) x) (X x) =
            (cov (frame b) x) (frame d x) := by
        have hV1_ev : (fun y : M => V 1 y) =ᶠ[𝓝 x] frame b := by
          simpa [V, DifferentialGeometry.Tensor.Coordinates.slots3] using hsec_ev b
        have hcov_congr :=
          cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
            hV1 hframeb (by simp) hV1_ev
        rw [hXx]
        rw [hcov_congr]
      rw [hcov_eq, hcov_slot b]
    let A := metricCovDeriv (I := I) g h 1 x
    let slots : Fin 3 -> TangentSpace I x := fun q => V q x
    calc
      A
          (Function.update slots 1
            ((cov (fun y : M => V 1 y) x) (X x)))
          =
        A
          (Function.update slots 1
            (∑ p : Idx,
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d b p •
                frame p x)) := by
          rw [hcov1]
      _ =
        ∑ p : Idx,
          A
            (Function.update slots 1
              (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d b p •
                frame p x)) := by
          have hsum :=
            A.toMultilinearMap.map_update_sum
              (Finset.univ : Finset Idx) (1 : Fin 3)
              (fun p : Idx =>
                DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d b p •
                  frame p x) slots
          simpa [A, slots, ContinuousMultilinearMap.map_update_smul,
            Tensor0SBundle.Tensor0SSpace.map_update_smul, smul_eq_mul] using hsum
      _ =
        ∑ p : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d b p *
            DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g cov frame hframe1 x a p c := by
          refine Finset.sum_congr rfl ?_
          intro p _
          have hcomp :=
            metricCov1_coord (I := I) g h frame hframe hu hx a p c
          rw [Tensor0SBundle.component0S_apply] at hcomp
          have hsmul :=
            A.map_update_smul slots (1 : Fin 3)
              (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d b p)
              (frame p x)
          have hslots1 :
              Function.update slots 1 (frame p x) =
                fun q : Fin 3 =>
                  frame
                    ((Fin.cons a (fun q : Fin 2 => if q = 0 then p else c) :
                      Fin 3 -> Idx) q) x := by
            rw [slots3_cons a p c]
            funext q
            fin_cases q <;>
              simp [slots, V, DifferentialGeometry.Tensor.Coordinates.slots3, Function.update, hsec_x a, hsec_x c]
          have hframeComp :
              A (Function.update slots 1 (frame p x)) =
                DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
                  (I := I) g cov frame hframe1 x a p c := by
            rw [hslots1]
            simpa [A, cov, hframe1, IsLocalFrameOn.toBasisAt_coe] using hcomp
          calc
            A
                (Function.update slots 1
                  (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d b p •
                    frame p x))
                =
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d b p *
                A (Function.update slots 1 (frame p x)) := by
                rw [hsmul]
                simp [smul_eq_mul]
            _ =
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d b p *
                DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
                  (I := I) g cov frame hframe1 x a p c := by
                rw [hframeComp]
  have hcorr2 :
      metricCovDeriv (I := I) g h 1 x
        (Function.update (fun q : Fin 3 => V q x) 2
          ((cov (fun y : M => V 2 y) x) (X x))) =
        ∑ p : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d c p *
            DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g cov frame hframe1 x a b p := by
    have hcov2 :
        (cov (fun y : M => V 2 y) x) (X x) =
          ∑ p : Idx,
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d c p •
              frame p x := by
      have hV2 : MDiffAt (T% (fun y : M => V 2 y)) x :=
        (V 2).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
      have hframec : MDiffAt (T% (frame c)) x :=
        (hframe.contMDiffAt hu hx c).mdifferentiableAt (by simp)
      have hcov_eq :
          (cov (fun y : M => V 2 y) x) (X x) =
            (cov (frame c) x) (frame d x) := by
        have hV2_ev : (fun y : M => V 2 y) =ᶠ[𝓝 x] frame c := by
          simpa [V, DifferentialGeometry.Tensor.Coordinates.slots3] using hsec_ev c
        have hcov_congr :=
          cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
            hV2 hframec (by simp) hV2_ev
        rw [hXx]
        rw [hcov_congr]
      rw [hcov_eq, hcov_slot c]
    let A := metricCovDeriv (I := I) g h 1 x
    let slots : Fin 3 -> TangentSpace I x := fun q => V q x
    calc
      A
          (Function.update slots 2
            ((cov (fun y : M => V 2 y) x) (X x)))
          =
        A
          (Function.update slots 2
            (∑ p : Idx,
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d c p •
                frame p x)) := by
          rw [hcov2]
      _ =
        ∑ p : Idx,
          A
            (Function.update slots 2
              (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d c p •
                frame p x)) := by
          have hsum :=
            A.toMultilinearMap.map_update_sum
              (Finset.univ : Finset Idx) (2 : Fin 3)
              (fun p : Idx =>
                DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d c p •
                  frame p x) slots
          simpa [A, slots, ContinuousMultilinearMap.map_update_smul,
            Tensor0SBundle.Tensor0SSpace.map_update_smul, smul_eq_mul] using hsum
      _ =
        ∑ p : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d c p *
            DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g cov frame hframe1 x a b p := by
          refine Finset.sum_congr rfl ?_
          intro p _
          have hcomp :=
            metricCov1_coord (I := I) g h frame hframe hu hx a b p
          rw [Tensor0SBundle.component0S_apply] at hcomp
          have hsmul :=
            A.map_update_smul slots (2 : Fin 3)
              (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d c p)
              (frame p x)
          have hslots2 :
              Function.update slots 2 (frame p x) =
                fun q : Fin 3 =>
                  frame
                    ((Fin.cons a (fun q : Fin 2 => if q = 0 then b else p) :
                      Fin 3 -> Idx) q) x := by
            rw [slots3_cons a b p]
            funext q
            fin_cases q <;>
              simp [slots, V, DifferentialGeometry.Tensor.Coordinates.slots3, Function.update, hsec_x a, hsec_x b]
          have hframeComp :
              A (Function.update slots 2 (frame p x)) =
                DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
                  (I := I) g cov frame hframe1 x a b p := by
            rw [hslots2]
            simpa [A, cov, hframe1, IsLocalFrameOn.toBasisAt_coe] using hcomp
          calc
            A
                (Function.update slots 2
                  (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d c p •
                    frame p x))
                =
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d c p *
                A (Function.update slots 2 (frame p x)) := by
                rw [hsmul]
                simp [smul_eq_mul]
            _ =
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x d c p *
                DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame
                  (I := I) g cov frame hframe1 x a b p := by
                rw [hframeComp]
  rw [hext]
  rw [Fin.sum_univ_three]
  rw [hcorr0, hcorr1, hcorr2]
  unfold DifferentialGeometry.Tensor.Coordinates.metricCovDeriv2ForMetricCompInFrame
  ring

set_option linter.unusedDecidableInType false in


omit [SigmaCompactSpace M] in
theorem metricCov3_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g h : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (m d a b c : Idx) :
    Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hx)
        (metricCovDeriv (I := I) g h 3 x)
        (Fin.cons m (DifferentialGeometry.Tensor.Coordinates.slots4 d a b c) : Fin 5 -> Idx) =
      DifferentialGeometry.Tensor.Coordinates.metricCovDeriv3ForMetricCompInFrame
        (I := I) g
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
        frame (localFrameOneOfInf (I := I) frame hframe) x m d a b c := by
  classical
  let cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h
  let hframe1 : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u :=
    localFrameOneOfInf (I := I) frame hframe
  let slot : Fin 4 -> Idx := DifferentialGeometry.Tensor.Coordinates.slots4 d a b c
  obtain ⟨sec, hsec⟩ :=
    hframe.exists_contMDiffSection_eqOn_nhd hu hx
  let X :
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) := sec m
  let V : Fin 4 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) :=
    fun q => sec (slot q)
  have hsec_ev (i : Idx) :
      (fun y : M => sec i y) =ᶠ[𝓝 x] frame i :=
    hsec.mono fun y hy => hy i
  have hsec_x (i : Idx) : sec i x = frame i x :=
    (hsec_ev i).self_of_nhds
  have hXx : X x = frame m x := hsec_x m
  have hVx (q : Fin 4) : V q x = frame (slot q) x :=
    hsec_x (slot q)
  have slots4_cons (i j k l : Idx) :
      (Fin.cons i (DifferentialGeometry.Tensor.Coordinates.slots3 j k l) : Fin 4 -> Idx) =
        DifferentialGeometry.Tensor.Coordinates.slots4 i j k l := by
    funext q
    cases q using Fin.cases with
    | zero =>
        simp [DifferentialGeometry.Tensor.Coordinates.slots4]
    | succ q =>
        rw [Fin.cons_succ]
        fin_cases q <;> simp [DifferentialGeometry.Tensor.Coordinates.slots3, DifferentialGeometry.Tensor.Coordinates.slots4]
  have slots4_eta (s : Fin 4 -> Idx) :
      (Fin.cons (s 0) (DifferentialGeometry.Tensor.Coordinates.slots3 (s 1) (s 2) (s 3)) :
        Fin 4 -> Idx) = s := by
    funext q
    cases q using Fin.cases with
    | zero =>
        simp
    | succ q =>
        rw [Fin.cons_succ]
        fin_cases q <;> simp [DifferentialGeometry.Tensor.Coordinates.slots3]
  have hslots :
      (fun q : Fin 5 =>
          hframe.toBasisAt hx
            ((Fin.cons m (DifferentialGeometry.Tensor.Coordinates.slots4 d a b c) : Fin 5 -> Idx) q)) =
        Fin.cons (X x) (fun q : Fin 4 => V q x) := by
    funext q
    cases q using Fin.cases with
    | zero =>
        simpa [X, IsLocalFrameOn.toBasisAt_coe] using hXx.symm
    | succ q =>
        simpa [V, slot, IsLocalFrameOn.toBasisAt_coe] using (hVx q).symm
  rw [Tensor0SBundle.component0S_apply]
  rw [hslots]
  have hmain :=
    metricCovDeriv_three_eval_smooth_slots (I := I) g h X V x
  rw [hmain]
  have hscalar :
      (fun y : M =>
          metricCovDeriv (I := I) g h 2 y
            (fun q : Fin 4 => V q y)) =ᶠ[𝓝 x]
        (fun y : M =>
          DifferentialGeometry.Tensor.Coordinates.metricCovDeriv2ForMetricCompInFrame
            (I := I) g cov frame hframe1 y d a b c) := by
    filter_upwards [hsec_ev d, hsec_ev a, hsec_ev b, hsec_ev c, hu.mem_nhds hx]
      with y hsd hsa hsb hsc hy
    have hVy :
        (fun q : Fin 4 => V q y) =
          fun q : Fin 4 => frame (slot q) y := by
      funext q
      fin_cases q <;> simp [V, slot, DifferentialGeometry.Tensor.Coordinates.slots4, hsd, hsa, hsb, hsc]
    have hcomp :=
      metricCov2_coord (I := I) g h frame hframe hu hy d a b c
    rw [Tensor0SBundle.component0S_apply] at hcomp
    simpa [hVy, slot, slots4_cons, IsLocalFrameOn.toBasisAt_coe, cov, hframe1]
      using hcomp
  have hext :
      extDerivFun (I := I)
          (fun p : M =>
            metricCovDeriv (I := I) g h 2 p
              (fun q : Fin 4 => V q p)) x (X x) =
        extDerivFun (I := I)
          (fun y : M =>
            DifferentialGeometry.Tensor.Coordinates.metricCovDeriv2ForMetricCompInFrame
              (I := I) g cov frame hframe1 y d a b c) x (frame m x) := by
    calc
      extDerivFun (I := I)
          (fun p : M =>
            metricCovDeriv (I := I) g h 2 p
              (fun q : Fin 4 => V q p)) x (X x)
          =
        extDerivFun (I := I)
          (fun y : M =>
            DifferentialGeometry.Tensor.Coordinates.metricCovDeriv2ForMetricCompInFrame
              (I := I) g cov frame hframe1 y d a b c) x (X x) := by
          exact DifferentialGeometry.Tensor.Coordinates.extDerivFun_congr_eventually
            (I := I) (X x) hscalar
      _ =
        extDerivFun (I := I)
          (fun y : M =>
            DifferentialGeometry.Tensor.Coordinates.metricCovDeriv2ForMetricCompInFrame
              (I := I) g cov frame hframe1 y d a b c) x (frame m x) := by
          rw [hXx]
  have hcov_slot (i : Idx) :
      (cov (frame i) x) (frame m x) =
        ∑ p : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x m i p •
            frame p x :=
    DifferentialGeometry.Tensor.Coordinates.covariantDerivative_eq_sum_christoffel
      (I := I) cov frame hframe1 hx m i
  let A := metricCovDeriv (I := I) g h 2 x
  let slotsT : Fin 4 -> TangentSpace I x := fun q => V q x
  have hcorr (r : Fin 4) :
      A
        (Function.update slotsT r
          ((cov (fun y : M => V r y) x) (X x))) =
        ∑ p : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x m (slot r) p *
            DifferentialGeometry.Tensor.Coordinates.metricCovDeriv2ForMetricCompInFrame
              (I := I) g cov frame hframe1 x
              ((Function.update slot r p) 0)
              ((Function.update slot r p) 1)
              ((Function.update slot r p) 2)
              ((Function.update slot r p) 3) := by
    have hcovr :
        (cov (fun y : M => V r y) x) (X x) =
          ∑ p : Idx,
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x m (slot r) p •
              frame p x := by
      have hVr : MDiffAt (T% (fun y : M => V r y)) x :=
        (V r).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
      have hfr : MDiffAt (T% (frame (slot r))) x :=
        (hframe.contMDiffAt hu hx (slot r)).mdifferentiableAt (by simp)
      have hcov_eq :
          (cov (fun y : M => V r y) x) (X x) =
            (cov (frame (slot r)) x) (frame m x) := by
        have hVr_ev : (fun y : M => V r y) =ᶠ[𝓝 x] frame (slot r) := by
          simpa [V] using hsec_ev (slot r)
        have hcov_congr :=
          cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
            hVr hfr (by simp) hVr_ev
        rw [hXx]
        rw [hcov_congr]
      rw [hcov_eq, hcov_slot (slot r)]
    calc
      A
          (Function.update slotsT r
            ((cov (fun y : M => V r y) x) (X x)))
          =
        A
          (Function.update slotsT r
            (∑ p : Idx,
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x m (slot r) p •
                frame p x)) := by
          rw [hcovr]
      _ =
        ∑ p : Idx,
          A
            (Function.update slotsT r
              (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x m (slot r) p •
                frame p x)) := by
          have hsum :=
            A.toMultilinearMap.map_update_sum
              (Finset.univ : Finset Idx) r
              (fun p : Idx =>
                DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x m (slot r) p •
                  frame p x) slotsT
          simpa [A, slotsT, ContinuousMultilinearMap.map_update_smul,
            Tensor0SBundle.Tensor0SSpace.map_update_smul, smul_eq_mul] using hsum
      _ =
        ∑ p : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x m (slot r) p *
            DifferentialGeometry.Tensor.Coordinates.metricCovDeriv2ForMetricCompInFrame
              (I := I) g cov frame hframe1 x
              ((Function.update slot r p) 0)
              ((Function.update slot r p) 1)
              ((Function.update slot r p) 2)
              ((Function.update slot r p) 3) := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          let slot' : Fin 4 -> Idx := Function.update slot r p
          have hcomp :=
            metricCov2_coord (I := I) g h frame hframe hu hx
              (slot' 0) (slot' 1) (slot' 2) (slot' 3)
          rw [Tensor0SBundle.component0S_apply] at hcomp
          have hsmul :=
            A.map_update_smul slotsT r
              (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x m (slot r) p)
              (frame p x)
          have hslotsUpdate :
              Function.update slotsT r (frame p x) =
                fun q : Fin 4 => frame (slot' q) x := by
            funext q
            by_cases hqr : q = r
            · subst q
              simp [slot', Function.update]
            · simp [slot', slotsT, V, Function.update, hqr, hsec_x (slot q)]
          have hslotEta :
              (Fin.cons (slot' 0) (DifferentialGeometry.Tensor.Coordinates.slots3 (slot' 1) (slot' 2) (slot' 3)) :
                Fin 4 -> Idx) = slot' :=
            slots4_eta slot'
          have hframeComp :
              A (Function.update slotsT r (frame p x)) =
                DifferentialGeometry.Tensor.Coordinates.metricCovDeriv2ForMetricCompInFrame
                  (I := I) g cov frame hframe1 x
                  (slot' 0) (slot' 1) (slot' 2) (slot' 3) := by
            rw [hslotsUpdate]
            simpa [A, cov, hframe1, IsLocalFrameOn.toBasisAt_coe, hslotEta] using hcomp
          calc
            A
                (Function.update slotsT r
                  (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x m (slot r) p •
                    frame p x))
                =
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x m (slot r) p *
                A (Function.update slotsT r (frame p x)) := by
                rw [hsmul]
                simp [smul_eq_mul]
            _ =
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe1 x m (slot r) p *
                DifferentialGeometry.Tensor.Coordinates.metricCovDeriv2ForMetricCompInFrame
                  (I := I) g cov frame hframe1 x
                  (slot' 0) (slot' 1) (slot' 2) (slot' 3) := by
                rw [hframeComp]
  rw [hext]
  rw [Fin.sum_univ_four]
  rw [hcorr 0, hcorr 1, hcorr 2, hcorr 3]
  unfold DifferentialGeometry.Tensor.Coordinates.metricCovDeriv3ForMetricCompInFrame
  simp [slot, Function.update, cov]
  ring







noncomputable def lcMetricFamily
    (g : Real -> SmoothRiemannianMetric I M) :
    DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real where
  metric := g
  connection := fun t : Real =>
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) (g t)
  metricCompatible := fun t : Real =>
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) (g t)






omit [SigmaCompactSpace M] in
theorem metricCovDeriv_one_component_eq_metricCovAtBase
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g : Real -> SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real) (d a b : Idx) :
    Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hx)
        (metricCovDeriv (I := I) (g var) (g base) 1 x)
        (Fin.cons d (fun q : Fin 2 => if q = 0 then a else b) :
          Fin 3 -> Idx) =
      DifferentialGeometry.Integral.Connection.metricCovAtBase (I := I)
        (lcMetricFamily (I := I) (M := M) g) frame base var x d a b := by
  rw [metricCovDeriv_one_component_localFrame (I := I)
    (h := g var) (gRef := g base) frame hframe hu hx d a b]
  unfold DifferentialGeometry.Integral.Connection.metricCovAtBase lcMetricFamily
  ring


omit [SigmaCompactSpace M] in
theorem componentL2Sq3_metricCovDeriv_one_eq_metricCovAtBase
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g : Real -> SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real) :
    DifferentialGeometry.Integral.Connection.componentL2Sq3
        (fun d a b : Idx =>
          Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hx)
            (metricCovDeriv (I := I) (g var) (g base) 1 x)
            (Fin.cons d (fun q : Fin 2 => if q = 0 then a else b) :
              Fin 3 -> Idx)) =
      DifferentialGeometry.Integral.Connection.componentL2Sq3
        (fun d a b : Idx =>
          DifferentialGeometry.Integral.Connection.metricCovAtBase (I := I)
            (lcMetricFamily (I := I) (M := M) g) frame base var x d a b) := by
  unfold DifferentialGeometry.Integral.Connection.componentL2Sq3
  apply Finset.sum_congr rfl
  intro p _
  exact congrArg (fun r : Real => r ^ 2)
    (metricCovDeriv_one_component_eq_metricCovAtBase
      (I := I) g frame hframe hu hx base var p.1 p.2.1 p.2.2)







omit [SigmaCompactSpace M] in
theorem metricGammaEquiv
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g : Real -> SmoothRiemannianMetric I M)
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real)
    (hinv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (g var) gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0)
    (hmetric_id : ∀ i j : Idx,
      (g var).inner x (frame i x) (frame j x) =
        if i = j then 1 else 0) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g var) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            ((lcMetricFamily (I := I) (M := M) g).connection var)
            ((lcMetricFamily (I := I) (M := M) g).connection base) x)) <=
      (3 / 2 : Real) *
        Real.sqrt
          (Tensor0SBundle.normSq0S
            (I := I) (g var) x 3
            (metricCovDeriv (I := I) (g var) (g base) 1 x)) ∧
    Real.sqrt
        (Tensor0SBundle.normSq0S
          (I := I) (g var) x 3
          (metricCovDeriv (I := I) (g var) (g base) 1 x)) <=
      2 *
        Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := g var) (x := x) 1 2
            (Tensor0SBundle.connectionDifferenceTensorAt
              (I := I)
              ((lcMetricFamily (I := I) (M := M) g).connection var)
              ((lcMetricFamily (I := I) (M := M) g).connection base) x)) := by
  classical
  let hframe1 : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u :=
    { linearIndependent := hframe.linearIndependent
      generating := hframe.generating
      contMDiffOn := fun i => (hframe.contMDiffOn i).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ∞) }
  have hLC :
      ∀ s : Real,
        DifferentialGeometry.Integral.Connection.IsLeviCivita
          (I := I) ((lcMetricFamily (I := I) (M := M) g).connection s)
          ((lcMetricFamily (I := I) (M := M) g).metric s) := by
    intro s
    simpa [lcMetricFamily] using
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isLeviCivita
        (I := I) (g s)
  have hinvBasis :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (g var) x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)) := by
    intro i j
    constructor
    · simp [Tensor0SBundle.identityInvMetric,
        Tensor0SBundle.diagonalInvMetric, IsLocalFrameOn.toBasisAt_coe,
        hmetric_id]
    · simp [Tensor0SBundle.identityInvMetric,
        Tensor0SBundle.diagonalInvMetric, IsLocalFrameOn.toBasisAt_coe,
        hmetric_id]
  have hmetricSq :
      Tensor0SBundle.normSq0S
          (I := I) (g var) x 3
          (metricCovDeriv (I := I) (g var) (g base) 1 x) =
        DifferentialGeometry.Integral.Connection.componentL2Sq3
          (fun d a b : Idx =>
            DifferentialGeometry.Integral.Connection.metricCovAtBase (I := I)
              (lcMetricFamily (I := I) (M := M) g) frame base var x d a b) := by
    exact
      DifferentialGeometry.Integral.Connection.normSq0S_three_eq_componentL2Sq3_of_components
        (I := I) (g := g var) x (hframe.toBasisAt hx) hinvBasis
        (metricCovDeriv (I := I) (g var) (g base) 1 x)
        (fun d a b : Idx =>
          DifferentialGeometry.Integral.Connection.metricCovAtBase (I := I)
            (lcMetricFamily (I := I) (M := M) g) frame base var x d a b)
        (by
          intro d a b
          exact metricCovDeriv_one_component_eq_metricCovAtBase
            (I := I) g frame hframe hu hx base var d a b)
  have hconnSq :
      Tensor0SBundle.normSqRS
          (I := I) (g := g var) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            ((lcMetricFamily (I := I) (M := M) g).connection var)
            ((lcMetricFamily (I := I) (M := M) g).connection base) x) =
        DifferentialGeometry.Integral.Connection.componentL2Sq3
          (fun a b e : Idx =>
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                ((lcMetricFamily (I := I) (M := M) g).connection var)
                frame hframe1 x a b e -
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                ((lcMetricFamily (I := I) (M := M) g).connection base)
                frame hframe1 x a b e) := by
    exact
      DifferentialGeometry.Integral.Connection.normSqRS_connDiff_eq_componentL2Sq3
        (I := I) (G := lcMetricFamily (I := I) (M := M) g) gInv
        frame hframe1 hu hx base var hinv hinv_id
  have hcomp :=
    DifferentialGeometry.Integral.Connection.covGamma_l2_equiv
      (I := I) (G := lcMetricFamily (I := I) (M := M) g) hLC
      gInv frame hframe1 hu hx base var hinv hinv_id hmetric_id
  constructor
  · rw [hconnSq, hmetricSq]
    exact hcomp.1
  · rw [hconnSq, hmetricSq]
    exact hcomp.2








omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem sqrt_normSq0S_three_diag_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g h : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (μ : Idx -> Real) (C : Real)
    (hC : 0 <= C)
    (hginv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x basis
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hhinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis
        (Tensor0SBundle.diagonalInvMetric μ))
    (hμ_nonneg : forall i : Idx, 0 <= μ i)
    (hμ_le : forall i : Idx, μ i <= C)
    (A : Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 3 A) <=
      Real.sqrt (C ^ 3) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 3 A) := by
  have hsq :
      Tensor0SBundle.normSq0S (I := I) h x 3 A <=
        C ^ 3 * Tensor0SBundle.normSq0S (I := I) g x 3 A := by
    simpa using
      Tensor0SBundle.normSq0S_diag_le
        (I := I) (g := g) (h := h) (x := x) (s := 3)
        basis μ C hginv hhinv hμ_nonneg hμ_le A
  calc
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 3 A)
        <= Real.sqrt
          (C ^ 3 * Tensor0SBundle.normSq0S (I := I) g x 3 A) :=
          Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (C ^ 3) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 3 A) := by
          rw [Real.sqrt_mul (pow_nonneg hC 3)]







omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem exists_diagInv_of_metricUniformEquivalentOn
    {K : Set M} {g h : SmoothRiemannianMetric I M} {C : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K g h C)
    {x : M} (hx : x ∈ K) :
    exists
      μ : Fin (Module.finrank Real (TangentSpace I x)) -> Real,
    exists
      basis :
        Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
          (TangentSpace I x),
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x basis
        (Tensor0SBundle.identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I x)))) ∧
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis
        (Tensor0SBundle.diagonalInvMetric μ) ∧
      (forall i : Fin (Module.finrank Real (TangentSpace I x)), 0 <= μ i) ∧
      (forall i : Fin (Module.finrank Real (TangentSpace I x)), μ i <= C) := by
  classical
  let D := (Tensor0SBundle.tangentMetricData (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _
      D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let T : TangentSpace I x →ₗ[Real] TangentSpace I x :=
    ((Tensor0SBundle.tangentFlatEquiv (I := I) g x).symm.toLinearMap).comp
      (Tensor0SBundle.tangentFlatEquiv (I := I) h x).toLinearMap
  have hTg (X Y : TangentSpace I x) :
      g.inner x (T X) Y = h.inner x X Y := by
    change (Tensor0SBundle.tangentFlatEquiv (I := I) g x
        ((Tensor0SBundle.tangentFlatEquiv (I := I) g x).symm
          ((Tensor0SBundle.tangentFlatEquiv (I := I) h x) X))) Y =
      h.inner x X Y
    rw [(Tensor0SBundle.tangentFlatEquiv (I := I) g x).apply_symm_apply]
    rfl
  have hT : T.IsSymmetric := by
    intro X Y
    rw [Tensor0SBundle.MetricFiberData.toCore_inner D (T X) Y,
      Tensor0SBundle.MetricFiberData.toCore_inner D X (T Y)]
    calc
      g.inner x (T X) Y = h.inner x X Y := hTg X Y
      _ = h.inner x Y X := h.symm x X Y
      _ = g.inner x (T Y) X := (hTg Y X).symm
      _ = g.inner x X (T Y) := g.symm x (T Y) X
  let n := Module.finrank Real (TangentSpace I x)
  have hn : Module.finrank Real (TangentSpace I x) = n := rfl
  let ob := hT.eigenvectorBasis hn
  let basis : Module.Basis (Fin n) Real (TangentSpace I x) := ob.toBasis
  let lam : Fin n -> Real := fun i => hT.eigenvalues hn i
  let μ : Fin n -> Real := fun i => (lam i)⁻¹
  have hg_orth :
      forall i j : Fin n,
        g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
    intro i j
    have hij := ob.inner_eq_ite i j
    have hinner :
        Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
      Tensor0SBundle.MetricFiberData.toCore_inner D (ob i) (ob j)
    simpa [basis, Tensor0SBundle.MetricFiberData.inner,
      Tensor0SBundle.tangentMetricData] using hinner.symm.trans hij
  have hT_eig (i : Fin n) :
      T (basis i) = lam i • basis i := by
    simpa [basis, lam, ob] using
      hT.apply_eigenvectorBasis hn i
  have hh_diag :
      forall i j : Fin n,
        h.inner x (basis i) (basis j) = if i = j then lam i else 0 := by
    intro i j
    calc
      h.inner x (basis i) (basis j) =
          g.inner x (T (basis i)) (basis j) := (hTg (basis i) (basis j)).symm
      _ = g.inner x (lam i • basis i) (basis j) := by rw [hT_eig i]
      _ = if i = j then lam i else 0 := by
          by_cases hij : i = j
          · simp [hij, hg_orth]
          · simp [hij, hg_orth]
  have hginv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x basis
        (Tensor0SBundle.identityInvMetric (Idx := Fin n)) := by
    intro i j
    constructor
    · simp [Tensor0SBundle.identityInvMetric,
        Tensor0SBundle.diagonalInvMetric, hg_orth]
    · simp [Tensor0SBundle.identityInvMetric,
        Tensor0SBundle.diagonalInvMetric, hg_orth]
  have hlam_pos : forall i : Fin n, 0 < lam i := by
    intro i
    have hne : basis i ≠ 0 := by
      simpa [basis] using ob.orthonormal.ne_zero i
    have hpos : 0 < h.inner x (basis i) (basis i) := h.pos x (basis i) hne
    have hii := hh_diag i i
    rw [hii] at hpos
    simpa using hpos
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hEq.1
  have hlam_lower : forall i : Fin n, C⁻¹ <= lam i := by
    intro i
    have hlow := (hEq.2 x hx (basis i)).1
    have hgii := hg_orth i i
    have hhii := hh_diag i i
    simpa [hgii, hhii] using hlow
  have hμ_nonneg : forall i : Fin n, 0 <= μ i := by
    intro i
    exact le_of_lt (inv_pos.mpr (hlam_pos i))
  have hμ_le : forall i : Fin n, μ i <= C := by
    intro i
    have h :=
      (one_div_le (hlam_pos i) hC_pos).mpr (by
        simpa [one_div] using hlam_lower i)
    simpa [μ, one_div] using h
  have hhinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.diagonalInvMetric μ) := by
    intro i j
    have hμlam (i : Fin n) : μ i * lam i = 1 := by
      simpa [μ] using inv_mul_cancel₀ (ne_of_gt (hlam_pos i))
    have hlamμ (i : Fin n) : lam i * μ i = 1 := by
      simpa [μ] using mul_inv_cancel₀ (ne_of_gt (hlam_pos i))
    constructor
    · rw [Finset.sum_eq_single i]
      · by_cases hij : i = j
        · subst j
          simp [Tensor0SBundle.diagonalInvMetric, hh_diag, hμlam]
        · simp [Tensor0SBundle.diagonalInvMetric, hh_diag, hij]
      · intro k _ hk
        simp [Tensor0SBundle.diagonalInvMetric, Ne.symm hk]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    · rw [Finset.sum_eq_single j]
      · by_cases hij : i = j
        · subst j
          simp [Tensor0SBundle.diagonalInvMetric, hh_diag, hlamμ]
        · simp [Tensor0SBundle.diagonalInvMetric, hh_diag, hij]
      · intro k _ hk
        simp [Tensor0SBundle.diagonalInvMetric, hk]
      · intro hj
        exact False.elim (hj (Finset.mem_univ j))
  exact ⟨μ, basis, hginv, hhinv, hμ_nonneg, hμ_le⟩



omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem metricUniformEquivalentOn_symm
    {K : Set M} {g h : SmoothRiemannianMetric I M} {C : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K g h C) :
    MetricUniformEquivalentOn (I := I) K h g C := by
  constructor
  · exact hEq.1
  · intro x hx v
    have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hEq.1
    have hC_nonneg : 0 <= C := le_of_lt hC_pos
    have hCinv_nonneg : 0 <= C⁻¹ := inv_nonneg.mpr hC_nonneg
    have hlow := (hEq.2 x hx v).1
    have hhigh := (hEq.2 x hx v).2
    constructor
    · calc
        C⁻¹ * h.inner x v v <= C⁻¹ * (C * g.inner x v v) :=
          mul_le_mul_of_nonneg_left hhigh hCinv_nonneg
        _ = g.inner x v v := by
          field_simp [hC_pos.ne']
    · calc
        g.inner x v v = C * (C⁻¹ * g.inner x v v) := by
          field_simp [hC_pos.ne']
        _ <= C * h.inner x v v :=
          mul_le_mul_of_nonneg_left hlow hC_nonneg





omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem sqrt_normSq0S_three_le_of_metricUniformEquivalentOn
    {K : Set M} {g h : SmoothRiemannianMetric I M} {C : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K g h C)
    {x : M} (hx : x ∈ K)
    (A : Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 3 A) <=
      Real.sqrt (C ^ 3) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 3 A) := by
  obtain ⟨μ, basis, hginv, hhinv, hμ_nonneg, hμ_le⟩ :=
    exists_diagInv_of_metricUniformEquivalentOn
      (I := I) (K := K) (g := g) (h := h) (C := C) hEq hx
  exact
    sqrt_normSq0S_three_diag_le
      (I := I) (g := g) (h := h) (x := x)
      (hC := le_trans zero_le_one hEq.1) basis μ C
      hginv hhinv hμ_nonneg hμ_le A




omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem sqrt_normSq0S_three_le_of_metricUniformEquivalentOn_symm
    {K : Set M} {g h : SmoothRiemannianMetric I M} {C : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K g h C)
    {x : M} (hx : x ∈ K)
    (A : Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 3 A) <=
      Real.sqrt (C ^ 3) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 3 A) :=
  sqrt_normSq0S_three_le_of_metricUniformEquivalentOn
    (I := I) (K := K) (g := h) (h := g) (C := C)
    (metricUniformEquivalentOn_symm (I := I) hEq) hx A






omit [SigmaCompactSpace M] in
theorem covOne_le_connDiff
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u K : Set M}
    (g : Real -> SmoothRiemannianMetric I M)
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (hxK : x ∈ K)
    (base var C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K (g base) (g var) C)
    (hinv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (g var) gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0)
    (hmetric_id : ∀ i j : Idx,
      (g var).inner x (frame i x) (frame j x) =
        if i = j then 1 else 0) :
    metricCovDerivNorm (I := I) 1 (g var) (g base) x <=
      Real.sqrt (C ^ 3) *
        (2 *
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := g var) (x := x) 1 2
              (Tensor0SBundle.connectionDifferenceTensorAt
                (I := I)
                ((lcMetricFamily (I := I) (M := M) g).connection var)
                ((lcMetricFamily (I := I) (M := M) g).connection base) x))) := by
  let A :=
    metricCovDeriv (I := I) (g var) (g base) 1 x
  have hcompare :
      metricCovDerivNorm (I := I) 1 (g var) (g base) x <=
        Real.sqrt (C ^ 3) *
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) (g var) x 3 A) := by
    simpa [metricCovDerivNorm, A] using
      sqrt_normSq0S_three_le_of_metricUniformEquivalentOn_symm
        (I := I) (K := K) (g := g base) (h := g var) (C := C)
        hEq hxK A
  have hgamma :=
    (metricGammaEquiv
      (I := I) g gInv frame hframe hu hx base var
      hinv hinv_id hmetric_id).2
  exact le_trans hcompare
    (mul_le_mul_of_nonneg_left hgamma (Real.sqrt_nonneg _))






omit [SigmaCompactSpace M] in
theorem connDiff_le_covOne
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u K : Set M}
    (g : Real -> SmoothRiemannianMetric I M)
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (hxK : x ∈ K)
    (base var C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K (g base) (g var) C)
    (hinv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (g var) gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0)
    (hmetric_id : ∀ i j : Idx,
      (g var).inner x (frame i x) (frame j x) =
        if i = j then 1 else 0) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g var) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            ((lcMetricFamily (I := I) (M := M) g).connection var)
            ((lcMetricFamily (I := I) (M := M) g).connection base) x)) <=
      (3 / 2 : Real) *
        (Real.sqrt (C ^ 3) *
          metricCovDerivNorm (I := I) 1 (g var) (g base) x) := by
  let A :=
    metricCovDeriv (I := I) (g var) (g base) 1 x
  have hnorm :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) (g var) x 3 A) <=
        Real.sqrt (C ^ 3) *
          metricCovDerivNorm (I := I) 1 (g var) (g base) x := by
    simpa [metricCovDerivNorm, A] using
      sqrt_normSq0S_three_le_of_metricUniformEquivalentOn
        (I := I) (K := K) (g := g base) (h := g var) (C := C)
        hEq hxK A
  have hgamma :=
    (metricGammaEquiv
      (I := I) g gInv frame hframe hu hx base var
      hinv hinv_id hmetric_id).1
  exact le_trans hgamma
    (mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : Real) <= 3 / 2))



omit [SigmaCompactSpace M] in
theorem covOne_le_diff
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u K : Set M}
    (h gRef : SmoothRiemannianMetric I M)
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (hxK : x ∈ K)
    (C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K gRef h C)
    (hinv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) h gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0)
    (hmetric_id : ∀ i j : Idx,
      h.inner x (frame i x) (frame j x) =
        if i = j then 1 else 0) :
    metricCovDerivNorm (I := I) 1 h gRef x <=
      Real.sqrt (C ^ 3) *
        (2 *
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := h) (x := x) 1 2
              (Tensor0SBundle.connectionDifferenceTensorAt
                (I := I)
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x))) := by
  let pair : Real -> SmoothRiemannianMetric I M :=
    fun s => if s = (0 : Real) then gRef else h
  have hEq' :
      MetricUniformEquivalentOn (I := I) K (pair 0) (pair 1) C := by
    simpa [pair] using hEq
  have hinv' :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (pair 1) gInv frame := by
    simpa [pair] using hinv
  have hmetric_id' : ∀ i j : Idx,
      (pair 1).inner x (frame i x) (frame j x) =
        if i = j then 1 else 0 := by
    simpa [pair] using hmetric_id
  have hmain :=
    covOne_le_connDiff
      (I := I) (K := K) (u := u) pair gInv frame hframe hu hx hxK
      (base := 0) (var := 1) (C := C)
      hEq' hinv' hinv_id hmetric_id'
  simpa [pair, lcMetricFamily] using hmain



omit [SigmaCompactSpace M] in
theorem diff_le_covOne
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u K : Set M}
    (h gRef : SmoothRiemannianMetric I M)
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (hxK : x ∈ K)
    (C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K gRef h C)
    (hinv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) h gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0)
    (hmetric_id : ∀ i j : Idx,
      h.inner x (frame i x) (frame j x) =
        if i = j then 1 else 0) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)) <=
      (3 / 2 : Real) *
        (Real.sqrt (C ^ 3) *
          metricCovDerivNorm (I := I) 1 h gRef x) := by
  let pair : Real -> SmoothRiemannianMetric I M :=
    fun s => if s = (0 : Real) then gRef else h
  have hEq' :
      MetricUniformEquivalentOn (I := I) K (pair 0) (pair 1) C := by
    simpa [pair] using hEq
  have hinv' :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (pair 1) gInv frame := by
    simpa [pair] using hinv
  have hmetric_id' : ∀ i j : Idx,
      (pair 1).inner x (frame i x) (frame j x) =
        if i = j then 1 else 0 := by
    simpa [pair] using hmetric_id
  have hmain :=
    connDiff_le_covOne
      (I := I) (K := K) (u := u) pair gInv frame hframe hu hx hxK
      (base := 0) (var := 1) (C := C)
      hEq' hinv' hinv_id hmetric_id'
  simpa [pair, lcMetricFamily] using hmain




omit [T2Space M] [SigmaCompactSpace M] in
theorem diffNormSq_eq_l2
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (h gRef : SmoothRiemannianMetric I M)
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hinv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) h gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0) :
    Tensor0SBundle.normSqRS
        (I := I) (g := h) (x := x) 1 2
        (Tensor0SBundle.connectionDifferenceTensorAt
          (I := I)
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x) =
      DifferentialGeometry.Integral.Connection.componentL2Sq3
        (fun a b e : Idx =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x a b e -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
              frame hframe x a b e) := by
  let pair : Real -> SmoothRiemannianMetric I M :=
    fun s => if s = (0 : Real) then gRef else h
  have hinv' :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) ((lcMetricFamily (I := I) (M := M) pair).metric 1)
        gInv frame := by
    simpa [pair, lcMetricFamily] using hinv
  have hmain :=
    DifferentialGeometry.Integral.Connection.normSqRS_connDiff_eq_componentL2Sq3
      (I := I) (G := lcMetricFamily (I := I) (M := M) pair)
      gInv frame hframe hu hx
      (base := 0) (var := 1) hinv' hinv_id
  simpa [pair, lcMetricFamily] using hmain




omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem normSqRS12_eq_l2
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (A : Tensor0SBundle.TensorRSSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 2 x) :
    Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2 A =
      DifferentialGeometry.Integral.Connection.componentL2Sq3
        (fun a b e : Idx =>
          Tensor0SBundle.componentRS (I := I) basis A
            (fun _ : Fin 1 => e)
            (fun q : Fin 2 => if q = 0 then a else b)) := by
  classical
  rw [Tensor0SBundle.normSqRS_one_two_identity_eq_sum
    (I := I) h x basis hinv A]
  rw [DifferentialGeometry.Integral.Connection.componentL2Sq3_eq_sum_upper_first]
  simp only [Tensor0SBundle.componentRS_apply_gen, Tensor0SBundle.componentRS_apply]





omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem applyCons3
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (A : Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (a : Idx) (tail : Fin 2 -> Idx) :
    A (fun q : Fin 3 => basis ((Fin.cons a tail : Fin 3 -> Idx) q)) =
      A (Fin.cons (basis a) (fun q : Fin 2 => basis (tail q))) := by
  have hslots :
      (fun q : Fin 3 => basis ((Fin.cons a tail : Fin 3 -> Idx) q)) =
        Fin.cons (basis a) (fun q : Fin 2 => basis (tail q)) := by
    funext q
    fin_cases q <;> rfl
  rw [hslots]

private theorem sub_swap_of_sub_eq_sub
    {V : Type*} [AddCommGroup V] {a b c d : V}
    (h : a - b = c - d) :
    a - c = b - d := by
  have ha : a = (c - d) + b := sub_eq_iff_eq_add.mp h
  calc
    a - c = ((c - d) + b) - c := by rw [ha]
    _ = b - d := by abel



omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem coord_eq_inner_id
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (a : Idx) (V : TangentSpace I x) :
    basis.coord a V = h.inner x (basis a) V := by
  have hcoord :=
    DifferentialGeometry.Integral.Connection.coordinate_basis_coord_eq_sum_inv_metric_inner
      (I := I) h basis (Tensor0SBundle.identityInvMetric (Idx := Idx))
      hinv a V
  simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric]
    using hcoord








omit [SigmaCompactSpace M] in
theorem covOneCompDiff
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (a b c : Idx) :
    Tensor0SBundle.component0S (I := I) basis
        (metricCovDeriv (I := I) h gRef 1 x)
        (Fin.cons a (fun q : Fin 2 => if q = 0 then b else c)) =
      Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
          (fun _ : Fin 1 => b)
          (fun q : Fin 2 => if q = 0 then a else c) +
        Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
          (fun _ : Fin 1 => c)
          (fun q : Fin 2 => if q = 0 then a else b) := by
  classical
  let covH := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h
  let covG := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef
  let alpha := Tensor0SBundle.metricTensorField (I := I) h
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis a)).choose
  let Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis b)).choose
  let Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis c)).choose
  have hX : X x = basis a :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis a)).choose_spec
  have hY : Y x = basis b :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis b)).choose_spec
  have hZ : Z x = basis c :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis c)).choose_spec
  have hleft :
      Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) h gRef 1 x)
          (Fin.cons a (fun q : Fin 2 => if q = 0 then b else c)) =
        Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 covG X alpha x
          (fun q : Fin 2 => if q = 0 then Y x else Z x) := by
    rw [Tensor0SBundle.component0S_apply]
    rw [applyCons3 (I := I) basis
      (metricCovDeriv (I := I) h gRef 1 x)
      a (fun q : Fin 2 => if q = 0 then b else c)]
    have htail :
        (fun q : Fin 2 => basis (if q = 0 then b else c)) =
          (fun q : Fin 2 => if q = 0 then Y x else Z x) := by
      funext q
      fin_cases q <;> simp [hY, hZ]
    rw [← hX, htail]
    simpa [covG, alpha] using
      metricCovDeriv_one_apply_section (I := I) h gRef X x
        (fun q : Fin 2 => if q = 0 then Y x else Z x)
  have hnabla :
      Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 covG X alpha x
          (fun q : Fin 2 => if q = 0 then Y x else Z x) =
        alpha x
          (fun q : Fin 2 =>
            if q = 0 then
              ((CovariantDerivative.difference covH covG x) (Y x)) (X x)
            else Z x) +
          alpha x
            (fun q : Fin 2 =>
              if q = 0 then Y x
              else ((CovariantDerivative.difference covH covG x) (Z x)) (X x)) := by
    have hsub :=
      Tensor0SBundle.nabla0SFun_sub_cov_two
        (I := I) covH covG X Y Z alpha x
    have hzero :
        Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) 2 covH X alpha x = 0 := by
      simpa [covH, alpha] using
        Tensor0SBundle.nabla_metric_zero (I := I) covH h
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
            (I := I) h) X x
    let slots : Fin 2 -> TangentSpace I x :=
      fun q : Fin 2 => if q = 0 then Y x else Z x
    let N : Real :=
      Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 covG X alpha x slots
    let T1 : Real :=
      alpha x
        (fun q : Fin 2 =>
          if q = 0 then
            ((CovariantDerivative.difference covH covG x) (Y x)) (X x)
          else Z x)
    let T2 : Real :=
      alpha x
        (fun q : Fin 2 =>
          if q = 0 then Y x
          else ((CovariantDerivative.difference covH covG x) (Z x)) (X x))
    have hraw : 0 - N = -(T1 + T2) := by
      rw [hzero] at hsub
      let NG := Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 covG X alpha x
      change ((0 - NG) slots = _) at hsub
      rw [show (0 - NG) = 0 + -NG by exact sub_eq_add_neg 0 NG,
        Tensor0SBundle.Tensor0SSpace.add_apply,
        Tensor0SBundle.Tensor0SSpace.zero_apply, zero_add,
        show -NG = (-1 : Real) • NG by exact (neg_one_smul Real NG).symm,
        Tensor0SBundle.Tensor0SSpace.smul_apply, neg_one_smul] at hsub
      simpa [slots, N, T1, T2, NG] using hsub
    have hN : N = T1 + T2 := by
      linarith
    simpa [slots, N, T1, T2] using hN
  have hterm1 :
      alpha x
          (fun q : Fin 2 =>
            if q = 0 then
              ((CovariantDerivative.difference covH covG x) (Y x)) (X x)
            else Z x) =
        Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt (I := I) covH covG x)
          (fun _ : Fin 1 => c)
          (fun q : Fin 2 => if q = 0 then a else b) := by
    rw [componentRS_eq_gen, Tensor0SBundle.componentRS_connectionDifferenceTensorAt]
    rw [coord_eq_inner_id (I := I) h basis hinv c]
    simp [alpha, Tensor0SBundle.metricTensorField_apply, hX, hY, hZ]
    exact h.symm x
      (((CovariantDerivative.difference covH covG x) (basis b)) (basis a))
      (basis c)
  have hterm2 :
      alpha x
          (fun q : Fin 2 =>
            if q = 0 then Y x
            else ((CovariantDerivative.difference covH covG x) (Z x)) (X x)) =
        Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt (I := I) covH covG x)
          (fun _ : Fin 1 => b)
          (fun q : Fin 2 => if q = 0 then a else c) := by
    rw [componentRS_eq_gen, Tensor0SBundle.componentRS_connectionDifferenceTensorAt]
    rw [coord_eq_inner_id (I := I) h basis hinv b]
    simp [alpha, Tensor0SBundle.metricTensorField_apply, hX, hY, hZ]
  calc
    Tensor0SBundle.component0S (I := I) basis
        (metricCovDeriv (I := I) h gRef 1 x)
        (Fin.cons a (fun q : Fin 2 => if q = 0 then b else c)) =
      Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 covG X alpha x
          (fun q : Fin 2 => if q = 0 then Y x else Z x) := hleft
    _ = alpha x
          (fun q : Fin 2 =>
            if q = 0 then
              ((CovariantDerivative.difference covH covG x) (Y x)) (X x)
            else Z x) +
          alpha x
            (fun q : Fin 2 =>
              if q = 0 then Y x
              else ((CovariantDerivative.difference covH covG x) (Z x)) (X x)) := hnabla
    _ =
      Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
          (fun _ : Fin 1 => b)
          (fun q : Fin 2 => if q = 0 then a else c) +
        Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
          (fun _ : Fin 1 => c)
          (fun q : Fin 2 => if q = 0 then a else b) := by
        rw [hterm1, hterm2]
        simp [covH, covG, add_comm]




omit [SigmaCompactSpace M] in
theorem connDiffBasisSymm
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (a b : Idx) :
    ((CovariantDerivative.difference
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
        (basis b)) (basis a) =
      ((CovariantDerivative.difference
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
        (basis a)) (basis b) := by
  classical
  let covH := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h
  let covG := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis a)).choose
  let Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis b)).choose
  have hX : X x = basis a :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis a)).choose_spec
  have hY : Y x = basis b :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis b)).choose_spec
  have hXd :
      MDiffAt (T% (fun p : M => X p)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYd :
      MDiffAt (T% (fun p : M => Y p)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hdY :
      ((CovariantDerivative.difference covH covG x) (Y x)) (X x) =
        ((covH (fun p : M => Y p) x) (X x)) -
          ((covG (fun p : M => Y p) x) (X x)) := by
    have hdiff :=
      IsCovariantDerivativeOn.difference_apply
        (hcov := covH.isCovariantDerivativeOnUniv)
        (hcov' := covG.isCovariantDerivativeOnUniv)
        (σ := fun p : M => Y p) (x := x) (hx := by trivial) hYd
    exact congrArg (fun L : TangentSpace I x →L[Real] TangentSpace I x =>
      L (X x)) hdiff
  have hdX :
      ((CovariantDerivative.difference covH covG x) (X x)) (Y x) =
        ((covH (fun p : M => X p) x) (Y x)) -
          ((covG (fun p : M => X p) x) (Y x)) := by
    have hdiff :=
      IsCovariantDerivativeOn.difference_apply
        (hcov := covH.isCovariantDerivativeOnUniv)
        (hcov' := covG.isCovariantDerivativeOnUniv)
        (σ := fun p : M => X p) (x := x) (hx := by trivial) hXd
    exact congrArg (fun L : TangentSpace I x →L[Real] TangentSpace I x =>
      L (Y x)) hdiff
  have htorH :=
    DifferentialGeometry.Integral.Connection.torsion_free_apply (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isTorsionFree
        (I := I) h)
      (X := fun p : M => X p) (Y := fun p : M => Y p) hXd hYd
  have htorG :=
    DifferentialGeometry.Integral.Connection.torsion_free_apply (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isTorsionFree
        (I := I) gRef)
      (X := fun p : M => X p) (Y := fun p : M => Y p) hXd hYd
  have hsub :
      ((covH (fun p : M => Y p) x) (X x)) -
          ((covG (fun p : M => Y p) x) (X x)) =
        ((covH (fun p : M => X p) x) (Y x)) -
          ((covG (fun p : M => X p) x) (Y x)) := by
    have htor : ((covH (fun p : M => Y p) x) (X x)) -
          ((covH (fun p : M => X p) x) (Y x)) =
        ((covG (fun p : M => Y p) x) (X x)) -
          ((covG (fun p : M => X p) x) (Y x)) := by
      rw [htorH, htorG]
    exact sub_swap_of_sub_eq_sub htor
  calc
    ((CovariantDerivative.difference
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
        (basis b)) (basis a)
        = ((CovariantDerivative.difference covH covG x) (Y x)) (X x) := by
          simp [covH, covG, hX, hY]
    _ = ((covH (fun p : M => Y p) x) (X x)) -
          ((covG (fun p : M => Y p) x) (X x)) := hdY
    _ = ((covH (fun p : M => X p) x) (Y x)) -
          ((covG (fun p : M => X p) x) (Y x)) := hsub
    _ = ((CovariantDerivative.difference covH covG x) (X x)) (Y x) := hdX.symm
    _ = ((CovariantDerivative.difference
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
        (basis a)) (basis b) := by
          simp [covH, covG, hX, hY]


omit [SigmaCompactSpace M] in
theorem connDiffCompSymm
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (a b e : Idx) :
    Tensor0SBundle.componentRS (I := I) basis
        (Tensor0SBundle.connectionDifferenceTensorAt
          (I := I)
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
        (fun _ : Fin 1 => e)
        (fun q : Fin 2 => if q = 0 then a else b) =
      Tensor0SBundle.componentRS (I := I) basis
        (Tensor0SBundle.connectionDifferenceTensorAt
          (I := I)
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
        (fun _ : Fin 1 => e)
        (fun q : Fin 2 => if q = 0 then b else a) := by
  rw [componentRS_eq_gen, Tensor0SBundle.componentRS_connectionDifferenceTensorAt]
  rw [componentRS_eq_gen, Tensor0SBundle.componentRS_connectionDifferenceTensorAt]
  exact congrArg (basis.coord e)
    (connDiffBasisSymm (I := I) h gRef basis a b)








omit [SigmaCompactSpace M] in
theorem covOne_le_diff_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hcombo :
      ∀ a b c : Idx,
        Tensor0SBundle.component0S (I := I) basis
            (metricCovDeriv (I := I) h gRef 1 x)
            (Fin.cons a (fun q : Fin 2 => if q = 0 then b else c)) =
          Tensor0SBundle.componentRS (I := I) basis
              (Tensor0SBundle.connectionDifferenceTensorAt
                (I := I)
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
              (fun _ : Fin 1 => b)
              (fun q : Fin 2 => if q = 0 then a else c) +
            Tensor0SBundle.componentRS (I := I) basis
              (Tensor0SBundle.connectionDifferenceTensorAt
                (I := I)
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
              (fun _ : Fin 1 => c)
              (fun q : Fin 2 => if q = 0 then a else b)) :
    Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) h x 3
          (metricCovDeriv (I := I) h gRef 1 x)) <=
      2 *
        Real.sqrt
          (Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2
            (Tensor0SBundle.connectionDifferenceTensorAt
              (I := I)
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)) := by
  classical
  let A0 :=
    metricCovDeriv (I := I) h gRef 1 x
  let D0 :=
    Tensor0SBundle.connectionDifferenceTensorAt
      (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x
  let A : Idx -> Idx -> Idx -> Real :=
    fun a b c =>
      Tensor0SBundle.component0S (I := I) basis A0
        (Fin.cons a (fun q : Fin 2 => if q = 0 then b else c))
  let D : Idx -> Idx -> Idx -> Real :=
    fun a b e =>
      Tensor0SBundle.componentRS (I := I) basis D0
        (fun _ : Fin 1 => e)
        (fun q : Fin 2 => if q = 0 then a else b)
  have hA :
      Tensor0SBundle.normSq0S (I := I) h x 3 A0 =
        DifferentialGeometry.Integral.Connection.componentL2Sq3 A := by
    exact
      DifferentialGeometry.Integral.Connection.normSq0S_three_eq_componentL2Sq3_of_components
        (I := I) h x basis hinv A0 A (by intro d a b; rfl)
  have hD :
      Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2 D0 =
        DifferentialGeometry.Integral.Connection.componentL2Sq3 D := by
    exact normSqRS12_eq_l2 (I := I) h basis hinv D0
  have hmain :
      Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 A) <=
        2 * Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 D) := by
    exact DifferentialGeometry.Integral.Connection.metricCov_l2_le (Idx := Idx) A D (by
      intro a b c
      simpa [A, D, add_comm, add_left_comm, add_assoc] using hcombo a b c)
  rw [hA, hD]
  exact hmain



omit [SigmaCompactSpace M] in
theorem covOne_le_diff_basis_lc
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) h x 3
          (metricCovDeriv (I := I) h gRef 1 x)) <=
      2 *
        Real.sqrt
          (Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2
            (Tensor0SBundle.connectionDifferenceTensorAt
              (I := I)
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)) := by
  exact covOne_le_diff_basis (I := I) h gRef basis hinv
    (fun a b c => covOneCompDiff (I := I) h gRef basis hinv a b c)







omit [SigmaCompactSpace M] in
theorem diff_le_covOne_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hcombo :
      ∀ a b e : Idx,
        2 *
          Tensor0SBundle.componentRS (I := I) basis
            (Tensor0SBundle.connectionDifferenceTensorAt
              (I := I)
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
            (fun _ : Fin 1 => e)
            (fun q : Fin 2 => if q = 0 then a else b) =
          Tensor0SBundle.component0S (I := I) basis
              (metricCovDeriv (I := I) h gRef 1 x)
              (Fin.cons a (fun q : Fin 2 => if q = 0 then b else e)) +
            Tensor0SBundle.component0S (I := I) basis
              (metricCovDeriv (I := I) h gRef 1 x)
              (Fin.cons b (fun q : Fin 2 => if q = 0 then a else e)) -
            Tensor0SBundle.component0S (I := I) basis
              (metricCovDeriv (I := I) h gRef 1 x)
              (Fin.cons e (fun q : Fin 2 => if q = 0 then a else b))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)) <=
      (3 / 2 : Real) *
        Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) h x 3
            (metricCovDeriv (I := I) h gRef 1 x)) := by
  classical
  let A0 :=
    metricCovDeriv (I := I) h gRef 1 x
  let D0 :=
    Tensor0SBundle.connectionDifferenceTensorAt
      (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x
  let A : Idx -> Idx -> Idx -> Real :=
    fun a b c =>
      Tensor0SBundle.component0S (I := I) basis A0
        (Fin.cons a (fun q : Fin 2 => if q = 0 then b else c))
  let D : Idx -> Idx -> Idx -> Real :=
    fun a b e =>
      Tensor0SBundle.componentRS (I := I) basis D0
        (fun _ : Fin 1 => e)
        (fun q : Fin 2 => if q = 0 then a else b)
  have hA :
      Tensor0SBundle.normSq0S (I := I) h x 3 A0 =
        DifferentialGeometry.Integral.Connection.componentL2Sq3 A := by
    exact
      DifferentialGeometry.Integral.Connection.normSq0S_three_eq_componentL2Sq3_of_components
        (I := I) h x basis hinv A0 A (by intro d a b; rfl)
  have hD :
      Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2 D0 =
        DifferentialGeometry.Integral.Connection.componentL2Sq3 D := by
    exact normSqRS12_eq_l2 (I := I) h basis hinv D0
  have hmain :
      Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 D) <=
        (3 / 2 : Real) * Real.sqrt (DifferentialGeometry.Integral.Connection.componentL2Sq3 A) := by
    exact DifferentialGeometry.Integral.Connection.gammaSub_l2_le (Idx := Idx) A D (by
      intro a b e
      simpa [A, D, add_comm, add_left_comm, add_assoc] using hcombo a b e)
  rw [hA, hD]
  exact hmain




omit [SigmaCompactSpace M] in
theorem connDiffCompEq
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (a b e : Idx) :
    2 *
        Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
          (fun _ : Fin 1 => e)
          (fun q : Fin 2 => if q = 0 then a else b) =
      Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) h gRef 1 x)
          (Fin.cons a (fun q : Fin 2 => if q = 0 then b else e)) +
        Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) h gRef 1 x)
          (Fin.cons b (fun q : Fin 2 => if q = 0 then a else e)) -
        Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) h gRef 1 x)
          (Fin.cons e (fun q : Fin 2 => if q = 0 then a else b)) := by
  classical
  let A0 := metricCovDeriv (I := I) h gRef 1 x
  let D0 :=
    Tensor0SBundle.connectionDifferenceTensorAt
      (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x
  let A : Idx -> Idx -> Idx -> Real := fun i j k =>
    Tensor0SBundle.component0S (I := I) basis A0
      (Fin.cons i (fun q : Fin 2 => if q = 0 then j else k))
  let D : Idx -> Idx -> Idx -> Real := fun i j k =>
    Tensor0SBundle.componentRS (I := I) basis D0
      (fun _ : Fin 1 => k)
      (fun q : Fin 2 => if q = 0 then i else j)
  have hAabe : A a b e = D a e b + D a b e := by
    simpa [A, D, A0, D0] using
      covOneCompDiff (I := I) h gRef basis hinv a b e
  have hAbae : A b a e = D b e a + D b a e := by
    simpa [A, D, A0, D0] using
      covOneCompDiff (I := I) h gRef basis hinv b a e
  have hAeab : A e a b = D e b a + D e a b := by
    simpa [A, D, A0, D0] using
      covOneCompDiff (I := I) h gRef basis hinv e a b
  have hsym_ba : D b a e = D a b e := by
    simpa [D, D0] using
      connDiffCompSymm (I := I) h gRef basis b a e
  have hsym_ae : D a e b = D e a b := by
    simpa [D, D0] using
      connDiffCompSymm (I := I) h gRef basis a e b
  have hsym_be : D b e a = D e b a := by
    simpa [D, D0] using
      connDiffCompSymm (I := I) h gRef basis b e a
  change 2 * D a b e = A a b e + A b a e - A e a b
  calc
    2 * D a b e = D a b e + D a b e := by ring
    _ = (D a e b + D a b e) + (D b e a + D b a e) -
        (D e b a + D e a b) := by
          rw [hsym_ba, hsym_ae, hsym_be]
          ring
    _ = A a b e + A b a e - A e a b := by
          rw [hAabe, hAbae, hAeab]



omit [SigmaCompactSpace M] in
theorem diff_le_covOne_basis_lc
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)) <=
      (3 / 2 : Real) *
        Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) h x 3
            (metricCovDeriv (I := I) h gRef 1 x)) := by
  exact diff_le_covOne_basis (I := I) h gRef basis hinv
    (fun a b e => connDiffCompEq (I := I) h gRef basis hinv a b e)





omit [SigmaCompactSpace M] in
theorem covOne_le_diff_basis_ref
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {K : Set M}
    (h gRef : SmoothRiemannianMetric I M) {x : M} (hxK : x ∈ K)
    (C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K gRef h C)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hcombo :
      ∀ a b c : Idx,
        Tensor0SBundle.component0S (I := I) basis
            (metricCovDeriv (I := I) h gRef 1 x)
            (Fin.cons a (fun q : Fin 2 => if q = 0 then b else c)) =
          Tensor0SBundle.componentRS (I := I) basis
              (Tensor0SBundle.connectionDifferenceTensorAt
                (I := I)
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
              (fun _ : Fin 1 => b)
              (fun q : Fin 2 => if q = 0 then a else c) +
            Tensor0SBundle.componentRS (I := I) basis
              (Tensor0SBundle.connectionDifferenceTensorAt
                (I := I)
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
              (fun _ : Fin 1 => c)
              (fun q : Fin 2 => if q = 0 then a else b)) :
    metricCovDerivNorm (I := I) 1 h gRef x <=
      Real.sqrt (C ^ 3) *
        (2 *
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := h) (x := x) 1 2
              (Tensor0SBundle.connectionDifferenceTensorAt
                (I := I)
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x))) := by
  let A0 :=
    metricCovDeriv (I := I) h gRef 1 x
  have hcompare :
      metricCovDerivNorm (I := I) 1 h gRef x <=
        Real.sqrt (C ^ 3) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 3 A0) := by
    simpa [metricCovDerivNorm, A0] using
      sqrt_normSq0S_three_le_of_metricUniformEquivalentOn_symm
        (I := I) (K := K) (g := gRef) (h := h) (C := C)
        hEq hxK A0
  have hbasis :=
    covOne_le_diff_basis (I := I) h gRef basis hinv hcombo
  exact le_trans hcompare
    (mul_le_mul_of_nonneg_left hbasis (Real.sqrt_nonneg _))



omit [SigmaCompactSpace M] in
theorem covOne_le_diff_basis_ref_lc
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {K : Set M}
    (h gRef : SmoothRiemannianMetric I M) {x : M} (hxK : x ∈ K)
    (C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K gRef h C)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    metricCovDerivNorm (I := I) 1 h gRef x <=
      Real.sqrt (C ^ 3) *
        (2 *
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := h) (x := x) 1 2
              (Tensor0SBundle.connectionDifferenceTensorAt
                (I := I)
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x))) := by
  exact covOne_le_diff_basis_ref (I := I) h gRef hxK C hEq basis hinv
    (fun a b c => covOneCompDiff (I := I) h gRef basis hinv a b c)




omit [SigmaCompactSpace M] in
theorem diff_le_covOne_basis_ref
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {K : Set M}
    (h gRef : SmoothRiemannianMetric I M) {x : M} (hxK : x ∈ K)
    (C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K gRef h C)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hcombo :
      ∀ a b e : Idx,
        2 *
          Tensor0SBundle.componentRS (I := I) basis
            (Tensor0SBundle.connectionDifferenceTensorAt
              (I := I)
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
            (fun _ : Fin 1 => e)
            (fun q : Fin 2 => if q = 0 then a else b) =
          Tensor0SBundle.component0S (I := I) basis
              (metricCovDeriv (I := I) h gRef 1 x)
              (Fin.cons a (fun q : Fin 2 => if q = 0 then b else e)) +
            Tensor0SBundle.component0S (I := I) basis
              (metricCovDeriv (I := I) h gRef 1 x)
              (Fin.cons b (fun q : Fin 2 => if q = 0 then a else e)) -
            Tensor0SBundle.component0S (I := I) basis
              (metricCovDeriv (I := I) h gRef 1 x)
              (Fin.cons e (fun q : Fin 2 => if q = 0 then a else b))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)) <=
      (3 / 2 : Real) *
        (Real.sqrt (C ^ 3) *
          metricCovDerivNorm (I := I) 1 h gRef x) := by
  let A0 :=
    metricCovDeriv (I := I) h gRef 1 x
  have hbasis :=
    diff_le_covOne_basis (I := I) h gRef basis hinv hcombo
  have hnorm :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 3 A0) <=
        Real.sqrt (C ^ 3) *
          metricCovDerivNorm (I := I) 1 h gRef x := by
    simpa [metricCovDerivNorm, A0] using
      sqrt_normSq0S_three_le_of_metricUniformEquivalentOn
        (I := I) (K := K) (g := gRef) (h := h) (C := C)
        hEq hxK A0
  exact le_trans hbasis
    (mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : Real) <= 3 / 2))




omit [SigmaCompactSpace M] in
theorem diff_le_covOne_basis_ref_lc
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {K : Set M}
    (h gRef : SmoothRiemannianMetric I M) {x : M} (hxK : x ∈ K)
    (C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K gRef h C)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)) <=
      (3 / 2 : Real) *
        (Real.sqrt (C ^ 3) *
          metricCovDerivNorm (I := I) 1 h gRef x) := by
  exact diff_le_covOne_basis_ref (I := I) h gRef hxK C hEq basis hinv
    (fun a b e => connDiffCompEq (I := I) h gRef basis hinv a b e)



omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem metricInvBasisId
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (h : SmoothRiemannianMetric I M)
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    {x : M} (hx : x ∈ u)
    (hinv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) h gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0) :
    Tensor0SBundle.MetricInverseInBasis
      (I := I) h x (hframe.toBasisAt hx)
      (Tensor0SBundle.identityInvMetric (Idx := Idx)) := by
  intro i j
  constructor
  · simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric,
      IsLocalFrameOn.toBasisAt_coe, hinv_id] using (hinv x i j).1
  · simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric,
      IsLocalFrameOn.toBasisAt_coe, hinv_id] using (hinv x i j).2








omit [SigmaCompactSpace M] in
theorem covOne_le_christoffel
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u K : Set M}
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (gRef : SmoothRiemannianMetric I M)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (hxK : x ∈ K)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    {a b R Ca Cb : Real}
    (hsub : Set.uIcc a b ⊆ D.carrier)
    (hregular : ∀ s : Real, s ∈ Set.uIcc a b -> s ∈ D.regular)
    (hinv_id :
      ∀ s : Real, s ∈ Set.uIcc a b ->
        ∀ e l : Idx, gInv s x e l = if e = l then 1 else 0)
    (hevol :
      DifferentialGeometry.PDE.RicciFlow.ChristoffelEvolutionEquationInFrameOn
        (I := I) S gInv frame (localFrameOneOfInf (I := I) frame hframe)
        nablaRic)
    (hRic :
      ∀ s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt
          (DifferentialGeometry.Integral.Connection.componentL2Sq3
            (fun i j k : Idx => nablaRic s x i j k)) <= R)
    (hEq_b :
      MetricUniformEquivalentOn (I := I) K gRef (S.family.metric b) Cb)
    (hinv_b :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (S.family.metric b) (gInv b) frame)
    (hEq_a :
      MetricUniformEquivalentOn (I := I) K gRef (S.family.metric a) Ca)
    (hinv_a :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (S.family.metric a) (gInv a) frame) :
    metricCovDerivNorm (I := I) 1 (S.family.metric b) gRef x <=
      Real.sqrt (Cb ^ 3) *
        (2 *
          (3 * R * |b - a| +
            (3 / 2 : Real) *
              (Real.sqrt (Ca ^ 3) *
                metricCovDerivNorm (I := I) 1 (S.family.metric a) gRef x))) := by
  let hframe1 := localFrameOneOfInf (I := I) frame hframe
  let baseGamma : Idx -> Idx -> Idx -> Real :=
    fun i j k =>
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
        frame hframe1 x i j k
  have hgamma :=
    gammaL2_le_of_christoffel
      (I := I) S gInv frame hframe1 nablaRic hx baseGamma
      hsub hregular hinv_id hevol hRic
  have hsq_b_raw :=
    diffNormSq_eq_l2
      (I := I) (h := S.family.metric b) (gRef := gRef)
      (gInv := gInv b) frame hframe1 hu hx hinv_b
      (hinv_id b Set.right_mem_uIcc)
  have hsq_b :
      Tensor0SBundle.normSqRS
          (I := I) (g := S.family.metric b) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric
              (I := I) (S.family.metric b))
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x) =
        DifferentialGeometry.Integral.Connection.componentL2Sq3
          (fun i j k : Idx =>
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (S.family.connection b) frame hframe1 x i j k -
              baseGamma i j k) := by
    simpa [baseGamma, DifferentialGeometry.PDE.RicciFlow.SolutionOn.family,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.connection] using hsq_b_raw
  have hsq_a_raw :=
    diffNormSq_eq_l2
      (I := I) (h := S.family.metric a) (gRef := gRef)
      (gInv := gInv a) frame hframe1 hu hx hinv_a
      (hinv_id a Set.left_mem_uIcc)
  have hsq_a :
      Tensor0SBundle.normSqRS
          (I := I) (g := S.family.metric a) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric
              (I := I) (S.family.metric a))
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x) =
        DifferentialGeometry.Integral.Connection.componentL2Sq3
          (fun i j k : Idx =>
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (S.family.connection a) frame hframe1 x i j k -
              baseGamma i j k) := by
    simpa [baseGamma, DifferentialGeometry.PDE.RicciFlow.SolutionOn.family,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.connection] using hsq_a_raw
  have hinvBasis_a :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (S.family.metric a) x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)) :=
    metricInvBasisId
      (I := I) (h := S.family.metric a) (gInv := gInv a)
      frame hframe hx hinv_a (hinv_id a Set.left_mem_uIcc)
  have hinvBasis_b :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (S.family.metric b) x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)) :=
    metricInvBasisId
      (I := I) (h := S.family.metric b) (gInv := gInv b)
      frame hframe hx hinv_b (hinv_id b Set.right_mem_uIcc)
  have hinit_norm :=
    diff_le_covOne_basis_ref_lc
      (I := I) (K := K)
      (h := S.family.metric a) (gRef := gRef)
      hxK (C := Ca) hEq_a (hframe.toBasisAt hx) hinvBasis_a
  have hinit_component :
      Real.sqrt
          (DifferentialGeometry.Integral.Connection.componentL2Sq3
            (fun i j k : Idx =>
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                  (S.family.connection a) frame hframe1 x i j k -
                baseGamma i j k)) <=
        (3 / 2 : Real) *
          (Real.sqrt (Ca ^ 3) *
            metricCovDerivNorm (I := I) 1 (S.family.metric a) gRef x) := by
    rw [← hsq_a]
    exact hinit_norm
  have hconn :
      Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := S.family.metric b) (x := x) 1 2
            (Tensor0SBundle.connectionDifferenceTensorAt
              (I := I)
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric
                (I := I) (S.family.metric b))
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)) <=
        3 * R * |b - a| +
          (3 / 2 : Real) *
            (Real.sqrt (Ca ^ 3) *
              metricCovDerivNorm (I := I) 1 (S.family.metric a) gRef x) := by
    rw [hsq_b]
    exact le_trans hgamma
      (by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hinit_component (3 * R * |b - a|))
  have hcov :=
    covOne_le_diff_basis_ref_lc
      (I := I) (K := K)
      (h := S.family.metric b) (gRef := gRef)
      hxK (C := Cb) hEq_b (hframe.toBasisAt hx) hinvBasis_b
  exact le_trans hcov
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hconn (by norm_num : (0 : Real) <= 2))
      (Real.sqrt_nonneg _))




omit [SigmaCompactSpace M] in
theorem covOne_le_init
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u K : Set M}
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (gRef : SmoothRiemannianMetric I M)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (hxK : x ∈ K)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    {a b R Ca Cb C1 : Real}
    (hsub : Set.uIcc a b ⊆ D.carrier)
    (hregular : ∀ s : Real, s ∈ Set.uIcc a b -> s ∈ D.regular)
    (hinv_id :
      ∀ s : Real, s ∈ Set.uIcc a b ->
        ∀ e l : Idx, gInv s x e l = if e = l then 1 else 0)
    (hevol :
      DifferentialGeometry.PDE.RicciFlow.ChristoffelEvolutionEquationInFrameOn
        (I := I) S gInv frame (localFrameOneOfInf (I := I) frame hframe)
        nablaRic)
    (hRic :
      ∀ s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt
          (DifferentialGeometry.Integral.Connection.componentL2Sq3
            (fun i j k : Idx => nablaRic s x i j k)) <= R)
    (hEq_b :
      MetricUniformEquivalentOn (I := I) K gRef (S.family.metric b) Cb)
    (hinv_b :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (S.family.metric b) (gInv b) frame)
    (hEq_a :
      MetricUniformEquivalentOn (I := I) K gRef (S.family.metric a) Ca)
    (hinv_a :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (S.family.metric a) (gInv a) frame)
    (hinit :
      metricCovDerivNorm (I := I) 1 (S.family.metric a) gRef x <= C1) :
    metricCovDerivNorm (I := I) 1 (S.family.metric b) gRef x <=
      Real.sqrt (Cb ^ 3) *
        (2 *
          (3 * R * |b - a| +
            (3 / 2 : Real) * (Real.sqrt (Ca ^ 3) * C1))) := by
  have hmain :=
    covOne_le_christoffel
      (I := I) (K := K) (u := u) S gRef gInv frame hframe hu hx hxK
      nablaRic hsub hregular hinv_id hevol hRic
      hEq_b hinv_b hEq_a hinv_a
  refine le_trans hmain ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : Real) <= 2)
  have hinit_scaled :
      (3 / 2 : Real) *
          (Real.sqrt (Ca ^ 3) *
            metricCovDerivNorm (I := I) 1 (S.family.metric a) gRef x) <=
        (3 / 2 : Real) * (Real.sqrt (Ca ^ 3) * C1) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hinit (Real.sqrt_nonneg _))
      (by norm_num : (0 : Real) <= 3 / 2)
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left hinit_scaled (3 * R * |b - a|)



def CurvDerivBoundOn
    (K : Set M) (p : Nat)
    (h : SmoothRiemannianMetric I M)
    (C : Real) : Prop :=
  forall x : M, x ∈ K -> curvDerivNorm (I := I) p h x <= C



def CurvDerivBoundOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (p : Nat) (C : Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    CurvDerivBoundOn (I := I) K p (gSeq i t) C


def CurvDerivBoundsOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (C : Nat -> Real) : Prop :=
  forall p : Nat, CurvDerivBoundOnWindow (I := I) K β ψ gSeq p (C p)




def TwoTensorQuadBoundOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x)
    (A : Real) : Prop :=
  0 <= A /\
    forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
      forall x : M, x ∈ K ->
        forall v : TangentSpace I x,
          |T i t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)| <=
            A * (gSeq i t).inner x v v









structure MetricLogDerivativeInput
    (K : Set M) (β ψ t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x)
    (A : Real) : Prop where
  quad_bound : TwoTensorQuadBoundOnWindow (I := I) K β ψ gSeq T A
  metric_deriv :
    forall i : Nat, forall x : M, x ∈ K ->
      forall v : TangentSpace I x, v ≠ 0 ->
        forall t : Real, t ∈ Set.Icc β ψ ->
          HasDerivAt
            (fun s : Real => (gSeq i s).inner x v v)
            ((-2 : Real) * T i t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v))
            t
  log_integrable :
    forall i : Nat, forall x : M, x ∈ K ->
      forall v : TangentSpace I x, v ≠ 0 ->
        forall t : Real, t ∈ Set.Icc β ψ ->
          IntervalIntegrable
            (fun s : Real =>
              ((-2 : Real) * T i s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)) /
                (gSeq i s).inner x v v)
            MeasureTheory.volume t0 t

private theorem metric_factor_one_le
    {C A t t0 : Real}
    (hC : 1 <= C) (hA : 0 <= A) :
    1 <= metricEquivalenceFactor C A t t0 := by
  have harg_nonneg : 0 <= 2 * A * |t - t0| := by
    nlinarith [hA, abs_nonneg (t - t0)]
  have hexp : 1 <= Real.exp (2 * A * |t - t0|) :=
    Real.one_le_exp harg_nonneg
  have hprod : 0 <= (C - 1) * (Real.exp (2 * A * |t - t0|) - 1) :=
    mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hexp)
  rw [metricEquivalenceFactor]
  nlinarith

private theorem metric_factor_inv_mul
    {C A t t0 g : Real}
    (hC : 1 <= C) :
    (metricEquivalenceFactor C A t t0)⁻¹ * g =
      Real.exp (-(2 * A) * |t - t0|) * (C⁻¹ * g) := by
  have hCne : C ≠ 0 := by nlinarith
  rw [metricEquivalenceFactor,
    show -(2 * A) * |t - t0| = -(2 * A * |t - t0|) by ring,
    Real.exp_neg]
  field_simp [hCne, Real.exp_ne_zero]

private theorem metric_factor_mul
    {C A t t0 g : Real} :
    Real.exp ((2 * A) * |t - t0|) * (C * g) =
      metricEquivalenceFactor C A t t0 * g := by
  rw [metricEquivalenceFactor]
  ring




omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem metricUniformEquivalentOnWindow_of_logDerivativeInput
    (K : Set M) (β ψ t0 C A : Real)
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x)
    (ht0 : t0 ∈ Set.Icc β ψ)
    (hC : 1 <= C)
    (hequiv0 :
      forall i : Nat,
        MetricUniformEquivalentOn (I := I) K gRef (gSeq i t0) C)
    (hlog : MetricLogDerivativeInput (I := I) K β ψ t0 gSeq T A) :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq
      (fun t : Real => metricEquivalenceFactor C A t t0) := by
  intro i t ht
  refine ⟨metric_factor_one_le hC hlog.quad_bound.1, ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · subst v
    simp
  have hwindow : Set.uIcc t0 t ⊆ Set.Icc β ψ :=
    Set.uIcc_subset_Icc ht0 ht
  let f : Real -> Real := fun s => (gSeq i s).inner x v v
  let f' : Real -> Real :=
    fun s => (-2 : Real) * T i s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)
  have hf_pos : forall s : Real, s ∈ Set.uIcc t0 t -> 0 < f s := by
    intro s _hs
    exact (gSeq i s).pos x v hv
  have hf_deriv :
      forall s : Real, s ∈ Set.uIcc t0 t -> HasDerivAt f (f' s) s := by
    intro s hs
    exact hlog.metric_deriv i x hx v hv s (hwindow hs)
  have hA : 0 <= A := hlog.quad_bound.1
  have hbound :
      forall s : Real, s ∈ Set.uIcc t0 t -> |f' s / f s| <= 2 * A := by
    intro s hs
    have hswin : s ∈ Set.Icc β ψ := hwindow hs
    have hquad := hlog.quad_bound.2 i s hswin x hx v
    have hden_pos : 0 < f s := hf_pos s hs
    have hnum :
        |(-2 : Real) * T i s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)| <=
          2 * (A * f s) := by
      calc
        |(-2 : Real) * T i s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)|
            = 2 * |T i s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)| := by
              rw [abs_mul]
              norm_num
        _ <= 2 * (A * f s) :=
              mul_le_mul_of_nonneg_left hquad (by norm_num)
    calc
      |f' s / f s|
          = |f' s| / f s := by
            rw [abs_div, abs_of_pos hden_pos]
      _ <= (2 * (A * f s)) / f s :=
            div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
      _ = 2 * A := by
            field_simp [hden_pos.ne']
  have hscalar :
      Real.exp (-(2 * A) * |t - t0|) * f t0 <= f t /\
        f t <= Real.exp ((2 * A) * |t - t0|) * f t0 :=
    exp_bounds_of_log_deriv_bound f f' hf_pos hf_deriv hbound
  have h0 := (hequiv0 i).2 x hx v
  constructor
  · have hlow0 : C⁻¹ * gRef.inner x v v <= f t0 := h0.1
    have hlow_exp :
        Real.exp (-(2 * A) * |t - t0|) *
            (C⁻¹ * gRef.inner x v v) <=
          Real.exp (-(2 * A) * |t - t0|) * f t0 :=
      mul_le_mul_of_nonneg_left hlow0 (le_of_lt (Real.exp_pos _))
    calc
      (metricEquivalenceFactor C A t t0)⁻¹ * gRef.inner x v v
          = Real.exp (-(2 * A) * |t - t0|) *
              (C⁻¹ * gRef.inner x v v) :=
            metric_factor_inv_mul hC
      _ <= Real.exp (-(2 * A) * |t - t0|) * f t0 := hlow_exp
      _ <= f t := hscalar.1
  · have hhigh0 : f t0 <= C * gRef.inner x v v := h0.2
    have hhigh_exp :
        Real.exp ((2 * A) * |t - t0|) * f t0 <=
          Real.exp ((2 * A) * |t - t0|) *
            (C * gRef.inner x v v) :=
      mul_le_mul_of_nonneg_left hhigh0 (le_of_lt (Real.exp_pos _))
    calc
      f t <= Real.exp ((2 * A) * |t - t0|) * f t0 := hscalar.2
      _ <= Real.exp ((2 * A) * |t - t0|) *
          (C * gRef.inner x v v) := hhigh_exp
      _ = metricEquivalenceFactor C A t t0 * gRef.inner x v v :=
          metric_factor_mul






structure MetricAllTimesBoundsInput
    (K : Set M) (β ψ t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  compact : IsCompact K
  t0_mem : t0 ∈ Set.Icc β ψ
  equivC : Real
  equiv_at_t0 :
    forall i : Nat,
      MetricUniformEquivalentOn (I := I) K gRef (gSeq i t0) equivC
  metricC : Nat -> Real
  metricC_nonneg : forall p : Nat, 0 <= metricC p
  metric_at_t0 :
    MetricCovDerivBoundsAtTimeOn (I := I) K t0 gSeq gRef metricC
  curvC : Nat -> Real
  curvC_nonneg : forall p : Nat, 0 <= curvC p
  curv_on_window :
    CurvDerivBoundsOnWindow (I := I) K β ψ gSeq curvC





structure MetricAllTimesSpatialConclusion
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  B : Real -> Real
  equiv_on_window :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B
  metricC : Nat -> Real
  metric_on_window :
    MetricCovDerivBoundsOnWindow (I := I) K β ψ gSeq gRef metricC






structure MetricAllTimesSpatialInput
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  B : Real -> Real
  equiv_on_window :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B
  orderC : Nat -> Real
  orderC_nonneg : forall a : Nat, 0 <= orderC a
  order_on_window :
    forall a : Nat,
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef a
        (orderC a)



noncomputable def metricAllTimes_spatial
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (H : MetricAllTimesSpatialInput (I := I) K β ψ gSeq gRef) :
    MetricAllTimesSpatialConclusion (I := I) K β ψ gSeq gRef where
  B := H.B
  equiv_on_window := H.equiv_on_window
  metricC := metricCovCumulativeConstant H.orderC
  metric_on_window :=
    metricCovBoundsWindow_of_orderBounds (I := I) K β ψ gSeq gRef
      H.orderC H.orderC_nonneg H.order_on_window







noncomputable def metricMixedDeriv
    (p q : Nat) (h : Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (x : M) (t : Real) :
    Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x :=
  let F :=
    Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x
  let Dfiber := Tensor0SBundle.tensor0SMetricData (I := I) gRef x (p + 2)
  letI : PreInnerProductSpace.Core Real F := Dfiber.toCore.toCore
  letI : SeminormedAddCommGroup F :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := Real) (F := F)
  letI : InnerProductSpace.Core Real F := Dfiber.toCore
  letI : NormedAddCommGroup F :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := Real) (F := F)
  letI : NormedSpace Real F :=
    InnerProductSpace.Core.toNormedSpace (𝕜 := Real) (F := F)
  iteratedDeriv (𝕜 := Real) (F := F) q
    (fun s : Real => metricCovDeriv (I := I) (h s) gRef p x) t


noncomputable def metricMixedDerivNorm
    (p q : Nat) (h : Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (x : M) (t : Real) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
      (metricMixedDeriv (I := I) p q h gRef x t))

omit [SigmaCompactSpace M] in
@[simp]
theorem metricMixedDerivNorm_zero
    (p : Nat) (h : Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (x : M) (t : Real) :
    metricMixedDerivNorm (I := I) p 0 h gRef x t =
      metricCovDerivNorm (I := I) p (h t) gRef x := by
  simp [metricMixedDerivNorm, metricMixedDeriv, metricCovDerivNorm]


def MetricMixedDerivBoundOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (p q : Nat) (C : Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    forall x : M, x ∈ K ->
      metricMixedDerivNorm (I := I) p q (gSeq i) gRef x t <= C


def MetricMixedDerivBoundsOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Nat -> Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    forall p q : Nat,
      forall a : Nat, a <= p ->
        forall b : Nat, b <= q ->
          forall x : M, x ∈ K ->
            metricMixedDerivNorm (I := I) a b (gSeq i) gRef x t <= C p q


omit [SigmaCompactSpace M] in
theorem metricMixedWindow_of_pointwise
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (p q : Nat) (C : Real)
    (hpoint :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall x : M, x ∈ K ->
          metricMixedDerivNorm (I := I) p q (gSeq i) gRef x t <= C) :
    MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef p q C := by
  intro i t ht x hx
  exact hpoint i t ht x hx


omit [SigmaCompactSpace M] in
theorem metricMixedBoundsWindow_of_pointwise
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Nat -> Real)
    (hpoint :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall p q : Nat,
          forall a : Nat, a <= p ->
            forall b : Nat, b <= q ->
              forall x : M, x ∈ K ->
                metricMixedDerivNorm (I := I) a b (gSeq i) gRef x t <= C p q) :
    MetricMixedDerivBoundsOnWindow (I := I) K β ψ gSeq gRef C := by
  intro i t ht p q a ha b hb x hx
  exact hpoint i t ht p q a ha b hb x hx


omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem normSq0S_smul
    (gRef : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (c : Real)
    (A :
      Tensor0SBundle.Tensor0SSpace
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    Tensor0SBundle.normSq0S (I := I) gRef x s (c • A) =
      c ^ 2 * Tensor0SBundle.normSq0S (I := I) gRef x s A := by
  unfold Tensor0SBundle.normSq0S Tensor0SBundle.inner0S
    Tensor0SBundle.MetricFiberData.inner
  rw [((Tensor0SBundle.tensor0SMetricData (I := I) gRef x s).flat.map_smul c A)]
  simp [pow_two, mul_assoc]


omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem sqrt_normSq0S_smul
    (gRef : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (c : Real)
    (A :
      Tensor0SBundle.Tensor0SSpace
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x s (c • A)) =
      |c| * Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x s A) := by
  rw [normSq0S_smul]
  rw [Real.sqrt_mul (sq_nonneg c)]
  rw [Real.sqrt_sq_eq_abs]







def MetricMixedDerivOneEvolutionOn
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p : Nat)
    (nablaRic :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x) :
    Prop :=
  forall i : Nat, forall x : M, x ∈ K -> forall t : Real, t ∈ Set.Icc β ψ ->
    metricMixedDeriv (I := I) p 1 (gSeq i) gRef x t =
      (-2 : Real) • nablaRic i t x


omit [SigmaCompactSpace M] in
theorem metricMixedDeriv_one_eq_of_evolution
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {p : Nat}
    {nablaRic :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x}
    (hmixed :
      MetricMixedDerivOneEvolutionOn (I := I) K β ψ gSeq gRef p nablaRic)
    {i : Nat} {x : M} (hx : x ∈ K) {t : Real} (ht : t ∈ Set.Icc β ψ) :
    metricMixedDeriv (I := I) p 1 (gSeq i) gRef x t =
      (-2 : Real) • nablaRic i t x := by
  exact hmixed i x hx t ht


def metricMixedOneConstant (Cpp Csp0 Cppp : Real) : Real :=
  2 * (Cpp * Csp0 + Cppp)







omit [SigmaCompactSpace M] in
theorem metricMixedOneWindow_of_ric_bound
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {p : Nat} {Csp0 : Real}
    {nablaRic :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x}
    (Cpp Cppp : Real)
    (Cpp_nonneg : 0 <= Cpp)
    (ric_bound :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall x : M, x ∈ K ->
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (nablaRic i t x)) <=
            Cpp * metricCovDerivNorm (I := I) p (gSeq i t) gRef x + Cppp)
    (hmixed :
      MetricMixedDerivOneEvolutionOn (I := I) K β ψ gSeq gRef p nablaRic)
    (hspatial :
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef p Csp0) :
    MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef p 1
      (metricMixedOneConstant Cpp Csp0 Cppp) := by
  refine
    metricMixedWindow_of_pointwise (I := I) K β ψ gSeq gRef p 1
      (metricMixedOneConstant Cpp Csp0 Cppp) ?_
  intro i t ht x hx
  have hmixed_eq :
      metricMixedDeriv (I := I) p 1 (gSeq i) gRef x t =
        (-2 : Real) • nablaRic i t x :=
    metricMixedDeriv_one_eq_of_evolution (I := I)
      (K := K) (β := β) (ψ := ψ) (gSeq := gSeq) (gRef := gRef)
      (p := p) (nablaRic := nablaRic) hmixed hx ht
  have hnorm_eq :
      metricMixedDerivNorm (I := I) p 1 (gSeq i) gRef x t =
        2 *
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (nablaRic i t x)) := by
    unfold metricMixedDerivNorm
    rw [hmixed_eq]
    rw [sqrt_normSq0S_smul]
    norm_num
  have hric :
      Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
            (nablaRic i t x)) <=
        Cpp * metricCovDerivNorm (I := I) p (gSeq i t) gRef x + Cppp :=
    ric_bound i t ht x hx
  have hsp :
      metricCovDerivNorm (I := I) p (gSeq i t) gRef x <= Csp0 :=
    hspatial i t ht x hx
  have hric_sp :
      Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
            (nablaRic i t x)) <=
        Cpp * Csp0 + Cppp := by
    have hmul :
        Cpp * metricCovDerivNorm (I := I) p (gSeq i t) gRef x <=
          Cpp * Csp0 :=
      mul_le_mul_of_nonneg_left hsp Cpp_nonneg
    exact le_trans hric (by linarith)
  have hmain :
      2 *
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (nablaRic i t x)) <=
        metricMixedOneConstant Cpp Csp0 Cppp := by
    unfold metricMixedOneConstant
    exact mul_le_mul_of_nonneg_left hric_sp (by norm_num : (0 : Real) <= 2)
  simpa [hnorm_eq] using hmain


structure MetricAllTimesConclusion
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  B : Real -> Real
  equiv_on_window :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B
  metricC : Nat -> Nat -> Real
  mixed_on_window :
    MetricMixedDerivBoundsOnWindow (I := I) K β ψ gSeq gRef metricC






def metricFirstOrderConstant
    (Ca Cb R timeRadius M0 : Real) : Real :=
  Real.sqrt (Cb ^ 3) *
    (2 *
      (3 * R * timeRadius +
        (3 / 2 : Real) * (Real.sqrt (Ca ^ 3) * M0)))








structure MetricAllTimesFirstOrderInput
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (K u : Set M) (β ψ t0 : Real)
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (SSeq : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (gRef : SmoothRiemannianMetric I M)
    (T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x)
    (A : Real) where
  base :
    MetricAllTimesBoundsInput (I := I) K β ψ t0
      (fun i t => (SSeq i).family.metric t) gRef
  log_input :
    MetricLogDerivativeInput (I := I) K β ψ t0
      (fun i t => (SSeq i).family.metric t) T A
  frame : Idx -> (x : M) -> TangentSpace I x
  hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u
  hu : IsOpen u
  K_subset_u : K ⊆ u
  subset_carrier : Set.Icc β ψ ⊆ D.carrier
  regular_on_window : forall s : Real, s ∈ Set.Icc β ψ -> s ∈ D.regular
  gInv : Nat -> Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx
  nablaRic : Nat -> Real -> M -> Idx -> Idx -> Idx -> Real
  hinv_id :
    forall i : Nat, forall s : Real, s ∈ Set.Icc β ψ ->
      forall x : M, x ∈ K ->
        forall e l : Idx, gInv i s x e l = if e = l then 1 else 0
  hinv_frame :
    forall i : Nat, forall s : Real, s ∈ Set.Icc β ψ ->
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) ((SSeq i).family.metric s) (gInv i s) frame
  hevol :
    forall i : Nat,
      DifferentialGeometry.PDE.RicciFlow.ChristoffelEvolutionEquationInFrameOn
        (I := I) (SSeq i) (gInv i) frame
        (localFrameOneOfInf (I := I) frame hframe) (nablaRic i)
  R : Real
  R_nonneg : 0 <= R
  nablaRic_bound :
    forall i : Nat, forall s : Real, s ∈ Set.Icc β ψ ->
      forall x : M, x ∈ K ->
        Real.sqrt
          (DifferentialGeometry.Integral.Connection.componentL2Sq3
            (fun a b c : Idx => nablaRic i s x a b c)) <= R
  initialOneC : Real
  initial_one_bound :
    forall i : Nat, forall x : M, x ∈ K ->
      metricCovDerivNorm (I := I) 1 ((SSeq i).family.metric t0) gRef x <=
        initialOneC
  Bmax : Real
  B_le_Bmax :
    forall t : Real, t ∈ Set.Icc β ψ ->
      metricEquivalenceFactor base.equivC A t t0 <= Bmax
  timeRadius : Real
  time_abs_le :
    forall t : Real, t ∈ Set.Icc β ψ -> |t - t0| <= timeRadius






structure MetricAllTimesFirstOrderConclusion
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (K : Set M) (β ψ : Real)
    (SSeq : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (gRef : SmoothRiemannianMetric I M) where
  B : Real -> Real
  equiv_on_window :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef
      (fun i t => (SSeq i).family.metric t) B
  C1 : Real
  order_one_bound :
    MetricCovDerivOrderBoundOnWindow (I := I) K β ψ
      (fun i t => (SSeq i).family.metric t) gRef 1 C1



omit [SigmaCompactSpace M] in
theorem metricCovOrderOneWindow_of_christoffel
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {K u : Set M} {β ψ t0 : Real} {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {SSeq : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D}
    {gRef : SmoothRiemannianMetric I M}
    {T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x}
    {A : Real}
    (H :
      MetricAllTimesFirstOrderInput (I := I) (Idx := Idx) K u β ψ t0
        (D := D) SSeq gRef T A) :
    MetricCovDerivOrderBoundOnWindow (I := I) K β ψ
      (fun i t => (SSeq i).family.metric t) gRef 1
      (metricFirstOrderConstant
        H.base.equivC H.Bmax H.R H.timeRadius H.initialOneC) := by
  have hEquivC : 1 <= H.base.equivC := (H.base.equiv_at_t0 0).1
  have hequiv_window :
      MetricUniformEquivalentOnWindow (I := I) K β ψ gRef
        (fun i t => (SSeq i).family.metric t)
        (fun t : Real => metricEquivalenceFactor H.base.equivC A t t0) :=
    metricUniformEquivalentOnWindow_of_logDerivativeInput
      (I := I) K β ψ t0 H.base.equivC A gRef
      (fun i t => (SSeq i).family.metric t) T
      H.base.t0_mem hEquivC H.base.equiv_at_t0 H.log_input
  refine
    metricCovOrderWindow_of_pointwise (I := I) K β ψ
      (fun i t => (SSeq i).family.metric t) gRef 1
      (metricFirstOrderConstant
        H.base.equivC H.Bmax H.R H.timeRadius H.initialOneC) ?_
  intro i t ht x hxK
  have hsegment : Set.uIcc t0 t ⊆ Set.Icc β ψ :=
    Set.uIcc_subset_Icc H.base.t0_mem ht
  have hsub : Set.uIcc t0 t ⊆ D.carrier := fun s hs =>
    H.subset_carrier (hsegment hs)
  have hregular :
      forall s : Real, s ∈ Set.uIcc t0 t -> s ∈ D.regular := fun s hs =>
    H.regular_on_window s (hsegment hs)
  have hEq_t :
      MetricUniformEquivalentOn
        (I := I) K gRef ((SSeq i).family.metric t) H.Bmax :=
    metricUniformEquivalentOn_of_le
      (I := I) (hequiv_window i t ht) (H.B_le_Bmax t ht)
  have hraw :
      metricCovDerivNorm (I := I) 1 ((SSeq i).family.metric t) gRef x <=
        Real.sqrt (H.Bmax ^ 3) *
          (2 *
            (3 * H.R * |t - t0| +
              (3 / 2 : Real) *
                (Real.sqrt (H.base.equivC ^ 3) * H.initialOneC))) :=
    covOne_le_init
      (I := I) (K := K) (u := u) (SSeq i) gRef (H.gInv i)
      H.frame H.hframe H.hu (H.K_subset_u hxK) hxK (H.nablaRic i)
      hsub hregular
      (fun s hs e l => H.hinv_id i s (hsegment hs) x hxK e l)
      (H.hevol i)
      (fun s hs => H.nablaRic_bound i s (hsegment hs) x hxK)
      hEq_t (H.hinv_frame i t ht) (H.base.equiv_at_t0 i)
      (H.hinv_frame i t0 H.base.t0_mem)
      (H.initial_one_bound i x hxK)
  have htime :
      3 * H.R * |t - t0| <= 3 * H.R * H.timeRadius := by
    nlinarith [H.R_nonneg, H.time_abs_le t ht]
  have hinside :
      3 * H.R * |t - t0| +
          (3 / 2 : Real) *
            (Real.sqrt (H.base.equivC ^ 3) * H.initialOneC) <=
        3 * H.R * H.timeRadius +
          (3 / 2 : Real) *
            (Real.sqrt (H.base.equivC ^ 3) * H.initialOneC) :=
    by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right htime
          ((3 / 2 : Real) *
            (Real.sqrt (H.base.equivC ^ 3) * H.initialOneC))
  have hconst :
      Real.sqrt (H.Bmax ^ 3) *
          (2 *
            (3 * H.R * |t - t0| +
              (3 / 2 : Real) *
                (Real.sqrt (H.base.equivC ^ 3) * H.initialOneC))) <=
        metricFirstOrderConstant
          H.base.equivC H.Bmax H.R H.timeRadius H.initialOneC := by
    unfold metricFirstOrderConstant
    exact
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinside (by norm_num : (0 : Real) <= 2))
        (Real.sqrt_nonneg _)
  exact le_trans hraw hconst




def metricAllTimes_firstOrder
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {K u : Set M} {β ψ t0 : Real} {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {SSeq : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D}
    {gRef : SmoothRiemannianMetric I M}
    {T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x}
    {A : Real}
    (H :
      MetricAllTimesFirstOrderInput (I := I) (Idx := Idx) K u β ψ t0
        (D := D) SSeq gRef T A) :
    MetricAllTimesFirstOrderConclusion (I := I) K β ψ SSeq gRef where
  B := fun t : Real => metricEquivalenceFactor H.base.equivC A t t0
  equiv_on_window := by
    have hEquivC : 1 <= H.base.equivC := (H.base.equiv_at_t0 0).1
    exact
      metricUniformEquivalentOnWindow_of_logDerivativeInput
        (I := I) K β ψ t0 H.base.equivC A gRef
        (fun i t => (SSeq i).family.metric t) T
        H.base.t0_mem hEquivC H.base.equiv_at_t0 H.log_input
  C1 :=
    metricFirstOrderConstant
      H.base.equivC H.Bmax H.R H.timeRadius H.initialOneC
  order_one_bound :=
    metricCovOrderOneWindow_of_christoffel (I := I) (Idx := Idx) H



def metricCovOrderEvolutionAlpha (Cpp : Real) : Real :=
  1 + 8 * Cpp ^ 2






def metricCovOrderEvolutionBeta (Cppp : Real) : Real :=
  8 * Cppp ^ 2 + 1



def metricCovOrderEvolutionConstant
    (Cpp Cppp timeRadius initC : Real) : Real :=
  Real.sqrt
    (Real.exp (metricCovOrderEvolutionAlpha Cpp * timeRadius) *
      (initC ^ 2 +
        metricCovOrderEvolutionBeta Cppp /
          metricCovOrderEvolutionAlpha Cpp))







def MetricCovOrderEvolutionOn
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p : Nat)
    (nablaRic :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x) :
    Prop :=
  forall i : Nat, forall x : M, x ∈ K -> forall s : Real, s ∈ Set.Icc β ψ ->
      HasDerivAt
        (fun r : Real => metricCovDeriv (I := I) (gSeq i r) gRef p x)
        ((-2 : Real) • nablaRic i s x) s








def MetricCovOrderNormSqEvolutionOn
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p : Nat)
    (nablaRic :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x) :
    Prop :=
  forall i : Nat, forall x : M, x ∈ K -> forall s : Real, s ∈ Set.Icc β ψ ->
    exists d : Real,
      HasDerivAt
        (fun r : Real =>
          metricCovDerivNorm (I := I) p (gSeq i r) gRef x ^ 2) d s ∧
        |d| <=
          metricCovDerivNorm (I := I) p (gSeq i s) gRef x ^ 2 +
            (2 *
              Real.sqrt
                (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
                  (nablaRic i s x))) ^ 2









structure MetricCovOrderEvolutionInput
    (K : Set M) (β ψ t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p : Nat) where
  t0_mem : t0 ∈ Set.Icc β ψ
  nablaRic :
    Nat -> Real -> (x : M) ->
      Tensor0SBundle.Tensor0SSpace
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x
  normsq_evol :
    MetricCovOrderNormSqEvolutionOn (I := I) K β ψ gSeq gRef p nablaRic
  Cpp : Real
  Cppp : Real
  Cpp_nonneg : 0 <= Cpp
  Cppp_nonneg : 0 <= Cppp
  ric_bound :
    forall i : Nat, forall s : Real, s ∈ Set.Icc β ψ ->
      forall x : M, x ∈ K ->
        Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
            (nablaRic i s x)) <=
          Cpp * metricCovDerivNorm (I := I) p (gSeq i s) gRef x + Cppp
  initC : Real
  initC_nonneg : 0 <= initC
  init_bound :
    forall i : Nat, forall x : M, x ∈ K ->
      metricCovDerivNorm (I := I) p (gSeq i t0) gRef x <= initC
  timeRadius : Real
  time_abs_le :
    forall t : Real, t ∈ Set.Icc β ψ -> |t - t0| <= timeRadius




omit [SigmaCompactSpace M] in
theorem metricCovOrderWindow_of_evolution
    {K : Set M} {β ψ t0 : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {p : Nat}
    (Hin :
      MetricCovOrderEvolutionInput (I := I) K β ψ t0 gSeq gRef p) :
    MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef p
      (metricCovOrderEvolutionConstant
        Hin.Cpp Hin.Cppp Hin.timeRadius Hin.initC) := by
  refine
    metricCovOrderWindow_of_pointwise (I := I) K β ψ gSeq gRef p
      (metricCovOrderEvolutionConstant
        Hin.Cpp Hin.Cppp Hin.timeRadius Hin.initC) ?_
  intro i t ht x hxK
  let U : Real -> Real := fun s =>
    metricCovDerivNorm (I := I) p (gSeq i s) gRef x ^ 2
  have hsegment : Set.uIcc t0 t ⊆ Set.Icc β ψ :=
    Set.uIcc_subset_Icc Hin.t0_mem ht
  let derivData :
      forall s : Real, s ∈ Set.Icc β ψ ->
        exists d : Real, HasDerivAt U d s ∧
          |d| <= U s +
            (2 *
              Real.sqrt
                (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
                  (Hin.nablaRic i s x))) ^ 2 := fun s hs =>
    by
      simpa [U] using Hin.normsq_evol i x hxK s hs
  let U' : Real -> Real := fun s =>
    if hs : s ∈ Set.Icc β ψ then Classical.choose (derivData s hs) else 0
  have hU_nonneg : forall s : Real, s ∈ Set.uIcc t0 t -> 0 <= U s := by
    intro s hs
    exact sq_nonneg _
  have hU_deriv :
      forall s : Real, s ∈ Set.uIcc t0 t -> HasDerivAt U (U' s) s := by
    intro s hs
    have hswin : s ∈ Set.Icc β ψ := hsegment hs
    have hspec := Classical.choose_spec (derivData s hswin)
    have hchoose : U' s = Classical.choose (derivData s hswin) := by
      dsimp [U']
      exact dif_pos hswin
    simpa [hchoose] using hspec.1
  have halpha_pos : 0 < metricCovOrderEvolutionAlpha Hin.Cpp := by
    unfold metricCovOrderEvolutionAlpha
    nlinarith [sq_nonneg Hin.Cpp]
  have hbeta_pos : 0 < metricCovOrderEvolutionBeta Hin.Cppp := by
    unfold metricCovOrderEvolutionBeta
    nlinarith [sq_nonneg Hin.Cppp]
  have hbound :
      forall s : Real, s ∈ Set.uIcc t0 t ->
        |U' s| <=
          metricCovOrderEvolutionAlpha Hin.Cpp * U s +
            metricCovOrderEvolutionBeta Hin.Cppp := by
    intro s hs
    have hswin : s ∈ Set.Icc β ψ := hsegment hs
    have hspec := Classical.choose_spec (derivData s hswin)
    have hchoose : U' s = Classical.choose (derivData s hswin) := by
      dsimp [U']
      exact dif_pos hswin
    have hbase :
        |U' s| <=
          U s +
            (2 *
              Real.sqrt
                (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
                  (Hin.nablaRic i s x))) ^ 2 := by
      simpa [hchoose] using hspec.2
    let q : Real :=
      Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
          (Hin.nablaRic i s x))
    let y : Real := metricCovDerivNorm (I := I) p (gSeq i s) gRef x
    have hq_nonneg : 0 <= q := by
      exact Real.sqrt_nonneg _
    have hy_nonneg : 0 <= y := by
      exact Real.sqrt_nonneg _
    have hRic_le :
        q <= Hin.Cpp * y + Hin.Cppp := by
      simpa [q, y] using Hin.ric_bound i s hswin x hxK
    have hRhs_nonneg : 0 <= Hin.Cpp * y + Hin.Cppp := by
      exact add_nonneg (mul_nonneg Hin.Cpp_nonneg hy_nonneg) Hin.Cppp_nonneg
    have hRic_sq :
        q ^ 2 <= (Hin.Cpp * y + Hin.Cppp) ^ 2 := by
      exact (sq_le_sq₀ hq_nonneg hRhs_nonneg).2 hRic_le
    have hYoung :
        (Hin.Cpp * y + Hin.Cppp) ^ 2 <=
          2 * (Hin.Cpp * y) ^ 2 + 2 * Hin.Cppp ^ 2 := by
      nlinarith [sq_nonneg (Hin.Cpp * y - Hin.Cppp)]
    have htwo_sq :
        (2 * q) ^ 2 <=
          8 * Hin.Cpp ^ 2 * U s + 8 * Hin.Cppp ^ 2 := by
      have hmain :
          (2 * q) ^ 2 <=
            8 * Hin.Cpp ^ 2 * y ^ 2 + 8 * Hin.Cppp ^ 2 := by
        nlinarith [hRic_sq, hYoung]
      simpa [U, y, pow_two, mul_assoc, mul_left_comm, mul_comm] using hmain
    have hbase' :
        |U' s| <= U s + (2 * q) ^ 2 := by
      simpa [q] using hbase
    calc
      |U' s| <= U s + (2 * q) ^ 2 := hbase'
      _ <= U s + (8 * Hin.Cpp ^ 2 * U s + 8 * Hin.Cppp ^ 2) := by
            simpa [U, add_comm, add_left_comm, add_assoc] using
              add_le_add_left htwo_sq (U s)
      _ <= metricCovOrderEvolutionAlpha Hin.Cpp * U s +
            metricCovOrderEvolutionBeta Hin.Cppp := by
            unfold metricCovOrderEvolutionAlpha metricCovOrderEvolutionBeta U
            ring_nf
            nlinarith [sq_nonneg y]
  have hgronwall :
      U t <=
        Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * |t - t0|) *
          (U t0 +
            metricCovOrderEvolutionBeta Hin.Cppp /
              metricCovOrderEvolutionAlpha Hin.Cpp) :=
    affineGronwall_of_abs_deriv_le U U'
      halpha_pos hbeta_pos hU_nonneg hU_deriv hbound
  have hU0 :
      U t0 <= Hin.initC ^ 2 := by
    have hinit := Hin.init_bound i x hxK
    have hnorm_nonneg :
        0 <= metricCovDerivNorm (I := I) p (gSeq i t0) gRef x :=
      Real.sqrt_nonneg _
    have hsquare :
        (metricCovDerivNorm (I := I) p (gSeq i t0) gRef x) ^ 2 <=
          Hin.initC ^ 2 :=
      (sq_le_sq₀ hnorm_nonneg Hin.initC_nonneg).2 hinit
    simpa [U] using hsquare
  have hshift_nonneg :
      0 <=
        metricCovOrderEvolutionBeta Hin.Cppp /
          metricCovOrderEvolutionAlpha Hin.Cpp :=
    le_of_lt (div_pos hbeta_pos halpha_pos)
  have hbracket :
      U t0 +
          metricCovOrderEvolutionBeta Hin.Cppp /
            metricCovOrderEvolutionAlpha Hin.Cpp <=
        Hin.initC ^ 2 +
          metricCovOrderEvolutionBeta Hin.Cppp /
            metricCovOrderEvolutionAlpha Hin.Cpp := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right hU0
        (metricCovOrderEvolutionBeta Hin.Cppp /
          metricCovOrderEvolutionAlpha Hin.Cpp)
  have hafter_init :
      U t <=
        Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * |t - t0|) *
          (Hin.initC ^ 2 +
            metricCovOrderEvolutionBeta Hin.Cppp /
              metricCovOrderEvolutionAlpha Hin.Cpp) :=
    le_trans hgronwall
      (mul_le_mul_of_nonneg_left hbracket
        (le_of_lt (Real.exp_pos _)))
  have htime_exp :
      Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * |t - t0|) <=
        Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * Hin.timeRadius) :=
    Real.exp_le_exp.mpr (by
      nlinarith [le_of_lt halpha_pos, Hin.time_abs_le t ht])
  have hbracket_nonneg :
      0 <=
        Hin.initC ^ 2 +
          metricCovOrderEvolutionBeta Hin.Cppp /
            metricCovOrderEvolutionAlpha Hin.Cpp :=
    add_nonneg (sq_nonneg Hin.initC) hshift_nonneg
  have hfinal_sq :
      U t <=
        Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * Hin.timeRadius) *
          (Hin.initC ^ 2 +
            metricCovOrderEvolutionBeta Hin.Cppp /
              metricCovOrderEvolutionAlpha Hin.Cpp) :=
    le_trans hafter_init
      (mul_le_mul_of_nonneg_right htime_exp hbracket_nonneg)
  have htarget_nonneg :
      0 <=
        Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * Hin.timeRadius) *
          (Hin.initC ^ 2 +
            metricCovOrderEvolutionBeta Hin.Cppp /
              metricCovOrderEvolutionAlpha Hin.Cpp) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) hbracket_nonneg
  have hnorm_le :
      metricCovDerivNorm (I := I) p (gSeq i t) gRef x <=
        metricCovOrderEvolutionConstant Hin.Cpp Hin.Cppp Hin.timeRadius Hin.initC := by
    unfold metricCovOrderEvolutionConstant
    refine
      (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).1 ?_
    rw [Real.sq_sqrt htarget_nonneg]
    simpa [U] using hfinal_sq
  exact hnorm_le






omit [SigmaCompactSpace M] in
theorem metricMixedOneWindow_of_evolution
    {K : Set M} {β ψ t0 : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {p : Nat} {Csp0 : Real}
    (Hin :
      MetricCovOrderEvolutionInput (I := I) K β ψ t0 gSeq gRef p)
    (hmixed :
      MetricMixedDerivOneEvolutionOn (I := I) K β ψ gSeq gRef p Hin.nablaRic)
    (hspatial :
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef p Csp0) :
    MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef p 1
      (metricMixedOneConstant Hin.Cpp Csp0 Hin.Cppp) := by
  exact
    metricMixedOneWindow_of_ric_bound (I := I)
      (K := K) (β := β) (ψ := ψ) (gSeq := gSeq) (gRef := gRef)
      (p := p) (Csp0 := Csp0) (nablaRic := Hin.nablaRic)
      Hin.Cpp Hin.Cppp Hin.Cpp_nonneg Hin.ric_bound hmixed hspatial






def MetricMixedDerivLayerEvolutionOn
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p q : Nat)
    (layer :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x) :
    Prop :=
  forall i : Nat, forall x : M, x ∈ K -> forall t : Real, t ∈ Set.Icc β ψ ->
    metricMixedDeriv (I := I) p q (gSeq i) gRef x t =
      (-2 : Real) • layer i t x


def metricMixedQConstant (Cpq : Real) : Real :=
  2 * Cpq





omit [SigmaCompactSpace M] in
theorem metricMixedQWindow_of_evolution
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {p q : Nat}
    {layer :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x}
    (Cpq : Real)
    (hmixed :
      MetricMixedDerivLayerEvolutionOn (I := I) K β ψ gSeq gRef p q layer)
    (layer_bound :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall x : M, x ∈ K ->
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (layer i t x)) <= Cpq) :
    MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef p q
      (metricMixedQConstant Cpq) := by
  refine
    metricMixedWindow_of_pointwise (I := I) K β ψ gSeq gRef p q
      (metricMixedQConstant Cpq) ?_
  intro i t ht x hx
  have heq :
      metricMixedDeriv (I := I) p q (gSeq i) gRef x t =
        (-2 : Real) • layer i t x :=
    hmixed i x hx t ht
  have hnorm :
      metricMixedDerivNorm (I := I) p q (gSeq i) gRef x t =
        2 *
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (layer i t x)) := by
    unfold metricMixedDerivNorm
    rw [heq, sqrt_normSq0S_smul]
    norm_num
  have hlayer :=
    layer_bound i t ht x hx
  have hscaled :
      2 *
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (layer i t x)) <=
        2 * Cpq :=
    mul_le_mul_of_nonneg_left hlayer (by norm_num : (0 : Real) <= 2)
  simpa [hnorm, metricMixedQConstant] using hscaled


omit [SigmaCompactSpace M] in
theorem metricMixedZeroWindow_of_spatial
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (a : Nat) (C : Real)
    (h :
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef a C) :
    MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef a 0 C := by
  refine metricMixedWindow_of_pointwise (I := I) K β ψ gSeq gRef a 0 C ?_
  intro i t ht x hx
  simpa using h i t ht x hx


noncomputable def metricMixedCumulativeConstant
    (D : Nat -> Nat -> Real) (p q : Nat) : Real :=
  (Finset.range (p + 1) ×ˢ Finset.range (q + 1)).sup' (by
    refine ⟨(0, 0), ?_⟩
    exact Finset.mem_product.mpr ⟨by simp, by simp⟩)
    (fun ab : Nat × Nat => D ab.1 ab.2)


omit [SigmaCompactSpace M] in
theorem metricMixedBoundsWindow_of_layerBounds
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (D : Nat -> Nat -> Real)
    (hD : forall a b : Nat, 0 <= D a b)
    (hlayer :
      forall a b : Nat,
        MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef a b
          (D a b)) :
    MetricMixedDerivBoundsOnWindow (I := I) K β ψ gSeq gRef
      (metricMixedCumulativeConstant D) := by
  refine
    metricMixedBoundsWindow_of_pointwise (I := I) K β ψ gSeq gRef
      (metricMixedCumulativeConstant D) ?_
  intro i t ht p q a ha b hb x hx
  have hmem :
      (a, b) ∈ Finset.range (p + 1) ×ˢ Finset.range (q + 1) := by
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ha),
        Finset.mem_range.mpr (Nat.lt_succ_of_le hb)⟩
  have hsup : D a b <= metricMixedCumulativeConstant D p q := by
    unfold metricMixedCumulativeConstant
    exact Finset.le_sup' (fun ab : Nat × Nat => D ab.1 ab.2) hmem
  have _hcum_nonneg : 0 <= metricMixedCumulativeConstant D p q :=
    le_trans (hD a b) hsup
  exact le_trans (hlayer a b i t ht x hx) hsup







structure MetricAllTimesInput
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  B : Real -> Real
  equiv_on_window :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B
  layerC : Nat -> Nat -> Real
  layerC_nonneg : forall a b : Nat, 0 <= layerC a b
  layer_on_window :
    forall a b : Nat,
      MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef a b
        (layerC a b)


noncomputable def metricAllTimes
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (H : MetricAllTimesInput (I := I) K β ψ gSeq gRef) :
    MetricAllTimesConclusion (I := I) K β ψ gSeq gRef where
  B := H.B
  equiv_on_window := H.equiv_on_window
  metricC := metricMixedCumulativeConstant H.layerC
  mixed_on_window :=
    metricMixedBoundsWindow_of_layerBounds (I := I)
      H.layerC H.layerC_nonneg H.layer_on_window

end FixedDomain

end HCGCompactness
end DifferentialGeometry
