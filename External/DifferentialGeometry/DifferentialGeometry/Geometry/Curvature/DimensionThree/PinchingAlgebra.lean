import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity









namespace DifferentialGeometry.Integral.Connection

variable {R : Type*}


def ricciEigenScalar3 [CommRing R] (l1 l2 l3 : R) : R :=
  l1 + l2 + l3


def ricciEigenNormSq3 [CommRing R] (l1 l2 l3 : R) : R :=
  l1 ^ 2 + l2 ^ 2 + l3 ^ 2


theorem ricciEigenNormSq3_nonneg
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] (l1 l2 l3 : R) :
    0 <= ricciEigenNormSq3 l1 l2 l3 := by
  unfold ricciEigenNormSq3
  positivity


theorem ricciEigenNormSq3_le_scalar_sq_of_nonnegative
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (l1 l2 l3 : R) (h1 : 0 <= l1) (h2 : 0 <= l2) (h3 : 0 <= l3) :
    ricciEigenNormSq3 l1 l2 l3 <= ricciEigenScalar3 l1 l2 l3 ^ 2 := by
  unfold ricciEigenNormSq3 ricciEigenScalar3
  nlinarith


def ricciEigenTraceCube3 [CommRing R] (l1 l2 l3 : R) : R :=
  l1 ^ 3 + l2 ^ 3 + l3 ^ 3


def hamiltonCubicQ3 [CommRing R] (l1 l2 l3 : R) : R :=
  2 * ricciEigenNormSq3 l1 l2 l3 ^ 2 +
    ricciEigenScalar3 l1 l2 l3 ^ 4 -
    5 * ricciEigenScalar3 l1 l2 l3 ^ 2 * ricciEigenNormSq3 l1 l2 l3 +
    4 * ricciEigenScalar3 l1 l2 l3 * ricciEigenTraceCube3 l1 l2 l3


def hamiltonCubicQFactorized3 [CommRing R] (l1 l2 l3 : R) : R :=
  (l1 - l2) ^ 2 * (ricciEigenScalar3 l1 l2 l3 - 2 * l3) ^ 2 +
    (l1 - l3) ^ 2 * (ricciEigenScalar3 l1 l2 l3 - 2 * l2) ^ 2 +
    (l2 - l3) ^ 2 * (ricciEigenScalar3 l1 l2 l3 - 2 * l1) ^ 2


theorem hamiltonCubicQ3_factorized [CommRing R] (l1 l2 l3 : R) :
    hamiltonCubicQ3 l1 l2 l3 = hamiltonCubicQFactorized3 l1 l2 l3 := by
  unfold hamiltonCubicQ3 hamiltonCubicQFactorized3 ricciEigenScalar3 ricciEigenNormSq3
    ricciEigenTraceCube3
  ring


theorem hamiltonCubicQ3_nonneg
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] (l1 l2 l3 : R) :
    0 <= hamiltonCubicQ3 l1 l2 l3 := by
  rw [hamiltonCubicQ3_factorized]
  unfold hamiltonCubicQFactorized3
  positivity


def ricciEigenPairwiseGapSq3 [CommRing R] (l1 l2 l3 : R) : R :=
  (l1 - l2) ^ 2 + (l1 - l3) ^ 2 + (l2 - l3) ^ 2


def tracefreeRicciEigenNormSq3 [Field R] (l1 l2 l3 : R) : R :=
  ricciEigenPairwiseGapSq3 l1 l2 l3 / 3


theorem tracefreeRicciEigenNormSq3_nonneg
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] (l1 l2 l3 : R) :
    0 <= tracefreeRicciEigenNormSq3 l1 l2 l3 := by
  have hpair : 0 <= ricciEigenPairwiseGapSq3 l1 l2 l3 := by
    unfold ricciEigenPairwiseGapSq3
    nlinarith [sq_nonneg (l1 - l2), sq_nonneg (l1 - l3), sq_nonneg (l2 - l3)]
  unfold tracefreeRicciEigenNormSq3
  exact div_nonneg hpair (by norm_num)



theorem tracefreeRicciEigenNormSq3_eq_zero_iff
    (l1 l2 l3 : Real) :
    tracefreeRicciEigenNormSq3 l1 l2 l3 = 0 <->
      l1 = l2 /\ l2 = l3 := by
  constructor
  · intro htf
    have hpair : ricciEigenPairwiseGapSq3 l1 l2 l3 = 0 := by
      unfold tracefreeRicciEigenNormSq3 at htf
      nlinarith
    have h12sq : (l1 - l2) ^ 2 = 0 := by
      have hnon1 : 0 <= (l1 - l3) ^ 2 := sq_nonneg (l1 - l3)
      have hnon2 : 0 <= (l2 - l3) ^ 2 := sq_nonneg (l2 - l3)
      unfold ricciEigenPairwiseGapSq3 at hpair
      nlinarith
    have h23sq : (l2 - l3) ^ 2 = 0 := by
      have hnon1 : 0 <= (l1 - l2) ^ 2 := sq_nonneg (l1 - l2)
      have hnon2 : 0 <= (l1 - l3) ^ 2 := sq_nonneg (l1 - l3)
      unfold ricciEigenPairwiseGapSq3 at hpair
      nlinarith
    constructor <;> nlinarith
  · rintro ⟨h12, h23⟩
    subst l2
    subst l3
    simp [tracefreeRicciEigenNormSq3, ricciEigenPairwiseGapSq3]



def hamiltonCubicQOrderedGaps3 [CommRing R] (a b z : R) : R :=
  a ^ 2 * (z + a + 2 * b) ^ 2 +
    (a + b) ^ 2 * (z + a) ^ 2 +
    b ^ 2 * (z - a) ^ 2


def orderedEigenPairwiseGapSq3 [CommRing R] (a b : R) : R :=
  a ^ 2 + (a + b) ^ 2 + b ^ 2

theorem hamiltonCubicQ3_ordered_gaps [CommRing R] (a b z : R) :
    hamiltonCubicQ3 (z + b + a) (z + b) z =
      hamiltonCubicQOrderedGaps3 a b z := by
  rw [hamiltonCubicQ3_factorized]
  unfold hamiltonCubicQFactorized3 hamiltonCubicQOrderedGaps3 ricciEigenScalar3
  ring

theorem ricciEigenPairwiseGapSq3_ordered_gaps [CommRing R] (a b z : R) :
    ricciEigenPairwiseGapSq3 (z + b + a) (z + b) z =
      orderedEigenPairwiseGapSq3 a b := by
  unfold ricciEigenPairwiseGapSq3 orderedEigenPairwiseGapSq3
  ring

theorem hamiltonCubicQOrderedGaps3_sub_zSq_pairwise [CommRing R] (a b z : R) :
    hamiltonCubicQOrderedGaps3 a b z - z ^ 2 * orderedEigenPairwiseGapSq3 a b =
      2 * a ^ 2 * (a ^ 2 + 3 * a * b + 2 * a * z + 3 * b ^ 2 + 4 * b * z) := by
  unfold hamiltonCubicQOrderedGaps3 orderedEigenPairwiseGapSq3
  ring

theorem hamiltonCubicQOrderedGaps3_ge_zSq_pairwise
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b z : R) (ha : 0 <= a) (hb : 0 <= b) (hz : 0 <= z) :
    z ^ 2 * orderedEigenPairwiseGapSq3 a b <= hamiltonCubicQOrderedGaps3 a b z := by
  have hdiff := hamiltonCubicQOrderedGaps3_sub_zSq_pairwise (R := R) a b z
  have hnonneg :
      0 <= 2 * a ^ 2 * (a ^ 2 + 3 * a * b + 2 * a * z + 3 * b ^ 2 + 4 * b * z) := by
    positivity
  nlinarith



theorem hamiltonCubicQOrderedGaps3_lower_bound
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b z delta scalar ricciNormSq : R)
    (ha : 0 <= a) (hb : 0 <= b) (hz : 0 <= z)
    (hdelta : 0 <= delta) (hscalar : 0 <= scalar)
    (hpinch : delta * scalar <= z)
    (hnorm : ricciNormSq <= scalar ^ 2) :
    2 * delta ^ 2 * ricciNormSq * (orderedEigenPairwiseGapSq3 a b / 3) <=
      hamiltonCubicQOrderedGaps3 a b z := by
  have hgap_ge :
      z ^ 2 * orderedEigenPairwiseGapSq3 a b <= hamiltonCubicQOrderedGaps3 a b z :=
    hamiltonCubicQOrderedGaps3_ge_zSq_pairwise a b z ha hb hz
  have htf_nonneg : 0 <= orderedEigenPairwiseGapSq3 a b / 3 := by
    have hpair : 0 <= orderedEigenPairwiseGapSq3 a b := by
      unfold orderedEigenPairwiseGapSq3
      positivity
    have hthree : (0 : R) <= 3 := by positivity
    exact div_nonneg hpair hthree
  have hdelta_sq_norm_le_zsq : delta ^ 2 * ricciNormSq <= z ^ 2 := by
    have hds_nonneg : 0 <= delta * scalar := mul_nonneg hdelta hscalar
    have hds_sq_le : (delta * scalar) ^ 2 <= z ^ 2 := by
      nlinarith [sq_nonneg (z - delta * scalar)]
    nlinarith [sq_nonneg delta, sq_nonneg scalar]
  have hscaled :
      2 * delta ^ 2 * ricciNormSq * (orderedEigenPairwiseGapSq3 a b / 3) <=
        3 * z ^ 2 * (orderedEigenPairwiseGapSq3 a b / 3) := by
    nlinarith [mul_le_mul_of_nonneg_right hdelta_sq_norm_le_zsq htf_nonneg]
  have hthree :
      3 * z ^ 2 * (orderedEigenPairwiseGapSq3 a b / 3) =
        z ^ 2 * orderedEigenPairwiseGapSq3 a b := by
    ring_nf
  rw [hthree] at hscaled
  exact le_trans hscaled hgap_ge





theorem hamiltonCubicQ3_lower_bound_ordered_eigenvalues
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (l1 l2 l3 delta : R)
    (h12 : l2 <= l1) (h23 : l3 <= l2)
    (hdelta : 0 <= delta)
    (hscalar : 0 <= ricciEigenScalar3 l1 l2 l3)
    (hpinch : delta * ricciEigenScalar3 l1 l2 l3 <= l3)
    (hnorm : ricciEigenNormSq3 l1 l2 l3 <= ricciEigenScalar3 l1 l2 l3 ^ 2) :
    2 * delta ^ 2 * ricciEigenNormSq3 l1 l2 l3 *
        tracefreeRicciEigenNormSq3 l1 l2 l3 <=
      hamiltonCubicQ3 l1 l2 l3 := by
  let a := l1 - l2
  let b := l2 - l3
  let z := l3
  have ha : 0 <= a := by
    dsimp [a]
    linarith
  have hb : 0 <= b := by
    dsimp [b]
    linarith
  have hz : 0 <= z := by
    dsimp [z]
    have hds_nonneg : 0 <= delta * ricciEigenScalar3 l1 l2 l3 :=
      mul_nonneg hdelta hscalar
    exact le_trans hds_nonneg hpinch
  have hgap_lower :
      2 * delta ^ 2 * ricciEigenNormSq3 l1 l2 l3 *
          (orderedEigenPairwiseGapSq3 a b / 3) <=
        hamiltonCubicQOrderedGaps3 a b z :=
    hamiltonCubicQOrderedGaps3_lower_bound a b z delta
      (ricciEigenScalar3 l1 l2 l3) (ricciEigenNormSq3 l1 l2 l3)
      ha hb hz hdelta hscalar hpinch hnorm
  have hQ_gap : hamiltonCubicQ3 l1 l2 l3 = hamiltonCubicQOrderedGaps3 a b z := by
    dsimp [a, b, z]
    unfold hamiltonCubicQ3 hamiltonCubicQOrderedGaps3 ricciEigenScalar3 ricciEigenNormSq3
      ricciEigenTraceCube3
    ring
  have htf_gap :
      tracefreeRicciEigenNormSq3 l1 l2 l3 = orderedEigenPairwiseGapSq3 a b / 3 := by
    dsimp [a, b]
    unfold tracefreeRicciEigenNormSq3 ricciEigenPairwiseGapSq3 orderedEigenPairwiseGapSq3
    ring
  rw [htf_gap, hQ_gap]
  exact hgap_lower



theorem hamiltonCubicQ3_lower_bound_ordered_nonnegative_eigenvalues
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (l1 l2 l3 delta : R)
    (h12 : l2 <= l1) (h23 : l3 <= l2)
    (h1 : 0 <= l1) (h2 : 0 <= l2) (h3 : 0 <= l3)
    (hdelta : 0 <= delta)
    (hpinch : delta * ricciEigenScalar3 l1 l2 l3 <= l3) :
    2 * delta ^ 2 * ricciEigenNormSq3 l1 l2 l3 *
        tracefreeRicciEigenNormSq3 l1 l2 l3 <=
      hamiltonCubicQ3 l1 l2 l3 := by
  exact hamiltonCubicQ3_lower_bound_ordered_eigenvalues l1 l2 l3 delta h12 h23 hdelta
    (by
      unfold ricciEigenScalar3
      nlinarith)
    hpinch
    (ricciEigenNormSq3_le_scalar_sq_of_nonnegative l1 l2 l3 h1 h2 h3)





theorem hamQ3_sub_nonneg
    (l1 l2 l3 delta epsilon : Real)
    (h12 : l2 <= l1) (h23 : l3 <= l2)
    (hdelta : 0 <= delta)
    (hepsilon : epsilon <= 2 * delta ^ 2)
    (hscalar : 0 <= ricciEigenScalar3 l1 l2 l3)
    (hpinch : delta * ricciEigenScalar3 l1 l2 l3 <= l3)
    (hnorm : ricciEigenNormSq3 l1 l2 l3 <= ricciEigenScalar3 l1 l2 l3 ^ 2) :
    0 <= hamiltonCubicQ3 l1 l2 l3 -
      epsilon * ricciEigenNormSq3 l1 l2 l3 *
        tracefreeRicciEigenNormSq3 l1 l2 l3 := by
  have hq :
      2 * delta ^ 2 * ricciEigenNormSq3 l1 l2 l3 *
          tracefreeRicciEigenNormSq3 l1 l2 l3 <=
        hamiltonCubicQ3 l1 l2 l3 :=
    hamiltonCubicQ3_lower_bound_ordered_eigenvalues
      l1 l2 l3 delta h12 h23 hdelta hscalar hpinch hnorm
  have hprod :
      0 <= ricciEigenNormSq3 l1 l2 l3 *
        tracefreeRicciEigenNormSq3 l1 l2 l3 := by
    exact mul_nonneg
      (ricciEigenNormSq3_nonneg l1 l2 l3)
      (tracefreeRicciEigenNormSq3_nonneg l1 l2 l3)
  have hcoef :
      epsilon * (ricciEigenNormSq3 l1 l2 l3 *
          tracefreeRicciEigenNormSq3 l1 l2 l3) <=
        (2 * delta ^ 2) *
          (ricciEigenNormSq3 l1 l2 l3 *
            tracefreeRicciEigenNormSq3 l1 l2 l3) :=
    mul_le_mul_of_nonneg_right hepsilon hprod
  have hcoef' :
      epsilon * ricciEigenNormSq3 l1 l2 l3 *
          tracefreeRicciEigenNormSq3 l1 l2 l3 <=
        2 * delta ^ 2 * ricciEigenNormSq3 l1 l2 l3 *
          tracefreeRicciEigenNormSq3 l1 l2 l3 := by
    calc
      epsilon * ricciEigenNormSq3 l1 l2 l3 *
          tracefreeRicciEigenNormSq3 l1 l2 l3 =
          epsilon * (ricciEigenNormSq3 l1 l2 l3 *
            tracefreeRicciEigenNormSq3 l1 l2 l3) := by ring
      _ <= (2 * delta ^ 2) *
          (ricciEigenNormSq3 l1 l2 l3 *
            tracefreeRicciEigenNormSq3 l1 l2 l3) := hcoef
      _ = 2 * delta ^ 2 * ricciEigenNormSq3 l1 l2 l3 *
          tracefreeRicciEigenNormSq3 l1 l2 l3 := by ring
  nlinarith




structure PinchEigen3 (l1 l2 l3 delta : Real) : Prop where
  ord12 : l2 <= l1
  ord23 : l3 <= l2
  nonneg1 : 0 <= l1
  nonneg2 : 0 <= l2
  nonneg3 : 0 <= l3
  delta_nonneg : 0 <= delta
  lower : delta * ricciEigenScalar3 l1 l2 l3 <= l3

namespace PinchEigen3

theorem scalar_nonneg {l1 l2 l3 delta : Real}
    (h : PinchEigen3 l1 l2 l3 delta) :
    0 <= ricciEigenScalar3 l1 l2 l3 := by
  unfold ricciEigenScalar3
  nlinarith [h.nonneg1, h.nonneg2, h.nonneg3]

theorem norm_le_scalar_sq {l1 l2 l3 delta : Real}
    (h : PinchEigen3 l1 l2 l3 delta) :
    ricciEigenNormSq3 l1 l2 l3 <= ricciEigenScalar3 l1 l2 l3 ^ 2 :=
  ricciEigenNormSq3_le_scalar_sq_of_nonnegative
    l1 l2 l3 h.nonneg1 h.nonneg2 h.nonneg3


theorem q_lower {l1 l2 l3 delta : Real}
    (h : PinchEigen3 l1 l2 l3 delta) :
    2 * delta ^ 2 * ricciEigenNormSq3 l1 l2 l3 *
        tracefreeRicciEigenNormSq3 l1 l2 l3 <=
      hamiltonCubicQ3 l1 l2 l3 :=
  hamiltonCubicQ3_lower_bound_ordered_nonnegative_eigenvalues
    l1 l2 l3 delta h.ord12 h.ord23 h.nonneg1 h.nonneg2 h.nonneg3
    h.delta_nonneg h.lower


theorem q_sub_nonneg {l1 l2 l3 delta epsilon : Real}
    (h : PinchEigen3 l1 l2 l3 delta)
    (hepsilon : epsilon <= 2 * delta ^ 2) :
    0 <= hamiltonCubicQ3 l1 l2 l3 -
      epsilon * ricciEigenNormSq3 l1 l2 l3 *
        tracefreeRicciEigenNormSq3 l1 l2 l3 :=
  hamQ3_sub_nonneg l1 l2 l3 delta epsilon h.ord12 h.ord23
    h.delta_nonneg hepsilon h.scalar_nonneg h.lower h.norm_le_scalar_sq

end PinchEigen3




structure PinchEigen3Unordered (l1 l2 l3 delta : Real) : Prop where
  nonneg1 : 0 <= l1
  nonneg2 : 0 <= l2
  nonneg3 : 0 <= l3
  delta_nonneg : 0 <= delta
  lower1 : delta * ricciEigenScalar3 l1 l2 l3 <= l1
  lower2 : delta * ricciEigenScalar3 l1 l2 l3 <= l2
  lower3 : delta * ricciEigenScalar3 l1 l2 l3 <= l3

namespace PinchEigen3Unordered

private theorem q_sub_nonneg_ordered_perm
    {l1 l2 l3 delta epsilon a b c : Real}
    (h : PinchEigen3Unordered l1 l2 l3 delta)
    (hepsilon : epsilon <= 2 * delta ^ 2)
    (hba : b <= a) (hcb : c <= b)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hlower : delta * ricciEigenScalar3 a b c <= c)
    (hperm :
      hamiltonCubicQ3 l1 l2 l3 -
          epsilon * ricciEigenNormSq3 l1 l2 l3 *
            tracefreeRicciEigenNormSq3 l1 l2 l3 =
        hamiltonCubicQ3 a b c -
          epsilon * ricciEigenNormSq3 a b c *
            tracefreeRicciEigenNormSq3 a b c) :
    0 <= hamiltonCubicQ3 l1 l2 l3 -
      epsilon * ricciEigenNormSq3 l1 l2 l3 *
        tracefreeRicciEigenNormSq3 l1 l2 l3 := by
  rw [hperm]
  exact PinchEigen3.q_sub_nonneg
    ({ ord12 := hba
       ord23 := hcb
       nonneg1 := ha
       nonneg2 := hb
       nonneg3 := hc
       delta_nonneg := h.delta_nonneg
       lower := hlower } : PinchEigen3 a b c delta)
    hepsilon

private theorem q_expr_perm_123_132
    (l1 l2 l3 epsilon : Real) :
    hamiltonCubicQ3 l1 l2 l3 -
        epsilon * ricciEigenNormSq3 l1 l2 l3 *
          tracefreeRicciEigenNormSq3 l1 l2 l3 =
      hamiltonCubicQ3 l1 l3 l2 -
        epsilon * ricciEigenNormSq3 l1 l3 l2 *
          tracefreeRicciEigenNormSq3 l1 l3 l2 := by
  unfold hamiltonCubicQ3 ricciEigenNormSq3 tracefreeRicciEigenNormSq3
    ricciEigenPairwiseGapSq3 ricciEigenScalar3 ricciEigenTraceCube3
  ring

private theorem q_expr_perm_123_312
    (l1 l2 l3 epsilon : Real) :
    hamiltonCubicQ3 l1 l2 l3 -
        epsilon * ricciEigenNormSq3 l1 l2 l3 *
          tracefreeRicciEigenNormSq3 l1 l2 l3 =
      hamiltonCubicQ3 l3 l1 l2 -
        epsilon * ricciEigenNormSq3 l3 l1 l2 *
          tracefreeRicciEigenNormSq3 l3 l1 l2 := by
  unfold hamiltonCubicQ3 ricciEigenNormSq3 tracefreeRicciEigenNormSq3
    ricciEigenPairwiseGapSq3 ricciEigenScalar3 ricciEigenTraceCube3
  ring

private theorem q_expr_perm_123_213
    (l1 l2 l3 epsilon : Real) :
    hamiltonCubicQ3 l1 l2 l3 -
        epsilon * ricciEigenNormSq3 l1 l2 l3 *
          tracefreeRicciEigenNormSq3 l1 l2 l3 =
      hamiltonCubicQ3 l2 l1 l3 -
        epsilon * ricciEigenNormSq3 l2 l1 l3 *
          tracefreeRicciEigenNormSq3 l2 l1 l3 := by
  unfold hamiltonCubicQ3 ricciEigenNormSq3 tracefreeRicciEigenNormSq3
    ricciEigenPairwiseGapSq3 ricciEigenScalar3 ricciEigenTraceCube3
  ring

private theorem q_expr_perm_123_231
    (l1 l2 l3 epsilon : Real) :
    hamiltonCubicQ3 l1 l2 l3 -
        epsilon * ricciEigenNormSq3 l1 l2 l3 *
          tracefreeRicciEigenNormSq3 l1 l2 l3 =
      hamiltonCubicQ3 l2 l3 l1 -
        epsilon * ricciEigenNormSq3 l2 l3 l1 *
          tracefreeRicciEigenNormSq3 l2 l3 l1 := by
  unfold hamiltonCubicQ3 ricciEigenNormSq3 tracefreeRicciEigenNormSq3
    ricciEigenPairwiseGapSq3 ricciEigenScalar3 ricciEigenTraceCube3
  ring

private theorem q_expr_perm_123_321
    (l1 l2 l3 epsilon : Real) :
    hamiltonCubicQ3 l1 l2 l3 -
        epsilon * ricciEigenNormSq3 l1 l2 l3 *
          tracefreeRicciEigenNormSq3 l1 l2 l3 =
      hamiltonCubicQ3 l3 l2 l1 -
        epsilon * ricciEigenNormSq3 l3 l2 l1 *
          tracefreeRicciEigenNormSq3 l3 l2 l1 := by
  unfold hamiltonCubicQ3 ricciEigenNormSq3 tracefreeRicciEigenNormSq3
    ricciEigenPairwiseGapSq3 ricciEigenScalar3 ricciEigenTraceCube3
  ring


theorem q_sub_nonneg {l1 l2 l3 delta epsilon : Real}
    (h : PinchEigen3Unordered l1 l2 l3 delta)
    (hepsilon : epsilon <= 2 * delta ^ 2) :
    0 <= hamiltonCubicQ3 l1 l2 l3 -
      epsilon * ricciEigenNormSq3 l1 l2 l3 *
        tracefreeRicciEigenNormSq3 l1 l2 l3 := by
  by_cases h12 : l2 <= l1
  · by_cases h23 : l3 <= l2
    · exact q_sub_nonneg_ordered_perm h hepsilon h12 h23
        h.nonneg1 h.nonneg2 h.nonneg3 h.lower3 rfl
    · have h23' : l2 <= l3 := le_of_not_ge h23
      by_cases h13 : l3 <= l1
      · have hscal :
            delta * ricciEigenScalar3 l1 l3 l2 <= l2 := by
          have hs :
              ricciEigenScalar3 l1 l3 l2 = ricciEigenScalar3 l1 l2 l3 := by
            unfold ricciEigenScalar3
            ring
          rw [hs]
          exact h.lower2
        exact q_sub_nonneg_ordered_perm h hepsilon h13 h23'
          h.nonneg1 h.nonneg3 h.nonneg2 hscal
          (q_expr_perm_123_132 l1 l2 l3 epsilon)
      · have h31 : l1 <= l3 := le_of_not_ge h13
        have hscal :
            delta * ricciEigenScalar3 l3 l1 l2 <= l2 := by
          have hs :
              ricciEigenScalar3 l3 l1 l2 = ricciEigenScalar3 l1 l2 l3 := by
            unfold ricciEigenScalar3
            ring
          rw [hs]
          exact h.lower2
        exact q_sub_nonneg_ordered_perm h hepsilon h31 h12
          h.nonneg3 h.nonneg1 h.nonneg2 hscal
          (q_expr_perm_123_312 l1 l2 l3 epsilon)
  · have h21 : l1 <= l2 := le_of_not_ge h12
    by_cases h13 : l3 <= l1
    · have hscal :
          delta * ricciEigenScalar3 l2 l1 l3 <= l3 := by
        have hs :
            ricciEigenScalar3 l2 l1 l3 = ricciEigenScalar3 l1 l2 l3 := by
          unfold ricciEigenScalar3
          ring
        rw [hs]
        exact h.lower3
      exact q_sub_nonneg_ordered_perm h hepsilon h21 h13
        h.nonneg2 h.nonneg1 h.nonneg3 hscal
        (q_expr_perm_123_213 l1 l2 l3 epsilon)
    · have h31 : l1 <= l3 := le_of_not_ge h13
      by_cases h32 : l3 <= l2
      · have hscal :
            delta * ricciEigenScalar3 l2 l3 l1 <= l1 := by
          have hs :
              ricciEigenScalar3 l2 l3 l1 = ricciEigenScalar3 l1 l2 l3 := by
            unfold ricciEigenScalar3
            ring
          rw [hs]
          exact h.lower1
        exact q_sub_nonneg_ordered_perm h hepsilon h32 h31
          h.nonneg2 h.nonneg3 h.nonneg1 hscal
          (q_expr_perm_123_231 l1 l2 l3 epsilon)
      · have h23 : l2 <= l3 := le_of_not_ge h32
        have hscal :
            delta * ricciEigenScalar3 l3 l2 l1 <= l1 := by
          have hs :
              ricciEigenScalar3 l3 l2 l1 = ricciEigenScalar3 l1 l2 l3 := by
            unfold ricciEigenScalar3
            ring
          rw [hs]
          exact h.lower1
        exact q_sub_nonneg_ordered_perm h hepsilon h23 h21
          h.nonneg3 h.nonneg2 h.nonneg1 hscal
          (q_expr_perm_123_321 l1 l2 l3 epsilon)

end PinchEigen3Unordered

end DifferentialGeometry.Integral.Connection
