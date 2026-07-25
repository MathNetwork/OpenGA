import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RiemannNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Uhlenbeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RiemannNormHeatProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BernsteinShi
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false






















































noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators









section ComponentAlgebra

variable {Idx : Type*} [Fintype Idx]



def compNormSq5 (T : Idx → Idx → Idx → Idx → Idx → Real) : Real :=
  ∑ m : Idx, ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx, (T m a b c d) ^ 2

theorem compNormSq5_nonneg (T : Idx → Idx → Idx → Idx → Idx → Real) :
    0 ≤ compNormSq5 T := by
  unfold compNormSq5
  refine Finset.sum_nonneg fun m _ => ?_
  refine Finset.sum_nonneg fun a _ => ?_
  refine Finset.sum_nonneg fun b _ => ?_
  refine Finset.sum_nonneg fun c _ => ?_
  refine Finset.sum_nonneg fun d _ => ?_
  exact sq_nonneg _


theorem sq_le_compNormSq5
    (T : Idx → Idx → Idx → Idx → Idx → Real) (m a b c d : Idx) :
    (T m a b c d) ^ 2 ≤ compNormSq5 T := by
  classical
  unfold compNormSq5
  have hd : (T m a b c d) ^ 2 ≤ ∑ d' : Idx, (T m a b c d') ^ 2 :=
    Finset.single_le_sum (f := fun d' : Idx => (T m a b c d') ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ d)
  have hc : (∑ d' : Idx, (T m a b c d') ^ 2) ≤
      ∑ c' : Idx, ∑ d' : Idx, (T m a b c' d') ^ 2 :=
    Finset.single_le_sum
      (f := fun c' : Idx => ∑ d' : Idx, (T m a b c' d') ^ 2)
      (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ c)
  have hb : (∑ c' : Idx, ∑ d' : Idx, (T m a b c' d') ^ 2) ≤
      ∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (T m a b' c' d') ^ 2 :=
    Finset.single_le_sum
      (f := fun b' : Idx => ∑ c' : Idx, ∑ d' : Idx, (T m a b' c' d') ^ 2)
      (fun i _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ b)
  have ha : (∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (T m a b' c' d') ^ 2) ≤
      ∑ a' : Idx, ∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (T m a' b' c' d') ^ 2 :=
    Finset.single_le_sum
      (f := fun a' : Idx => ∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (T m a' b' c' d') ^ 2)
      (fun i _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ a)
  have hm : (∑ a' : Idx, ∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (T m a' b' c' d') ^ 2) ≤
      ∑ m' : Idx, ∑ a' : Idx, ∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (T m' a' b' c' d') ^ 2 :=
    Finset.single_le_sum
      (f := fun m' : Idx =>
        ∑ a' : Idx, ∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (T m' a' b' c' d') ^ 2)
      (fun i _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ m)
  exact le_trans hd (le_trans hc (le_trans hb (le_trans ha hm)))


theorem abs_le_sqrt_compNormSq5
    (T : Idx → Idx → Idx → Idx → Idx → Real) (m a b c d : Idx) :
    |T m a b c d| ≤ Real.sqrt (compNormSq5 T) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_le_compNormSq5 T m a b c d)












def compNormSqMulti {r : ℕ} (A : (Fin r → Idx) → Real) : Real :=
  ∑ m : Fin r → Idx, (A m) ^ 2

theorem compNormSqMulti_nonneg {r : ℕ} (A : (Fin r → Idx) → Real) :
    0 ≤ compNormSqMulti A := by
  unfold compNormSqMulti
  exact Finset.sum_nonneg fun m _ => sq_nonneg _


theorem sq_le_compNormSqMulti {r : ℕ}
    (A : (Fin r → Idx) → Real) (m : Fin r → Idx) :
    (A m) ^ 2 ≤ compNormSqMulti A := by
  classical
  unfold compNormSqMulti
  exact Finset.single_le_sum (f := fun m' : Fin r → Idx => (A m') ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ m)


theorem abs_le_sqrt_compNormSqMulti {r : ℕ}
    (A : (Fin r → Idx) → Real) (m : Fin r → Idx) :
    |A m| ≤ Real.sqrt (compNormSqMulti A) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_le_compNormSqMulti A m)








def nablaStarRm (R : Idx → Idx → Idx → Idx → Real)
    (T : Idx → Idx → Idx → Idx → Idx → Real)
    (m a b c d : Idx) : Real :=
  ∑ e : Idx, ∑ f : Idx, R a e c f * T m e b f d




theorem abs_nablaStarRm_le
    (R : Idx → Idx → Idx → Idx → Real)
    (T : Idx → Idx → Idx → Idx → Idx → Real)
    (m a b c d : Idx) :
    |nablaStarRm R T m a b c d| ≤
      (Fintype.card Idx : Real) ^ 2 *
        (Real.sqrt (compNormSq4 R) * Real.sqrt (compNormSq5 T)) := by
  classical
  have hStep :
      |nablaStarRm R T m a b c d| ≤
        ∑ e : Idx, ∑ f : Idx, |R a e c f * T m e b f d| := by
    unfold nablaStarRm
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun e _ => ?_
    exact Finset.abs_sum_le_sum_abs _ _
  refine le_trans hStep ?_
  have hsqrtR : 0 ≤ Real.sqrt (compNormSq4 R) := Real.sqrt_nonneg _
  have hsqrtT : 0 ≤ Real.sqrt (compNormSq5 T) := Real.sqrt_nonneg _
  have hTerm : ∀ e f : Idx,
      |R a e c f * T m e b f d| ≤
        Real.sqrt (compNormSq4 R) * Real.sqrt (compNormSq5 T) := by
    intro e f
    rw [abs_mul]
    have hbnd : |R a e c f| ≤ Real.sqrt (compNormSq4 R) :=
      abs_le_sqrt_compNormSq4 R a e c f
    have hbnd2 : |T m e b f d| ≤ Real.sqrt (compNormSq5 T) :=
      abs_le_sqrt_compNormSq5 T m e b f d
    exact mul_le_mul hbnd hbnd2 (abs_nonneg _) hsqrtR
  calc
    (∑ e : Idx, ∑ f : Idx, |R a e c f * T m e b f d|)
        ≤ ∑ e : Idx, ∑ f : Idx,
            Real.sqrt (compNormSq4 R) * Real.sqrt (compNormSq5 T) := by
          refine Finset.sum_le_sum fun e _ => ?_
          exact Finset.sum_le_sum fun f _ => hTerm e f
    _ = (Fintype.card Idx : Real) ^ 2 *
          (Real.sqrt (compNormSq4 R) * Real.sqrt (compNormSq5 T)) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sq]
          ring








def nablaRmReactionDown (R : Idx → Idx → Idx → Idx → Real)
    (T : Idx → Idx → Idx → Idx → Idx → Real) : Real :=
  2 * ∑ m : Idx, ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
    T m a b c d * nablaStarRm R T m a b c d










theorem abs_nablaRmReactionDown_le
    (R : Idx → Idx → Idx → Idx → Real)
    (T : Idx → Idx → Idx → Idx → Idx → Real) :
    |nablaRmReactionDown R T| ≤
      2 * (Fintype.card Idx : Real) ^ 7 *
        (compNormSq5 T * Real.sqrt (compNormSq4 R)) := by
  classical
  set NT : Real := compNormSq5 T with hNT
  set NR : Real := compNormSq4 R with hNR
  have hNTnonneg : 0 ≤ NT := compNormSq5_nonneg T
  have hsqrtT_nonneg : 0 ≤ Real.sqrt NT := Real.sqrt_nonneg _
  have hsqrtR_nonneg : 0 ≤ Real.sqrt NR := Real.sqrt_nonneg _

  have hInner :
      |∑ m : Idx, ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
          T m a b c d * nablaStarRm R T m a b c d| ≤
        ∑ m : Idx, ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
          (Real.sqrt NT *
            ((Fintype.card Idx : Real) ^ 2 * (Real.sqrt NR * Real.sqrt NT))) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun m _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun a _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun b _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun c _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun d _ => ?_
    rw [abs_mul]
    have hbnd1 : |T m a b c d| ≤ Real.sqrt NT := by
      rw [hNT]; exact abs_le_sqrt_compNormSq5 T m a b c d
    have hbnd2 :
        |nablaStarRm R T m a b c d| ≤
          (Fintype.card Idx : Real) ^ 2 * (Real.sqrt NR * Real.sqrt NT) := by
      rw [hNR, hNT]; exact abs_nablaStarRm_le R T m a b c d
    have hnn : (0 : Real) ≤
        (Fintype.card Idx : Real) ^ 2 * (Real.sqrt NR * Real.sqrt NT) :=
      mul_nonneg (by positivity) (mul_nonneg hsqrtR_nonneg hsqrtT_nonneg)
    exact mul_le_mul hbnd1 hbnd2 (abs_nonneg _) hsqrtT_nonneg

  have hConst :
      (∑ m : Idx, ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
          (Real.sqrt NT *
            ((Fintype.card Idx : Real) ^ 2 * (Real.sqrt NR * Real.sqrt NT)))) =
        (Fintype.card Idx : Real) ^ 5 *
          (Real.sqrt NT *
            ((Fintype.card Idx : Real) ^ 2 * (Real.sqrt NR * Real.sqrt NT))) := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring

  have hsqrtT_sq : Real.sqrt NT * Real.sqrt NT = NT :=
    Real.mul_self_sqrt hNTnonneg
  rw [hNT, hNR] at hInner hConst ⊢
  unfold nablaRmReactionDown
  rw [abs_mul]
  have h2 : |(2 : Real)| = 2 := by norm_num
  rw [h2]
  calc
    2 * |∑ m : Idx, ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
          T m a b c d * nablaStarRm R T m a b c d|
        ≤ 2 * ((Fintype.card Idx : Real) ^ 5 *
            (Real.sqrt (compNormSq5 T) *
              ((Fintype.card Idx : Real) ^ 2 *
                (Real.sqrt (compNormSq4 R) * Real.sqrt (compNormSq5 T))))) := by
          have hInner' := le_trans hInner (le_of_eq hConst)
          exact mul_le_mul_of_nonneg_left hInner' (by norm_num)
    _ = 2 * (Fintype.card Idx : Real) ^ 7 *
          (compNormSq5 T * Real.sqrt (compNormSq4 R)) := by
          have hcollapse :
              Real.sqrt (compNormSq5 T) * Real.sqrt (compNormSq5 T) = compNormSq5 T :=
            Real.mul_self_sqrt (compNormSq5_nonneg T)
          set s : Real := Real.sqrt (compNormSq5 T)
          set r : Real := Real.sqrt (compNormSq4 R)
          set c : Real := (Fintype.card Idx : Real)
          calc
            2 * (c ^ 5 * (s * (c ^ 2 * (r * s))))
                = 2 * c ^ 7 * ((s * s) * r) := by ring
            _ = 2 * c ^ 7 * (compNormSq5 T * r) := by rw [hcollapse]


















def nablaRmReactionMulti {k : ℕ}
    (Tk : (Fin (4 + k) → Idx) → Real)
    (star : ℕ → (Fin (4 + k) → Idx) → Real) : Real :=
  ∑ j ∈ Finset.range (k + 1),
    2 * ∑ m : Fin (4 + k) → Idx, Tk m * star j m











theorem abs_nablaRmReactionMulti_le {k : ℕ}
    (Tk : (Fin (4 + k) → Idx) → Real)
    (star : ℕ → (Fin (4 + k) → Idx) → Real)
    (w : ℕ → Real)
    (hwk : compNormSqMulti Tk = w k)
    (hstar : ∀ j ∈ Finset.range (k + 1), ∀ m : Fin (4 + k) → Idx,
      |star j m| ≤
        (Fintype.card Idx : Real) ^ 2 * (Real.sqrt (w j) * Real.sqrt (w (k - j)))) :
    |nablaRmReactionMulti Tk star| ≤
      ∑ j ∈ Finset.range (k + 1),
        (2 * (Fintype.card Idx : Real) ^ (6 + k)) *
          Real.sqrt (w j) * Real.sqrt (w (k - j)) * Real.sqrt (w k) := by
  classical
  unfold nablaRmReactionMulti
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun j hj => ?_

  rw [abs_mul]
  have h2 : |(2 : Real)| = 2 := by norm_num
  rw [h2]
  have hsqrtk : 0 ≤ Real.sqrt (w k) := Real.sqrt_nonneg _
  have hsqrtj : 0 ≤ Real.sqrt (w j) := Real.sqrt_nonneg _
  have hsqrtkj : 0 ≤ Real.sqrt (w (k - j)) := Real.sqrt_nonneg _

  have hinner :
      |∑ m : Fin (4 + k) → Idx, Tk m * star j m| ≤
        ∑ m : Fin (4 + k) → Idx,
          (Real.sqrt (w k) *
            ((Fintype.card Idx : Real) ^ 2 *
              (Real.sqrt (w j) * Real.sqrt (w (k - j))))) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun m _ => ?_
    rw [abs_mul]
    have hTk : |Tk m| ≤ Real.sqrt (w k) := by
      rw [← hwk]; exact abs_le_sqrt_compNormSqMulti Tk m
    have hst : |star j m| ≤
        (Fintype.card Idx : Real) ^ 2 * (Real.sqrt (w j) * Real.sqrt (w (k - j))) :=
      hstar j hj m
    exact mul_le_mul hTk hst (abs_nonneg _) hsqrtk

  have hcardpi :
      (Fintype.card (Fin (4 + k) → Idx) : Real) =
        (Fintype.card Idx : Real) ^ (4 + k) := by
    rw [Fintype.card_pi]
    simp [Finset.prod_const, Finset.card_univ]
  have hcard :
      (∑ m : Fin (4 + k) → Idx,
          (Real.sqrt (w k) *
            ((Fintype.card Idx : Real) ^ 2 *
              (Real.sqrt (w j) * Real.sqrt (w (k - j)))))) =
        (Fintype.card Idx : Real) ^ (4 + k) *
          (Real.sqrt (w k) *
            ((Fintype.card Idx : Real) ^ 2 *
              (Real.sqrt (w j) * Real.sqrt (w (k - j))))) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardpi]
  have hpow :
      (Fintype.card Idx : Real) ^ (4 + k) * (Fintype.card Idx : Real) ^ 2 =
        (Fintype.card Idx : Real) ^ (6 + k) := by
    rw [← pow_add]; congr 1; omega
  calc
    2 * |∑ m : Fin (4 + k) → Idx, Tk m * star j m|
        ≤ 2 * ((Fintype.card Idx : Real) ^ (4 + k) *
            (Real.sqrt (w k) *
              ((Fintype.card Idx : Real) ^ 2 *
                (Real.sqrt (w j) * Real.sqrt (w (k - j)))))) := by
          exact mul_le_mul_of_nonneg_left (le_trans hinner (le_of_eq hcard)) (by norm_num)
    _ = (2 * (Fintype.card Idx : Real) ^ (6 + k)) *
          Real.sqrt (w j) * Real.sqrt (w (k - j)) * Real.sqrt (w k) := by
          rw [← hpow]; ring

end ComponentAlgebra










section Solution

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]



omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem nablaRm04NormSqInFrame_eq_compNormSq5
    (nablaRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (t : Real) (x : M)
    (horth : InverseMetricOrthonormalAt (M := M) gInv t x) :
    nablaRm04NormSqInFrame (M := M) nablaRm04 gInv t x =
      compNormSq5 (fun m a b c d : Idx => nablaRm04 t x m a b c d) := by
  classical
  unfold nablaRm04NormSqInFrame compNormSq5
  unfold InverseMetricOrthonormalAt at horth


  refine Finset.sum_congr rfl fun a _ => ?_

  rw [Finset.sum_eq_single a]
  ·
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_



    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · rw [Finset.sum_eq_single k]
        · rw [Finset.sum_eq_single l]
          · simp [horth, sq]
          · intro s _ hs; simp [horth, Ne.symm hs]
          · intro h; exact absurd (Finset.mem_univ l) h
        · intro r _ hr; simp [horth, Ne.symm hr]
        · intro h; exact absurd (Finset.mem_univ k) h
      · intro q _ hq; simp [horth, Ne.symm hq]
      · intro h; exact absurd (Finset.mem_univ j) h
    · intro p _ hp; simp [horth, Ne.symm hp]
    · intro h; exact absurd (Finset.mem_univ i) h
  ·
    intro b _ hb
    simp [horth, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ a) h





def nablaRmReactionInFrame
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (nablaRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    nablaRmReactionDown
      (fun a b c d : Idx =>
        DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x a b c d)
      (fun m a b c d : Idx => nablaRm04 t x m a b c d)






omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem abs_nablaRmReactionInFrame_le
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (nablaRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (horth : InverseMetricOrthonormalAt (M := M) gInv t x) :
    |nablaRmReactionInFrame (I := I) Rm04 nablaRm04 frame t x| ≤
      2 * (Fintype.card Idx : Real) ^ 7 *
        (nablaRm04NormSqInFrame (M := M) nablaRm04 gInv t x *
          Real.sqrt (rm04NormSqInFrame (I := I) Rm04 gInv frame t x)) := by
  rw [nablaRmReactionInFrame]
  rw [nablaRm04NormSqInFrame_eq_compNormSq5 (M := M) nablaRm04 gInv t x horth]
  rw [rm04NormSqInFrame_eq_compNormSq4 (I := I) Rm04 gInv frame t x horth]
  exact abs_nablaRmReactionDown_le _ _


















def NablaRm04NormHeatEquationOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (nablaRmNormSq nablaRmNormLap nabla2RmNormSq reaction : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => nablaRmNormSq s x)
      (nablaRmNormLap (t : Real) x +
        (-2 * nabla2RmNormSq (t : Real) x + reaction (t : Real) x))
      D.carrier
      (t : Real)













omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem nablaRm04NormHeatBoundSharp_of_components
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (nablaRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRmNormLap nabla2RmNormSq : Real -> M -> Real)
    (horth : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      InverseMetricOrthonormalAt (M := M) gInv (t : Real) x)
    (h_heat : NablaRm04NormHeatEquationOn
      (D := D) (nablaRm04NormSqInFrame (M := M) nablaRm04 gInv)
      nablaRmNormLap nabla2RmNormSq
      (nablaRmReactionInFrame (I := I) Rm04 nablaRm04 frame)) :
    ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      ∃ d : Real,
        HasDerivWithinAt
          (fun s : Real => nablaRm04NormSqInFrame (M := M) nablaRm04 gInv s x)
          d D.carrier (t : Real) ∧
        d ≤ nablaRmNormLap (t : Real) x +
          (-2 * nabla2RmNormSq (t : Real) x +
            (2 * (Fintype.card Idx : Real) ^ 7) *
              Real.sqrt (rm04NormSqInFrame (I := I) Rm04 gInv frame (t : Real) x) *
                nablaRm04NormSqInFrame (M := M) nablaRm04 gInv (t : Real) x) := by
  intro t x
  refine ⟨_, h_heat t x, ?_⟩

  set u : Real := nablaRm04NormSqInFrame (M := M) nablaRm04 gInv (t : Real) x with hu
  set v : Real := rm04NormSqInFrame (I := I) Rm04 gInv frame (t : Real) x with hv
  have hreact_le :
      nablaRmReactionInFrame (I := I) Rm04 nablaRm04 frame (t : Real) x ≤
        2 * (Fintype.card Idx : Real) ^ 7 * (u * Real.sqrt v) := by
    have habs := abs_nablaRmReactionInFrame_le (I := I) Rm04 nablaRm04 gInv frame
      (t : Real) x (horth t x)
    rw [← hu, ← hv] at habs
    exact le_trans (le_abs_self _) habs

  have hrewrite :
      2 * (Fintype.card Idx : Real) ^ 7 * (u * Real.sqrt v) =
        (2 * (Fintype.card Idx : Real) ^ 7) * Real.sqrt v * u := by ring
  rw [hrewrite] at hreact_le

  linarith [hreact_le]












omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem nablaRm04NormHeatBoundOn_of_components
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (nablaRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRmNormLap nabla2RmNormSq : Real -> M -> Real)
    (horth : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      InverseMetricOrthonormalAt (M := M) gInv (t : Real) x)
    (hnabla2_nonneg : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M), 0 ≤ nabla2RmNormSq (t : Real) x)
    (h_heat : NablaRm04NormHeatEquationOn
      (D := D) (nablaRm04NormSqInFrame (M := M) nablaRm04 gInv)
      nablaRmNormLap nabla2RmNormSq
      (nablaRmReactionInFrame (I := I) Rm04 nablaRm04 frame)) :
    NablaRm04NormHeatBoundOn
      (D := D) (nablaRm04NormSqInFrame (M := M) nablaRm04 gInv)
      nablaRmNormLap (rm04NormSqInFrame (I := I) Rm04 gInv frame)
      (2 * (Fintype.card Idx : Real) ^ 7) := by
  intro t x
  obtain ⟨d, hderiv, hle⟩ :=
    nablaRm04NormHeatBoundSharp_of_components (I := I) Rm04 nablaRm04 gInv frame
      nablaRmNormLap nabla2RmNormSq horth h_heat t x
  refine ⟨d, hderiv, ?_⟩

  have hdrop : 0 ≤ 2 * nabla2RmNormSq (t : Real) x := by
    have := hnabla2_nonneg t x; linarith
  linarith [hle, hdrop]

end Solution

end DifferentialGeometry.PDE.RicciFlow
