import DifferentialGeometry.Analysis.Spectral.Scalar.EigenIdx
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Real


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.Spectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def scalarSobolevWeight {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) (σ : ℝ) : ℝ :=
  (1 + EigenIdx.lambda (I := I) (M := M) i) ^ σ

omit [NeZero (Module.finrank ℝ E)] in
lemma one_le_one_add_lambda {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) :
    (1 : ℝ) ≤ 1 + EigenIdx.lambda (I := I) (M := M) i := by
  have h := EigenIdx.lambda_nonneg (I := I) (M := M) i
  linarith

omit [NeZero (Module.finrank ℝ E)] in
lemma scalarSobolevWeight_pos {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) (σ : ℝ) :
    0 < scalarSobolevWeight (I := I) (M := M) i σ := by
  unfold scalarSobolevWeight
  have h : (1 : ℝ) ≤ 1 + EigenIdx.lambda (I := I) (M := M) i :=
    one_le_one_add_lambda (I := I) (M := M) i
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos h) σ

omit [NeZero (Module.finrank ℝ E)] in
lemma scalarSobolevWeight_nonneg {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) (σ : ℝ) :
    0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
  (scalarSobolevWeight_pos (I := I) (M := M) i σ).le

omit [NeZero (Module.finrank ℝ E)] in
lemma one_le_scalarSobolevWeight {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) {σ : ℝ} (hσ : 0 ≤ σ) :
    1 ≤ scalarSobolevWeight (I := I) (M := M) i σ := by
  unfold scalarSobolevWeight
  exact Real.one_le_rpow (one_le_one_add_lambda (I := I) (M := M) i) hσ

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma scalarSobolevWeight_zero {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) :
    scalarSobolevWeight (I := I) (M := M) i (0 : ℝ) = 1 := by
  unfold scalarSobolevWeight
  exact Real.rpow_zero _

omit [NeZero (Module.finrank ℝ E)] in
lemma sq_sqrt_scalarSobolevWeight {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) (σ : ℝ) :
    Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) ^ 2 =
      scalarSobolevWeight (I := I) (M := M) i σ :=
  Real.sq_sqrt (scalarSobolevWeight_nonneg (I := I) (M := M) i σ)

def scalarL2Coeff {g : SmoothRiemannianMetric I M}
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (i : EigenIdx (I := I) (M := M) g) : ℝ :=
  (resolventHilbertEigenbasisSigma (I := I) (M := M) g).repr u i

structure scalarHs (g : SmoothRiemannianMetric I M) (σ : ℝ) where

  coeff : EigenIdx (I := I) (M := M) g → ℝ

  weighted_summable :
    Summable (fun i => scalarSobolevWeight (I := I) (M := M) i σ *
      (coeff i) ^ 2)

namespace scalarHs

variable {g : SmoothRiemannianMetric I M} {σ : ℝ}

omit [NeZero (Module.finrank ℝ E)] in
@[ext] lemma ext {S T : scalarHs (I := I) (M := M) g σ}
    (h : S.coeff = T.coeff) : S = T := by
  cases S; cases T; cases h; rfl

instance : Zero (scalarHs (I := I) (M := M) g σ) where
  zero := ⟨fun _ => 0, by simp⟩

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma zero_coeff :
    (0 : scalarHs (I := I) (M := M) g σ).coeff =
      (fun _ => 0) := rfl

instance : Add (scalarHs (I := I) (M := M) g σ) where
  add S T :=
    { coeff := fun i => S.coeff i + T.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have hT := T.weighted_summable
        have h_dom : Summable
            (fun i : EigenIdx (I := I) (M := M) g =>
              2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                  (S.coeff i) ^ 2) +
                2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                  (T.coeff i) ^ 2)) :=
          (hS.mul_left 2).add (hT.mul_left 2)
        refine Summable.of_nonneg_of_le ?_ ?_ h_dom
        · intro i
          have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
            scalarSobolevWeight_nonneg (I := I) (M := M) i σ
          positivity
        · intro i
          have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
            scalarSobolevWeight_nonneg (I := I) (M := M) i σ
          have h_sq : (S.coeff i + T.coeff i) ^ 2 ≤
              2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2 := by
            nlinarith [sq_nonneg (S.coeff i - T.coeff i)]
          calc
            scalarSobolevWeight (I := I) (M := M) i σ *
                  (S.coeff i + T.coeff i) ^ 2
                ≤ scalarSobolevWeight (I := I) (M := M) i σ *
                  (2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2) :=
                  mul_le_mul_of_nonneg_left h_sq hw
            _ = 2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                    (S.coeff i) ^ 2) +
                  2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                    (T.coeff i) ^ 2) := by ring }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma add_coeff
    (S T : scalarHs (I := I) (M := M) g σ) :
    (S + T).coeff = (fun i => S.coeff i + T.coeff i) := rfl

instance : Neg (scalarHs (I := I) (M := M) g σ) where
  neg S :=
    { coeff := fun i => -S.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have h_eq :
            (fun i : EigenIdx (I := I) (M := M) g =>
              scalarSobolevWeight (I := I) (M := M) i σ *
                (-S.coeff i) ^ 2) =
            (fun i => scalarSobolevWeight (I := I) (M := M) i σ *
                (S.coeff i) ^ 2) := by
          funext i; ring
        rwa [h_eq] }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma neg_coeff (S : scalarHs (I := I) (M := M) g σ) :
    (-S).coeff = (fun i => -S.coeff i) := rfl

instance : Sub (scalarHs (I := I) (M := M) g σ) where
  sub S T :=
    { coeff := fun i => S.coeff i - T.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have hT := T.weighted_summable
        have h_dom : Summable
            (fun i : EigenIdx (I := I) (M := M) g =>
              2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                  (S.coeff i) ^ 2) +
                2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                  (T.coeff i) ^ 2)) :=
          (hS.mul_left 2).add (hT.mul_left 2)
        refine Summable.of_nonneg_of_le ?_ ?_ h_dom
        · intro i
          have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
            scalarSobolevWeight_nonneg (I := I) (M := M) i σ
          positivity
        · intro i
          have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
            scalarSobolevWeight_nonneg (I := I) (M := M) i σ
          have h_sq : (S.coeff i - T.coeff i) ^ 2 ≤
              2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2 := by
            nlinarith [sq_nonneg (S.coeff i + T.coeff i)]
          calc
            scalarSobolevWeight (I := I) (M := M) i σ *
                  (S.coeff i - T.coeff i) ^ 2
                ≤ scalarSobolevWeight (I := I) (M := M) i σ *
                  (2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2) :=
                  mul_le_mul_of_nonneg_left h_sq hw
            _ = 2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                    (S.coeff i) ^ 2) +
                  2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                    (T.coeff i) ^ 2) := by ring }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma sub_coeff
    (S T : scalarHs (I := I) (M := M) g σ) :
    (S - T).coeff = (fun i => S.coeff i - T.coeff i) := rfl

instance : SMul ℝ (scalarHs (I := I) (M := M) g σ) where
  smul c S :=
    { coeff := fun i => c * S.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have h_eq :
            (fun i : EigenIdx (I := I) (M := M) g =>
              scalarSobolevWeight (I := I) (M := M) i σ *
                (c * S.coeff i) ^ 2) =
            (fun i => c ^ 2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                (S.coeff i) ^ 2)) := by
          funext i; ring
        rw [h_eq]
        exact hS.mul_left _ }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma smul_coeff (c : ℝ)
    (S : scalarHs (I := I) (M := M) g σ) :
    (c • S).coeff = (fun i => c * S.coeff i) := rfl

instance : AddCommGroup (scalarHs (I := I) (M := M) g σ) where
  add_assoc S T U := by ext i; simp [add_assoc]
  zero_add S := by ext i; simp
  add_zero S := by ext i; simp
  add_comm S T := by ext i; simp [add_comm]
  neg_add_cancel S := by ext i; simp
  sub_eq_add_neg S T := by ext i; simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℝ (scalarHs (I := I) (M := M) g σ) where
  one_smul S := by ext i; simp
  mul_smul a b S := by ext i; simp [mul_assoc]
  smul_zero c := by ext i; simp
  smul_add c S T := by ext i; simp [mul_add]
  add_smul a b S := by ext i; simp [add_mul]
  zero_smul S := by ext i; simp

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedProd_summable
    (S T : scalarHs (I := I) (M := M) g σ) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      scalarSobolevWeight (I := I) (M := M) i σ *
        (S.coeff i * T.coeff i)) := by
  have hS := S.weighted_summable
  have hT := T.weighted_summable
  have h_dom : Summable
      (fun i : EigenIdx (I := I) (M := M) g =>
        (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
            (S.coeff i) ^ 2) +
          (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
            (T.coeff i) ^ 2)) :=
    (hS.mul_left _).add (hT.mul_left _)
  refine Summable.of_norm_bounded h_dom ?_
  intro i
  have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
    scalarSobolevWeight_nonneg (I := I) (M := M) i σ
  have h_amgm :
      |scalarSobolevWeight (I := I) (M := M) i σ *
          (S.coeff i * T.coeff i)| ≤
        (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
            (S.coeff i) ^ 2) +
          (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
            (T.coeff i) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hw]
    have h_prod : |S.coeff i * T.coeff i| ≤
        (1 / 2) * (S.coeff i) ^ 2 + (1 / 2) * (T.coeff i) ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|S.coeff i| - |T.coeff i|),
        abs_nonneg (S.coeff i), abs_nonneg (T.coeff i),
        sq_abs (S.coeff i), sq_abs (T.coeff i)]
    calc
      scalarSobolevWeight (I := I) (M := M) i σ *
            |S.coeff i * T.coeff i|
          ≤ scalarSobolevWeight (I := I) (M := M) i σ *
            ((1 / 2) * (S.coeff i) ^ 2 + (1 / 2) * (T.coeff i) ^ 2) :=
            mul_le_mul_of_nonneg_left h_prod hw
      _ = (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
              (S.coeff i) ^ 2) +
            (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
              (T.coeff i) ^ 2) := by ring
  simpa using h_amgm

def innerFun (S T : scalarHs (I := I) (M := M) g σ) : ℝ :=
  ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
    (S.coeff i * T.coeff i)

omit [NeZero (Module.finrank ℝ E)] in
lemma innerFun_self (T : scalarHs (I := I) (M := M) g σ) :
    innerFun (I := I) (M := M) T T =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 := by
  unfold innerFun
  refine tsum_congr (fun i => ?_)
  rw [sq]

@[reducible] def innerCore :
    InnerProductSpace.Core ℝ
      (scalarHs (I := I) (M := M) g σ) where
  inner S T := innerFun (I := I) (M := M) S T
  conj_inner_symm S T := by
    simp only [conj_trivial]
    unfold innerFun
    refine tsum_congr (fun i => ?_)
    ring
  re_inner_nonneg T := by
    simp only [RCLike.re_to_real]
    rw [show (innerFun (I := I) (M := M) T T) =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 from innerFun_self (I := I) (M := M) T]
    refine tsum_nonneg (fun i => ?_)
    have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
      scalarSobolevWeight_nonneg (I := I) (M := M) i σ
    positivity
  add_left S T U := by
    change innerFun (I := I) (M := M) (S + T) U =
      innerFun (I := I) (M := M) S U + innerFun (I := I) (M := M) T U
    unfold innerFun
    rw [← Summable.tsum_add
      (weightedProd_summable (I := I) (M := M) S U)
      (weightedProd_summable (I := I) (M := M) T U)]
    refine tsum_congr (fun i => ?_)
    simp only [add_coeff]
    ring
  smul_left S T c := by
    simp only [conj_trivial]
    change innerFun (I := I) (M := M) (c • S) T =
      c * innerFun (I := I) (M := M) S T
    unfold innerFun
    rw [← tsum_mul_left]
    refine tsum_congr (fun i => ?_)
    simp only [smul_coeff]
    ring
  definite T hT := by
    rw [show (innerFun (I := I) (M := M) T T) =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 from innerFun_self (I := I) (M := M) T] at hT
    have h_nonneg : ∀ i : EigenIdx (I := I) (M := M) g,
        0 ≤ scalarSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 := by
      intro i
      have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
        scalarSobolevWeight_nonneg (I := I) (M := M) i σ
      positivity
    have h_zero : ∀ i : EigenIdx (I := I) (M := M) g,
        scalarSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 = 0 := by
      intro i
      have h_le := Summable.le_tsum T.weighted_summable i
        (fun j _ => h_nonneg j)
      rw [hT] at h_le
      exact le_antisymm h_le (h_nonneg i)
    ext i
    have hwi : scalarSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2
        = 0 := h_zero i
    have hw_ne : scalarSobolevWeight (I := I) (M := M) i σ ≠ 0 :=
      (scalarSobolevWeight_pos (I := I) (M := M) i σ).ne'
    have h_sq : (T.coeff i) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hwi with h | h
      · exact absurd h hw_ne
      · exact h
    have : T.coeff i = 0 := by nlinarith [h_sq]
    simpa using this

instance instNormedAddCommGroup :
    NormedAddCommGroup (scalarHs (I := I) (M := M) g σ) :=
  InnerProductSpace.Core.toNormedAddCommGroup
    (cd := innerCore (I := I) (M := M) (g := g) (σ := σ))

instance instInnerProductSpace :
    InnerProductSpace ℝ (scalarHs (I := I) (M := M) g σ) :=
  InnerProductSpace.ofCore
    (innerCore (I := I) (M := M) (g := g) (σ := σ)).1

omit [NeZero (Module.finrank ℝ E)] in
lemma inner_def (S T : scalarHs (I := I) (M := M) g σ) :
    (inner ℝ S T : ℝ) =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (S.coeff i * T.coeff i) := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma inner_self_eq (T : scalarHs (I := I) (M := M) g σ) :
    (inner ℝ T T : ℝ) =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 :=
  innerFun_self (I := I) (M := M) T

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_sq_eq_tsum
    (T : scalarHs (I := I) (M := M) g σ) :
    ‖T‖ ^ 2 =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_self_eq]

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_eq_sqrt_tsum
    (T : scalarHs (I := I) (M := M) g σ) :
    ‖T‖ =
      Real.sqrt (∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2) := by
  rw [← norm_sq_eq_tsum]
  exact (Real.sqrt_sq (norm_nonneg T)).symm

end scalarHs

namespace scalarHs

variable {g : SmoothRiemannianMetric I M} {σ : ℝ}

omit [NeZero (Module.finrank ℝ E)] in
lemma rescale_memℓp (T : scalarHs (I := I) (M := M) g σ) :
    Memℓp (fun i : EigenIdx (I := I) (M := M) g =>
      Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
        T.coeff i) 2 := by
  apply memℓp_gen
  have h_eq :
      (fun i : EigenIdx (I := I) (M := M) g =>
        ‖Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
            T.coeff i‖ ^ (2 : ℝ≥0∞).toReal) =
      (fun i => scalarSobolevWeight (I := I) (M := M) i σ *
          (T.coeff i) ^ 2) := by
    funext i
    have hpr : ‖Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
          T.coeff i‖ ^ (2 : ℝ≥0∞).toReal =
        ‖Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
          T.coeff i‖ ^ (2 : ℕ) := by
      rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    have hsq : Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) ^ 2 =
        scalarSobolevWeight (I := I) (M := M) i σ :=
      sq_sqrt_scalarSobolevWeight (I := I) (M := M) i σ
    rw [hpr, Real.norm_eq_abs, sq_abs, mul_pow, hsq]
  rw [h_eq]
  exact T.weighted_summable

def rescaleToL2 (T : scalarHs (I := I) (M := M) g σ) :
    lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2 :=
  ⟨fun i => Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
      T.coeff i, rescale_memℓp (I := I) (M := M) T⟩

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma rescaleToL2_apply
    (T : scalarHs (I := I) (M := M) g σ)
    (i : EigenIdx (I := I) (M := M) g) :
    (rescaleToL2 (I := I) (M := M) T : _ → ℝ) i =
      Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
        T.coeff i := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma rescaleFromL2_weighted_summable
    (f : lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      scalarSobolevWeight (I := I) (M := M) i σ *
        ((Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ))⁻¹ *
          (f : _ → ℝ) i) ^ 2) := by
  have hf : Summable (fun i : EigenIdx (I := I) (M := M) g =>
      ((f : _ → ℝ) i) ^ 2) := by
    have hmem := lp.memℓp f
    have h := hmem.summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_eq :
        (fun i : EigenIdx (I := I) (M := M) g =>
          ‖(f : _ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal) =
        (fun i => ((f : _ → ℝ) i) ^ 2) := by
      funext i
      rw [hpr, Real.norm_eq_abs, ← sq_abs]
      norm_num
    rwa [h_eq] at h
  have h_eq :
      (fun i : EigenIdx (I := I) (M := M) g =>
        scalarSobolevWeight (I := I) (M := M) i σ *
          ((Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ))⁻¹ *
            (f : _ → ℝ) i) ^ 2) =
      (fun i => ((f : _ → ℝ) i) ^ 2) := by
    funext i
    have hw_pos : 0 < scalarSobolevWeight (I := I) (M := M) i σ :=
      scalarSobolevWeight_pos (I := I) (M := M) i σ
    have hsq : Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) ^ 2 =
        scalarSobolevWeight (I := I) (M := M) i σ :=
      sq_sqrt_scalarSobolevWeight (I := I) (M := M) i σ
    rw [mul_pow, inv_pow, hsq]
    rw [← mul_assoc, mul_inv_cancel₀ hw_pos.ne', one_mul]
  rw [h_eq]
  exact hf

def rescaleFromL2
    (f : lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2) :
    scalarHs (I := I) (M := M) g σ where
  coeff i := (Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ))⁻¹ *
    (f : _ → ℝ) i
  weighted_summable := rescaleFromL2_weighted_summable (I := I) (M := M) f

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma rescaleFromL2_coeff
    (f : lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2)
    (i : EigenIdx (I := I) (M := M) g) :
    (rescaleFromL2 (I := I) (M := M) (g := g) (σ := σ) f).coeff i =
      (Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ))⁻¹ *
        (f : _ → ℝ) i := rfl

def rescaleEquivL2 :
    scalarHs (I := I) (M := M) g σ ≃ₗᵢ[ℝ]
      lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2 where
  toFun := rescaleToL2 (I := I) (M := M)
  invFun := rescaleFromL2 (I := I) (M := M)
  map_add' S T := by
    apply lp.ext
    funext i
    simp only [rescaleToL2, lp.coeFn_add, Pi.add_apply, add_coeff]
    ring
  map_smul' c T := by
    apply lp.ext
    funext i
    simp only [rescaleToL2, lp.coeFn_smul, Pi.smul_apply, smul_coeff,
      smul_eq_mul, RingHom.id_apply]
    ring
  left_inv T := by
    ext i
    simp only [rescaleFromL2_coeff, rescaleToL2_apply]
    have hsqrt_pos :
        0 < Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) :=
      Real.sqrt_pos.mpr (scalarSobolevWeight_pos (I := I) (M := M) i σ)
    rw [← mul_assoc, inv_mul_cancel₀ hsqrt_pos.ne', one_mul]
  right_inv f := by
    apply lp.ext
    funext i
    simp only [rescaleToL2_apply, rescaleFromL2_coeff]
    have hsqrt_pos :
        0 < Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) :=
      Real.sqrt_pos.mpr (scalarSobolevWeight_pos (I := I) (M := M) i σ)
    rw [← mul_assoc, mul_inv_cancel₀ hsqrt_pos.ne', one_mul]
  norm_map' T := by
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_lp_sq :
        ‖rescaleToL2 (I := I) (M := M) T‖ ^ 2 =
          ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
            (T.coeff i) ^ 2 := by
      have h := lp.norm_rpow_eq_tsum
        (p := 2)
        (E := fun _ : EigenIdx (I := I) (M := M) g => ℝ)
        (by norm_num) (rescaleToL2 (I := I) (M := M) T)
      rw [hpr] at h
      have h_lhs : ‖rescaleToL2 (I := I) (M := M) T‖ ^ (2 : ℝ) =
          ‖rescaleToL2 (I := I) (M := M) T‖ ^ 2 := by norm_cast
      rw [h_lhs] at h
      rw [h]
      refine tsum_congr (fun i => ?_)
      have hsq :
          Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) ^ 2 =
            scalarSobolevWeight (I := I) (M := M) i σ :=
        sq_sqrt_scalarSobolevWeight (I := I) (M := M) i σ
      have hcast :
          ‖(rescaleToL2 (I := I) (M := M) T : _ → ℝ) i‖ ^ (2 : ℝ) =
            ‖(rescaleToL2 (I := I) (M := M) T : _ → ℝ) i‖ ^ (2 : ℕ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hcast, rescaleToL2_apply, Real.norm_eq_abs, sq_abs, mul_pow, hsq]
    have h_norm_sq : ‖T‖ ^ 2 =
        ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
          (T.coeff i) ^ 2 :=
      norm_sq_eq_tsum (I := I) (M := M) T
    have h_eq_sq :
        ‖rescaleToL2 (I := I) (M := M) T‖ ^ 2 = ‖T‖ ^ 2 := by
      rw [h_lp_sq, h_norm_sq]
    have h1 : 0 ≤ ‖rescaleToL2 (I := I) (M := M) T‖ := norm_nonneg _
    have h2 : 0 ≤ ‖T‖ := norm_nonneg T
    have := congrArg Real.sqrt h_eq_sq
    rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at this

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma rescaleEquivL2_apply
    (T : scalarHs (I := I) (M := M) g σ) :
    (rescaleEquivL2 (I := I) (M := M) (g := g) (σ := σ) T : _ → ℝ) =
      (fun i => Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
        T.coeff i) := rfl

instance instCompleteSpace :
    CompleteSpace (scalarHs (I := I) (M := M) g σ) :=
  (rescaleEquivL2 (I := I) (M := M)
    (g := g) (σ := σ)).toIsometryEquiv.completeSpace

end scalarHs

abbrev HkScalar (g : SmoothRiemannianMetric I M) (k : ℕ) : Type _ :=
  scalarHs (I := I) (M := M) g (k : ℝ)

end Hs
end Sobolev
end Analysis
end DifferentialGeometry

end
