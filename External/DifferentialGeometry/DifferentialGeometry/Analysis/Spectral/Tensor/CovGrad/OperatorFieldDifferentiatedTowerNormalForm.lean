import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldContractionBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.GenuineCurvatureField


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_finset_sum {ι : Type*} (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (t : Finset ι) (F : ι → SmoothCcTensor g r s) :
    covGrad (I := I) (M := M) g r s (∑ i ∈ t, F i) =
      ∑ i ∈ t, covGrad (I := I) (M := M) g r s (F i) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, covGrad_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, covGrad_add, ih]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem castRankCc_db_finset_sum {ι : Type*} {a b : ℕ} (g : SmoothRiemannianMetric I M)
    (r : ℕ) (h : a = b) (t : Finset ι) (F : ι → SmoothCcTensor g r a) :
    castCcTensorRank (g := g) r h (∑ i ∈ t, F i) =
      ∑ i ∈ t, castCcTensorRank (g := g) r h (F i) := by
  subst h; rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem castRankCc_db_heq {a b : ℕ} (g : SmoothRiemannianMetric I M) (r : ℕ)
    (h : a = b) (W : SmoothCcTensor g r a) : HEq (castCcTensorRank (g := g) r h W) W := by
  subst h; exact HEq.rfl

def castCcTensorSourceRank {a a' : ℕ} (g : SmoothRiemannianMetric I M) (b : ℕ) (h : a = a')
    (W : SmoothCcTensor g a b) : SmoothCcTensor g a' b :=
  h ▸ W

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem appCc_castRankCc_db {a a' b b' : ℕ} (g : SmoothRiemannianMetric I M)
    (ha : a = a') (hb : b = b')
    (Φ : SmoothCcTensor g a b) (V : SmoothCcTensor g 0 a) :
    castCcTensorRank (g := g) 0 hb (operatorFieldApply (I := I) (M := M) (g := g) a b Φ V) =
      operatorFieldApply (I := I) (M := M) (g := g) a' b' (castCcTensorSourceRank g b' ha (castCcTensorRank (g := g) a hb Φ))
        (castCcTensorRank (g := g) 0 ha V) := by
  subst ha; subst hb; rfl

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_heq_congr' (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    HEq (covGrad g r a Y) (covGrad g r b Z) := by
  subst h; rw [eq_of_heq hYZ]

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_covGrad_comm_heq' (g : SmoothRiemannianMetric I M) (r s m : ℕ)
    (X : SmoothCcTensor g r s) :
    HEq (iteratedCovGrad g r (s + 1) m (covGrad g r s X))
      (iteratedCovGrad g r s (m + 1) X) := by
  induction m with
  | zero => rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]; exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s + 1) (j := k) (covGrad g r s X)]
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s) (j := k + 1) X]
      exact covGrad_heq_congr' g r (by omega : (s + 1) + k = s + (k + 1)) ih

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [CompleteSpace E] in
theorem appCc_zero_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) (g := g) r s (0 : SmoothCcTensor g r s) W = 0 := by
  have h := appCc_add_left (I := I) (M := M) g r s (0 : SmoothCcTensor g r s) 0 W
  rw [add_zero] at h

  have h2 : operatorFieldApply (I := I) (M := M) (g := g) r s (0 : SmoothCcTensor g r s) W -
      operatorFieldApply (I := I) (M := M) (g := g) r s (0 : SmoothCcTensor g r s) W =
      operatorFieldApply (I := I) (M := M) (g := g) r s (0 : SmoothCcTensor g r s) W := by
    nth_rewrite 1 [h]; abel
  rwa [sub_self] at h2

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [CompleteSpace E] in
theorem appCc_neg_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) (g := g) r s (-Φ) W = -operatorFieldApply (I := I) (M := M) (g := g) r s Φ W := by
  have h := appCc_add_left (I := I) (M := M) g r s Φ (-Φ) W
  rw [add_neg_cancel, appCc_zero_left] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [CompleteSpace E] in
theorem appCc_sub_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) (g := g) r s (Φ₁ - Φ₂) W =
      operatorFieldApply (I := I) (M := M) (g := g) r s Φ₁ W - operatorFieldApply (I := I) (M := M) (g := g) r s Φ₂ W := by
  rw [sub_eq_add_neg, appCc_add_left, appCc_neg_left, sub_eq_add_neg]

def IsIteratedCovGradNormalForm (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (p r : ℕ) : Prop :=
  ∃ Ψ : (k : ℕ) → SmoothCcTensor g (r + k) (r + p),
    ∀ W : SmoothCcTensor g 0 r,
      op p r W =
        ∑ k ∈ Finset.range (p + 1),
          operatorFieldApply (I := I) (M := M) (g := g) (r + k) (r + p) (Ψ k) (iteratedCovGrad g 0 r k W)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_normalForm_sum (g : SmoothRiemannianMetric I M) (p r : ℕ)
    (Ψ : (k : ℕ) → SmoothCcTensor g (r + k) (r + p)) (W : SmoothCcTensor g 0 r) :
    covGrad (I := I) (M := M) g 0 (r + p)
        (∑ k ∈ Finset.range (p + 1),
          operatorFieldApply (I := I) (M := M) (g := g) (r + k) (r + p) (Ψ k) (iteratedCovGrad g 0 r k W)) =
      ∑ k ∈ Finset.range (p + 1),
        (operatorFieldApply (I := I) (M := M) (g := g) (r + k) (r + (p + 1))
            (covGrad (I := I) (M := M) g (r + k) (r + p) (Ψ k)) (iteratedCovGrad g 0 r k W) +
          operatorFieldApply (I := I) (M := M) (g := g) (r + (k + 1)) (r + (p + 1))
            (slotExtend (I := I) (M := M) g (r + k) (r + p) (Ψ k))
            (iteratedCovGrad g 0 r (k + 1) W)) := by
  rw [covGrad_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covGrad_operatorFieldApply_eq (I := I) (M := M) g (r + k) (r + p) (Ψ k) (iteratedCovGrad g 0 r k W)]
  rw [show covGrad (I := I) (M := M) g 0 (r + k) (iteratedCovGrad g 0 r k W) =
      iteratedCovGrad g 0 r (k + 1) W from (iteratedCovGrad_succ g 0 r k W).symm]
  rfl

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem appCc_iteratedCovGrad_succ_of_covGrad (g : SmoothRiemannianMetric I M) (p r k : ℕ)
    (Ψ : SmoothCcTensor g ((r + 1) + k) ((r + 1) + p)) (W : SmoothCcTensor g 0 r) :
    castCcTensorRank (g := g) 0 (by omega : (r + 1) + p = r + (p + 1))
        (operatorFieldApply (I := I) (M := M) (g := g) ((r + 1) + k) ((r + 1) + p) Ψ
          (iteratedCovGrad g 0 (r + 1) k (covGrad g 0 r W))) =
      operatorFieldApply (I := I) (M := M) (g := g) (r + (k + 1)) (r + (p + 1))
        (castCcTensorSourceRank g (r + (p + 1)) (by omega : (r + 1) + k = r + (k + 1))
          (castCcTensorRank (g := g) ((r + 1) + k) (by omega : (r + 1) + p = r + (p + 1)) Ψ))
        (iteratedCovGrad g 0 r (k + 1) W) := by
  rw [appCc_castRankCc_db g (by omega : (r + 1) + k = r + (k + 1))
    (by omega : (r + 1) + p = r + (p + 1)) Ψ (iteratedCovGrad g 0 (r + 1) k (covGrad g 0 r W))]
  congr 1
  apply eq_of_heq
  refine HEq.trans ?_ (iteratedCovGrad_covGrad_comm_heq' g 0 r k W)
  exact castRankCc_db_heq g 0 (by omega : (r + 1) + k = r + (k + 1))
    (iteratedCovGrad g 0 (r + 1) k (covGrad g 0 r W))

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem isIteratedCovGradNormalForm_succ (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (covGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      covGrad g 0 (r + p) (op p r W) =
        op (p + 1) r W +
          castCcTensorRank (g := g) 0 (by omega : (r + 1) + p = r + (p + 1)) (op p (r + 1) (covGrad g 0 r W)))
    (p : ℕ) (hp : ∀ r, IsIteratedCovGradNormalForm (I := I) (M := M) g op p r) (r : ℕ) :
    IsIteratedCovGradNormalForm (I := I) (M := M) g op (p + 1) r := by
  classical
  obtain ⟨Ψr, hΨr⟩ := hp r
  obtain ⟨Ψr1, hΨr1⟩ := hp (r + 1)

  set Tk : (k : ℕ) → SmoothCcTensor g (r + (k + 1)) (r + (p + 1)) := fun k =>
    slotExtend (I := I) (M := M) g (r + k) (r + p) (Ψr k) -
      castCcTensorSourceRank g (r + (p + 1)) (by omega : (r + 1) + k = r + (k + 1))
        (castCcTensorRank (g := g) ((r + 1) + k) (by omega : (r + 1) + p = r + (p + 1)) (Ψr1 k))
    with hTk_def

  refine ⟨fun j => match j with
    | 0 => covGrad (I := I) (M := M) g (r + 0) (r + p) (Ψr 0)
    | (k + 1) =>
        (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (r + (k + 1)) (r + p) (Ψr (k + 1)) else 0)
          + Tk k, ?_⟩
  intro W

  have hrec : op (p + 1) r W =
      covGrad g 0 (r + p) (op p r W) -
        castCcTensorRank (g := g) 0 (by omega : (r + 1) + p = r + (p + 1))
          (op p (r + 1) (covGrad g 0 r W)) := by
    rw [covGrad_op p r W]; abel
  rw [hrec, hΨr W]

  rw [covGrad_normalForm_sum (I := I) (M := M) g p r Ψr W]

  rw [hΨr1 (covGrad g 0 r W), castRankCc_db_finset_sum]
  rw [show (∑ k ∈ Finset.range (p + 1),
        castCcTensorRank (g := g) 0 (by omega : (r + 1) + p = r + (p + 1))
          (operatorFieldApply (I := I) (M := M) (g := g) ((r + 1) + k) ((r + 1) + p) (Ψr1 k)
            (iteratedCovGrad g 0 (r + 1) k (covGrad g 0 r W)))) =
      ∑ k ∈ Finset.range (p + 1),
        operatorFieldApply (I := I) (M := M) (g := g) (r + (k + 1)) (r + (p + 1))
          (castCcTensorSourceRank g (r + (p + 1)) (by omega : (r + 1) + k = r + (k + 1))
            (castCcTensorRank (g := g) ((r + 1) + k) (by omega : (r + 1) + p = r + (p + 1)) (Ψr1 k)))
          (iteratedCovGrad g 0 r (k + 1) W) from
    Finset.sum_congr rfl (fun k _ =>
      appCc_iteratedCovGrad_succ_of_covGrad (I := I) (M := M) g p r k (Ψr1 k) W)]

  rw [Finset.sum_add_distrib]

  rw [Finset.sum_range_succ' (fun j =>
    operatorFieldApply (I := I) (M := M) (g := g) (r + j) (r + (p + 1))
      ((match j with
        | 0 => covGrad (I := I) (M := M) g (r + 0) (r + p) (Ψr 0)
        | (k + 1) =>
            (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (r + (k + 1)) (r + p) (Ψr (k + 1))
              else 0) + Tk k))
      (iteratedCovGrad g 0 r j W)) (p + 1)]

  rw [show (∑ k ∈ Finset.range (p + 1),
        operatorFieldApply (I := I) (M := M) (g := g) (r + (k + 1)) (r + (p + 1))
          ((if k + 1 < p + 1 then covGrad (I := I) (M := M) g (r + (k + 1)) (r + p) (Ψr (k + 1))
            else 0) + Tk k)
          (iteratedCovGrad g 0 r (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        operatorFieldApply (I := I) (M := M) (g := g) (r + (k + 1)) (r + (p + 1))
          (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (r + (k + 1)) (r + p) (Ψr (k + 1))
            else 0)
          (iteratedCovGrad g 0 r (k + 1) W)) +
      (∑ k ∈ Finset.range (p + 1),
        operatorFieldApply (I := I) (M := M) (g := g) (r + (k + 1)) (r + (p + 1)) (Tk k)
          (iteratedCovGrad g 0 r (k + 1) W)) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [appCc_add_left]]

  rw [show (∑ k ∈ Finset.range (p + 1),
        operatorFieldApply (I := I) (M := M) (g := g) (r + (k + 1)) (r + (p + 1)) (Tk k)
          (iteratedCovGrad g 0 r (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        operatorFieldApply (I := I) (M := M) (g := g) (r + (k + 1)) (r + (p + 1))
          (slotExtend (I := I) (M := M) g (r + k) (r + p) (Ψr k))
          (iteratedCovGrad g 0 r (k + 1) W)) -
      (∑ k ∈ Finset.range (p + 1),
        operatorFieldApply (I := I) (M := M) (g := g) (r + (k + 1)) (r + (p + 1))
          (castCcTensorSourceRank g (r + (p + 1)) (by omega : (r + 1) + k = r + (k + 1))
            (castCcTensorRank (g := g) ((r + 1) + k) (by omega : (r + 1) + p = r + (p + 1)) (Ψr1 k)))
          (iteratedCovGrad g 0 r (k + 1) W)) from by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hTk_def, appCc_sub_left]]

  rw [show (∑ k ∈ Finset.range (p + 1),
        operatorFieldApply (I := I) (M := M) (g := g) (r + (k + 1)) (r + (p + 1))
          (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (r + (k + 1)) (r + p) (Ψr (k + 1))
            else 0)
          (iteratedCovGrad g 0 r (k + 1) W)) =
      ∑ k ∈ Finset.range p,
        operatorFieldApply (I := I) (M := M) (g := g) (r + (k + 1)) (r + (p + 1))
          (covGrad (I := I) (M := M) g (r + (k + 1)) (r + p) (Ψr (k + 1)))
          (iteratedCovGrad g 0 r (k + 1) W) from by
    rw [Finset.sum_range_succ]
    rw [if_neg (by omega : ¬ (p + 1 < p + 1)), appCc_zero_left, add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [if_pos (by simp only [Finset.mem_range] at hk; omega : k + 1 < p + 1)]]

  rw [Finset.sum_range_succ' (fun k =>
    operatorFieldApply (I := I) (M := M) (g := g) (r + k) (r + (p + 1))
      (covGrad (I := I) (M := M) g (r + k) (r + p) (Ψr k)) (iteratedCovGrad g 0 r k W)) p]

  abel

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem normalForm_zero (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (r : ℕ) (Φ₀ : SmoothCcTensor g (r + 0) (r + 0))
    (hbase : ∀ W : SmoothCcTensor g 0 r, op 0 r W = operatorFieldApply (I := I) (M := M) (g := g) (r + 0) (r + 0) Φ₀ W) :
    IsIteratedCovGradNormalForm (I := I) (M := M) g op 0 r := by
  refine ⟨fun k => match k with | 0 => Φ₀ | (_ + 1) => 0, fun W => ?_⟩
  rw [hbase W, Finset.sum_range_one]
  rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem normalForm_of_base (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (covGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      covGrad g 0 (r + p) (op p r W) =
        op (p + 1) r W +
          castCcTensorRank (g := g) 0 (by omega : (r + 1) + p = r + (p + 1)) (op p (r + 1) (covGrad g 0 r W)))
    (Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0))
    (hbase : ∀ (r : ℕ) (W : SmoothCcTensor g 0 r),
      op 0 r W = operatorFieldApply (I := I) (M := M) (g := g) (r + 0) (r + 0) (Φ₀ r) W)
    (p : ℕ) : ∀ r : ℕ, IsIteratedCovGradNormalForm (I := I) (M := M) g op p r := by
  induction p with
  | zero => exact fun r => normalForm_zero (I := I) (M := M) g op r (Φ₀ r) (hbase r)
  | succ p ih => exact fun r => isIteratedCovGradNormalForm_succ (I := I) (M := M) g op covGrad_op p ih r

omit [CompleteSpace E] in
omit [BoundarylessManifold I M] in
theorem exists_jet_bound_of_normalForm (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (p r : ℕ) (hNF : IsIteratedCovGradNormalForm (I := I) (M := M) g op p r) :
    ∃ kappa : ℝ, 0 ≤ kappa ∧
      ∀ (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x ((op p r W).toSection x) ≤
          kappa * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  classical
  obtain ⟨Ψ, hΨ⟩ := hNF

  choose C hC_nn hC using fun k =>
    exists_uniform_riemannianFiberNormSq_appCc_le (I := I) (M := M) (g := g) (r + k) (r + p) (Ψ k)
  refine ⟨(p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), C k,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hC_nn k), fun W x => ?_⟩

  set a : ℕ → ℝ := fun k => riemannianFiberNormSq (I := I) (M := M) g 0 (r + k) x
    ((iteratedCovGrad g 0 r k W).toSection x) with ha_def
  have ha_nn : ∀ k, 0 ≤ a k := fun k =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + k) x _

  rw [hΨ W, SmoothCcTensor.toSection_sum_apply]

  refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 (r + p) x
    (Finset.range (p + 1))
    (fun k => (operatorFieldApply (I := I) (M := M) (g := g) (r + k) (r + p) (Ψ k)
      (iteratedCovGrad g 0 r k W)).toSection x)) ?_
  rw [Finset.card_range]

  have hsummand : ∀ k ∈ Finset.range (p + 1),
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x
          ((operatorFieldApply (I := I) (M := M) (g := g) (r + k) (r + p) (Ψ k)
            (iteratedCovGrad g 0 r k W)).toSection x) ≤ C k * a k := fun k _ => hC k _ x
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsummand) (by positivity)) ?_

  have hCa_le : (∑ k ∈ Finset.range (p + 1), C k * a k) ≤
      (∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hC_nn k)
    exact Finset.single_le_sum (f := a) (fun j _ => ha_nn j) ‹k ∈ Finset.range (p + 1)›
  rw [show ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 from by push_cast; ring]
  calc (p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), C k * a k
      ≤ (p + 1 : ℝ) * ((∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k) :=
        mul_le_mul_of_nonneg_left hCa_le (by positivity)
    _ = (p + 1 : ℝ) * (∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k := by ring

end Connection
end Integral
end DifferentialGeometry

end
