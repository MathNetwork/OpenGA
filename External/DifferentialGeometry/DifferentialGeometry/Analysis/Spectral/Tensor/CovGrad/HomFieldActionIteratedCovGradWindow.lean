import DifferentialGeometry.Geometry.Connection.TensorNabla.FullHomCovariantCalculusRS


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

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [NeZero (Module.finrank ℝ E)] in
theorem homFieldAction_iteratedCovGrad_expansion (g : SmoothRiemannianMetric I M) (r m c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r m c I) (k : ℕ) :
    ∃ D : (i : ℕ) → HomTensorRSField (E := E) (M := M) r (m + i) (c + k) I,
      ∀ W : SmoothCcTensor g r m,
        iteratedCovGrad g r c k (homTensorRSFieldApply (I := I) (M := M) g r m c Q W) =
          ∑ i ∈ Finset.range (k + 1),
            homTensorRSFieldApply (I := I) (M := M) g r (m + i) (c + k) (D i)
              (iteratedCovGrad g r m i W) := by
  classical
  induction k with
  | zero =>
      refine ⟨fun i => match i with | 0 => Q | (_ + 1) => 0, fun W => ?_⟩
      rw [Finset.sum_range_one]
      rfl
  | succ k ih =>
      obtain ⟨D, hD⟩ := ih
      refine ⟨fun i => match i with
        | 0 => homTensorRSCovGradSec (I := I) (M := M) g r (m + 0) (c + k) (D 0)
        | (i + 1) =>
            (if i + 1 < k + 1 then
                homTensorRSCovGradSec (I := I) (M := M) g r (m + (i + 1)) (c + k) (D (i + 1))
              else 0) +
              slotExtendFullSec (I := I) (M := M) g r (m + i) (c + k) (D i), fun W => ?_⟩

      rw [show iteratedCovGrad g r c (k + 1) (homTensorRSFieldApply (I := I) (M := M) g r m c Q W) =
          covGrad (I := I) (M := M) g r (c + k)
            (iteratedCovGrad g r c k (homTensorRSFieldApply (I := I) (M := M) g r m c Q W)) from rfl,
        hD W, covGrad_finset_sum]

      rw [show (∑ i ∈ Finset.range (k + 1), covGrad (I := I) (M := M) g r (c + k)
            (homTensorRSFieldApply (I := I) (M := M) g r (m + i) (c + k) (D i)
              (iteratedCovGrad g r m i W))) =
          ∑ i ∈ Finset.range (k + 1),
            (homTensorRSFieldApply (I := I) (M := M) g r (m + i) (c + (k + 1))
                (homTensorRSCovGradSec (I := I) (M := M) g r (m + i) (c + k) (D i))
                (iteratedCovGrad g r m i W) +
              homTensorRSFieldApply (I := I) (M := M) g r (m + (i + 1)) (c + (k + 1))
                (slotExtendFullSec (I := I) (M := M) g r (m + i) (c + k) (D i))
                (iteratedCovGrad g r m (i + 1) W)) from
        Finset.sum_congr rfl (fun i _ => by
          rw [covGrad_appFullSec_eq (I := I) (M := M) g r (m + i) (c + k) (D i)
            (iteratedCovGrad g r m i W)]
          rfl)]
      rw [Finset.sum_add_distrib]

      rw [Finset.sum_range_succ' (fun j =>
        homTensorRSFieldApply (I := I) (M := M) g r (m + j) (c + (k + 1))
          ((match j with
            | 0 => homTensorRSCovGradSec (I := I) (M := M) g r (m + 0) (c + k) (D 0)
            | (i + 1) =>
                (if i + 1 < k + 1 then
                    homTensorRSCovGradSec (I := I) (M := M) g r (m + (i + 1)) (c + k) (D (i + 1))
                  else 0) +
                  slotExtendFullSec (I := I) (M := M) g r (m + i) (c + k) (D i)))
          (iteratedCovGrad g r m j W)) (k + 1)]

      rw [show (∑ i ∈ Finset.range (k + 1),
            homTensorRSFieldApply (I := I) (M := M) g r (m + (i + 1)) (c + (k + 1))
              ((if i + 1 < k + 1 then
                  homTensorRSCovGradSec (I := I) (M := M) g r (m + (i + 1)) (c + k) (D (i + 1))
                else 0) +
                slotExtendFullSec (I := I) (M := M) g r (m + i) (c + k) (D i))
              (iteratedCovGrad g r m (i + 1) W)) =
          (∑ i ∈ Finset.range (k + 1),
            homTensorRSFieldApply (I := I) (M := M) g r (m + (i + 1)) (c + (k + 1))
              (if i + 1 < k + 1 then
                  homTensorRSCovGradSec (I := I) (M := M) g r (m + (i + 1)) (c + k) (D (i + 1))
                else 0)
              (iteratedCovGrad g r m (i + 1) W)) +
          (∑ i ∈ Finset.range (k + 1),
            homTensorRSFieldApply (I := I) (M := M) g r (m + (i + 1)) (c + (k + 1))
              (slotExtendFullSec (I := I) (M := M) g r (m + i) (c + k) (D i))
              (iteratedCovGrad g r m (i + 1) W)) from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [appFullSec_add_left]]

      rw [show (∑ i ∈ Finset.range (k + 1),
            homTensorRSFieldApply (I := I) (M := M) g r (m + (i + 1)) (c + (k + 1))
              (if i + 1 < k + 1 then
                  homTensorRSCovGradSec (I := I) (M := M) g r (m + (i + 1)) (c + k) (D (i + 1))
                else 0)
              (iteratedCovGrad g r m (i + 1) W)) =
          ∑ i ∈ Finset.range k,
            homTensorRSFieldApply (I := I) (M := M) g r (m + (i + 1)) (c + (k + 1))
              (homTensorRSCovGradSec (I := I) (M := M) g r (m + (i + 1)) (c + k) (D (i + 1)))
              (iteratedCovGrad g r m (i + 1) W) from by
        rw [Finset.sum_range_succ]
        rw [if_neg (by omega : ¬ (k + 1 < k + 1)), appFullSec_zero_left, add_zero]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [if_pos (by simp only [Finset.mem_range] at hi; omega : i + 1 < k + 1)]]

      rw [Finset.sum_range_succ' (fun i =>
        homTensorRSFieldApply (I := I) (M := M) g r (m + i) (c + (k + 1))
          (homTensorRSCovGradSec (I := I) (M := M) g r (m + i) (c + k) (D i))
          (iteratedCovGrad g r m i W)) k]

      abel


omit [NeZero (Module.finrank ℝ E)] in
theorem exists_appFullSec_iteratedCovGrad_window_bound (g : SmoothRiemannianMetric I M)
    (r m c : ℕ) (Q : HomTensorRSField (E := E) (M := M) r m c I) :
    ∃ cc : ℕ → ℝ, (∀ k, 0 ≤ cc k) ∧
      ∀ (W : SmoothCcTensor g r m) (k : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (c + k) x
            ((iteratedCovGrad g r c k
              (homTensorRSFieldApply (I := I) (M := M) g r m c Q W)).toSection x) ≤
          cc k * ∑ i ∈ Finset.range (k + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (m + i) x
              ((iteratedCovGrad g r m i W).toSection x) := by
  classical

  choose D hD using fun k =>
    homFieldAction_iteratedCovGrad_expansion (I := I) (M := M) g r m c Q k

  set C : ℕ → ℕ → ℝ := fun k i =>
    (exists_uniform_riemannianFiberNormSq_appFullRS_le (I := I) (M := M) g r (m + i) (c + k)
      (fun x : M => D k i x) (D k i).contMDiff).choose with hC_def
  have hC_nn : ∀ k i, 0 ≤ C k i := fun k i =>
    (exists_uniform_riemannianFiberNormSq_appFullRS_le (I := I) (M := M) g r (m + i) (c + k)
      (fun x : M => D k i x) (D k i).contMDiff).choose_spec.1
  have hC_bound : ∀ (k i : ℕ) (V : SmoothCcTensor g r (m + i)) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g r (c + k) x
          ((homTensorRSApply (I := I) (M := M) g r (m + i) (c + k) (fun x : M => D k i x)
            (D k i).contMDiff V).toSection x) ≤
        C k i * riemannianFiberNormSq (I := I) (M := M) g r (m + i) x (V.toSection x) :=
    fun k i V x =>
      (exists_uniform_riemannianFiberNormSq_appFullRS_le (I := I) (M := M) g r (m + i) (c + k)
        (fun x : M => D k i x) (D k i).contMDiff).choose_spec.2 V x
  refine ⟨fun k => ((k + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (k + 1), C k i,
    fun k => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => hC_nn k i),
    fun W k x => ?_⟩

  set a : ℕ → ℝ := fun i => riemannianFiberNormSq (I := I) (M := M) g r (m + i) x
    ((iteratedCovGrad g r m i W).toSection x) with ha_def
  have ha_nn : ∀ i, 0 ≤ a i := fun i =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + i) x _

  rw [hD k W, SmoothCcTensor.toSection_sum_apply]
  refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g r (c + k) x
    (Finset.range (k + 1))
    (fun i => (homTensorRSFieldApply (I := I) (M := M) g r (m + i) (c + k) (D k i)
      (iteratedCovGrad g r m i W)).toSection x)) ?_
  rw [Finset.card_range]

  have hsummand : ∀ i ∈ Finset.range (k + 1),
      riemannianFiberNormSq (I := I) (M := M) g r (c + k) x
          ((homTensorRSFieldApply (I := I) (M := M) g r (m + i) (c + k) (D k i)
            (iteratedCovGrad g r m i W)).toSection x) ≤ C k i * a i :=
    fun i _ => hC_bound k i (iteratedCovGrad g r m i W) x
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsummand) (by positivity)) ?_

  have hCa_le : (∑ i ∈ Finset.range (k + 1), C k i * a i) ≤
      (∑ i ∈ Finset.range (k + 1), C k i) * ∑ i ∈ Finset.range (k + 1), a i := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hC_nn k i)
    exact Finset.single_le_sum (f := a) (fun j _ => ha_nn j) hi
  calc ((k + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (k + 1), C k i * a i
      ≤ ((k + 1 : ℕ) : ℝ) * ((∑ i ∈ Finset.range (k + 1), C k i) *
          ∑ i ∈ Finset.range (k + 1), a i) :=
        mul_le_mul_of_nonneg_left hCa_le (by positivity)
    _ = ((k + 1 : ℕ) : ℝ) * (∑ i ∈ Finset.range (k + 1), C k i) *
          ∑ i ∈ Finset.range (k + 1), a i := by ring

section NormedIteratedCovGrad

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covGrad_heq_congr_hw (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    HEq (covGrad (I := I) (M := M) g r a Y) (covGrad (I := I) (M := M) g r b Z) := by
  subst h
  rw [eq_of_heq hYZ]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_comp_heq (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (S : SmoothCcTensor g r s) (i : ℕ) :
    HEq (iteratedCovGrad g r (s + j) i (iteratedCovGrad g r s j S))
      (iteratedCovGrad g r s (j + i) S) := by
  induction i with
  | zero => exact HEq.rfl
  | succ i ihi =>
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s + j) (j := i)
        (iteratedCovGrad g r s j S)]
      rw [show iteratedCovGrad g r s (j + (i + 1)) S =
        covGrad (I := I) (M := M) g r (s + (j + i)) (iteratedCovGrad g r s (j + i) S) from rfl]
      exact covGrad_heq_congr_hw (I := I) (M := M) g r
        (by omega : (s + j) + i = s + (j + i)) ihi

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem riemannianFiberNormSq_congr_of_heq (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r b x (Z.toSection x) := by
  subst h
  rw [eq_of_heq hYZ]


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_iteratedCovGrad_comp (g : SmoothRiemannianMetric I M) (r s j i : ℕ)
    (S : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r ((s + j) + i) x
        ((iteratedCovGrad g r (s + j) i (iteratedCovGrad g r s j S)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + (j + i)) x
        ((iteratedCovGrad g r s (j + i) S).toSection x) :=
  riemannianFiberNormSq_congr_of_heq (I := I) (M := M) g r
    (by omega : (s + j) + i = s + (j + i))
    (iteratedCovGrad_comp_heq (I := I) (M := M) g r s j S i) x

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem riemannianFiberNormSq_iteratedCovGrad_order_congr (g : SmoothRiemannianMetric I M)
    (r s : ℕ) {n n' : ℕ} (h : n = n') (S : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + n) x
        ((iteratedCovGrad g r s n S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + n') x
        ((iteratedCovGrad g r s n' S).toSection x) := by
  subst h
  rfl

end NormedIteratedCovGrad


omit [NeZero (Module.finrank ℝ E)] in
theorem exists_appFullSec_on_jet_iteratedCovGrad_window_bound (g : SmoothRiemannianMetric I M)
    (r s j c : ℕ) (Q : HomTensorRSField (E := E) (M := M) r (s + j) c I) :
    ∃ cc : ℕ → ℝ, (∀ k, 0 ≤ cc k) ∧
      ∀ (S : SmoothCcTensor g r s) (k : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (c + k) x
            ((iteratedCovGrad g r c k
              (homTensorRSFieldApply (I := I) (M := M) g r (s + j) c Q
                (iteratedCovGrad g r s j S))).toSection x) ≤
          cc k * ∑ i ∈ Finset.range (1 + k),
            riemannianFiberNormSq (I := I) (M := M) g r (s + (i + j)) x
              ((iteratedCovGrad g r s (i + j) S).toSection x) := by
  classical
  obtain ⟨cc, hcc_nn, hcc⟩ :=
    exists_appFullSec_iteratedCovGrad_window_bound (I := I) (M := M) g r (s + j) c Q
  refine ⟨cc, hcc_nn, fun S k x => ?_⟩
  refine (hcc (iteratedCovGrad g r s j S) k x).trans (le_of_eq ?_)
  refine congrArg (fun t => cc k * t) ?_

  rw [Nat.add_comm 1 k]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g r s j i S x]
  exact riemannianFiberNormSq_iteratedCovGrad_order_congr (I := I) (M := M) g r s
    (by omega : j + i = i + j) S x

end Connection
end Integral
end DifferentialGeometry

end
