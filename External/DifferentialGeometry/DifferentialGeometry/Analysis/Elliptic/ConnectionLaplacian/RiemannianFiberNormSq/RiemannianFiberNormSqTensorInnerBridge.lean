import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.Defs
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpVWFactorBound
import DifferentialGeometry.Geometry.Metric.PointwiseInner.SlotPermutation
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannianBundle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators Matrix RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private noncomputable def mixedGram
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i a => g.inner x ((chartModelBasis E) i) (frame a)

omit [CompleteSpace E] in
@[simp] private lemma mixedGram_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (i a : Fin (Module.finrank ℝ E)) :
    mixedGram (I := I) (M := M) g x frame i a =
      g.inner x ((chartModelBasis E) i) (frame a) := rfl

omit [Module.Finite ℝ E] [CompleteSpace E] in
private lemma orthoFrame_expansion
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0)
    (v : TangentSpace I x) :
    v = ∑ a : Fin (Module.finrank ℝ E), g.inner x v (frame a) • frame a := by
  classical
  conv_lhs => rw [← frame.sum_repr v]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  have hv : g.inner x v (frame a) =
      ∑ b : Fin (Module.finrank ℝ E),
        frame.repr v b * g.inner x (frame b) (frame a) := by
    conv_lhs => rw [show v = ∑ b : Fin (Module.finrank ℝ E),
      frame.repr v b • frame b from (frame.sum_repr v).symm]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hv, Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, mul_one]
  · intro b _ hba
    rw [horth b a, if_neg (by simpa [eq_comm] using hba), mul_zero]
  · intro hb
    exact absurd (Finset.mem_univ a) hb

omit [CompleteSpace E] in
private lemma gramMatrixAt_eq_mixedGram_mul_transpose
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0) :
    gramMatrixAt (I := I) (M := M) g x =
      mixedGram (I := I) (M := M) g x frame *
        (mixedGram (I := I) (M := M) g x frame)ᵀ := by
  classical
  ext i j
  rw [gramMatrixAt_apply, Matrix.mul_apply]
  have hexp : (chartModelBasis E) j =
      ∑ a : Fin (Module.finrank ℝ E),
        g.inner x ((chartModelBasis E) j) (frame a) • frame a :=
    orthoFrame_expansion (I := I) (M := M) g x frame horth ((chartModelBasis E) j)
  calc g.inner x ((chartModelBasis E) i) ((chartModelBasis E) j)
      = g.inner x ((chartModelBasis E) i)
          (∑ a : Fin (Module.finrank ℝ E),
            g.inner x ((chartModelBasis E) j) (frame a) • frame a) := by rw [← hexp]
    _ = ∑ a : Fin (Module.finrank ℝ E),
          mixedGram (I := I) (M := M) g x frame i a *
            (mixedGram (I := I) (M := M) g x frame)ᵀ a j := by
        rw [map_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [ContinuousLinearMap.map_smul, smul_eq_mul,
          mixedGram_apply, Matrix.transpose_apply, mixedGram_apply]
        ring

omit [CompleteSpace E] in
private lemma mixedGram_isUnit
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0) :
    IsUnit (mixedGram (I := I) (M := M) g x frame) := by
  classical
  rw [Matrix.isUnit_iff_isUnit_det]
  have hG := gramMatrixAt_eq_mixedGram_mul_transpose (I := I) (M := M) g x frame horth
  have hdetG : (gramMatrixAt (I := I) (M := M) g x).det ≠ 0 := by
    have := gramMatrixAt_isUnit (I := I) (M := M) g x
    rwa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at this
  rw [hG, Matrix.det_mul, Matrix.det_transpose] at hdetG
  rw [isUnit_iff_ne_zero]
  intro h
  rw [h] at hdetG
  simp at hdetG

omit [CompleteSpace E] in
private lemma mixedGram_transpose_mul_inv_mul
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0) :
    (mixedGram (I := I) (M := M) g x frame)ᵀ *
        ((gramMatrixAt (I := I) (M := M) g x)⁻¹ *
          mixedGram (I := I) (M := M) g x frame) = 1 := by
  classical
  set S := mixedGram (I := I) (M := M) g x frame with hS_def
  have hS_unit : IsUnit S := mixedGram_isUnit (I := I) (M := M) g x frame horth
  have hG : gramMatrixAt (I := I) (M := M) g x = S * Sᵀ :=
    gramMatrixAt_eq_mixedGram_mul_transpose (I := I) (M := M) g x frame horth
  have hGinv : (gramMatrixAt (I := I) (M := M) g x)⁻¹ = Sᵀ⁻¹ * S⁻¹ := by
    rw [hG, Matrix.mul_inv_rev]
  rw [hGinv]
  have hSdet : IsUnit S.det := Matrix.isUnit_iff_isUnit_det _ |>.mp hS_unit
  have hSTdet : IsUnit Sᵀ.det := by
    rw [Matrix.det_transpose]; exact hSdet
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv Sᵀ hSTdet,
    Matrix.one_mul, Matrix.nonsing_inv_mul S hSdet]

omit [CompleteSpace E] in
private lemma tensorInnerPointwise_0s_sum_smul_left
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι : Type*} (A : Finset ι) (a : ι → ℝ)
    (ψ : ι → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x (∑ i ∈ A, a i • ψ i) T =
      ∑ i ∈ A, a i *
        covariantTensorInnerPointwise (I := I) (M := M) s g x (ψ i) T := by
  classical
  induction A using Finset.induction with
  | empty => simp [tensorInnerPointwise_0s_zero_left]
  | insert i A hi ih =>
      rw [Finset.sum_insert hi, tensorInnerPointwise_0s_add_left,
        tensorInnerPointwise_0s_smul_left, ih, Finset.sum_insert hi]

omit [CompleteSpace E] in
private lemma tensorInnerPointwise_0s_sum_smul_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι : Type*} (A : Finset ι) (a : ι → ℝ)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (ψ : ι → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x S (∑ i ∈ A, a i • ψ i) =
      ∑ i ∈ A, a i *
        covariantTensorInnerPointwise (I := I) (M := M) s g x S (ψ i) := by
  classical
  induction A using Finset.induction with
  | empty => simp [tensorInnerPointwise_0s_zero_right]
  | insert i A hi ih =>
      rw [Finset.sum_insert hi, tensorInnerPointwise_0s_add_right,
        tensorInnerPointwise_0s_smul_right, ih, Finset.sum_insert hi]

omit [CompleteSpace E] in
private lemma tensorInnerPointwise_0s_bisum
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι : Type*} (A : Finset ι) (c d : ι → ℝ)
    (ψ φ : ι → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x
        (∑ a ∈ A, c a • ψ a) (∑ b ∈ A, d b • φ b) =
      ∑ a ∈ A, ∑ b ∈ A,
        (c a * d b) *
          covariantTensorInnerPointwise (I := I) (M := M) s g x (ψ a) (φ b) := by
  classical
  rw [tensorInnerPointwise_0s_sum_smul_left]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tensorInnerPointwise_0s_sum_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

omit [Module.Finite ℝ E] [CompleteSpace E] in
private lemma curryLeft_sum_smul {s : ℕ}
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
    {ι : Type*} (A : Finset ι) (c : ι → ℝ) (w : ι → E) :
    P.curryLeft (∑ a ∈ A, c a • w a) =
      ∑ a ∈ A, c a • P.curryLeft (w a) := by
  classical
  induction A using Finset.induction with
  | empty => simp
  | insert a A ha ih =>
      rw [Finset.sum_insert ha, map_add, map_smul, ih, Finset.sum_insert ha]

omit [CompleteSpace E] in
private lemma tensorInnerPointwise_0s_succ_orthoFrame
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) (s + 1) g x S T =
      ∑ a : Fin (Module.finrank ℝ E),
        covariantTensorInnerPointwise (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame a)) := by
  classical
  rw [tensorInnerPointwise_0s_succ]
  have hmodel_exp : ∀ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E) i =
        ∑ a : Fin (Module.finrank ℝ E),
          mixedGram (I := I) (M := M) g x frame i a • frame a := by
    intro i
    have hexp := orthoFrame_expansion (I := I) (M := M) g x frame horth
      ((chartModelBasis E) i)
    rw [hexp]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [mixedGram_apply]
  have hcurry_exp : ∀ (P : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
      (i : Fin (Module.finrank ℝ E)),
      P.curryLeft ((chartModelBasis E) i) =
        ∑ a : Fin (Module.finrank ℝ E),
          mixedGram (I := I) (M := M) g x frame i a • P.curryLeft (frame a) := by
    intro P i
    rw [hmodel_exp i]
    exact curryLeft_sum_smul (E := E) P Finset.univ _ _
  have hstep : ∀ i j : Fin (Module.finrank ℝ E),
      (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          covariantTensorInnerPointwise (I := I) (M := M) s g x
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j)) =
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (mixedGram (I := I) (M := M) g x frame i a *
              (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
              mixedGram (I := I) (M := M) g x frame j b) *
            covariantTensorInnerPointwise (I := I) (M := M) s g x
              (S.curryLeft (frame a)) (T.curryLeft (frame b)) := by
    intro i j
    rw [hcurry_exp S i, hcurry_exp T j]
    rw [tensorInnerPointwise_0s_bisum (I := I) (M := M) g x s
      (A := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro b _
    ring
  rw [show (∑ i, ∑ j,
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          covariantTensorInnerPointwise (I := I) (M := M) s g x
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j))) =
      ∑ i, ∑ j, ∑ a, ∑ b,
        (mixedGram (I := I) (M := M) g x frame i a *
            (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            mixedGram (I := I) (M := M) g x frame j b) *
          covariantTensorInnerPointwise (I := I) (M := M) s g x
            (S.curryLeft (frame a)) (T.curryLeft (frame b))
    from by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      exact hstep i j]
  have hkey := mixedGram_transpose_mul_inv_mul (I := I) (M := M) g x frame horth
  set F := fun (i j a b : Fin (Module.finrank ℝ E)) =>
    (mixedGram (I := I) (M := M) g x frame i a *
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
        mixedGram (I := I) (M := M) g x frame j b) *
      covariantTensorInnerPointwise (I := I) (M := M) s g x
        (S.curryLeft (frame a)) (T.curryLeft (frame b)) with hF_def
  have hreindex :
      ∑ i, ∑ j, ∑ a, ∑ b, F i j a b =
        ∑ a, ∑ b, ∑ i, ∑ j, F i j a b := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm
      (f := fun j a => ∑ b, F i j a b))]
    rw [Finset.sum_comm (f := fun i a => ∑ j, ∑ b, F i j a b)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm
      (f := fun j b => F i j a b))]
    rw [Finset.sum_comm (f := fun i b => ∑ j, F i j a b)]
  rw [hreindex]
  have hcollapse : ∀ a b : Fin (Module.finrank ℝ E),
      ∑ i, ∑ j, F i j a b =
        ((mixedGram (I := I) (M := M) g x frame)ᵀ *
            ((gramMatrixAt (I := I) (M := M) g x)⁻¹ *
              mixedGram (I := I) (M := M) g x frame)) a b *
          covariantTensorInnerPointwise (I := I) (M := M) s g x
            (S.curryLeft (frame a)) (T.curryLeft (frame b)) := by
    intro a b
    rw [Matrix.mul_apply]
    rw [show (∑ i, (mixedGram (I := I) (M := M) g x frame)ᵀ a i *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ *
            mixedGram (I := I) (M := M) g x frame) i b) *
        covariantTensorInnerPointwise (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame b))
      = ∑ i, ((mixedGram (I := I) (M := M) g x frame)ᵀ a i *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ *
            mixedGram (I := I) (M := M) g x frame) i b) *
        covariantTensorInnerPointwise (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame b))
      from by rw [Finset.sum_mul]]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mul_apply]
    rw [show ((mixedGram (I := I) (M := M) g x frame)ᵀ a i *
          ∑ j, (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            mixedGram (I := I) (M := M) g x frame j b) *
        covariantTensorInnerPointwise (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame b))
      = ∑ j, ((mixedGram (I := I) (M := M) g x frame)ᵀ a i *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            mixedGram (I := I) (M := M) g x frame j b)) *
        covariantTensorInnerPointwise (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame b))
      from by rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.transpose_apply, hF_def]
    ring
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hcollapse a b))]
  rw [hkey]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro b _ hba
    rw [Matrix.one_apply_ne (Ne.symm hba), zero_mul]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

omit [CompleteSpace E] in
theorem tensorInnerPointwise_0s_eq_diag_sum_orthoFrame
    (g : SmoothRiemannianMetric I M) (x : M) (N : ℕ)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin N => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) N g x S T =
      ∑ φ : Fin N → Fin (Module.finrank ℝ E),
        S (fun k => frame (φ k)) * T (fun k => frame (φ k)) := by
  classical
  induction N with
  | zero =>
      rw [tensorInnerPointwise_0s_zero_arity]
      rw [Finset.sum_eq_single (fun a : Fin 0 => a.elim0)]
      · congr 1 <;>
          (congr 1; funext a; exact a.elim0)
      · intro b _ hb
        exact absurd (funext fun a => a.elim0) hb
      · intro h
        exact absurd (Finset.mem_univ _) h
  | succ s ih =>
      rw [tensorInnerPointwise_0s_succ_orthoFrame (I := I) (M := M) g x s frame horth S T]
      have hstep : ∀ a : Fin (Module.finrank ℝ E),
          covariantTensorInnerPointwise (I := I) (M := M) s g x
              (S.curryLeft (frame a)) (T.curryLeft (frame a)) =
            ∑ ψ : Fin s → Fin (Module.finrank ℝ E),
              S (fun k => frame ((Fin.cons a ψ : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) *
                T (fun k => frame
                  ((Fin.cons a ψ : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) := by
        intro a
        rw [ih (S.curryLeft (frame a)) (T.curryLeft (frame a))]
        refine Finset.sum_congr rfl (fun ψ _ => ?_)
        have hS : (S.curryLeft (frame a)) (fun k => frame (ψ k)) =
            S (fun k => frame
              ((Fin.cons a ψ : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) := by
          rw [ContinuousMultilinearMap.curryLeft_apply]
          congr 1
          funext k
          refine Fin.cases ?_ ?_ k
          · simp
          · intro m; simp
        have hT : (T.curryLeft (frame a)) (fun k => frame (ψ k)) =
            T (fun k => frame
              ((Fin.cons a ψ : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) := by
          rw [ContinuousMultilinearMap.curryLeft_apply]
          congr 1
          funext k
          refine Fin.cases ?_ ?_ k
          · simp
          · intro m; simp
        rw [hS, hT]
      rw [Finset.sum_congr rfl (fun a _ => hstep a)]
      rw [← Fintype.sum_equiv
        (Fin.consEquiv (fun _ : Fin (s + 1) => Fin (Module.finrank ℝ E)))
        (fun p => S (fun k => frame
            ((Fin.cons p.1 p.2 : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) *
          T (fun k => frame
            ((Fin.cons p.1 p.2 : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)))
        (fun φ => S (fun k => frame (φ k)) * T (fun k => frame (φ k)))
        (fun p => rfl)]
      rw [Fintype.sum_prod_type]

omit [CompleteSpace E] in
private lemma lower_toModel_append_eq_fiberNormSqComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (T : TensorRSSpace r s I x)
    (n : ℕ) (e : Fin n → TangentSpace I x)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    lowerAllUpperIndices (I := I) (M := M) g r s x
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := r) (s := s) (x := x) T)
        (Fin.append (fun k => e (K k)) (fun j => e (J j)))
      = fiberNormSqComponent (I := I) (M := M) g x r s T n e K J := by
  rw [lowerAllUpperIndices_apply]
  simp only [Fin.append_left, Fin.append_right]
  unfold fiberNormSqComponent separableFormAt
  rfl

omit [CompleteSpace E] in
private lemma riemannianFiberNormSq_frame_witness
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x)
      (bse : Module.Basis (Fin n) ℝ (TangentSpace I x)),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i : Fin n, bse i = e i) ∧
      (∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) ∧
      ∀ T : TensorRSSpace r s I x,
        riemannianFiberNormSq (I := I) (M := M) g r s x T =
          ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
            fiberNormSqComponent (I := I) (M := M) g x r s T n e K J ^ 2 := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set eob : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _
    with heob_def
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  refine ⟨n, fun i => eob i, eob.toBasis, rfl, ?_, ?_, ?_⟩
  · intro i
    rw [OrthonormalBasis.coe_toBasis]
  · intro a b
    have horth : Orthonormal ℝ (fun i : Fin n => eob i) := eob.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I x)).mp horth a b
    rw [← hinner_eq (eob a) (eob b)]
    exact hite
  · intro T
    rw [show riemannianFiberNormSq (I := I) (M := M) g r s x T =
        ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x r s T n (fun i => eob i) K J from rfl]
    refine Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => ?_))
    rfl

omit [CompleteSpace E] in
theorem riemannianFiberNormSq_eq_tensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (T : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x T =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := r) (s := s) (x := x) T)
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := r) (s := s) (x := x) T) := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hrepr⟩ :=
    riemannianFiberNormSq_frame_witness (I := I) (M := M) g r s x
  have hn' : n = Module.finrank ℝ E := hn
  subst hn'
  have hbse_orth : ∀ a b, g.inner x (bse a) (bse b) = if a = b then (1 : ℝ) else 0 := by
    intro a b; rw [hbse a, hbse b]; exact horth a b
  rw [hrepr T]
  set Tm := TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
    (r := r) (s := s) (x := x) T with hTm_def
  rw [show tensorInnerPointwise (I := I) (M := M) g r s x Tm Tm =
      covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
        (lowerAllUpperIndices (I := I) (M := M) g r s x Tm)
        (lowerAllUpperIndices (I := I) (M := M) g r s x Tm) from rfl]
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (r + s)
    bse hbse_orth _ _]
  rw [← Fintype.sum_equiv (Fin.appendEquiv r s)
    (fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
      fiberNormSqComponent (I := I) (M := M) g x r s T (Module.finrank ℝ E) e p.1 p.2 ^ 2)
    (fun φ : Fin (r + s) → Fin (Module.finrank ℝ E) =>
      (lowerAllUpperIndices (I := I) (M := M) g r s x Tm) (fun k => bse (φ k)) *
        (lowerAllUpperIndices (I := I) (M := M) g r s x Tm) (fun k => bse (φ k)))
    ?_]
  · rw [Fintype.sum_prod_type]
  · intro p
    have hbse_e : ∀ i : Fin (Module.finrank ℝ E), bse i = e i := hbse
    have happend :
        (fun k => bse ((Fin.appendEquiv r s) p k)) =
          Fin.append (fun k => e (p.1 k)) (fun j => e (p.2 j)) := by
      funext k
      simp only [hbse_e, Fin.appendEquiv_apply]
      induction k using Fin.addCases with
      | left i => simp only [Fin.append_left]
      | right i => simp only [Fin.append_right]
    dsimp only
    rw [happend, hTm_def, pow_two]
    congr 1 <;>
      exact (lower_toModel_append_eq_fiberNormSqComponent (I := I) (M := M) g r s x T
        (Module.finrank ℝ E) e p.1 p.2).symm

omit [CompleteSpace E] in
theorem tensorInnerPointwise_eq_sum_componentS_mul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hn : n = Module.finrank ℝ E) (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (A B : TensorRSSpace r s I x) :
    tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := r) (s := s) (x := x) A)
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := r) (s := s) (x := x) B) =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        fiberNormSqComponent (I := I) (M := M) g x r s A n e K J *
          fiberNormSqComponent (I := I) (M := M) g x r s B n e K J := by
  classical
  subst hn
  have hbse_orth : ∀ a b, g.inner x (bse a) (bse b) = if a = b then (1 : ℝ) else 0 := by
    intro a b; rw [hbse a, hbse b]; exact horth a b
  set Am := TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
    (r := r) (s := s) (x := x) A with hAm_def
  set Bm := TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
    (r := r) (s := s) (x := x) B with hBm_def
  rw [show tensorInnerPointwise (I := I) (M := M) g r s x Am Bm =
      covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
        (lowerAllUpperIndices (I := I) (M := M) g r s x Am)
        (lowerAllUpperIndices (I := I) (M := M) g r s x Bm) from rfl]
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (r + s)
    bse hbse_orth _ _]
  rw [← Fintype.sum_equiv (Fin.appendEquiv r s)
    (fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
      fiberNormSqComponent (I := I) (M := M) g x r s A (Module.finrank ℝ E) e p.1 p.2 *
        fiberNormSqComponent (I := I) (M := M) g x r s B (Module.finrank ℝ E) e p.1 p.2)
    (fun φ : Fin (r + s) → Fin (Module.finrank ℝ E) =>
      (lowerAllUpperIndices (I := I) (M := M) g r s x Am) (fun k => bse (φ k)) *
        (lowerAllUpperIndices (I := I) (M := M) g r s x Bm) (fun k => bse (φ k)))
    ?_]
  · rw [Fintype.sum_prod_type]
  · intro p
    have hbse_e : ∀ i : Fin (Module.finrank ℝ E), bse i = e i := hbse
    have happend :
        (fun k => bse ((Fin.appendEquiv r s) p k)) =
          Fin.append (fun k => e (p.1 k)) (fun j => e (p.2 j)) := by
      funext k
      simp only [hbse_e, Fin.appendEquiv_apply]
      induction k using Fin.addCases with
      | left i => simp only [Fin.append_left]
      | right i => simp only [Fin.append_right]
    dsimp only
    rw [happend, hAm_def, hBm_def]
    congr 1
    · exact (lower_toModel_append_eq_fiberNormSqComponent (I := I) (M := M) g r s x A
        (Module.finrank ℝ E) e p.1 p.2).symm
    · exact (lower_toModel_append_eq_fiberNormSqComponent (I := I) (M := M) g r s x B
        (Module.finrank ℝ E) e p.1 p.2).symm

open MeasureTheory in
omit [CompleteSpace E] in
theorem tensorL2Norm_sq_eq_integral_riemannianFiberNormSq
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : ∀ x, TensorRSSpace r s I x) :
    tensorL2Norm (I := I) (M := M) g r s
          (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
            (r := r) (s := s) (x := x) (T x)) ^ 2
      = ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (T x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [tensorL2Norm_def, Real.sq_sqrt (by
        unfold tensorL2Inner
        refine integral_nonneg (fun x => ?_)
        exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s x _)]
  unfold tensorL2Inner
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  exact (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (T x)).symm

end Connection
end Integral
end DifferentialGeometry

end
