import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.SlotSplitParsevalBridge


noncomputable section

set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem tensor0S_uncurry_cons_eval_of_expansion
    {s : ℕ} {x : M} (T : Tensor0SSpace (s + 1) I x)
    {n : ℕ} (c : Fin n → ℝ) (e : Fin n → TangentSpace I x)
    (w : TangentSpace I x) (hw : w = ∑ a : Fin n, c a • e a)
    (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel T (Fin.cons w m) =
      ∑ a : Fin n, c a • Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x T (e a)) m := by
  classical
  rw [← TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := s) (b := x) T w m]
  rw [hw]
  rw [map_sum (tensor0S_curry (I := I) (M := M) s x T) (fun a => c a • e a) Finset.univ]
  rw [show Tensor0SSpace.toModel
        (∑ a : Fin n, tensor0S_curry (I := I) (M := M) s x T (c a • e a)) =
      ∑ a : Fin n, Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x T (c a • e a)) from by
    rw [← Tensor0SSpace.toModelL_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Tensor0SSpace.toModelL_apply]]
  rw [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [(tensor0S_curry (I := I) (M := M) s x T).map_smul (c a) (e a)]
  rw [Tensor0SSpace.toModel_smul (c a) (tensor0S_curry (I := I) (M := M) s x T (e a))]
  rw [ContinuousMultilinearMap.smul_apply]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem tensor0S_uncurry_cons_eval_orthonormal
    (g : SmoothRiemannianMetric I M) {s : ℕ} {x : M} (T : Tensor0SSpace (s + 1) I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hv_expand : ∀ u : TangentSpace I x, u = ∑ a : Fin n, g.inner x (e a) u • e a)
    (w : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel T (Fin.cons w m) =
      ∑ a : Fin n, g.inner x (e a) w • Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x T (e a)) m :=
  tensor0S_uncurry_cons_eval_of_expansion (I := I) (M := M) T
    (fun a => g.inner x (e a) w) e w (hv_expand w) m

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma slot0Curry_coframeS_eq_tensor0S_curry
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (T : TensorRSSpace 0 (s + 1) I x) (a : Fin n) :
    (slot0Curry (I := I) (M := M) g x s e K₀ T a :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x)
        (coframeS (I := I) (M := M) g x 0 e K₀) =
      tensor0S_curry (I := I) (M := M) s x
        ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
          (coframeS (I := I) (M := M) g x 0 e K₀)) (e a) := by
  classical
  rw [slot0Curry_apply (I := I) (M := M) g x s e K₀ T a
    (coframeS (I := I) (M := M) g x 0 e K₀)]
  have hscalar : tensor00Scalar (I := I) (M := M) x
      (coframeS (I := I) (M := M) g x 0 e K₀) = 1 := by
    rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
      coframeS_apply (I := I) (M := M) g x 0 e K₀]
    simp
  rw [hscalar, one_smul]
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem tensorRS_section_uncurry_cons_eval_slot0Curry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hv_expand : ∀ u : TangentSpace I x, u = ∑ a : Fin n, g.inner x (e a) u • e a)
    (T : TensorRSSpace 0 (s + 1) I x)
    (w : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
          (coframeS (I := I) (M := M) g x 0 e K₀)) (Fin.cons w m) =
      ∑ a : Fin n, g.inner x (e a) w • Tensor0SSpace.toModel
        ((slot0Curry (I := I) (M := M) g x s e K₀ T a :
            Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x)
          (coframeS (I := I) (M := M) g x 0 e K₀)) m := by
  classical
  rw [tensor0S_uncurry_cons_eval_orthonormal (I := I) (M := M) g
    ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
      (coframeS (I := I) (M := M) g x 0 e K₀)) e hv_expand w m]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [slot0Curry_coframeS_eq_tensor0S_curry (I := I) (M := M) g x s e K₀ T a]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem tensor0S_eq_sum_slot0_uncurry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (T : Tensor0SSpace (s + 1) I x) (w : TangentSpace I x)
        (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel T (Fin.cons w m) =
          ∑ a : Fin n, g.inner x (e a) w • Tensor0SSpace.toModel
            (tensor0S_curry (I := I) (M := M) s x T (e a)) m := by
  classical
  obtain ⟨n, e, _bse, hn, _hbse, horth, _hpars, hv_expand, _hrepr⟩ :=
    tangent_orthonormalBasisS_witness (I := I) (M := M) g s x
  refine ⟨n, e, hn, horth, fun T w m => ?_⟩
  exact tensor0S_uncurry_cons_eval_orthonormal (I := I) (M := M) g T e hv_expand w m

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem tensorRS_section_eq_sum_slot0Curry_uncurry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (T : TensorRSSpace 0 (s + 1) I x) (w : TangentSpace I x)
        (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel
            ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
              (coframeS (I := I) (M := M) g x 0 e K₀)) (Fin.cons w m) =
          ∑ a : Fin n, g.inner x (e a) w • Tensor0SSpace.toModel
            ((slot0Curry (I := I) (M := M) g x s e K₀ T a :
                Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x)
              (coframeS (I := I) (M := M) g x 0 e K₀)) m := by
  classical
  obtain ⟨n, e, _bse, hn, _hbse, horth, _hpars, hv_expand, _hrepr⟩ :=
    tangent_orthonormalBasisS_witness (I := I) (M := M) g s x
  refine ⟨n, e, fun k => k.elim0, hn, horth, fun T w m => ?_⟩
  exact tensorRS_section_uncurry_cons_eval_slot0Curry (I := I) (M := M) g s x e
    (fun k => k.elim0) hv_expand T w m

end Connection
end Integral
end DifferentialGeometry
