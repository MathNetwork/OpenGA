import DifferentialGeometry.Geometry.Connection.Realization.Tensor0SBridge
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Topology
open Bundle
open Tensor0SBundle
open Tensor0SNabla

namespace Tensor0SPartialEval

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

noncomputable def tensor0SPartialEval {s : ℕ}
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (Y : Π b : M, TangentSpace I b) :
    Π b : M, Tensor0SSpace s I b :=
  fun b => tensor0S_curry (I := I) (M := M) s b (T b) (Y b)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem tensor0SPartialEval_apply {s : ℕ}
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (Y : Π b : M, TangentSpace I b) (b : M) :
    tensor0SPartialEval I M T Y b =
      tensor0S_curry (I := I) (M := M) s b (T b) (Y b) := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SPartialEval_eq_curriedSection {s : ℕ}
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (Y : Π b : M, TangentSpace I b) (b : M) :
    tensor0SPartialEval I M T Y b = curriedSection I M T b (Y b) := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SPartialEval_toModel_apply {s : ℕ}
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (Y : Π b : M, TangentSpace I b) (b : M) (v : Fin s → E) :
    Tensor0SSpace.toModel (tensor0SPartialEval I M T Y b) v =
      Tensor0SSpace.toModel (T b) (Fin.cons (Y b) v) := by
  change Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) s b (T b) (Y b)) v =
    Tensor0SSpace.toModel (T b) (Fin.cons (Y b) v)
  exact TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := T b) (v0 := Y b) (vs := v)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SPartialEval_add_T {s : ℕ}
    (T₁ T₂ : Π b : M, Tensor0SSpace (s + 1) I b)
    (Y : Π b : M, TangentSpace I b) :
    tensor0SPartialEval I M (T₁ + T₂) Y =
      tensor0SPartialEval I M T₁ Y + tensor0SPartialEval I M T₂ Y := by
  funext b
  change tensor0S_curry (I := I) (M := M) s b ((T₁ + T₂) b) (Y b) =
    tensor0S_curry (I := I) (M := M) s b (T₁ b) (Y b) +
    tensor0S_curry (I := I) (M := M) s b (T₂ b) (Y b)
  change tensor0S_curry (I := I) (M := M) s b (T₁ b + T₂ b) (Y b) = _
  rw [map_add (tensor0S_curry (I := I) (M := M) s b) (T₁ b) (T₂ b)]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SPartialEval_smul_T {s : ℕ}
    (g : M → ℝ) (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (Y : Π b : M, TangentSpace I b) :
    tensor0SPartialEval I M (g • T) Y = g • tensor0SPartialEval I M T Y := by
  funext b
  change tensor0S_curry (I := I) (M := M) s b ((g • T) b) (Y b) =
    g b • tensor0S_curry (I := I) (M := M) s b (T b) (Y b)
  change tensor0S_curry (I := I) (M := M) s b (g b • T b) (Y b) = _
  rw [map_smul (tensor0S_curry (I := I) (M := M) s b) (g b) (T b)]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SPartialEval_zero_T {s : ℕ}
    (Y : Π b : M, TangentSpace I b) :
    tensor0SPartialEval I M (0 : Π b : M, Tensor0SSpace (s + 1) I b) Y = 0 := by
  funext b
  change tensor0S_curry (I := I) (M := M) s b
      ((0 : Π b : M, Tensor0SSpace (s + 1) I b) b) (Y b) = 0
  change tensor0S_curry (I := I) (M := M) s b
      (0 : Tensor0SSpace (s + 1) I b) (Y b) = 0
  rw [map_zero (tensor0S_curry (I := I) (M := M) s b)]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SPartialEval_add_Y {s : ℕ}
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (Y₁ Y₂ : Π b : M, TangentSpace I b) :
    tensor0SPartialEval I M T (Y₁ + Y₂) =
      tensor0SPartialEval I M T Y₁ + tensor0SPartialEval I M T Y₂ := by
  funext b
  change tensor0S_curry (I := I) (M := M) s b (T b) ((Y₁ + Y₂) b) =
    tensor0S_curry (I := I) (M := M) s b (T b) (Y₁ b) +
    tensor0S_curry (I := I) (M := M) s b (T b) (Y₂ b)
  change tensor0S_curry (I := I) (M := M) s b (T b) (Y₁ b + Y₂ b) = _
  exact ContinuousLinearMap.map_add _ (Y₁ b) (Y₂ b)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SPartialEval_smul_Y {s : ℕ}
    (g : M → ℝ) (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (Y : Π b : M, TangentSpace I b) :
    tensor0SPartialEval I M T (g • Y) = g • tensor0SPartialEval I M T Y := by
  funext b
  change tensor0S_curry (I := I) (M := M) s b (T b) ((g • Y) b) =
    g b • tensor0S_curry (I := I) (M := M) s b (T b) (Y b)
  change tensor0S_curry (I := I) (M := M) s b (T b) (g b • Y b) = _
  exact ContinuousLinearMap.map_smul _ (g b) (Y b)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SPartialEval_zero_Y {s : ℕ}
    (T : Π b : M, Tensor0SSpace (s + 1) I b) :
    tensor0SPartialEval I M T (0 : Π b : M, TangentSpace I b) = 0 := by
  funext b
  change tensor0S_curry (I := I) (M := M) s b (T b)
      ((0 : Π b : M, TangentSpace I b) b) = 0
  change tensor0S_curry (I := I) (M := M) s b (T b)
      (0 : TangentSpace I b) = 0
  exact ContinuousLinearMap.map_zero _

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem contMDiff_tensor0SPartialEval {s : ℕ}
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun x : M => Tensor0SSpace (s + 1) I x) b (T b)))
    (Y : Π b : M, TangentSpace I b)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (Y b))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun x : M => Tensor0SSpace s I x) b
        (tensor0SPartialEval I M T Y b)) := by
  have hCurried : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)
        b (curriedSection I M T b)) :=
    (contMDiff_curriedSection_iff_section (I := I) (M := M) T).mp hT
  have hApplied : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun x : M => Tensor0SSpace s I x) b
        (curriedSection I M T b (Y b))) :=
    ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
      (F₁ := E) (F₂ := Tensor0SModel s ℝ E)
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => Tensor0SSpace s I x)
      (IM := I) (IB := I)
      (b := id) (ϕ := fun b : M => curriedSection I M T b)
      (v := fun b : M => Y b) hCurried hY
  exact hApplied

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem contMDiff_tensor0SPartialEval_of_smoothSections {s : ℕ}
    (T :
      letI _h_top : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
          (fun x : M => Tensor0SSpace (s + 1) I x)) :=
        tensor0SBundle_topology (s + 1)
      Cₛ^∞⟮I; Tensor0SModel (s + 1) ℝ E,
        (fun x : M => Tensor0SSpace (s + 1) I x)⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun x : M => Tensor0SSpace s I x) b
        (tensor0SPartialEval I M (fun b => T b) (fun b => Y b) b)) := by
  letI _h_top : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun x : M => Tensor0SSpace (s + 1) I x)) :=
    tensor0SBundle_topology (s + 1)
  exact contMDiff_tensor0SPartialEval (I := I) (M := M) (s := s)
    (T := fun b => T b) T.contMDiff (Y := fun b => Y b) Y.contMDiff

end Tensor0SPartialEval

end
