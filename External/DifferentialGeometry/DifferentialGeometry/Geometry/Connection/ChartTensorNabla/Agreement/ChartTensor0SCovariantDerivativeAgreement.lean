import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartTensor0SCovariantDerivative
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.Tensor0SChartChristoffel
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs


noncomputable section


open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open Tensor0SNabla

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma tensor0Iso_symm_apply_empty (x : M) (a : ℝ) :
    (show ContinuousMultilinearMap ℝ (fun _ : Fin 0 => TangentSpace I x) ℝ from
        ((tensor0Iso (I := I) (M := M) x).symm a))
      (fun i => Fin.elim0 i) = a := by
  classical
  let T₀ : Π y : M, Tensor0SSpace 0 I y :=
    fun y => if h : y = x then h ▸ ((tensor0Iso (I := I) (M := M) x).symm a) else 0
  have hT0x : T₀ x = (tensor0Iso (I := I) (M := M) x).symm a := by
    simp [T₀]
  have hscalarFn :
      (show ContinuousMultilinearMap ℝ (fun _ : Fin 0 => TangentSpace I x) ℝ from
          T₀ x) (0 : Fin 0 → TangentSpace I x) = scalarFn I M T₀ x :=
    (scalarFn_eq_apply_zero (I := I) (M := M) T₀ x).symm
  have hscalar :
      scalarFn I M T₀ x = a := by
    change (tensor0Iso (I := I) (M := M) x) (T₀ x) = a
    rw [hT0x]
    exact (tensor0Iso (I := I) (M := M) x).apply_symm_apply a
  have h_inputs : (fun i : Fin 0 => Fin.elim0 i) =
      (0 : Fin 0 → TangentSpace I x) :=
    Subsingleton.elim _ _
  rw [h_inputs]
  rw [← hT0x]
  rw [hscalarFn, hscalar]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma extDerivFun_apply_scalar (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    extDerivFun (I := I) f x v = mfderiv I 𝓘(ℝ, ℝ) f x v := by
  simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma mfderiv_section_zero_eq_scalarFn
    (T : Π b : M, Tensor0SSpace 0 I b) (b : M) (v : TangentSpace I b) :
    mfderiv I 𝓘(ℝ, ℝ)
        (fun b' : M =>
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
          (fun i => Fin.elim0 i)) b v =
      mfderiv I 𝓘(ℝ, ℝ) (scalarFn I M T) b v := by
  classical
  have h_funeq :
      (fun b' : M =>
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
          (fun i => Fin.elim0 i)) =
        scalarFn I M T := by
    funext b'
    rw [scalarFn_eq_apply_zero (I := I) (M := M) T b']
    congr 1
    funext i
    exact i.elim0
  rw [h_funeq]
  rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartTensor0SCovariantDerivative_eq_abstract_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, Tensor0SSpace 0 I b) (X : Π b : M, TangentSpace I b)
    {b : M} (_hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartTensor0SCovariantDerivative (I := I) 0 g α T X b =
      Tensor0SNabla.tensor0SCovariantDerivative I M 0
          (LeviCivita (I := I) g) T b (X b) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro m
  have hm : m = (fun i : Fin 0 => Fin.elim0 i) := by
    funext i; exact i.elim0
  subst hm
  rw [chartTensor0SCovariantDerivative_zero_apply
      (I := I) g α T X b (fun i : Fin 0 => Fin.elim0 i)]
  rw [tensor0SCovariantDerivative_apply_zero
      (I := I) (M := M) (LeviCivita (I := I) g) T b (X b)]
  rw [mfderiv_section_zero_eq_scalarFn (I := I) (M := M) T b (X b)]
  rw [tensor0Iso_symm_apply_empty (I := I) (M := M) b
      (extDerivFun (I := I) (scalarFn I M T) b (X b))]
  exact (extDerivFun_apply_scalar (I := I) (scalarFn I M T) b (X b)).symm

example
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, Tensor0SSpace 0 I b) (X : Π b : M, TangentSpace I b)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartTensor0SCovariantDerivative (I := I) 0 g α T X b =
      Tensor0SNabla.tensor0SCovariantDerivative I M 0
          (LeviCivita (I := I) g) T b (X b) :=
  chartTensor0SCovariantDerivative_eq_abstract_zero
    (I := I) (M := M) g α T X hb

end Connection
end Integral
end DifferentialGeometry
