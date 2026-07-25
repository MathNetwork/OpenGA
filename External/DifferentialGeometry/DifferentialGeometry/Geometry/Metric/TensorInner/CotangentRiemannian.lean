import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import Mathlib.LinearAlgebra.Dual.Basis



namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def cotangentToCLM {x : M} (α : Tensor0SSpace 1 I x) :
    TangentSpace I x →L[Real] Real :=
  continuousMultilinearCurryFin1 Real (TangentSpace I x) Real
    (Tensor0SSpace.toModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) α)

def cotangentToDual {x : M} (α : Tensor0SSpace 1 I x) :
    Module.Dual Real (TangentSpace I x) :=
  (cotangentToCLM (I := I) α).toLinearMap

omit [FiniteDimensional ℝ E] in
@[simp] theorem cotangentToDual_apply {x : M}
    (α : Tensor0SSpace 1 I x) (X : TangentSpace I x) :
    cotangentToDual (I := I) α X = α (fun _ : Fin 1 => X) := by
  simpa [cotangentToDual, cotangentToCLM, Tensor0SSpace.toModel,
    tensor0SSpace_continuousLinearEquiv] using
    congrArg (fun v : Fin 1 -> TangentSpace I x => α v)
    (funext fun i => by fin_cases i; rfl)

def cotangentToDualLinear {x : M} :
    Tensor0SSpace 1 I x →ₗ[Real] Module.Dual Real (TangentSpace I x) where
  toFun := cotangentToDual (I := I)
  map_add' α β := by
    ext X
    rfl
  map_smul' c α := by
    ext X
    rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem cotangentToDualLinear_apply {x : M}
    (α : Tensor0SSpace 1 I x) :
    cotangentToDualLinear (I := I) α = cotangentToDual (I := I) α := by
  rfl

omit [FiniteDimensional ℝ E] in
theorem cotangentToDualLinear_injective {x : M} :
    Function.Injective (cotangentToDualLinear (I := I) (x := x)) := by
  intro α β h
  ext v
  have hv :
      (fun _ : Fin 1 => v 0) = v := by
    funext i
    fin_cases i
    rfl
  have h0 := congrArg (fun L : Module.Dual Real (TangentSpace I x) => L (v 0)) h
  simpa [cotangentToDualLinear, cotangentToDual_apply, hv] using h0

def dualToCotangent {x : M} (α : Module.Dual Real (TangentSpace I x)) :
    Tensor0SSpace 1 I x :=
  Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
      (LinearMap.toContinuousLinearMap α))

@[simp] theorem dualToCotangent_apply {x : M}
    (α : Module.Dual Real (TangentSpace I x)) (X : TangentSpace I x) :
    dualToCotangent (I := I) α (fun _ : Fin 1 => X) = α X := by
  change
    ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
        (LinearMap.toContinuousLinearMap α)) (fun _ : Fin 1 => X) = α X
  rfl

@[simp] theorem cotangentToDual_dualToCotangent {x : M}
    (α : Module.Dual Real (TangentSpace I x)) :
    cotangentToDual (I := I) (dualToCotangent (I := I) α) = α := by
  ext X
  simp

def cotangentSharpLinear (g : SmoothMetric I M) (x : M) :
    Tensor0SSpace 1 I x →ₗ[Real] TangentSpace I x :=
  ((tangentMetricData (I := I) g x).metric.sharp).toLinearMap.comp
    (cotangentToDualLinear (I := I) (x := x))

def cotangentSharp (g : SmoothMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) : TangentSpace I x :=
  cotangentSharpLinear (I := I) g x α

@[simp] theorem cotangentSharpLinear_apply
    (g : SmoothMetric I M) (x : M) (α : Tensor0SSpace 1 I x) :
    cotangentSharpLinear (I := I) g x α = cotangentSharp (I := I) g x α := by
  rfl

theorem cotangentSharpLinear_injective
    (g : SmoothMetric I M) (x : M) :
    Function.Injective (cotangentSharpLinear (I := I) g x) := by
  intro α β h
  apply cotangentToDualLinear_injective (I := I) (x := x)
  exact ((tangentMetricData (I := I) g x).metric.sharp.injective h)

def cotangentInner (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) : Real :=
  g.inner x
    (cotangentSharpLinear (I := I) g x α)
    (cotangentSharpLinear (I := I) g x β)

@[simp] theorem cotangentInner_eq_sharp
    (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cotangentInner (I := I) g x α β =
      g.inner x (cotangentSharp (I := I) g x α)
        (cotangentSharp (I := I) g x β) := by
  rfl

def cotangentFlatLinear (g : SmoothMetric I M) (x : M) :
    Tensor0SSpace 1 I x →ₗ[Real] Module.Dual Real (Tensor0SSpace 1 I x) where
  toFun α :=
    { toFun := fun β => cotangentInner (I := I) g x α β
      map_add' := by
        intro β γ
        let S := cotangentSharpLinear (I := I) g x
        have hS : S (β + γ) = S β + S γ := map_add S β γ
        change g.inner x (S α) (S (β + γ)) =
          g.inner x (S α) (S β) + g.inner x (S α) (S γ)
        rw [hS]
        simp
      map_smul' := by
        intro c β
        let S := cotangentSharpLinear (I := I) g x
        have hS : S (c • β) = c • S β := map_smul S c β
        change g.inner x (S α) (S (c • β)) = c * g.inner x (S α) (S β)
        rw [hS]
        simp }
  map_add' α β := by
    ext γ
    let S := cotangentSharpLinear (I := I) g x
    have hS : S (α + β) = S α + S β := map_add S α β
    change g.inner x (S (α + β)) (S γ) =
      g.inner x (S α) (S γ) + g.inner x (S β) (S γ)
    rw [hS]
    simp
  map_smul' c α := by
    ext β
    let S := cotangentSharpLinear (I := I) g x
    have hS : S (c • α) = c • S α := map_smul S c α
    change g.inner x (S (c • α)) (S β) = c * g.inner x (S α) (S β)
    rw [hS]
    simp

@[simp] theorem cotangentFlatLinear_apply
    (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cotangentFlatLinear (I := I) g x α β =
      cotangentInner (I := I) g x α β := by
  rfl

theorem cotangentFlatLinear_injective
    (g : SmoothMetric I M) (x : M) :
    Function.Injective (cotangentFlatLinear (I := I) g x) := by
  intro α β h
  have hsub : cotangentSharpLinear (I := I) g x (α - β) = 0 := by
    by_contra hsharp
    have hpos :
        0 <
          g.inner x
            (cotangentSharpLinear (I := I) g x (α - β))
            (cotangentSharpLinear (I := I) g x (α - β)) :=
      g.pos x (cotangentSharpLinear (I := I) g x (α - β)) hsharp
    have h_eval :
        cotangentFlatLinear (I := I) g x α (α - β) =
          cotangentFlatLinear (I := I) g x β (α - β) :=
      congrArg
        (fun L : Module.Dual Real (Tensor0SSpace 1 I x) => L (α - β)) h
    have hdiff : cotangentFlatLinear (I := I) g x (α - β) (α - β) = 0 := by
      calc
        cotangentFlatLinear (I := I) g x (α - β) (α - β)
            = (cotangentFlatLinear (I := I) g x α -
                cotangentFlatLinear (I := I) g x β) (α - β) := by
                exact congrArg
                  (fun L : Module.Dual Real (Tensor0SSpace 1 I x) => L (α - β))
                  (map_sub (cotangentFlatLinear (I := I) g x) α β)
        _ = cotangentFlatLinear (I := I) g x α (α - β) -
              cotangentFlatLinear (I := I) g x β (α - β) := rfl
        _ = 0 := sub_eq_zero.mpr h_eval
    have hzero :
        g.inner x
            (cotangentSharpLinear (I := I) g x (α - β))
            (cotangentSharpLinear (I := I) g x (α - β)) = 0 := by
      simpa [cotangentFlatLinear, cotangentInner] using hdiff
    exact (lt_irrefl (0 : Real)) (hzero ▸ hpos)
  apply cotangentSharpLinear_injective (I := I) g x
  have hdiff :
      cotangentSharpLinear (I := I) g x α -
        cotangentSharpLinear (I := I) g x β = 0 := by
    have hmap :
        cotangentSharpLinear (I := I) g x (α - β) =
          cotangentSharpLinear (I := I) g x α -
            cotangentSharpLinear (I := I) g x β :=
      map_sub (cotangentSharpLinear (I := I) g x) α β
    rwa [hmap] at hsub
  exact sub_eq_zero.mp hdiff

def cotangentMetricData (g : SmoothMetric I M) (x : M) :
    MetricFiberData (Tensor0SSpace 1 I x) :=
  MetricFiberData.ofFlat
    (cotangentFlatLinear (I := I) g x)
    (cotangentFlatLinear_injective (I := I) g x)
    (by
      intro α β
      change g.inner x
          (cotangentSharpLinear (I := I) g x α)
          (cotangentSharpLinear (I := I) g x β) =
        g.inner x
          (cotangentSharpLinear (I := I) g x β)
          (cotangentSharpLinear (I := I) g x α)
      exact g.symm x _ _)
    (by
      intro α
      by_cases hα : cotangentSharpLinear (I := I) g x α = 0
      · change 0 <=
          g.inner x
            (cotangentSharpLinear (I := I) g x α)
            (cotangentSharpLinear (I := I) g x α)
        rw [hα]
        simp
      · exact le_of_lt (g.pos x (cotangentSharpLinear (I := I) g x α) hα))

theorem cotangentMetricData_inner
    (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    (cotangentMetricData (I := I) g x).inner α β =
      cotangentInner (I := I) g x α β := by
  rfl

def MetricInverseOnFiniteFrameGram {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (frame : Idx -> TangentSpace I x)
    (gInv : Idx -> Idx -> Real) : Prop :=
  forall i j : Idx,
    (∑ k : Idx, gInv i k * g.inner x (frame k) (frame j)) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, g.inner x (frame i) (frame k) * gInv k j) =
        (if i = j then 1 else 0)

def MetricInverseInBasis {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) : Prop :=
  forall i j : Idx,
    (∑ k : Idx, gInv i k * g.inner x (basis k) (basis j)) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, g.inner x (basis i) (basis k) * gInv k j) =
        (if i = j then 1 else 0)

theorem cotangentSharp_inner
    (g : SmoothMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) (X : TangentSpace I x) :
    g.inner x (cotangentSharp (I := I) g x α) X =
      cotangentToDual (I := I) α X := by
  have h :=
    congrArg
      (fun L : Module.Dual Real (TangentSpace I x) => L X)
      ((tangentMetricData (I := I) g x).metric.flat.apply_symm_apply
        (cotangentToDual (I := I) α))
  change
    (tangentMetricData (I := I) g x).metric.flat
        ((tangentMetricData (I := I) g x).metric.sharp
          (cotangentToDual (I := I) α)) X =
      cotangentToDual (I := I) α X
  exact h

omit [FiniteDimensional ℝ E] in
theorem eq_of_inner_basis_eq
    {Idx : Type*} [Finite Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    {X Y : TangentSpace I x}
    (h : forall i : Idx, g.inner x X (basis i) = g.inner x Y (basis i)) :
    X = Y := by
  letI : Fintype Idx := Fintype.ofFinite Idx
  apply tangentFlatLinear_injective (I := I) g x
  ext Z
  have hcoord (L : TangentSpace I x →ₗ[Real] Real) :
      L Z = ∑ i : Idx, basis.repr Z i • L (basis i) := by
    conv_lhs => rw [← basis.sum_repr Z]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
  calc
    tangentFlatLinear (I := I) g x X Z
        = ∑ i : Idx, basis.repr Z i • tangentFlatLinear (I := I) g x X (basis i) :=
          hcoord (tangentFlatLinear (I := I) g x X)
    _ = ∑ i : Idx, basis.repr Z i • tangentFlatLinear (I := I) g x Y (basis i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [tangentFlatLinear_apply, tangentFlatLinear_apply, h i]
    _ = tangentFlatLinear (I := I) g x Y Z := by
          exact (hcoord (tangentFlatLinear (I := I) g x Y)).symm

theorem cotangentSharp_eq_sum_inv
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (β : Tensor0SSpace 1 I x) :
    cotangentSharp (I := I) g x β =
      ∑ i : Idx,
        (∑ j : Idx, gInv i j * cotangentToDual (I := I) β (basis j)) •
          basis i := by
  apply eq_of_inner_basis_eq (I := I) g x basis
  intro l
  calc
    g.inner x (cotangentSharp (I := I) g x β) (basis l)
        = cotangentToDual (I := I) β (basis l) := by
          rw [cotangentSharp_inner]
    _ = ∑ j : Idx, (if l = j then 1 else 0) *
          cotangentToDual (I := I) β (basis j) := by
          simp
    _ = ∑ j : Idx,
          (∑ i : Idx, g.inner x (basis l) (basis i) * gInv i j) *
            cotangentToDual (I := I) β (basis j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [(hinv l j).2]
    _ = ∑ i : Idx,
          (∑ j : Idx, gInv i j * cotangentToDual (I := I) β (basis j)) *
            g.inner x (basis i) (basis l) := by
          calc
            (∑ j : Idx,
                (∑ i : Idx, g.inner x (basis l) (basis i) * gInv i j) *
                  cotangentToDual (I := I) β (basis j))
                = ∑ j : Idx, ∑ i : Idx,
                    (g.inner x (basis l) (basis i) * gInv i j) *
                      cotangentToDual (I := I) β (basis j) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    rw [Finset.sum_mul]
            _ = ∑ i : Idx, ∑ j : Idx,
                    (g.inner x (basis l) (basis i) * gInv i j) *
                      cotangentToDual (I := I) β (basis j) := by
                    rw [Finset.sum_comm]
            _ = ∑ i : Idx,
                  (∑ j : Idx, gInv i j * cotangentToDual (I := I) β (basis j)) *
                    g.inner x (basis i) (basis l) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro j _
                    rw [g.symm x (basis l) (basis i)]
                    ring
    _ = g.inner x
          (∑ i : Idx,
            (∑ j : Idx, gInv i j * cotangentToDual (I := I) β (basis j)) •
              basis i)
          (basis l) := by
          simp [map_sum]

theorem cotangentInner_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (α β : Tensor0SSpace 1 I x) :
    cotangentInner (I := I) g x α β =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * cotangentToDual (I := I) α (basis i) *
          cotangentToDual (I := I) β (basis j) := by
  calc
    cotangentInner (I := I) g x α β
        = g.inner x (cotangentSharp (I := I) g x α)
            (cotangentSharp (I := I) g x β) := rfl
    _ = cotangentToDual (I := I) α (cotangentSharp (I := I) g x β) := by
          rw [cotangentSharp_inner]
    _ = cotangentToDual (I := I) α
          (∑ i : Idx,
            (∑ j : Idx, gInv i j * cotangentToDual (I := I) β (basis j)) •
              basis i) := by
          rw [cotangentSharp_eq_sum_inv (I := I) g x basis gInv hinv β]
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j * cotangentToDual (I := I) α (basis i) *
            cotangentToDual (I := I) β (basis j) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [map_smul]
          change (∑ j : Idx, gInv i j * cotangentToDual (I := I) β (basis j)) *
              cotangentToDual (I := I) α (basis i) =
            ∑ j : Idx,
              gInv i j * cotangentToDual (I := I) α (basis i) *
                cotangentToDual (I := I) β (basis j)
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          change (gInv i j * cotangentToDual (I := I) β (basis j)) *
              cotangentToDual (I := I) α (basis i) =
            gInv i j * cotangentToDual (I := I) α (basis i) *
              cotangentToDual (I := I) β (basis j)
          ring

theorem cotangentMetricData_inner_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (α β : Tensor0SSpace 1 I x) :
    (cotangentMetricData (I := I) g x).inner α β =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * cotangentToDual (I := I) α (basis i) *
          cotangentToDual (I := I) β (basis j) := by
  rw [cotangentMetricData_inner, cotangentInner_eq_coord (I := I) g x basis gInv hinv]

end

end Tensor0SBundle
