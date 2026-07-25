import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.Basic
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.ApplyInput
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.ModelBridge
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.Formula
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.Special12
import DifferentialGeometry.Tensor.RSTensor.Components
import DifferentialGeometry.Tensor.RSTensor.CotangentRiemannian
import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.OneJet
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEvalRealized
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization

set_option autoImplicit false
set_option linter.style.longLine false







namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle Tensor0SBundle Filter
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



private def connTraceEvalLin
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x →ₗ[Real]
      Real where
  toFun β :=
    metricTrace0S2InBasis (I := I)
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x)
      (fun k l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
        DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component (I := I) g x k l
          (extChartAt I x x))
      (A β) Fin.elim0
  map_add' β γ := by
    simp only [metricTrace0S2InBasis, map_add, Tensor0SSpace.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring_nf
  map_smul' c β := by
    simp only [metricTrace0S2InBasis, map_smul, Tensor0SSpace.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [mul_left_comm]



def connTraceOneFormAt
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  dualToCotangent_gen (I := I)
    ((connTraceEvalLin (I := I) g A).comp
      ((dualToCotangentLinear (I := I)).comp (tangentFlatLinear_gen (I := I) g x)))

@[simp] theorem connTraceOneFormAt_apply
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x)
    (V : TangentSpace I x) :
    cotangentToDual_gen (I := I) (connTraceOneFormAt (I := I) g A) V =
      metricTraceFirstTwo0STensor (I := I) g
        (A (dualToCotangent_gen (I := I) ((tangentFlatLinear_gen (I := I) g x) V)))
        Fin.elim0 := by
  unfold connTraceOneFormAt connTraceEvalLin
  rw [cotangentToDual_dualToCotangent_gen]
  rw [metricTraceFirstTwo0STensor_apply]
  exact metricTrace0S2InBasis_eq_metricTrace (I := I) g
    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x)
    (fun k l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component (I := I) g x k l
        (extChartAt I x x))
    (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x)
    (A (dualToCotangent_gen (I := I) ((tangentFlatLinear_gen (I := I) g x) V))) Fin.elim0


theorem connTraceOneFormAt_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (q : Idx) :
    cotangentToDual_gen (I := I) (connTraceOneFormAt (I := I) g A) (basis q) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (A (dualToCotangent_gen (I := I) ((tangentFlatLinear_gen (I := I) g x) (basis q))))
            (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0) := by
  rw [connTraceOneFormAt_apply]
  rw [metricTraceFirstTwo0STensor_apply]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  rfl


def connTraceAt
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x) :
    TangentSpace I x :=
  cotangentSharp_gen (I := I) g x (connTraceOneFormAt (I := I) g A)

@[simp] theorem connTraceAt_eq
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x) :
    connTraceAt (I := I) g A =
      cotangentSharp_gen (I := I) g x (connTraceOneFormAt (I := I) g A) := by
  rfl


theorem connTraceAt_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv) :
    connTraceAt (I := I) g A =
      ∑ p : Idx,
        (∑ q : Idx,
          gInv p q *
            (∑ i : Idx, ∑ j : Idx,
              gInv i j *
                (A (dualToCotangent_gen (I := I)
                    ((tangentFlatLinear_gen (I := I) g x) (basis q))))
                  (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0))) •
          basis p := by
  rw [connTraceAt_eq]
  rw [cotangentSharp_eq_sum_inv_gen (I := I) g x basis gInv hinv]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [connTraceOneFormAt_coord (I := I) g A basis gInv hinv q]

private theorem sumFinOne {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 1 → Idx) → α) :
    (∑ r : Fin 1 → Idx, F r) =
      ∑ r : Idx, F (fun _ : Fin 1 => r) := by
  classical
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) Idx)
    F (fun r : Idx => F (fun _ : Fin 1 => r))]
  intro r
  congr 1
  funext a
  simpa [Equiv.funUnique] using congrArg r (Subsingleton.elim a (0 : Fin 1))

private theorem traceFlat_apply_sum
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (q i j : Idx) :
    (A (dualToCotangent_gen (I := I)
        ((tangentFlatLinear_gen (I := I) g x) (basis q))))
      (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0) =
      ∑ r : Idx,
        g.inner x (basis q) (basis r) *
          componentRS_gen (I := I) basis A
            (fun _ : Fin 1 => r)
            (fun a : Fin 2 => if a = 0 then i else j) := by
  have h := componentRS_apply_input_eq_sum (I := I) basis A
    (dualToCotangent_gen (I := I) ((tangentFlatLinear_gen (I := I) g x) (basis q)))
    (fun a : Fin 2 => if a = 0 then i else j)
  have hslots :
      metricTraceInput (I := I) (basis i) (basis j) Fin.elim0 =
        (fun a : Fin 2 => if a = 0 then basis i else basis j) := by
    funext a
    fin_cases a <;> rfl
  calc
    (A (dualToCotangent_gen (I := I)
        ((tangentFlatLinear_gen (I := I) g x) (basis q))))
      (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0) =
        ∑ r : Fin 1 → Idx,
          (dualToCotangent_gen (I := I)
            ((tangentFlatLinear_gen (I := I) g x) (basis q)))
              (fun a : Fin 1 => basis (r a)) *
            componentRS_gen (I := I) basis A r
              (fun a : Fin 2 => if a = 0 then i else j) := by
          rw [hslots]
          simpa [component0S_apply] using h
    _ =
      ∑ r : Idx,
        g.inner x (basis q) (basis r) *
          componentRS_gen (I := I) basis A
            (fun _ : Fin 1 => r)
            (fun a : Fin 2 => if a = 0 then i else j) := by
        rw [sumFinOne]
        simp [dualToCotangent_apply_gen, tangentFlatLinear_apply_gen]

private theorem sumFourComm
    {ι κ η μ α : Type*} [Fintype ι] [Fintype κ] [Fintype η] [Fintype μ]
    [AddCommMonoid α]
    (F : ι → κ → η → μ → α) :
    (∑ a : ι, ∑ b : κ, ∑ c : η, ∑ d : μ, F a b c d) =
      ∑ b : κ, ∑ c : η, ∑ d : μ, ∑ a : ι, F a b c d := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]

private theorem traceAlg
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gInv G : Idx → Idx → Real)
    (C : Idx → Idx → Idx → Real)
    (hInv : ∀ a b : Idx, (∑ q : Idx, gInv a q * G q b) =
      (if a = b then 1 else 0))
    (p : Idx) :
    (∑ q : Idx,
      gInv p q *
        (∑ i : Idx, ∑ j : Idx,
          gInv i j * (∑ r : Idx, G q r * C r i j))) =
      ∑ i : Idx, ∑ j : Idx, gInv i j * C p i j := by
  classical
  calc
    (∑ q : Idx,
      gInv p q *
        (∑ i : Idx, ∑ j : Idx,
          gInv i j * (∑ r : Idx, G q r * C r i j))) =
      ∑ q : Idx,
        ∑ i : Idx,
          ∑ j : Idx,
            ∑ r : Idx,
              gInv p q * (gInv i j * (G q r * C r i j)) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        calc
          gInv p q * (gInv i j * (∑ r : Idx, G q r * C r i j)) =
              (gInv p q * gInv i j) *
                (∑ r : Idx, G q r * C r i j) := by ring
          _ = ∑ r : Idx,
              (gInv p q * gInv i j) * (G q r * C r i j) := by
            rw [Finset.mul_sum]
          _ = ∑ r : Idx,
              gInv p q * (gInv i j * (G q r * C r i j)) := by
            apply Finset.sum_congr rfl
            intro r _
            ring
      _ =
      ∑ i : Idx,
        ∑ j : Idx,
          ∑ r : Idx,
            ∑ q : Idx,
              gInv p q * (gInv i j * (G q r * C r i j)) := by
        exact sumFourComm
          (fun q i j r => gInv p q * (gInv i j * (G q r * C r i j)))
      _ =
      ∑ i : Idx,
        ∑ j : Idx,
          ∑ r : Idx,
            (∑ q : Idx, gInv p q * G q r) *
              (gInv i j * C r i j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro r _
        calc
          ∑ q : Idx, gInv p q * (gInv i j * (G q r * C r i j)) =
              ∑ q : Idx, (gInv p q * G q r) * (gInv i j * C r i j) := by
            apply Finset.sum_congr rfl
            intro q _
            ring
          _ = (∑ q : Idx, gInv p q * G q r) *
              (gInv i j * C r i j) := by
            rw [Finset.sum_mul]
      _ =
      ∑ i : Idx,
        ∑ j : Idx,
          ∑ r : Idx,
            (if p = r then 1 else 0) *
              (gInv i j * C r i j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro r _
        rw [hInv p r]
      _ = ∑ i : Idx, ∑ j : Idx, gInv i j * C p i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_eq_single p]
        · simp
        · intro r _ hr
          have hpr : p ≠ r := fun h => hr h.symm
          simp [hpr]
        · intro hp
          exact False.elim (hp (Finset.mem_univ _))




theorem connTraceCoeff
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (p : Idx) :
    basis.repr (connTraceAt (I := I) g A) p =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          componentRS_gen (I := I) basis A
            (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) := by
  classical
  let coeff : Idx → Real := fun p0 =>
    ∑ q : Idx,
      gInv p0 q *
        (∑ i : Idx, ∑ j : Idx,
          gInv i j *
            (A (dualToCotangent_gen (I := I)
                ((tangentFlatLinear_gen (I := I) g x) (basis q))))
              (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0))
  have hvec :
      connTraceAt (I := I) g A =
        ∑ p0 : Idx, coeff p0 • basis p0 := by
    simpa [coeff] using connTraceAt_coord (I := I) g A basis gInv hinv
  have hcoeff :
      basis.repr (connTraceAt (I := I) g A) p = coeff p := by
    rw [hvec]
    rw [map_sum]
    simp only [map_smul, Module.Basis.repr_self]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    change (∑ c : Idx, Finsupp.single c (coeff c)) p = coeff p
    rw [Finsupp.finset_sum_apply
      (S := Finset.univ)
      (f := fun c : Idx => (Finsupp.single c (coeff c) : Idx →₀ Real))
      (a := p)]
    calc
      (∑ c : Idx, (Finsupp.single c (coeff c) : Idx →₀ Real) p) =
          (Finsupp.single p (coeff p) : Idx →₀ Real) p := by
        refine Finset.sum_eq_single
          (s := Finset.univ)
          (f := fun c : Idx => (Finsupp.single c (coeff c) : Idx →₀ Real) p)
          (a := p) ?_ ?_
        · intro b _ hb
          simpa using
            (Finsupp.single_eq_of_ne hb.symm :
              (Finsupp.single b (coeff b) : Idx →₀ Real) p = 0)
        · intro hp
          exact False.elim (hp (Finset.mem_univ _))
      _ = coeff p := by
        rw [Finsupp.single_eq_same]
  rw [hcoeff]
  dsimp [coeff]
  simp_rw [traceFlat_apply_sum (I := I) g A basis]
  exact traceAlg gInv (fun q r => g.inner x (basis q) (basis r))
    (fun r i j =>
      componentRS_gen (I := I) basis A
        (fun _ : Fin 1 => r)
        (fun q : Fin 2 => if q = 0 then i else j))
    (fun a b => (hinv a b).1) p

private theorem gInvComp_contMDiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        inverseMetricFlatModelInChart_component (I := I) g x₀ i j
          (extChartAt I x₀ y)) x₀ := by
  haveI : CompleteSpace E := FiniteDimensional.complete Real E
  let f : E → Real :=
    inverseMetricFlatModelInChart_component (I := I) g x₀ i j
  have hf :
      ContDiffWithinAt Real ∞ f (Set.range I) (extChartAt I x₀ x₀) :=
    inverseMetricFlatModelInChart_component_contDiffWithinAt (I := I) g x₀ i j
  have hchart :
      ContMDiffWithinAt I 𝓘(Real, E) ∞ (extChartAt I x₀)
        (extChartAt I x₀).source x₀ :=
    (contMDiffAt_extChartAt (I := I) (x := x₀)).contMDiffWithinAt
  have hcomp :
      ContMDiffWithinAt I 𝓘(Real, Real) ∞ (f ∘ extChartAt I x₀)
        (extChartAt I x₀).source x₀ := by
    exact hf.comp_contMDiffWithinAt hchart (by
      intro y hy
      exact extChartAt_target_subset_range x₀ ((extChartAt I x₀).map_source hy))
  have hcompAt :
      ContMDiffAt I 𝓘(Real, Real) ∞ (f ∘ extChartAt I x₀) x₀ :=
    hcomp.contMDiffAt ((isOpen_extChartAt_source (I := I) x₀).mem_nhds
      (mem_extChartAt_source (I := I) x₀))
  simpa [f, Function.comp_def] using hcompAt



private theorem trace02_eventually
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M) :
    (fun y : M => metricTracePair0SAt (I := I) g (A y)) =ᶠ[nhds x₀]
      fun y : M =>
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ y) *
              A y
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y) := by
  classical
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with y hy
  let basis := coordinateFrameAt_basis (I := I) x₀ hy
  let gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x₀ i j
        (extChartAt I x₀ y)
  have htrace :=
    metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv
      (gInvBasisAt (I := I) g x₀ hy) (A y)
  calc
    metricTracePair0SAt (I := I) g (A y) =
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            gInv i j * A y (vec2 (I := I) (basis i) (basis j)) := htrace
    _ =
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ y) *
              A y
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      apply congrArg
      funext q
      fin_cases q <;>
        simp [basis, coordinateFrameAt_basis_apply, DifferentialGeometry.Integral.Connection.vec2]


theorem trace02_smooth
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun x : M => metricTracePair0SAt (I := I) g (A x)) := by
  classical
  intro x₀
  have hRhs :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                  (extChartAt I x₀ y) *
                A y
        (fun q : Fin 2 =>
          coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y))
        x₀ := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    exact (gInvComp_contMDiffAt (I := I) g x₀ i j).mul
      (DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
        (𝕜 := Real) (I := I) (M := M) A x₀
        (fun q : Fin 2 => if q = 0 then i else j))
  exact hRhs.congr_of_eventuallyEq (trace02_eventually (I := I) g A x₀)



private theorem normSq02_eventually
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M) :
    (fun y : M => normSq0S (I := I) g y 2 (A y)) =ᶠ[nhds x₀]
      fun y : M =>
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            ∑ k : CoordinateIdx (𝕜 := Real) E,
              ∑ l : CoordinateIdx (𝕜 := Real) E,
                inverseMetricFlatModelInChart_component (I := I) g x₀ i k
                    (extChartAt I x₀ y) *
                  inverseMetricFlatModelInChart_component (I := I) g x₀ j l
                    (extChartAt I x₀ y) *
                  A y (fun q : Fin 2 =>
                    coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y) *
                  A y (fun q : Fin 2 =>
                    coordinateFrameAt (I := I) x₀ (if q = 0 then k else l) y) := by
  classical
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with y hy
  let basis := coordinateFrameAt_basis (I := I) x₀ hy
  let gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x₀ i j
        (extChartAt I x₀ y)
  have hsq :=
    normSq0S_two_eq_coord (I := I) g y basis gInv
      (gInvBasisAt (I := I) g x₀ hy) (A y)
  rw [hsq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have e1 : (fun a : Fin 2 => if a = 0 then basis i else basis j)
      = (fun q : Fin 2 => coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y) := by
    funext q; fin_cases q <;> simp [basis, coordinateFrameAt_basis_apply]
  have e2 : (fun a : Fin 2 => if a = 0 then basis k else basis l)
      = (fun q : Fin 2 => coordinateFrameAt (I := I) x₀ (if q = 0 then k else l) y) := by
    funext q; fin_cases q <;> simp [basis, coordinateFrameAt_basis_apply]
  rw [e1, e2]



theorem normSq02_smooth
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun x : M => normSq0S (I := I) g x 2 (A x)) := by
  classical
  intro x₀
  have hRhs :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              ∑ k : CoordinateIdx (𝕜 := Real) E,
                ∑ l : CoordinateIdx (𝕜 := Real) E,
                  inverseMetricFlatModelInChart_component (I := I) g x₀ i k
                      (extChartAt I x₀ y) *
                    inverseMetricFlatModelInChart_component (I := I) g x₀ j l
                      (extChartAt I x₀ y) *
                    A y (fun q : Fin 2 =>
                      coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y) *
                    A y (fun q : Fin 2 =>
                      coordinateFrameAt (I := I) x₀ (if q = 0 then k else l) y))
        x₀ := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ =>
      ContMDiffAt.sum fun k _ => ContMDiffAt.sum fun l _ => ?_
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    exact (((gInvComp_contMDiffAt (I := I) g x₀ i k).mul
        (gInvComp_contMDiffAt (I := I) g x₀ j l)).mul
        (DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
          (𝕜 := Real) (I := I) (M := M) A x₀
          (fun q : Fin 2 => if q = 0 then i else j))).mul
      (DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
        (𝕜 := Real) (I := I) (M := M) A x₀
        (fun q : Fin 2 => if q = 0 then k else l))
  exact hRhs.congr_of_eventuallyEq (normSq02_eventually (I := I) g A x₀)



private theorem normSq0S_eventually
    (g : SmoothRiemannianMetric I M) {s : Nat}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) :
    (fun y : M => normSq0S (I := I) g y s (A y)) =ᶠ[nhds x₀]
      fun y : M =>
        ∑ I0 : Fin s → CoordinateIdx (𝕜 := Real) E,
          ∑ J0 : Fin s → CoordinateIdx (𝕜 := Real) E,
            (∏ a : Fin s,
                inverseMetricFlatModelInChart_component (I := I) g x₀
                  (I0 a) (J0 a) (extChartAt I x₀ y)) *
              A y (fun a : Fin s => coordinateFrameAt (I := I) x₀ (I0 a) y) *
              A y (fun a : Fin s => coordinateFrameAt (I := I) x₀ (J0 a) y) := by
  classical
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with y hy
  let basis := coordinateFrameAt_basis (I := I) x₀ hy
  let gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x₀ i j
        (extChartAt I x₀ y)
  rw [normSq0S_eq_coord (I := I) g y s basis gInv
    (gInvBasisAt (I := I) g x₀ hy) (A y)]
  unfold coordInner0S tensor0SComponent
  refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun J0 _ => ?_
  have hI : (fun a : Fin s => basis (I0 a)) =
      (fun a : Fin s => coordinateFrameAt (I := I) x₀ (I0 a) y) := by
    funext a
    simp [basis, coordinateFrameAt_basis_apply]
  have hJ : (fun a : Fin s => basis (J0 a)) =
      (fun a : Fin s => coordinateFrameAt (I := I) x₀ (J0 a) y) := by
    funext a
    simp [basis, coordinateFrameAt_basis_apply]
  rw [hI, hJ]



theorem normSq0S_smooth {s : Nat}
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun x : M => normSq0S (I := I) g x s (A x)) := by
  classical
  intro x₀
  have hRhs :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          ∑ I0 : Fin s → CoordinateIdx (𝕜 := Real) E,
            ∑ J0 : Fin s → CoordinateIdx (𝕜 := Real) E,
              (∏ a : Fin s,
                  inverseMetricFlatModelInChart_component (I := I) g x₀
                    (I0 a) (J0 a) (extChartAt I x₀ y)) *
                A y (fun a : Fin s => coordinateFrameAt (I := I) x₀ (I0 a) y) *
                A y (fun a : Fin s => coordinateFrameAt (I := I) x₀ (J0 a) y))
        x₀ := by
    refine ContMDiffAt.sum fun I0 _ => ContMDiffAt.sum fun J0 _ => ?_
    have hInv :
        ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun y : M =>
            ∏ a : Fin s,
              inverseMetricFlatModelInChart_component (I := I) g x₀
                (I0 a) (J0 a) (extChartAt I x₀ y)) x₀ := by
      exact ContMDiffAt.prod fun a _ =>
        gInvComp_contMDiffAt (I := I) g x₀ (I0 a) (J0 a)
    exact ((hInv.mul
      (DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
        (𝕜 := Real) (I := I) (M := M) A x₀ I0)).mul
      (DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
        (𝕜 := Real) (I := I) (M := M) A x₀ J0))
  exact hRhs.congr_of_eventuallyEq (normSq0S_eventually (I := I) g A x₀)

theorem connTraceCoeff_eventually
    (g : SmoothRiemannianMetric I M)
    (A : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (x₀ : M) (p : CoordinateIdx (𝕜 := Real) E) :
    (fun y : M =>
        (coordinateFrameAt_isLocalFrame (I := I) x₀).coeff p y
          (connTraceAt (I := I) g (A y))) =ᶠ[nhds x₀]
      fun y : M =>
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ y) *
              (A y
                (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                  (I := I) (M := M) 1 x₀
                  ((continuousMultilinearMap_basis
                    (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                    (fun _ : Fin 1 => p)) y))
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y) := by
  classical
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with y hy
  let basis := coordinateFrameAt_basis (I := I) x₀ hy
  let gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x₀ i j
        (extChartAt I x₀ y)
  have hcoeff :=
    connTraceCoeff (I := I) g (A y) basis gInv
      (gInvBasisAt (I := I) g x₀ hy) p
  calc
    (coordinateFrameAt_isLocalFrame (I := I) x₀).coeff p y
        (connTraceAt (I := I) g (A y))
        =
          basis.repr (connTraceAt (I := I) g (A y)) p := by
            simp [basis, coordinateFrameAt_basis, IsLocalFrameOn.coeff, hy]
    _ =
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            gInv i j *
              componentRS_gen (I := I) basis (A y)
                (fun _ : Fin 1 => p)
                (fun q : Fin 2 => if q = 0 then i else j) := hcoeff
    _ =
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ y) *
              (A y
                (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                  (I := I) (M := M) 1 x₀
                  ((continuousMultilinearMap_basis
                    (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                    (fun _ : Fin 1 => p)) y))
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          have hconst :=
            constInChart_basisTensor0S_coordFrame (𝕜 := Real) (I := I)
              (M := M) (r := 1) x₀ hy (fun _ : Fin 1 => p)
          simp [basis, componentRS_apply_gen, coordinateFrameAt_basis_apply,
            hconst]

private theorem connTraceCoeff_contMDiffAt
    (g : SmoothRiemannianMetric I M)
    (A : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (x₀ : M) (p : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        (coordinateFrameAt_isLocalFrame (I := I) x₀).coeff p y
          (connTraceAt (I := I) g (A y))) x₀ := by
  classical
  have hRhs :
      ContMDiffAt I 𝓘(Real, Real) ∞
        (fun y : M =>
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                  (extChartAt I x₀ y) *
                (A y
                  (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                    (I := I) (M := M) 1 x₀
                    ((continuousMultilinearMap_basis
                      (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                      (fun _ : Fin 1 => p)) y))
                  (fun q : Fin 2 =>
                    coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y))
        x₀ := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    exact (gInvComp_contMDiffAt (I := I) g x₀ i j).mul
      (tensorRS_eval_constInChart_coordinateFrame_contMDiffAt
        (𝕜 := Real) (I := I) (M := M) A x₀
        (fun _ : Fin 1 => p)
        (fun q : Fin 2 => if q = 0 then i else j))
  exact hRhs.congr_of_eventuallyEq
    (connTraceCoeff_eventually (I := I) g A x₀ p)


def connTraceField
    (g : SmoothRiemannianMetric I M)
    (A : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) := by
  refine ⟨fun x : M => connTraceAt (I := I) g (A x), ?_⟩
  intro x₀
  exact (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt_of_coeff
    (fun p => connTraceCoeff_contMDiffAt (I := I) g A x₀ p)
    ((coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀))

@[simp] theorem connTraceField_apply
    (g : SmoothRiemannianMetric I M)
    (A : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) :
    connTraceField (I := I) g A x = connTraceAt (I := I) g (A x) := rfl


theorem connTraceField_coord
    (g : SmoothRiemannianMetric I M)
    (A : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (p : CoordinateIdx (𝕜 := Real) E) :
    (coordinateFrameAt_isLocalFrame (I := I) x₀).coeff p x
        (connTraceField (I := I) g A x) =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x₀ i j
              (extChartAt I x₀ x) *
            componentRS_gen (I := I) (coordinateFrameAt_basis (I := I) x₀ hx)
              (A x) (fun _ : Fin 1 => p)
              (fun q : Fin 2 => if q = 0 then i else j) := by
  classical
  let basis := coordinateFrameAt_basis (I := I) x₀ hx
  let gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x₀ i j
        (extChartAt I x₀ x)
  have hcoeff :=
    connTraceCoeff (I := I) g (A x) basis gInv
      (gInvBasisAt (I := I) g x₀ hx) p
  calc
    (coordinateFrameAt_isLocalFrame (I := I) x₀).coeff p x
        (connTraceField (I := I) g A x)
        =
          basis.repr (connTraceAt (I := I) g (A x)) p := by
            simp [basis, coordinateFrameAt_basis, IsLocalFrameOn.coeff, hx]
    _ =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInv i j *
            componentRS_gen (I := I) basis (A x) (fun _ : Fin 1 => p)
              (fun q : Fin 2 => if q = 0 then i else j) := hcoeff
    _ =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x₀ i j
              (extChartAt I x₀ x) *
            componentRS_gen (I := I) (coordinateFrameAt_basis (I := I) x₀ hx)
              (A x) (fun _ : Fin 1 => p)
              (fun q : Fin 2 => if q = 0 then i else j) := rfl

end

end DifferentialGeometry.Integral.Connection
