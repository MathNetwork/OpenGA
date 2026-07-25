import DifferentialGeometry.Geometry.Curvature.DimensionThree.PinchingAlgebra
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RiemannFromRicci
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Basic
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Coordinate
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Product
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Smooth
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic










noncomputable section

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Integral.Connection Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {x : M}


def ricciDiag3 (l1 l2 l3 : Real) (i j : Fin 3) : Real :=
  if i = j then
    if i = 0 then l1 else if i = 1 then l2 else l3
  else 0



def stdRmDiag3 (l1 l2 l3 : Real)
    (i j k l : Fin 3) : Real :=
  delta3 i k * ricciDiag3 l1 l2 l3 j l
    - delta3 i l * ricciDiag3 l1 l2 l3 j k
    - delta3 j k * ricciDiag3 l1 l2 l3 i l
    + delta3 j l * ricciDiag3 l1 l2 l3 i k
    - (1 / 2 : Real) * ricciEigenScalar3 l1 l2 l3 *
        (delta3 i k * delta3 j l - delta3 i l * delta3 j k)


def stdRmNormSq3
    (R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real) : Real :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
    (R i j k l) ^ 2

private def fin4SlotsEquiv :
    (Fin 4 -> Fin 3) ≃ (((Fin 3 × Fin 3) × Fin 3) × Fin 3) where
  toFun f := (((f 0, f 1), f 2), f 3)
  invFun p := slots4 p.1.1.1 p.1.1.2 p.1.2 p.2
  left_inv f := by
    funext a
    fin_cases a <;> simp [slots4]
  right_inv p := by
    rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
    simp [slots4]

private theorem sum_fin_four_fun {α : Type*} [AddCommMonoid α]
    (F : (Fin 4 -> Fin 3) -> α) :
    (∑ I0 : Fin 4 -> Fin 3, F I0) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        F (slots4 i j k l) := by
  classical
  rw [Fintype.sum_equiv fin4SlotsEquiv F
    (fun p : (((Fin 3 × Fin 3) × Fin 3) × Fin 3) =>
      F (slots4 p.1.1.1 p.1.1.2 p.1.2 p.2))]
  · repeat rw [Fintype.sum_prod_type]
  · intro I0
    have hslot :
        slots4 (fin4SlotsEquiv I0).1.1.1 (fin4SlotsEquiv I0).1.1.2
            (fin4SlotsEquiv I0).1.2 (fin4SlotsEquiv I0).2 = I0 := by
      change fin4SlotsEquiv.symm (fin4SlotsEquiv I0) = I0
      exact fin4SlotsEquiv.left_inv I0
    rw [hslot]

private theorem prod_delta3_slots4_eq_ite
    (I0 J0 : Fin 4 -> Fin 3) :
    (∏ a : Fin 4, delta3 (I0 a) (J0 a)) =
      if I0 = J0 then 1 else 0 := by
  classical
  rw [Fin.prod_univ_four]
  by_cases h : I0 = J0
  · subst J0
    simp [delta3]
  · have hne :
        I0 0 ≠ J0 0 ∨ I0 1 ≠ J0 1 ∨ I0 2 ≠ J0 2 ∨ I0 3 ≠ J0 3 := by
      by_contra hslots
      push Not at hslots
      apply h
      funext a
      fin_cases a <;> simp [hslots]
    rcases hne with h0 | h1 | h2 | h3
    · simp [delta3, h, h0]
    · simp [delta3, h, h1]
    · simp [delta3, h, h2]
    · simp [delta3, h, h3]

private theorem sum_delta3_slots4_contract
    (F : (Fin 4 -> Fin 3) -> Real) :
    (∑ I0 : Fin 4 -> Fin 3, ∑ J0 : Fin 4 -> Fin 3,
        (∏ a : Fin 4, delta3 (I0 a) (J0 a)) * F I0 * F J0) =
      ∑ I0 : Fin 4 -> Fin 3, (F I0) ^ 2 := by
  classical
  apply Finset.sum_congr rfl
  intro I0 _
  simp [prod_delta3_slots4_eq_ite, pow_two]




def RicciDiagAt
    (Ric : Tensor02At (I := I) (M := M) x)
    (scalar l1 l2 l3 : Real)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Prop :=
  scalar = ricciEigenScalar3 l1 l2 l3 /\
    forall i j : Fin 3,
      ricciCompAt (I := I) basis Ric i j = ricciDiag3 l1 l2 l3 i j



theorem ricciEigen3
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02At (I := I) (M := M) x)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hsymm : RicciSymAt (I := I) Ric) :
    exists basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      exists l1 l2 l3 : Real,
        OrthonormalBasisAt (I := I) g x basis /\
        RicciDiagAt (I := I) Ric (ricciEigenScalar3 l1 l2 l3)
          l1 l2 l3 basis := by
  classical
  let D := (tangentMetricData_gen (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _
      D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let T := ricciEndAt (I := I) g Ric
  have hT : T.IsSymmetric := by
    intro X Y
    rw [MetricFiberData.toCore_inner D (T X) Y,
      MetricFiberData.toCore_inner D X (T Y)]
    change g.inner x (T X) Y = g.inner x X (T Y)
    calc
      g.inner x (T X) Y = Ric (vec2 X Y) := by
        exact ricciEnd_inner (I := I) g Ric X Y
      _ = Ric (vec2 Y X) := hsymm X Y
      _ = g.inner x (T Y) X := by
        exact (ricciEnd_inner (I := I) g Ric Y X).symm
      _ = g.inner x X (T Y) := by
        exact g.symm x (T Y) X
  let ob := hT.eigenvectorBasis hdim
  let basis : Module.Basis (Fin 3) Real (TangentSpace I x) := ob.toBasis
  let l1 : Real := hT.eigenvalues hdim 0
  let l2 : Real := hT.eigenvalues hdim 1
  let l3 : Real := hT.eigenvalues hdim 2
  refine ⟨basis, l1, l2, l3, ?_, ?_⟩
  · intro i j
    have hinner :
        Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
      MetricFiberData.toCore_inner D (ob i) (ob j)
    have hob := ob.inner_eq_ite i j
    change g.inner x (basis i) (basis j) = delta3 i j
    rw [← TangentMetricData_gen.inner_eq_gen (tangentMetricData_gen (I := I) g x)
      (basis i) (basis j)]
    change D.inner (basis i) (basis j) = delta3 i j
    change D.inner (ob i) (ob j) = delta3 i j
    rw [← hinner]
    simpa [delta3] using hob
  · constructor
    · rfl
    · intro i j
      have heig := hT.apply_eigenvectorBasis hdim i
      have hcomp :
          Ric (vec2 (basis i) (basis j)) =
            hT.eigenvalues hdim i * delta3 i j := by
        calc
          Ric (vec2 (basis i) (basis j)) =
              g.inner x (T (basis i)) (basis j) := by
                exact (ricciEnd_inner (I := I) g Ric (basis i) (basis j)).symm
          _ = g.inner x ((hT.eigenvalues hdim i) • basis i) (basis j) := by
                change g.inner x (T (ob i)) (ob j) =
                  g.inner x ((hT.eigenvalues hdim i) • ob i) (ob j)
                simpa [ob] using congrArg (fun v => g.inner x v (ob j)) heig
          _ = hT.eigenvalues hdim i * delta3 i j := by
                have horth :
                    g.inner x (basis i) (basis j) = delta3 i j := by
                  change g.inner x (ob i) (ob j) = delta3 i j
                  have hinner :
                      Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
                    MetricFiberData.toCore_inner D (ob i) (ob j)
                  have hob := ob.inner_eq_ite i j
                  rw [← TangentMetricData_gen.inner_eq_gen (tangentMetricData_gen (I := I) g x)
                    (ob i) (ob j)]
                  change D.inner (ob i) (ob j) = delta3 i j
                  rw [← hinner]
                  simpa [delta3] using hob
                simp [horth]
      fin_cases i <;> fin_cases j <;>
        simpa [ricciCompAt_apply, ricciDiag3, l1, l2, l3, delta3] using hcomp



theorem ricciEigenBasis3
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02At (I := I) (M := M) x)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hsymm : RicciSymAt (I := I) Ric)
    (hnonneg : RicciNonnegAt (I := I) Ric) :
    exists basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      exists l1 l2 l3 : Real,
        OrthonormalBasisAt (I := I) g x basis /\
        RicciDiagAt (I := I) Ric (ricciEigenScalar3 l1 l2 l3)
          l1 l2 l3 basis /\
        0 <= l1 /\ 0 <= l2 /\ 0 <= l3 := by
  classical
  let D := (tangentMetricData_gen (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _
      D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let T := ricciEndAt (I := I) g Ric
  have hT : T.IsSymmetric := by
    intro X Y
    rw [MetricFiberData.toCore_inner D (T X) Y,
      MetricFiberData.toCore_inner D X (T Y)]
    change g.inner x (T X) Y = g.inner x X (T Y)
    calc
      g.inner x (T X) Y = Ric (vec2 X Y) := by
        exact ricciEnd_inner (I := I) g Ric X Y
      _ = Ric (vec2 Y X) := hsymm X Y
      _ = g.inner x (T Y) X := by
        exact (ricciEnd_inner (I := I) g Ric Y X).symm
      _ = g.inner x X (T Y) := by
        exact g.symm x (T Y) X
  let ob := hT.eigenvectorBasis hdim
  let basis : Module.Basis (Fin 3) Real (TangentSpace I x) := ob.toBasis
  let l1 : Real := hT.eigenvalues hdim 0
  let l2 : Real := hT.eigenvalues hdim 1
  let l3 : Real := hT.eigenvalues hdim 2
  refine ⟨basis, l1, l2, l3, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    have hinner :
        Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
      MetricFiberData.toCore_inner D (ob i) (ob j)
    have hob := ob.inner_eq_ite i j
    change g.inner x (basis i) (basis j) = delta3 i j
    rw [← TangentMetricData_gen.inner_eq_gen (tangentMetricData_gen (I := I) g x)
      (basis i) (basis j)]
    change D.inner (basis i) (basis j) = delta3 i j
    change D.inner (ob i) (ob j) = delta3 i j
    rw [← hinner]
    simpa [delta3] using hob
  · constructor
    · rfl
    · intro i j
      have heig := hT.apply_eigenvectorBasis hdim i
      have hcomp :
          Ric (vec2 (basis i) (basis j)) =
            hT.eigenvalues hdim i * delta3 i j := by
        calc
          Ric (vec2 (basis i) (basis j)) =
              g.inner x (T (basis i)) (basis j) := by
                exact (ricciEnd_inner (I := I) g Ric (basis i) (basis j)).symm
          _ = g.inner x ((hT.eigenvalues hdim i) • basis i) (basis j) := by
                change g.inner x (T (ob i)) (ob j) =
                  g.inner x ((hT.eigenvalues hdim i) • ob i) (ob j)
                simpa [ob] using congrArg (fun v => g.inner x v (ob j)) heig
          _ = hT.eigenvalues hdim i * delta3 i j := by
                have horth :
                    g.inner x (basis i) (basis j) = delta3 i j := by
                  change g.inner x (ob i) (ob j) = delta3 i j
                  have hinner :
                      Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
                    MetricFiberData.toCore_inner D (ob i) (ob j)
                  have hob := ob.inner_eq_ite i j
                  rw [← TangentMetricData_gen.inner_eq_gen (tangentMetricData_gen (I := I) g x)
                    (ob i) (ob j)]
                  change D.inner (ob i) (ob j) = delta3 i j
                  rw [← hinner]
                  simpa [delta3] using hob
                simp [horth]
      fin_cases i <;> fin_cases j <;>
        simpa [ricciCompAt_apply, ricciDiag3, l1, l2, l3, delta3] using hcomp
  · have hdiag :
        RicciDiagAt (I := I) Ric (ricciEigenScalar3 l1 l2 l3)
          l1 l2 l3 basis := by
      constructor
      · rfl
      · intro i j
        have heig := hT.apply_eigenvectorBasis hdim i
        have hcomp :
            Ric (vec2 (basis i) (basis j)) =
              hT.eigenvalues hdim i * delta3 i j := by
          calc
            Ric (vec2 (basis i) (basis j)) =
                g.inner x (T (basis i)) (basis j) := by
                  exact (ricciEnd_inner (I := I) g Ric (basis i) (basis j)).symm
            _ = g.inner x ((hT.eigenvalues hdim i) • basis i) (basis j) := by
                  change g.inner x (T (ob i)) (ob j) =
                    g.inner x ((hT.eigenvalues hdim i) • ob i) (ob j)
                  simpa [ob] using congrArg (fun v => g.inner x v (ob j)) heig
            _ = hT.eigenvalues hdim i * delta3 i j := by
                  have horth :
                      g.inner x (basis i) (basis j) = delta3 i j := by
                    change g.inner x (ob i) (ob j) = delta3 i j
                    have hinner :
                        Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
                      MetricFiberData.toCore_inner D (ob i) (ob j)
                    have hob := ob.inner_eq_ite i j
                    rw [← TangentMetricData_gen.inner_eq_gen (tangentMetricData_gen (I := I) g x)
                      (ob i) (ob j)]
                    change D.inner (ob i) (ob j) = delta3 i j
                    rw [← hinner]
                    simpa [delta3] using hob
                  simp [horth]
        fin_cases i <;> fin_cases j <;>
          simpa [ricciCompAt_apply, ricciDiag3, l1, l2, l3, delta3] using hcomp
    have h00 := hdiag.2 0 0
    have hnon := hnonneg (basis 0)
    rw [ricciCompAt_apply] at h00
    rw [h00] at hnon
    simpa [ricciDiag3, l1] using hnon
  · have hdiag :
        RicciDiagAt (I := I) Ric (ricciEigenScalar3 l1 l2 l3)
          l1 l2 l3 basis := by
      constructor
      · rfl
      · intro i j
        have heig := hT.apply_eigenvectorBasis hdim i
        have hcomp :
            Ric (vec2 (basis i) (basis j)) =
              hT.eigenvalues hdim i * delta3 i j := by
          calc
            Ric (vec2 (basis i) (basis j)) =
                g.inner x (T (basis i)) (basis j) := by
                  exact (ricciEnd_inner (I := I) g Ric (basis i) (basis j)).symm
            _ = g.inner x ((hT.eigenvalues hdim i) • basis i) (basis j) := by
                  change g.inner x (T (ob i)) (ob j) =
                    g.inner x ((hT.eigenvalues hdim i) • ob i) (ob j)
                  simpa [ob] using congrArg (fun v => g.inner x v (ob j)) heig
            _ = hT.eigenvalues hdim i * delta3 i j := by
                  have horth :
                      g.inner x (basis i) (basis j) = delta3 i j := by
                    change g.inner x (ob i) (ob j) = delta3 i j
                    have hinner :
                        Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
                      MetricFiberData.toCore_inner D (ob i) (ob j)
                    have hob := ob.inner_eq_ite i j
                    rw [← TangentMetricData_gen.inner_eq_gen (tangentMetricData_gen (I := I) g x)
                      (ob i) (ob j)]
                    change D.inner (ob i) (ob j) = delta3 i j
                    rw [← hinner]
                    simpa [delta3] using hob
                  simp [horth]
        fin_cases i <;> fin_cases j <;>
          simpa [ricciCompAt_apply, ricciDiag3, l1, l2, l3, delta3] using hcomp
    have hnon := hnonneg (basis 1)
    have h11 := hdiag.2 1 1
    rw [ricciCompAt_apply] at h11
    rw [h11] at hnon
    simpa [ricciDiag3, l2] using hnon
  · have hdiag :
        RicciDiagAt (I := I) Ric (ricciEigenScalar3 l1 l2 l3)
          l1 l2 l3 basis := by
      constructor
      · rfl
      · intro i j
        have heig := hT.apply_eigenvectorBasis hdim i
        have hcomp :
            Ric (vec2 (basis i) (basis j)) =
              hT.eigenvalues hdim i * delta3 i j := by
          calc
            Ric (vec2 (basis i) (basis j)) =
                g.inner x (T (basis i)) (basis j) := by
                  exact (ricciEnd_inner (I := I) g Ric (basis i) (basis j)).symm
            _ = g.inner x ((hT.eigenvalues hdim i) • basis i) (basis j) := by
                  change g.inner x (T (ob i)) (ob j) =
                    g.inner x ((hT.eigenvalues hdim i) • ob i) (ob j)
                  simpa [ob] using congrArg (fun v => g.inner x v (ob j)) heig
            _ = hT.eigenvalues hdim i * delta3 i j := by
                  have horth :
                      g.inner x (basis i) (basis j) = delta3 i j := by
                    change g.inner x (ob i) (ob j) = delta3 i j
                    have hinner :
                        Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
                      MetricFiberData.toCore_inner D (ob i) (ob j)
                    have hob := ob.inner_eq_ite i j
                    rw [← TangentMetricData_gen.inner_eq_gen (tangentMetricData_gen (I := I) g x)
                      (ob i) (ob j)]
                    change D.inner (ob i) (ob j) = delta3 i j
                    rw [← hinner]
                    simpa [delta3] using hob
                  simp [horth]
        fin_cases i <;> fin_cases j <;>
          simpa [ricciCompAt_apply, ricciDiag3, l1, l2, l3, delta3] using hcomp
    have hnon := hnonneg (basis 2)
    have h22 := hdiag.2 2 2
    rw [ricciCompAt_apply] at h22
    rw [h22] at hnon
    simpa [ricciDiag3, l3] using hnon




theorem exists_orthonormalBasisAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3) :
    exists basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      OrthonormalBasisAt (I := I) g x basis := by
  obtain ⟨basis, _, _, _, horth, _, _, _, _⟩ :=
    ricciEigenBasis3 (I := I) g (0 : Tensor02At (I := I) (M := M) x) hdim
      (fun _ _ => rfl) (fun _ => by simp)
  exact ⟨basis, horth⟩



theorem metricTrace_eq_ricciEnd
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02At (I := I) (M := M) x) :
    DifferentialGeometry.Integral.Connection.metricTracePair0SAt (I := I) g Ric =
      LinearMap.trace Real (TangentSpace I x)
        (ricciEndAt (I := I) g Ric) := by
  classical
  let basis : Module.Basis (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) Real
      (TangentSpace I x) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv :
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real := fun k l =>
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := I) g x k l (extChartAt I x x)
  have hinv :
      MetricInverseInBasis_gen (I := I) g x basis gInv := by
    simpa [basis, gInv] using
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) g x
  rw [DifferentialGeometry.Integral.Connection.metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  rw [linearMap_trace_eq_sum_inv_inner_apply (I := I) g x basis gInv hinv]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ricciEnd_inner (I := I) g Ric (basis i) (basis j)]




theorem metricTrace_pos_of_posDef
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02At (I := I) (M := M) x)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hpos : forall v : TangentSpace I x, v ≠ 0 ->
      0 < Ric (vec2 (I := I) v v)) :
    0 < DifferentialGeometry.Integral.Connection.metricTracePair0SAt (I := I) g Ric := by
  classical
  let D := (tangentMetricData_gen (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _
      D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  have htrace :
      0 < LinearMap.trace Real (TangentSpace I x)
        (ricciEndAt (I := I) g Ric) := by
    rw [LinearMap.trace_eq_sum_inner
      (ricciEndAt (I := I) g Ric)
      (stdOrthonormalBasis Real (TangentSpace I x))]
    refine Finset.sum_pos ?_ ?_
    · intro i _hi
      have hne :
          stdOrthonormalBasis Real (TangentSpace I x) i ≠ 0 := by
        intro hzero
        have hnorm :
            ‖stdOrthonormalBasis Real (TangentSpace I x) i‖ = (1 : Real) :=
          (stdOrthonormalBasis Real (TangentSpace I x)).norm_eq_one i
        simp [hzero] at hnorm
      have hinner :
          Inner.inner Real
              ((ricciEndAt (I := I) g Ric)
                (stdOrthonormalBasis Real (TangentSpace I x) i))
              (stdOrthonormalBasis Real (TangentSpace I x) i) =
            g.inner x
              ((ricciEndAt (I := I) g Ric)
                (stdOrthonormalBasis Real (TangentSpace I x) i))
              (stdOrthonormalBasis Real (TangentSpace I x) i) := by
        change D.inner
              ((ricciEndAt (I := I) g Ric)
                (stdOrthonormalBasis Real (TangentSpace I x) i))
              (stdOrthonormalBasis Real (TangentSpace I x) i) =
            g.inner x
              ((ricciEndAt (I := I) g Ric)
                (stdOrthonormalBasis Real (TangentSpace I x) i))
              (stdOrthonormalBasis Real (TangentSpace I x) i)
        rfl
      rw [real_inner_comm, hinner,
        ricciEnd_inner (I := I) g Ric
          (stdOrthonormalBasis Real (TangentSpace I x) i)
          (stdOrthonormalBasis Real (TangentSpace I x) i)]
      exact hpos (stdOrthonormalBasis Real (TangentSpace I x) i) hne
    · exact ⟨⟨0, by simp [hdim]⟩, Finset.mem_univ _⟩
  rwa [metricTrace_eq_ricciEnd (I := I) g Ric]

omit [FiniteDimensional ℝ E] in
private theorem scalar_eq_of_trace_diag
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar scalar0 l1 l2 l3 : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (htrace : RiemannFromRicci3DTraceDataAt g Ric scalar Rm04 basis)
    (hdiag : RicciDiagAt (I := I) Ric scalar0 l1 l2 l3 basis) :
    scalar = scalar0 := by
  rcases hdiag with ⟨hscalar0, hric⟩
  have h00 : stdRicci3 (standardRmCompAt basis Rm04) 0 0 = l1 := by
    rw [← htrace.ricci_trace 0 0]
    simpa [ricciDiag3] using hric 0 0
  have h11 : stdRicci3 (standardRmCompAt basis Rm04) 1 1 = l2 := by
    rw [← htrace.ricci_trace 1 1]
    simpa [ricciDiag3] using hric 1 1
  have h22 : stdRicci3 (standardRmCompAt basis Rm04) 2 2 = l3 := by
    rw [← htrace.ricci_trace 2 2]
    simpa [ricciDiag3] using hric 2 2
  calc
    scalar = stdScalar3 (standardRmCompAt basis Rm04) := htrace.scalar_trace
    _ = ricciEigenScalar3 l1 l2 l3 := by
      simp [stdScalar3, h00, h11, h22, ricciEigenScalar3]
    _ = scalar0 := hscalar0.symm


omit [FiniteDimensional ℝ E] in
theorem orthonormal_invBasis3
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis) :
    MetricInverseInBasis_gen (I := I) g x basis delta3 := by
  have h00 : g.inner x (basis 0) (basis 0) = 1 := by
    simpa [delta3] using horth 0 0
  have h01 : g.inner x (basis 0) (basis 1) = 0 := by
    simpa [delta3] using horth 0 1
  have h02 : g.inner x (basis 0) (basis 2) = 0 := by
    simpa [delta3] using horth 0 2
  have h10 : g.inner x (basis 1) (basis 0) = 0 := by
    simpa [delta3] using horth 1 0
  have h11 : g.inner x (basis 1) (basis 1) = 1 := by
    simpa [delta3] using horth 1 1
  have h12 : g.inner x (basis 1) (basis 2) = 0 := by
    simpa [delta3] using horth 1 2
  have h20 : g.inner x (basis 2) (basis 0) = 0 := by
    simpa [delta3] using horth 2 0
  have h21 : g.inner x (basis 2) (basis 1) = 0 := by
    simpa [delta3] using horth 2 1
  have h22 : g.inner x (basis 2) (basis 2) = 1 := by
    simpa [delta3] using horth 2 2
  intro i j
  constructor <;>
    fin_cases i <;> fin_cases j <;>
      simp [delta3, h00, h01, h02, h10, h11, h12, h20, h21, h22]


def sec12Ric3 (l1 l2 l3 : Real) : Real :=
  (l1 + l2 - l3) / 2


def sec13Ric3 (l1 l2 l3 : Real) : Real :=
  (l1 + l3 - l2) / 2


def sec23Ric3 (l1 l2 l3 : Real) : Real :=
  (l2 + l3 - l1) / 2




def rmSecNormSq3 (K12 K13 K23 : Real) : Real :=
  4 * (K12 ^ 2 + K13 ^ 2 + K23 ^ 2)



theorem stdRmNormSq3_diag
    (l1 l2 l3 : Real) :
    stdRmNormSq3 (stdRmDiag3 l1 l2 l3) =
      rmSecNormSq3 (sec12Ric3 l1 l2 l3) (sec13Ric3 l1 l2 l3)
        (sec23Ric3 l1 l2 l3) := by
  unfold stdRmNormSq3 stdRmDiag3 rmSecNormSq3 sec12Ric3 sec13Ric3 sec23Ric3
    ricciDiag3 ricciEigenScalar3 delta3
  simp [Fin.sum_univ_three]
  ring



omit [FiniteDimensional ℝ E] in
theorem stdRmComp_eq_diag
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (htrace : RiemannFromRicci3DTraceDataAt g Ric scalar Rm04 basis)
    {l1 l2 l3 : Real}
    (hdiag : RicciDiagAt (I := I) Ric scalar l1 l2 l3 basis) :
    forall i j k l : Fin 3,
      standardRmCompAt (I := I) basis Rm04 i j k l =
        stdRmDiag3 l1 l2 l3 i j k l := by
  intro i j k l
  have hformula :=
    rm04Comp_displayedRiemannFromRicci3D_at (I := I) htrace i j l k
  rw [standardRmCompAt_apply]
  rw [hformula]
  rcases hdiag with ⟨hscalar, hric⟩
  have r00 : Ric (vec2 (basis 0) (basis 0)) = l1 := by
    simpa [ricciCompAt_apply, ricciDiag3] using hric 0 0
  have r01 : Ric (vec2 (basis 0) (basis 1)) = 0 := by
    simpa [ricciCompAt_apply, ricciDiag3] using hric 0 1
  have r02 : Ric (vec2 (basis 0) (basis 2)) = 0 := by
    simpa [ricciCompAt_apply, ricciDiag3] using hric 0 2
  have r10 : Ric (vec2 (basis 1) (basis 0)) = 0 := by
    simpa [ricciCompAt_apply, ricciDiag3] using hric 1 0
  have r11 : Ric (vec2 (basis 1) (basis 1)) = l2 := by
    simpa [ricciCompAt_apply, ricciDiag3] using hric 1 1
  have r12 : Ric (vec2 (basis 1) (basis 2)) = 0 := by
    simpa [ricciCompAt_apply, ricciDiag3] using hric 1 2
  have r20 : Ric (vec2 (basis 2) (basis 0)) = 0 := by
    simpa [ricciCompAt_apply, ricciDiag3] using hric 2 0
  have r21 : Ric (vec2 (basis 2) (basis 1)) = 0 := by
    simpa [ricciCompAt_apply, ricciDiag3] using hric 2 1
  have r22 : Ric (vec2 (basis 2) (basis 2)) = l3 := by
    simpa [ricciCompAt_apply, ricciDiag3] using hric 2 2
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [stdRmDiag3, ricciDiag3, ricciEigenScalar3, delta3, hscalar,
      r00, r01, r02, r10, r11, r12, r20, r21, r22] <;> ring_nf



omit [FiniteDimensional ℝ E] in
theorem stdRmNormSq3_at
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (htrace : RiemannFromRicci3DTraceDataAt g Ric scalar Rm04 basis)
    {l1 l2 l3 : Real}
    (hdiag : RicciDiagAt (I := I) Ric scalar l1 l2 l3 basis) :
    stdRmNormSq3 (standardRmCompAt (I := I) basis Rm04) =
      rmSecNormSq3 (sec12Ric3 l1 l2 l3) (sec13Ric3 l1 l2 l3)
        (sec23Ric3 l1 l2 l3) := by
  have hcomp := stdRmComp_eq_diag (I := I) htrace hdiag
  unfold stdRmNormSq3
  simp_rw [hcomp]
  exact stdRmNormSq3_diag l1 l2 l3




omit [FiniteDimensional ℝ E] in
theorem coordInner0S_four_delta3_eq_stdRmNormSq3
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)} :
    coordInner0S (I := I) (x := x) 4 delta3 Rm04 Rm04 basis =
      stdRmNormSq3 (standardRmCompAt (I := I) basis Rm04) := by
  classical
  unfold coordInner0S
  rw [sum_delta3_slots4_contract]
  rw [sum_fin_four_fun]
  unfold stdRmNormSq3 standardRmCompAt rm04CompAt component0S
    tensor0SComponent DifferentialGeometry.Integral.Connection.slots4
  simp [Fin.sum_univ_three]



theorem normSq0S_four_eq_stdRmNormSq3
    {g : SmoothRiemannianMetric I M}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : OrthonormalBasisAt (I := I) g x basis) :
    normSq0S (I := I) g x 4 Rm04 =
      stdRmNormSq3 (standardRmCompAt (I := I) basis Rm04) := by
  have hinv : MetricInverseInBasis_gen (I := I) g x basis delta3 :=
    orthonormal_invBasis3 (I := I) g basis horth
  rw [normSq0S_eq_coord (I := I) g x 4 basis delta3 hinv Rm04]
  exact coordInner0S_four_delta3_eq_stdRmNormSq3 (I := I)

private theorem sq_le_of_abs_le {a b : Real} (h : |a| <= b) :
    a ^ 2 <= b ^ 2 := by
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  have hleft : 0 <= b + a := by linarith
  have hright : 0 <= b - a := by linarith
  have hprod : 0 <= (b + a) * (b - a) := mul_nonneg hleft hright
  nlinarith



theorem secAbsLe3
    (l1 l2 l3 : Real) (h1 : 0 <= l1) (h2 : 0 <= l2) (h3 : 0 <= l3) :
    |sec12Ric3 l1 l2 l3| <= ricciEigenScalar3 l1 l2 l3 / 2 ∧
      |sec13Ric3 l1 l2 l3| <= ricciEigenScalar3 l1 l2 l3 / 2 ∧
      |sec23Ric3 l1 l2 l3| <= ricciEigenScalar3 l1 l2 l3 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · apply abs_le.mpr
    constructor <;> unfold sec12Ric3 ricciEigenScalar3 <;> nlinarith
  · apply abs_le.mpr
    constructor <;> unfold sec13Ric3 ricciEigenScalar3 <;> nlinarith
  · apply abs_le.mpr
    constructor <;> unfold sec23Ric3 ricciEigenScalar3 <;> nlinarith






theorem rmSqLe100ScalSq3
    (l1 l2 l3 : Real) (h1 : 0 <= l1) (h2 : 0 <= l2) (h3 : 0 <= l3) :
    rmSecNormSq3 (sec12Ric3 l1 l2 l3) (sec13Ric3 l1 l2 l3)
        (sec23Ric3 l1 l2 l3) <=
      (100 : Real) ^ 2 * ricciEigenScalar3 l1 l2 l3 ^ 2 := by
  let R := ricciEigenScalar3 l1 l2 l3
  rcases secAbsLe3 l1 l2 l3 h1 h2 h3 with ⟨h12, h13, h23⟩
  have h12sq : sec12Ric3 l1 l2 l3 ^ 2 <= (R / 2) ^ 2 :=
    sq_le_of_abs_le h12
  have h13sq : sec13Ric3 l1 l2 l3 ^ 2 <= (R / 2) ^ 2 :=
    sq_le_of_abs_le h13
  have h23sq : sec23Ric3 l1 l2 l3 ^ 2 <= (R / 2) ^ 2 :=
    sq_le_of_abs_le h23
  have hsum :
      rmSecNormSq3 (sec12Ric3 l1 l2 l3) (sec13Ric3 l1 l2 l3)
          (sec23Ric3 l1 l2 l3) <= 4 * (3 * (R / 2) ^ 2) := by
    unfold rmSecNormSq3
    nlinarith
  have hcoarse : 4 * (3 * (R / 2) ^ 2) <= (100 : Real) ^ 2 * R ^ 2 := by
    nlinarith [sq_nonneg R]
  exact le_trans hsum hcoarse




omit [FiniteDimensional ℝ E] in
theorem stdRmNormSq3_at_le
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (htrace : RiemannFromRicci3DTraceDataAt g Ric scalar Rm04 basis)
    {l1 l2 l3 : Real}
    (hdiag : RicciDiagAt (I := I) Ric scalar l1 l2 l3 basis)
    (h1 : 0 <= l1) (h2 : 0 <= l2) (h3 : 0 <= l3) :
    stdRmNormSq3 (standardRmCompAt (I := I) basis Rm04) <= 100 ^ 2 * scalar ^ 2 := by
  have hnorm := stdRmNormSq3_at (I := I) htrace hdiag
  have hscalar : scalar = ricciEigenScalar3 l1 l2 l3 := hdiag.1
  rw [hnorm, hscalar]
  exact rmSqLe100ScalSq3 l1 l2 l3 h1 h2 h3



theorem normSq0S_four_at_le
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (htrace : RiemannFromRicci3DTraceDataAt g Ric scalar Rm04 basis)
    {l1 l2 l3 : Real}
    (hdiag : RicciDiagAt (I := I) Ric scalar l1 l2 l3 basis)
    (h1 : 0 <= l1) (h2 : 0 <= l2) (h3 : 0 <= l3) :
    normSq0S (I := I) g x 4 Rm04 <= 100 ^ 2 * scalar ^ 2 := by
  rw [normSq0S_four_eq_stdRmNormSq3 (I := I) htrace.orthonormal]
  exact stdRmNormSq3_at_le (I := I) htrace hdiag h1 h2 h3





theorem normSqLeOfRicNonneg
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hsymm : RicciSymAt (I := I) Ric)
    (hnonneg : RicciNonnegAt (I := I) Ric)
    (htrace : forall basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      OrthonormalBasisAt (I := I) g x basis ->
        RiemannFromRicci3DTraceDataAt g Ric scalar Rm04 basis) :
    normSq0S (I := I) g x 4 Rm04 <= 100 ^ 2 * scalar ^ 2 := by
  rcases ricciEigenBasis3 (I := I) g Ric hdim hsymm hnonneg with
    ⟨basis, l1, l2, l3, horth, hdiag0, h1, h2, h3⟩
  have htrace_basis := htrace basis horth
  have hscalar :
      scalar = ricciEigenScalar3 l1 l2 l3 :=
    scalar_eq_of_trace_diag (I := I) htrace_basis hdiag0
  have hdiag : RicciDiagAt (I := I) Ric scalar l1 l2 l3 basis := by
    rcases hdiag0 with ⟨_hscalar0, hric⟩
    exact ⟨hscalar, hric⟩
  exact normSq0S_four_at_le (I := I) htrace_basis hdiag h1 h2 h3


omit [FiniteDimensional ℝ E] in
private theorem ricciDiagAt_neg
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (hdiag : RicciDiagAt (I := I) Ric scalar l1 l2 l3 basis) :
    RicciDiagAt (I := I) (-Ric) (ricciEigenScalar3 (-l1) (-l2) (-l3))
      (-l1) (-l2) (-l3) basis := by
  rcases hdiag with ⟨_, hric⟩
  constructor
  · rfl
  · intro i j
    have hij := hric i j
    change -(ricciCompAt (I := I) basis Ric i j) =
      ricciDiag3 (-l1) (-l2) (-l3) i j
    rw [hij]
    fin_cases i <;> fin_cases j <;> simp [ricciDiag3]

omit [FiniteDimensional ℝ E] in
private theorem scalar_eq_of_signed_trace_diag
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (htrace : RiemannFromRicci3DTraceDataAt g (-Ric) (-scalar) Rm04 basis)
    (hdiag : RicciDiagAt (I := I) Ric (ricciEigenScalar3 l1 l2 l3)
      l1 l2 l3 basis) :
    scalar = ricciEigenScalar3 l1 l2 l3 := by
  have hnegdiag := ricciDiagAt_neg (I := I) hdiag
  have hneg :
      -scalar = ricciEigenScalar3 (-l1) (-l2) (-l3) :=
    scalar_eq_of_trace_diag (I := I) htrace hnegdiag
  unfold ricciEigenScalar3 at hneg ⊢
  linarith

private theorem rmSecNormSq3_neg
    (l1 l2 l3 : Real) :
    rmSecNormSq3 (sec12Ric3 (-l1) (-l2) (-l3))
        (sec13Ric3 (-l1) (-l2) (-l3))
        (sec23Ric3 (-l1) (-l2) (-l3)) =
      rmSecNormSq3 (sec12Ric3 l1 l2 l3)
        (sec13Ric3 l1 l2 l3) (sec23Ric3 l1 l2 l3) := by
  unfold rmSecNormSq3 sec12Ric3 sec13Ric3 sec23Ric3
  ring






theorem normSqLeOfFirstTrace
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hsymm : RicciSymAt (I := I) Ric)
    (hnonneg : RicciNonnegAt (I := I) Ric)
    (htrace : forall basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      OrthonormalBasisAt (I := I) g x basis ->
        RiemannFromRicci3DTraceDataAt g (-Ric) (-scalar) Rm04 basis) :
    normSq0S (I := I) g x 4 Rm04 <= 100 ^ 2 * scalar ^ 2 := by
  rcases ricciEigenBasis3 (I := I) g Ric hdim hsymm hnonneg with
    ⟨basis, l1, l2, l3, horth, hdiag0, h1, h2, h3⟩
  have htrace_basis := htrace basis horth
  have hscalar :
      scalar = ricciEigenScalar3 l1 l2 l3 :=
    scalar_eq_of_signed_trace_diag (I := I) htrace_basis hdiag0
  have hnegdiag0 := ricciDiagAt_neg (I := I) hdiag0
  have hnegdiag :
      RicciDiagAt (I := I) (-Ric) (-scalar) (-l1) (-l2) (-l3) basis := by
    rcases hnegdiag0 with ⟨_, hric⟩
    have hnegscalar :
        -scalar = ricciEigenScalar3 (-l1) (-l2) (-l3) := by
      unfold ricciEigenScalar3 at hscalar ⊢
      linarith
    exact ⟨hnegscalar, hric⟩
  rw [normSq0S_four_eq_stdRmNormSq3 (I := I) htrace_basis.orthonormal]
  have hnorm := stdRmNormSq3_at (I := I) htrace_basis hnegdiag
  rw [hnorm, rmSecNormSq3_neg, hscalar]
  exact rmSqLe100ScalSq3 l1 l2 l3 h1 h2 h3







theorem normSqLeOfFirstData
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hsymm : RicciSymAt (I := I) Ric)
    (hnonneg : RicciNonnegAt (I := I) Ric)
    (hcurv : forall basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      OrthonormalBasisAt (I := I) g x basis ->
        AlgebraicCurvatureSymmetries3 (standardRmCompAt (I := I) basis Rm04))
    (hRic : forall basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      OrthonormalBasisAt (I := I) g x basis ->
        RicciRealizesRm04FirstTraceAt (I := I) Ric Rm04 delta3 basis)
    (hScalar : forall basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      OrthonormalBasisAt (I := I) g x basis ->
        ScalarRealizesRicciTraceAt (I := I) scalar Ric delta3 basis) :
    normSq0S (I := I) g x 4 Rm04 <= 100 ^ 2 * scalar ^ 2 := by
  refine normSqLeOfFirstTrace (I := I) (M := M) hdim hsymm hnonneg ?_
  intro basis horth
  exact traceDataOfFirst (I := I) horth (hcurv basis horth)
    (hRic basis horth) (hScalar basis horth)

end DifferentialGeometry.Integral.Connection
