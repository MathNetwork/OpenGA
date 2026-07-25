import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Coordinate
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetric

set_option autoImplicit false
set_option linter.style.longLine false









namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



theorem inner0S_product_one_two
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric_gen I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (α β : Tensor0SSpace 1 I x)
    (A B : Tensor0SSpace 2 I x) :
    inner0S (I := I) g x 3
        (Bundle.continuousMultilinearMap.product_fun
          (𝕜 := Real) (F := E) (E := TangentSpace I) (s := 1) (q := 2) α A)
        (Bundle.continuousMultilinearMap.product_fun
          (𝕜 := Real) (F := E) (E := TangentSpace I) (s := 1) (q := 2) β B) =
      inner0S (I := I) g x 1 α β *
        inner0S (I := I) g x 2 A B := by
  classical
  rw [inner0S_eq_coord (I := I) g x 3 basis gInv hinv,
    inner0S_eq_coord (I := I) g x 1 basis gInv hinv,
    inner0S_eq_coord (I := I) g x 2 basis gInv hinv]
  rw [coordInner0S_succ_eq (I := I) 2 gInv
    (Bundle.continuousMultilinearMap.product_fun
      (𝕜 := Real) (F := E) (E := TangentSpace I) (s := 1) (q := 2) α A)
    (Bundle.continuousMultilinearMap.product_fun
      (𝕜 := Real) (F := E) (E := TangentSpace I) (s := 1) (q := 2) β B) basis]
  simp_rw [tensor0S_curry_product_one_two (I := I)]
  simp_rw [coordInner0S_smul_smul (I := I) 2 gInv A B basis]
  rw [coordInner0S_one_eq (I := I) gInv α β basis]
  simp only [cotangentToDual_apply_gen]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring



theorem inner0S_three_product_right
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric_gen I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (N : Tensor0SSpace 3 I x)
    (α : Tensor0SSpace 1 I x)
    (A : Tensor0SSpace 2 I x) :
    inner0S (I := I) g x 3 N
        (Bundle.continuousMultilinearMap.product_fun
          (𝕜 := Real) (F := E) (E := TangentSpace I) (s := 1) (q := 2) α A) =
      inner0S (I := I) g x 2
        ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x N)
          (cotangentSharp_gen (I := I) g x α))
        A := by
  classical
  rw [inner0S_eq_coord (I := I) g x 3 basis gInv hinv,
    inner0S_eq_coord (I := I) g x 2 basis gInv hinv]
  rw [coordInner0S_succ_eq (I := I) 2 gInv N
    (Bundle.continuousMultilinearMap.product_fun
      (𝕜 := Real) (F := E) (E := TangentSpace I) (s := 1) (q := 2) α A) basis]
  simp_rw [tensor0S_curry_product_one_two (I := I)]
  simp_rw [coordInner0S_smul_right (I := I) 2 gInv _ A basis]
  rw [cotangentSharp_eq_sum_inv_gen (I := I) g x basis gInv hinv α]
  simp_rw [cotangentToDual_apply_gen]
  rw [map_sum]
  simp_rw [map_smul]
  rw [coordInner0S_sum_left (I := I) 2 gInv
    (fun i : Idx =>
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x N) (basis i)))
    A basis
    (fun i : Idx =>
      ∑ j : Idx, gInv i j * α (fun _ : Fin 1 => basis j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring


theorem normSq0S_smul_sub_product_one_two
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric_gen I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (r : Real)
    (N : Tensor0SSpace 3 I x)
    (α : Tensor0SSpace 1 I x)
    (A : Tensor0SSpace 2 I x) :
    normSq0S (I := I) g x 3
        (r • N -
          (show Tensor0SSpace 3 I x from
            Bundle.continuousMultilinearMap.product_fun
              (𝕜 := Real) (F := E) (E := TangentSpace I)
              (s := 1) (q := 2) α A)) =
      r ^ 2 * normSq0S (I := I) g x 3 N -
        2 * r * inner0S (I := I) g x 3 N
          (Bundle.continuousMultilinearMap.product_fun
            (𝕜 := Real) (F := E) (E := TangentSpace I) (s := 1) (q := 2) α A) +
        inner0S (I := I) g x 1 α α *
          normSq0S (I := I) g x 2 A := by
  classical
  let P : Tensor0SSpace 3 I x :=
    Bundle.continuousMultilinearMap.product_fun
      (𝕜 := Real) (F := E) (E := TangentSpace I) (s := 1) (q := 2) α A
  have hprod :
      inner0S (I := I) g x 3 P P =
        inner0S (I := I) g x 1 α α *
          inner0S (I := I) g x 2 A A := by
    simpa [P] using
      inner0S_product_one_two (I := I) g x basis gInv hinv α α A A
  have hsymm :
      inner0S (I := I) g x 3 P N =
        inner0S (I := I) g x 3 N P := by
    simpa [inner0S] using
      (MetricFiberData.inner_comm
        (tensor0SMetricData (I := I) g x 3) P N)
  unfold normSq0S
  change inner0S (I := I) g x 3 (r • N - P) (r • N - P) =
      r ^ 2 * inner0S (I := I) g x 3 N N -
        2 * r * inner0S (I := I) g x 3 N P +
        inner0S (I := I) g x 1 α α *
          inner0S (I := I) g x 2 A A
  rw [← hprod]
  have hsymmFlat :
      ((tensor0SMetricData (I := I) g x 3).flat P) N =
        ((tensor0SMetricData (I := I) g x 3).flat N) P := by
    simpa [inner0S, MetricFiberData.inner] using hsymm
  change
    ((tensor0SMetricData (I := I) g x 3).flat (r • N - P)) (r • N - P) =
      r ^ 2 * ((tensor0SMetricData (I := I) g x 3).flat N) N -
        2 * r * ((tensor0SMetricData (I := I) g x 3).flat N) P +
        ((tensor0SMetricData (I := I) g x 3).flat P) P
  have hflatSub :
      ((tensor0SMetricData (I := I) g x 3).flat (r • N - P)) (r • N - P) =
        (((tensor0SMetricData (I := I) g x 3).flat (r • N)) -
          ((tensor0SMetricData (I := I) g x 3).flat P)) (r • N - P) := by
    exact congrArg (fun L : Module.Dual Real (Tensor0SSpace 3 I x) =>
      L (r • N - P))
      ((tensor0SMetricData (I := I) g x 3).flat.map_sub (r • N) P)
  rw [hflatSub]
  rw [((tensor0SMetricData (I := I) g x 3).flat.map_smul r N)]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  have hNapp :
      ((tensor0SMetricData (I := I) g x 3).flat N) (r • N - P) =
        r * ((tensor0SMetricData (I := I) g x 3).flat N) N -
          ((tensor0SMetricData (I := I) g x 3).flat N) P := by
    calc
      ((tensor0SMetricData (I := I) g x 3).flat N) (r • N - P)
          = ((tensor0SMetricData (I := I) g x 3).flat N) (r • N) -
              ((tensor0SMetricData (I := I) g x 3).flat N) P := by
            exact ((tensor0SMetricData (I := I) g x 3).flat N).map_sub (r • N) P
      _ = r * ((tensor0SMetricData (I := I) g x 3).flat N) N -
            ((tensor0SMetricData (I := I) g x 3).flat N) P := by
            rw [((tensor0SMetricData (I := I) g x 3).flat N).map_smul r N]
            rfl
  have hPapp :
      ((tensor0SMetricData (I := I) g x 3).flat P) (r • N - P) =
        r * ((tensor0SMetricData (I := I) g x 3).flat P) N -
          ((tensor0SMetricData (I := I) g x 3).flat P) P := by
    calc
      ((tensor0SMetricData (I := I) g x 3).flat P) (r • N - P)
          = ((tensor0SMetricData (I := I) g x 3).flat P) (r • N) -
              ((tensor0SMetricData (I := I) g x 3).flat P) P := by
            exact ((tensor0SMetricData (I := I) g x 3).flat P).map_sub (r • N) P
      _ = r * ((tensor0SMetricData (I := I) g x 3).flat P) N -
            ((tensor0SMetricData (I := I) g x 3).flat P) P := by
            rw [((tensor0SMetricData (I := I) g x 3).flat P).map_smul r N]
            rfl
  rw [hNapp, hPapp, hsymmFlat]
  simp only [smul_eq_mul]
  ring_nf

theorem sum5_swap_first_last
    {Idx : Type*} [Fintype Idx]
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j k l a) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F a j k l i) := by
  classical
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [show
      (∑ x : ((((Idx × Idx) × Idx) × Idx) × Idx),
        F x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.1.2 x.2) =
      (∑ x : ((((Idx × Idx) × Idx) × Idx) × Idx),
        F x.2 x.1.1.1.2 x.1.1.2 x.1.2 x.1.1.1.1) by
        let e : ((((Idx × Idx) × Idx) × Idx) × Idx) ≃
            ((((Idx × Idx) × Idx) × Idx) × Idx) :=
          { toFun := fun p => ((((p.2, p.1.1.1.2), p.1.1.2), p.1.2), p.1.1.1.1)
            invFun := fun p => ((((p.2, p.1.1.1.2), p.1.1.2), p.1.2), p.1.1.1.1)
            left_inv := by
              intro p
              rcases p with ⟨⟨⟨⟨i, j⟩, k⟩, l⟩, a⟩
              rfl
            right_inv := by
              intro p
              rcases p with ⟨⟨⟨⟨i, j⟩, k⟩, l⟩, a⟩
              rfl }
        simpa [e] using
          (Fintype.sum_equiv e
            (fun p => F p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
            (fun p => F p.2 p.1.1.1.2 p.1.1.2 p.1.2 p.1.1.1.1)
            (by intro p; rfl))]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]

theorem sum5_swap_second_last
    {Idx : Type*} [Fintype Idx]
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j k l a) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i a k l j) := by
  classical
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [show
      (∑ x : ((((Idx × Idx) × Idx) × Idx) × Idx),
        F x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.1.2 x.2) =
      (∑ x : ((((Idx × Idx) × Idx) × Idx) × Idx),
        F x.1.1.1.1 x.2 x.1.1.2 x.1.2 x.1.1.1.2) by
        let e : ((((Idx × Idx) × Idx) × Idx) × Idx) ≃
            ((((Idx × Idx) × Idx) × Idx) × Idx) :=
          { toFun := fun p => ((((p.1.1.1.1, p.2), p.1.1.2), p.1.2), p.1.1.1.2)
            invFun := fun p => ((((p.1.1.1.1, p.2), p.1.1.2), p.1.2), p.1.1.1.2)
            left_inv := by
              intro p
              rcases p with ⟨⟨⟨⟨i, j⟩, k⟩, l⟩, a⟩
              rfl
            right_inv := by
              intro p
              rcases p with ⟨⟨⟨⟨i, j⟩, k⟩, l⟩, a⟩
              rfl }
        simpa [e] using
          (Fintype.sum_equiv e
            (fun p => F p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
            (fun p => F p.1.1.1.1 p.2 p.1.1.2 p.1.2 p.1.1.1.2)
            (by intro p; rfl))]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]

theorem sum5_swap_third_last
    {Idx : Type*} [Fintype Idx]
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j k l a) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j a l k) := by
  classical
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [show
      (∑ x : ((((Idx × Idx) × Idx) × Idx) × Idx),
        F x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.1.2 x.2) =
      (∑ x : ((((Idx × Idx) × Idx) × Idx) × Idx),
        F x.1.1.1.1 x.1.1.1.2 x.2 x.1.2 x.1.1.2) by
        let e : ((((Idx × Idx) × Idx) × Idx) × Idx) ≃
            ((((Idx × Idx) × Idx) × Idx) × Idx) :=
          { toFun := fun p => ((((p.1.1.1.1, p.1.1.1.2), p.2), p.1.2), p.1.1.2)
            invFun := fun p => ((((p.1.1.1.1, p.1.1.1.2), p.2), p.1.2), p.1.1.2)
            left_inv := by
              intro p
              rcases p with ⟨⟨⟨⟨i, j⟩, k⟩, l⟩, a⟩
              rfl
            right_inv := by
              intro p
              rcases p with ⟨⟨⟨⟨i, j⟩, k⟩, l⟩, a⟩
              rfl }
        simpa [e] using
          (Fintype.sum_equiv e
            (fun p => F p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
            (fun p => F p.1.1.1.1 p.1.1.1.2 p.2 p.1.2 p.1.1.2)
            (by intro p; rfl))]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]

theorem sum5_swap_fourth_last
    {Idx : Type*} [Fintype Idx]
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j k l a) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j k a l) := by
  classical
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [show
      (∑ x : ((((Idx × Idx) × Idx) × Idx) × Idx),
        F x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.1.2 x.2) =
      (∑ x : ((((Idx × Idx) × Idx) × Idx) × Idx),
        F x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.2 x.1.2) by
        let e : ((((Idx × Idx) × Idx) × Idx) × Idx) ≃
            ((((Idx × Idx) × Idx) × Idx) × Idx) :=
          { toFun := fun p => ((((p.1.1.1.1, p.1.1.1.2), p.1.1.2), p.2), p.1.2)
            invFun := fun p => ((((p.1.1.1.1, p.1.1.1.2), p.1.1.2), p.2), p.1.2)
            left_inv := by
              intro p
              rcases p with ⟨⟨⟨⟨i, j⟩, k⟩, l⟩, a⟩
              rfl
            right_inv := by
              intro p
              rcases p with ⟨⟨⟨⟨i, j⟩, k⟩, l⟩, a⟩
              rfl }
        simpa [e] using
          (Fintype.sum_equiv e
            (fun p => F p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
            (fun p => F p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.2 p.1.2)
            (by intro p; rfl))]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]

theorem inner0S_two_metricCompatible_coord_corrA1
    {Idx : Type*} [Fintype Idx]
    (U Γ A B : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l)) =
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      (∑ a : Idx, Γ a i * U a k) * U j l * A i j * B k l) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l))
        = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx,
            U i k * U j l * ((Γ i a * A a j) * B k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul]
          rw [Finset.mul_sum]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx,
            U a k * U j l * ((Γ a i * A i j) * B k l) := by
          simpa using sum5_swap_first_last (fun i j k l a : Idx =>
            U i k * U j l * ((Γ i a * A a j) * B k l))
    _ = (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      (∑ a : Idx, Γ a i * U a k) * U j l * A i j * B k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          calc
            (∑ a : Idx, U a k * U j l * (Γ a i * A i j * B k l))
                = (∑ a : Idx, Γ a i * U a k) * (U j l * A i j * B k l) := by
                  rw [Finset.sum_mul]
                  refine Finset.sum_congr rfl fun a _ => ?_
                  ring
            _ = (∑ a : Idx, Γ a i * U a k) * U j l * A i j * B k l := by
                  ring

theorem inner0S_two_metricCompatible_coord_corrA2
    {Idx : Type*} [Fintype Idx]
    (U Γ A B : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l)) =
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * (∑ a : Idx, Γ a j * U a l) * A i j * B k l) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l))
        = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx,
            U i k * U j l * ((Γ j a * A i a) * B k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul]
          rw [Finset.mul_sum]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx,
            U i k * U a l * ((Γ a j * A i j) * B k l) := by
          simpa using sum5_swap_second_last (fun i j k l a : Idx =>
            U i k * U j l * ((Γ j a * A i a) * B k l))
    _ = (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * (∑ a : Idx, Γ a j * U a l) * A i j * B k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          calc
            (∑ a : Idx, U i k * U a l * (Γ a j * A i j * B k l))
                = U i k * (∑ a : Idx, Γ a j * U a l * (A i j * B k l)) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun a _ => ?_
                  ring
            _ = U i k * ((∑ a : Idx, Γ a j * U a l) * (A i j * B k l)) := by
                  rw [Finset.sum_mul]
            _ = U i k * (∑ a : Idx, Γ a j * U a l) * (A i j * B k l) := by
                  ring
            _ = U i k * (∑ a : Idx, Γ a j * U a l) * A i j * B k l := by
                  ring

theorem inner0S_two_metricCompatible_coord_corrB1
    {Idx : Type*} [Fintype Idx]
    (U Γ A B : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l))) =
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      (∑ a : Idx, Γ a k * U i a) * U j l * A i j * B k l) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l)))
        = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx,
            U i k * U j l * (A i j * (Γ k a * B a l)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← Finset.mul_sum]
          rw [Finset.mul_sum]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx,
            U i a * U j l * (A i j * (Γ a k * B k l)) := by
          simpa using sum5_swap_third_last (fun i j k l a : Idx =>
            U i k * U j l * (A i j * (Γ k a * B a l)))
    _ = (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      (∑ a : Idx, Γ a k * U i a) * U j l * A i j * B k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          calc
            (∑ a : Idx, U i a * U j l * (A i j * (Γ a k * B k l)))
                = (∑ a : Idx, Γ a k * U i a) * (U j l * A i j * B k l) := by
                  rw [Finset.sum_mul]
                  refine Finset.sum_congr rfl fun a _ => ?_
                  ring
            _ = (∑ a : Idx, Γ a k * U i a) * U j l * A i j * B k l := by
                  ring

theorem inner0S_two_metricCompatible_coord_corrB2
    {Idx : Type*} [Fintype Idx]
    (U Γ A B : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a))) =
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * (∑ a : Idx, Γ a l * U j a) * A i j * B k l) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a)))
        = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx,
            U i k * U j l * (A i j * (Γ l a * B k a)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← Finset.mul_sum]
          rw [Finset.mul_sum]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx,
            U i k * U j a * (A i j * (Γ a l * B k l)) := by
          simpa using sum5_swap_fourth_last (fun i j k l a : Idx =>
            U i k * U j l * (A i j * (Γ l a * B k a)))
    _ = (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * (∑ a : Idx, Γ a l * U j a) * A i j * B k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          calc
            (∑ a : Idx, U i k * U j a * (A i j * (Γ a l * B k l)))
                = U i k * (∑ a : Idx, Γ a l * U j a * (A i j * B k l)) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun a _ => ?_
                  ring
            _ = U i k * ((∑ a : Idx, Γ a l * U j a) * (A i j * B k l)) := by
                  rw [Finset.sum_mul]
            _ = U i k * (∑ a : Idx, Γ a l * U j a) * (A i j * B k l) := by
                  ring
            _ = U i k * (∑ a : Idx, Γ a l * U j a) * A i j * B k l := by
                  ring

theorem inner0S_two_metricCompatible_coord_DU_first
    {Idx : Type*} [Fintype Idx]
    (U Γ A B DU : Idx -> Idx -> Real)
    (hDU : ∀ p q : Idx,
      DU p q =
        - ((∑ a : Idx, Γ a p * U a q) + (∑ a : Idx, Γ a q * U p a))) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      DU i k * U j l * A i j * B k l) =
      - (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l)) -
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l))) := by
  classical
  have hA1 := inner0S_two_metricCompatible_coord_corrA1 (U := U) (Γ := Γ) (A := A) (B := B)
  have hB1 := inner0S_two_metricCompatible_coord_corrB1 (U := U) (Γ := Γ) (A := A) (B := B)
  rw [hA1, hB1]
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      DU i k * U j l * A i j * B k l)
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (-(∑ a : Idx, Γ a i * U a k) * U j l * A i j * B k l -
          (∑ a : Idx, Γ a k * U i a) * U j l * A i j * B k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hDU i k]
          ring
    _ =
      - (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (∑ a : Idx, Γ a i * U a k) * U j l * A i j * B k l) -
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (∑ a : Idx, Γ a k * U i a) * U j l * A i j * B k l) := by
          simp [Finset.sum_sub_distrib, Finset.sum_neg_distrib]

theorem inner0S_two_metricCompatible_coord_DU_second
    {Idx : Type*} [Fintype Idx]
    (U Γ A B DU : Idx -> Idx -> Real)
    (hDU : ∀ p q : Idx,
      DU p q =
        - ((∑ a : Idx, Γ a p * U a q) + (∑ a : Idx, Γ a q * U p a))) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * DU j l * A i j * B k l) =
      - (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l)) -
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a))) := by
  classical
  have hA2 := inner0S_two_metricCompatible_coord_corrA2 (U := U) (Γ := Γ) (A := A) (B := B)
  have hB2 := inner0S_two_metricCompatible_coord_corrB2 (U := U) (Γ := Γ) (A := A) (B := B)
  rw [hA2, hB2]
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * DU j l * A i j * B k l)
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (-(U i k * (∑ a : Idx, Γ a j * U a l) * A i j * B k l) -
          U i k * (∑ a : Idx, Γ a l * U j a) * A i j * B k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hDU j l]
          ring
    _ =
      - (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * (∑ a : Idx, Γ a j * U a l) * A i j * B k l) -
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * (∑ a : Idx, Γ a l * U j a) * A i j * B k l) := by
          simp [Finset.sum_sub_distrib, Finset.sum_neg_distrib]

theorem inner0S_two_metricCompatible_coord_NA_sum
    {Idx : Type*} [Fintype Idx]
    (U Γ A B DA NA : Idx -> Idx -> Real)
    (hNA : ∀ p q : Idx,
      NA p q =
        DA p q - (∑ a : Idx, Γ p a * A a q) -
          (∑ a : Idx, Γ q a * A p a)) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (NA i j * B k l)) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (DA i j * B k l)) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l)) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l)) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (NA i j * B k l))
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (U i k * U j l * (DA i j * B k l) -
          U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l) -
          U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hNA i j]
          ring
    _ =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (DA i j * B k l)) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l)) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l)) := by
          simp [Finset.sum_sub_distrib]

theorem inner0S_two_metricCompatible_coord_NB_sum
    {Idx : Type*} [Fintype Idx]
    (U Γ A B DB NB : Idx -> Idx -> Real)
    (hNB : ∀ p q : Idx,
      NB p q =
        DB p q - (∑ a : Idx, Γ p a * B a q) -
          (∑ a : Idx, Γ q a * B p a)) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * NB k l)) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * DB k l)) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l))) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a))) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * NB k l))
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (U i k * U j l * (A i j * DB k l) -
          U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l)) -
          U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hNB k l]
          ring
    _ =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * DB k l)) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l))) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a))) := by
          simp [Finset.sum_sub_distrib]

theorem inner0S_two_metricCompatible_scalar_sum_algebra
    (P Q A1 A2 B1 B2 : Real) :
    (-A1 - B1) + (-A2 - B2) + P + Q =
      (P - A1 - A2) + (Q - B1 - B2) := by
  ring

theorem inner0S_two_metricCompatible_coord_algebra
    {Idx : Type*} [Fintype Idx]
    (U Γ A B DA DB NA NB DU : Idx -> Idx -> Real)
    (hDU : ∀ p q : Idx,
      DU p q =
        - ((∑ a : Idx, Γ a p * U a q) + (∑ a : Idx, Γ a q * U p a)))
    (hNA : ∀ p q : Idx,
      NA p q =
        DA p q - (∑ a : Idx, Γ p a * A a q) -
          (∑ a : Idx, Γ q a * A p a))
    (hNB : ∀ p q : Idx,
      NB p q =
        DB p q - (∑ a : Idx, Γ p a * B a q) -
          (∑ a : Idx, Γ q a * B p a)) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      ((DU i k * U j l + U i k * DU j l) * A i j * B k l +
        U i k * U j l * (DA i j * B k l + A i j * DB k l))) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (NA i j * B k l + A i j * NB k l)) := by
  classical
  let P : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (DA i j * B k l)
  let Q : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * DB k l)
  let A1 : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l)
  let A2 : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l)
  let B1 : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l))
  let B2 : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a))
  have hDU1 :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        DU i k * U j l * A i j * B k l) = -A1 - B1 := by
    simpa [A1, B1] using
      inner0S_two_metricCompatible_coord_DU_first
        (U := U) (Γ := Γ) (A := A) (B := B) (DU := DU) hDU
  have hDU2 :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * DU j l * A i j * B k l) = -A2 - B2 := by
    simpa [A2, B2] using
      inner0S_two_metricCompatible_coord_DU_second
        (U := U) (Γ := Γ) (A := A) (B := B) (DU := DU) hDU
  have hNA_sum :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (NA i j * B k l)) = P - A1 - A2 := by
    simpa [P, A1, A2] using
      inner0S_two_metricCompatible_coord_NA_sum
        (U := U) (Γ := Γ) (A := A) (B := B) (DA := DA) (NA := NA) hNA
  have hNB_sum :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * NB k l)) = Q - B1 - B2 := by
    simpa [Q, B1, B2] using
      inner0S_two_metricCompatible_coord_NB_sum
        (U := U) (Γ := Γ) (A := A) (B := B) (DB := DB) (NB := NB) hNB
  have hleft :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        ((DU i k * U j l + U i k * DU j l) * A i j * B k l +
          U i k * U j l * (DA i j * B k l + A i j * DB k l))) =
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          DU i k * U j l * A i j * B k l) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * DU j l * A i j * B k l) + P + Q := by
    calc
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        ((DU i k * U j l + U i k * DU j l) * A i j * B k l +
          U i k * U j l * (DA i j * B k l + A i j * DB k l)))
          =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (DU i k * U j l * A i j * B k l +
            U i k * DU j l * A i j * B k l +
            U i k * U j l * (DA i j * B k l) +
            U i k * U j l * (A i j * DB k l)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
      _ =
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          DU i k * U j l * A i j * B k l) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * DU j l * A i j * B k l) + P + Q := by
            simp [P, Q, Finset.sum_add_distrib, add_assoc]
  have hright :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (NA i j * B k l + A i j * NB k l)) =
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (NA i j * B k l)) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (A i j * NB k l)) := by
    calc
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (NA i j * B k l + A i j * NB k l))
          =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (U i k * U j l * (NA i j * B k l) +
            U i k * U j l * (A i j * NB k l)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
      _ =
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (NA i j * B k l)) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (A i j * NB k l)) := by
            simp [Finset.sum_add_distrib]
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      ((DU i k * U j l + U i k * DU j l) * A i j * B k l +
        U i k * U j l * (DA i j * B k l + A i j * DB k l)))
        =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          DU i k * U j l * A i j * B k l) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * DU j l * A i j * B k l) + P + Q := hleft
    _ = (-A1 - B1) + (-A2 - B2) + P + Q := by
          rw [hDU1, hDU2]
    _ = (P - A1 - A2) + (Q - B1 - B2) := by
          exact inner0S_two_metricCompatible_scalar_sum_algebra P Q A1 A2 B1 B2
    _ =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (NA i j * B k l)) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (A i j * NB k l)) := by
          rw [hNA_sum, hNB_sum]
    _ =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (NA i j * B k l + A i j * NB k l)) := hright.symm

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem deriv4sum
    {Idx : Type*} [Fintype Idx]
    (U A B : M -> Idx -> Idx -> Real)
    {x : M} (v : TangentSpace I x)
    (hU : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => U y i j) x)
    (hA : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => A y i j) x)
    (hB : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => B y i j) x) :
    extDerivFun (I := I)
        (fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U y i k * U y j l * A y i j * B y k l) x v =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (((extDerivFun (I := I) (fun y : M => U y i k) x v) * U x j l +
            U x i k * (extDerivFun (I := I) (fun y : M => U y j l) x v)) *
            A x i j * B x k l +
          U x i k * U x j l *
            ((extDerivFun (I := I) (fun y : M => A y i j) x v) * B x k l +
              A x i j * (extDerivFun (I := I) (fun y : M => B y k l) x v))) := by
  classical
  let F : Idx -> Idx -> Idx -> Idx -> M -> Real :=
    fun i j k l y => U y i k * U y j l * A y i j * B y k l
  have hterm (i j k l : Idx) :
      extDerivFun (I := I) (F i j k l) x v =
        ((extDerivFun (I := I) (fun y : M => U y i k) x v) * U x j l +
            U x i k * (extDerivFun (I := I) (fun y : M => U y j l) x v)) *
            A x i j * B x k l +
          U x i k * U x j l *
            ((extDerivFun (I := I) (fun y : M => A y i j) x v) * B x k l +
              A x i j * (extDerivFun (I := I) (fun y : M => B y k l) x v)) := by
    have hUU := DifferentialGeometry.Tensor.Coordinates.extDerivFun_mul_real
      (I := I) (x := x) v (hU i k) (hU j l)
    have hAB := DifferentialGeometry.Tensor.Coordinates.extDerivFun_mul_real
      (I := I) (x := x) v (hA i j) (hB k l)
    have hAll := DifferentialGeometry.Tensor.Coordinates.extDerivFun_mul_real
      (I := I) (x := x) v ((hU i k).mul (hU j l)) ((hA i j).mul (hB k l))
    calc
      extDerivFun (I := I) (F i j k l) x v =
          (U x i k * U x j l) *
              extDerivFun (I := I) (fun y : M => A y i j * B y k l) x v +
            extDerivFun (I := I) (fun y : M => U y i k * U y j l) x v *
              (A x i j * B x k l) := by
            simpa [F, mul_assoc] using hAll
      _ =
          ((extDerivFun (I := I) (fun y : M => U y i k) x v) * U x j l +
              U x i k * (extDerivFun (I := I) (fun y : M => U y j l) x v)) *
              A x i j * B x k l +
            U x i k * U x j l *
              ((extDerivFun (I := I) (fun y : M => A y i j) x v) * B x k l +
                A x i j * (extDerivFun (I := I) (fun y : M => B y k l) x v)) := by
            rw [hUU, hAB]
            ring
  have hmdiff_l (i j k l : Idx) :
      MDifferentiableAt I 𝓘(Real, Real) (F i j k l) x :=
    (((hU i k).mul (hU j l)).mul (hA i j)).mul (hB k l)
  let F3 : Idx -> Idx -> Idx -> M -> Real :=
    fun i j k => (Finset.univ : Finset Idx).sum (fun l : Idx => F i j k l)
  let F2 : Idx -> Idx -> M -> Real :=
    fun i j => (Finset.univ : Finset Idx).sum (fun k : Idx => F3 i j k)
  let F1 : Idx -> M -> Real :=
    fun i => (Finset.univ : Finset Idx).sum (fun j : Idx => F2 i j)
  let F0 : M -> Real :=
    (Finset.univ : Finset Idx).sum (fun i : Idx => F1 i)
  have hF3_mdiff (i j k : Idx) :
      MDifferentiableAt I 𝓘(Real, Real) (F3 i j k) x := by
    dsimp [F3]
    exact
      DifferentialGeometry.Tensor.Coordinates.mdiffAt_finset_sum_real
      (I := I) (x := x) (t := (Finset.univ : Finset Idx))
      (fun l : Idx => fun y : M => F i j k l y)
      (by
        intro l _hl
        exact hmdiff_l i j k l)
  have hF2_mdiff (i j : Idx) :
      MDifferentiableAt I 𝓘(Real, Real) (F2 i j) x := by
    dsimp [F2]
    exact
      DifferentialGeometry.Tensor.Coordinates.mdiffAt_finset_sum_real
      (I := I) (x := x) (t := (Finset.univ : Finset Idx))
      (fun k : Idx => F3 i j k)
      (by
        intro k _hk
        exact hF3_mdiff i j k)
  have hF1_mdiff (i : Idx) :
      MDifferentiableAt I 𝓘(Real, Real) (F1 i) x := by
    dsimp [F1]
    exact
      DifferentialGeometry.Tensor.Coordinates.mdiffAt_finset_sum_real
      (I := I) (x := x) (t := (Finset.univ : Finset Idx))
      (fun j : Idx => F2 i j)
      (by
        intro j _hj
        exact hF2_mdiff i j)
  have hF0_mdiff :
      MDifferentiableAt I 𝓘(Real, Real) F0 x := by
    dsimp [F0]
    exact
      DifferentialGeometry.Tensor.Coordinates.mdiffAt_finset_sum_real
      (I := I) (x := x) (t := (Finset.univ : Finset Idx))
      (fun i : Idx => F1 i)
      (by
        intro i _hi
        exact hF1_mdiff i)
  have hF3_deriv (i j k : Idx) :
      extDerivFun (I := I) (F3 i j k) x v =
        ∑ l : Idx, extDerivFun (I := I) (F i j k l) x v := by
    dsimp [F3]
    exact
      DifferentialGeometry.Tensor.Coordinates.extDerivFun_finset_sum_real
      (I := I) (t := (Finset.univ : Finset Idx))
      (fun l : Idx => F i j k l) v
      (by
        intro l _hl
        exact hmdiff_l i j k l)
  have hF2_deriv (i j : Idx) :
      extDerivFun (I := I) (F2 i j) x v =
        ∑ k : Idx, ∑ l : Idx,
          extDerivFun (I := I) (F i j k l) x v := by
    have h := DifferentialGeometry.Tensor.Coordinates.extDerivFun_finset_sum_real
      (I := I) (t := (Finset.univ : Finset Idx))
      (fun k : Idx => F3 i j k) v
      (by
        intro k _hk
        exact hF3_mdiff i j k)
    simpa [F2, Finset.sum_apply, hF3_deriv] using h
  have hF1_deriv (i : Idx) :
      extDerivFun (I := I) (F1 i) x v =
        ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          extDerivFun (I := I) (F i j k l) x v := by
    have h := DifferentialGeometry.Tensor.Coordinates.extDerivFun_finset_sum_real
      (I := I) (t := (Finset.univ : Finset Idx))
      (fun j : Idx => F2 i j) v
      (by
        intro j _hj
        exact hF2_mdiff i j)
    simpa [F1, Finset.sum_apply, hF2_deriv] using h
  have hF0_deriv :
      extDerivFun (I := I) F0 x v =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          extDerivFun (I := I) (F i j k l) x v := by
    have h := DifferentialGeometry.Tensor.Coordinates.extDerivFun_finset_sum_real
      (I := I) (t := (Finset.univ : Finset Idx))
      (fun i : Idx => F1 i) v
      (by
        intro i _hi
        exact hF1_mdiff i)
    simpa [F0, Finset.sum_apply, hF1_deriv] using h
  have hF0_eq :
      (fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U y i k * U y j l * A y i j * B y k l) = F0 := by
    funext y
    simp [F0, F1, F2, F3, F]
  calc
    extDerivFun (I := I)
        (fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U y i k * U y j l * A y i j * B y k l) x v =
      extDerivFun (I := I) F0 x v := by
        rw [hF0_eq]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          extDerivFun (I := I) (F i j k l) x v := hF0_deriv
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (((extDerivFun (I := I) (fun y : M => U y i k) x v) * U x j l +
            U x i k * (extDerivFun (I := I) (fun y : M => U y j l) x v)) *
            A x i j * B x k l +
          U x i k * U x j l *
            ((extDerivFun (I := I) (fun y : M => A y i j) x v) * B x k l +
              A x i j * (extDerivFun (I := I) (fun y : M => B y k l) x v))) := by
        refine Finset.sum_congr rfl fun i _hi => ?_
        refine Finset.sum_congr rfl fun j _hj => ?_
        refine Finset.sum_congr rfl fun k _hk => ?_
        refine Finset.sum_congr rfl fun l _hl => ?_
        exact hterm i j k l

@[simp] theorem fin2_apply_ite {α β : Type*} (f : α -> β) (i j : α) :
    (fun q : Fin 2 => f (if q = 0 then i else j)) =
      fun q : Fin 2 => if q = 0 then f i else f j := by
  funext q
  by_cases hq : q = 0 <;> simp [hq]



end

end Tensor0SBundle
