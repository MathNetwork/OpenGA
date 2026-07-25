import DifferentialGeometry.Geometry.Connection.Chart.NablaComponents.Basic



noncomputable section

namespace DifferentialGeometry
namespace Coordinates

open Bundle Set Tensor0SBundle TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [IsManifold I (⊤ : WithTop ℕ∞) M]
variable [CompleteSpace Real]

omit [IsManifold I ω M] in
theorem nabla0S_one_model_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 1)
    (x₀ : M) (j : CoordinateIdx E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          1 cov X α x₀)
        (fun _ : Fin 1 => j) =
      modelDeriv0SAt (I := I) X x₀ (fun x => α x) (fun _ : Fin 1 => j) -
        ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
  classical
  simp only [nabla0SFun, TensorLieDeriv.mcovariantDeriv_tensor0SFromConnection,
    TensorLieDeriv.mcovariantDeriv_tensor0SWithinFromConnection]
  rw [← tensor0SModelAt_coordComponent0SAt (I := I) x₀
    (TensorLieDeriv.mcovariantDeriv_tensor0SWithin
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 1 X
      (connectionEndomorphismInChart (𝕜 := Real) (I := I) cov (fun x => X x) x₀)
      α Set.univ x₀) (fun _ : Fin 1 => j)]
  have hmodel := TensorLieDeriv.mcovariantDeriv_tensor0SWithin_one_apply_basis
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (⊤ : WithTop ℕ∞)) (Idx := CoordinateIdx E)
    (basis := Module.finBasis Real E)
    (X := X)
    (ΓX := connectionEndomorphismInChart (𝕜 := Real) (I := I) cov (fun x => X x) x₀)
    (α := α)
    (u := Set.univ)
    (x₀ := x₀)
    (j := j)
  refine hmodel.trans ?_
  simp_rw [connCoeff_eq_christoffelAlong_coord (I := I) cov (fun x => X x) x₀]
  simp only [modelDeriv0SAt]
  simp_rw [tensor0SModelAt_coordComponent0SAt (I := I)]

omit [IsManifold I ω M] in
theorem nabla0S_one_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (j : CoordinateIdx E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          1 cov X α x₀)
        (fun _ : Fin 1 => j) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x) (fun _ : Fin 1 => j) -
        ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
  rw [nabla0S_one_model_coord (I := I) cov X α x₀ j, hderiv]

omit [IsManifold I ω M] in
theorem nabla0SFun_one_eval_coordFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (j : CoordinateIdx E) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀)
        (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j x₀) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x) (fun _ : Fin 1 => j) -
        ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
  simpa [coordComponent0SAt, component0S] using
    nabla0S_one_coord (I := I) cov X α x₀ hderiv j

omit [IsManifold I 2 M] [IsManifold I (⊤ : WithTop ℕ∞) M] [CompleteSpace Real] in
theorem tensor0S_one_eval_coordFrame_sum
    {x₀ : M}
    (αx : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x₀)
    (Z : TangentSpace I x₀) :
    αx (fun _ : Fin 1 => Z) =
      ∑ j : CoordinateIdx E,
        (coordinateFrameAt_toBasis (I := I) x₀).coord j Z *
          αx (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j x₀) := by
  classical
  let b := coordinateFrameAt_toBasis (I := I) x₀
  have hupdate (w : TangentSpace I x₀) :
      Function.update (fun _ : Fin 1 => Z) (0 : Fin 1) w =
        fun _ : Fin 1 => w := by
    funext q
    fin_cases q
    simp
  have hmap := αx.toMultilinearMap.map_update_sum
    (Finset.univ : Finset (CoordinateIdx E)) (0 : Fin 1)
    (fun j : CoordinateIdx E => b.coord j Z • b j) (fun _ : Fin 1 => Z)
  calc
    αx (fun _ : Fin 1 => Z)
        = αx (Function.update (fun _ : Fin 1 => Z) (0 : Fin 1)
            (∑ j : CoordinateIdx E, b.coord j Z • b j)) := by
          rw [hupdate]
          congr 1
          funext q
          exact (b.sum_repr Z).symm
    _ = ∑ j : CoordinateIdx E,
          αx (Function.update (fun _ : Fin 1 => Z) (0 : Fin 1)
            (b.coord j Z • b j)) := by
          exact hmap
    _ = ∑ j : CoordinateIdx E,
          b.coord j Z * αx (fun _ : Fin 1 => b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hupdate]
          have hconst :
              (fun _ : Fin 1 => b.coord j Z • b j) =
                Function.update (fun _ : Fin 1 => b j) (0 : Fin 1)
                  (b.coord j Z • b j) := by
            funext q
            fin_cases q
            simp
          rw [hconst]
          have hsmul :
              αx (Function.update (fun _ : Fin 1 => b j) (0 : Fin 1)
                  (b.coord j Z • b j)) =
                b.coord j Z •
                  αx (Function.update (fun _ : Fin 1 => b j) (0 : Fin 1) (b j)) :=
            αx.toMultilinearMap.map_update_smul
              (m := fun _ : Fin 1 => b j) (i := (0 : Fin 1))
              (c := b.coord j Z) (x := b j)
          rw [hsmul]
          have hbase : Function.update (fun _ : Fin 1 => b j) (0 : Fin 1) (b j) =
              fun _ : Fin 1 => b j := by
            funext q; fin_cases q; simp
          rw [hbase, smul_eq_mul]
    _ = ∑ j : CoordinateIdx E,
          (coordinateFrameAt_toBasis (I := I) x₀).coord j Z *
            αx (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j x₀) := by
          simp [b]

omit [FiniteDimensional Real E] [IsManifold I 2 M] [IsManifold I ∞ M] [IsManifold I (⊤ : WithTop ℕ∞) M] [CompleteSpace Real] in
private theorem tensor0S_one_eval_finset_sum
    {ι : Type*} {x : M}
    (αx : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (t : Finset ι) (V : ι -> TangentSpace I x) :
    αx (fun _ : Fin 1 => t.sum V) =
      t.sum (fun i => αx (fun _ : Fin 1 => V i)) := by
  classical
  have hupdate (w : TangentSpace I x) :
      Function.update (fun _ : Fin 1 => t.sum V) (0 : Fin 1) w =
        fun _ : Fin 1 => w := by
    funext q
    fin_cases q
    simp
  have hmap := αx.toMultilinearMap.map_update_sum
    t (0 : Fin 1) V (fun _ : Fin 1 => t.sum V)
  calc
    αx (fun _ : Fin 1 => t.sum V)
        = αx (Function.update (fun _ : Fin 1 => t.sum V) (0 : Fin 1)
            (t.sum V)) := by
          rw [hupdate]
    _ = t.sum (fun i =>
          αx (Function.update (fun _ : Fin 1 => t.sum V) (0 : Fin 1)
            (V i))) := by
          simpa using hmap
    _ = t.sum (fun i => αx (fun _ : Fin 1 => V i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hupdate]

omit [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M] [IsManifold I (⊤ : WithTop ℕ∞) M] [CompleteSpace Real] in
private theorem mdifferentiableAt_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> Real) {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using (mdifferentiableAt_const
        (I := I) (I' := 𝓘(Real, Real)) (c := (0 : Real)) (x := x))
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := ih hft
      have hadd : MDifferentiableAt I 𝓘(Real, Real) (f i + t.sum f) x := hfi.add hsum
      simpa [Finset.sum_insert, hit] using hadd

omit [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M] [IsManifold I (⊤ : WithTop ℕ∞) M] [CompleteSpace Real] in
private theorem extDerivFun_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> Real)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    extDerivFun (I := I) (t.sum f) x v =
      t.sum (fun i => extDerivFun (I := I) (f i) x v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := by
        exact mdifferentiableAt_finset_sum (I := I) t f hft
      calc
        extDerivFun (I := I) ((insert i t).sum f) x v
            = extDerivFun (I := I)
                (f i + t.sum f) x v := by
              simp [Finset.sum_insert, hit]
        _ = extDerivFun (I := I) (f i) x v +
              extDerivFun (I := I) (t.sum f) x v := by
              have hadd := congr($(extDerivFun_add
                (I := I) (g := f i) (g' := t.sum f)
                (x := x) hfi hsum) v)
              simpa [Pi.add_apply] using hadd
        _ = (insert i t).sum (fun j => extDerivFun (I := I) (f j) x v) := by
              rw [ih hft]
              simp [Finset.sum_insert, hit]

omit [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M] [IsManifold I (⊤ : WithTop ℕ∞) M] [CompleteSpace Real] in
private theorem extDerivFun_mul
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hg : MDifferentiableAt I 𝓘(Real, Real) g x) :
    extDerivFun (I := I) (fun y : M => f y * g y) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x := by
  change extDerivFun (I := I) (f • g) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := f) (g := g) hf hg v
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    using hprod

omit [FiniteDimensional Real E] [IsManifold I 2 M] [IsManifold I ∞ M] [IsManifold I (⊤ : WithTop ℕ∞) M] [CompleteSpace Real] in
theorem covariantDerivative_finset_sum
    {ι : Type*} (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (t : Finset ι) (σ : ι -> (x : M) -> TangentSpace I x)
    {x : M} (v : TangentSpace I x)
    (hσ : ∀ i, MDiffAt (T% (σ i)) x) :
    (cov (t.sum σ) x) v = t.sum (fun i => (cov (σ i) x) v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp [cov.isCovariantDerivativeOnUniv.zero]
  | insert i t hit ih =>
      have hσi : MDiffAt (T% (σ i)) x := hσ i
      have hsum : MDiffAt (T% (t.sum σ)) x := by
        have hsum_raw := MDifferentiableAt.sum_section (s := t) (t := σ) hσ
        simpa using hsum_raw
      calc
        (cov ((insert i t).sum σ) x) v
            = (cov (σ i + t.sum σ) x) v := by
              simp [Finset.sum_insert, hit]
        _ = ((cov (σ i) x + cov (t.sum σ) x) v) := by
              rw [cov.isCovariantDerivativeOnUniv.add hσi hsum]
        _ = (cov (σ i) x) v + (cov (t.sum σ) x) v := by
              simp
        _ = (insert i t).sum (fun j => (cov (σ j) x) v) := by
              rw [ih]
              simp [Finset.sum_insert, hit]

omit [IsManifold I (⊤ : WithTop ℕ∞) M] [CompleteSpace Real] in
omit [IsManifold I 1 M] [IsManifold I 2 M] in
private theorem coordinateFrame_coeff_at_base_eq_coord
    (x₀ : M) (Z : TangentSpace I x₀) (j : CoordinateIdx E) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j x₀ Z =
      (coordinateFrameAt_toBasis (I := I) x₀).coord j Z := by
  have hbasis :
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀).toBasisAt
          (coordinateFrameAt_mem (I := I) x₀) =
        coordinateFrameAt_toBasis (I := I) x₀ := by
    ext k
    rw [IsLocalFrameOn.toBasisAt_coe]
    rw [coordinateFrameAt_toBasis_apply]
  unfold IsLocalFrameOn.coeff
  rw [dif_pos (coordinateFrameAt_mem (I := I) x₀)]
  rw [hbasis]

omit [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M] [IsManifold I (⊤ : WithTop ℕ∞) M] [CompleteSpace Real] in
private theorem extDerivFun_congr_eventually
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[𝓝 x] g) :
    extDerivFun (I := I) f x v = extDerivFun (I := I) g x v := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(Real, Real)) h
  have hx : f x = g x := h.eq_of_nhds
  unfold extDerivFun
  rw [hmf, hx]

omit [IsManifold I (⊤ : WithTop ℕ∞) M] [CompleteSpace Real] in
omit [IsManifold I 2 M] in
private theorem oneForm_pair_coordFrame_eventually
    (Z : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 1)
    (x₀ : M) :
    (fun y : M => α y (fun _ : Fin 1 => Z y)) =ᶠ[𝓝 x₀]
      (fun y : M =>
        ∑ j : CoordinateIdx E,
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y) *
            α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) := by
  classical
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with y hy
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have hZ :
      Z y = ∑ j : CoordinateIdx E,
        hframe.coeff j y (Z y) • coordinateFrameAt (I := I) x₀ j y := by
    exact hframe.coeff_sum_eq (fun y => Z y) hy
  have hupdate (w : TangentSpace I y) :
      Function.update (fun _ : Fin 1 => Z y) (0 : Fin 1) w =
        fun _ : Fin 1 => w := by
    funext q
    fin_cases q
    simp
  have hmap := (α y).toMultilinearMap.map_update_sum
    (Finset.univ : Finset (CoordinateIdx E)) (0 : Fin 1)
    (fun j : CoordinateIdx E =>
      hframe.coeff j y (Z y) • coordinateFrameAt (I := I) x₀ j y)
    (fun _ : Fin 1 => Z y)
  calc
    α y (fun _ : Fin 1 => Z y)
        = α y (Function.update (fun _ : Fin 1 => Z y) (0 : Fin 1)
            (∑ j : CoordinateIdx E,
              hframe.coeff j y (Z y) • coordinateFrameAt (I := I) x₀ j y)) := by
          congr 1
          funext q
          fin_cases q
          exact hZ
    _ = ∑ j : CoordinateIdx E,
          α y (Function.update (fun _ : Fin 1 => Z y) (0 : Fin 1)
            (hframe.coeff j y (Z y) • coordinateFrameAt (I := I) x₀ j y)) := by
          exact hmap
    _ = ∑ j : CoordinateIdx E,
          hframe.coeff j y (Z y) *
            α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hupdate]
          have hconst :
              (fun _ : Fin 1 =>
                  hframe.coeff j y (Z y) • coordinateFrameAt (I := I) x₀ j y) =
                Function.update
                  (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)
                  (0 : Fin 1)
                  (hframe.coeff j y (Z y) • coordinateFrameAt (I := I) x₀ j y) := by
            funext q
            fin_cases q
            simp
          rw [hconst]
          have hsmul :
              α y (Function.update
                  (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)
                  (0 : Fin 1)
                  (hframe.coeff j y (Z y) • coordinateFrameAt (I := I) x₀ j y)) =
                hframe.coeff j y (Z y) •
                  α y (Function.update
                    (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)
                    (0 : Fin 1) (coordinateFrameAt (I := I) x₀ j y)) :=
            (α y).toMultilinearMap.map_update_smul
              (m := fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)
              (i := (0 : Fin 1))
              (c := hframe.coeff j y (Z y))
              (x := coordinateFrameAt (I := I) x₀ j y)
          rw [hsmul]
          have hbase :
              Function.update
                  (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y) (0 : Fin 1)
                  (coordinateFrameAt (I := I) x₀ j y) =
                (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y) := by
            funext q; fin_cases q; simp
          rw [hbase, smul_eq_mul]

omit [IsManifold I (⊤ : WithTop ℕ∞) M] [CompleteSpace Real] in
omit [IsManifold I 2 M] in
theorem oneForm_pair_coordFrame_product_rule
    (X Z : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 1)
    (x₀ : M) (z dz : CoordinateIdx E -> Real)
    (hz : ∀ j : CoordinateIdx E,
      z j = (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀))
    (hdz : ∀ j : CoordinateIdx E,
      dz j =
        extDerivFun (I := I)
          (fun y : M =>
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
          x₀ (X x₀))
    (hdiff_z : ∀ j : CoordinateIdx E,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀)
    (hdiff_α : ∀ j : CoordinateIdx E,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀) :
    extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) =
      ∑ j : CoordinateIdx E,
        (dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
          z j *
            coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x)
              (fun _ : Fin 1 => j)) := by
  classical
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  let zfun : CoordinateIdx E -> M -> Real :=
    fun j y => hframe.coeff j y (Z y)
  let afun : CoordinateIdx E -> M -> Real :=
    fun j y => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)
  have hpair_ev := oneForm_pair_coordFrame_eventually (I := I) Z α x₀
  have hderiv_congr :
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) =
        extDerivFun (I := I)
          (fun y : M => ∑ j : CoordinateIdx E, zfun j y * afun j y) x₀ (X x₀) := by
    exact extDerivFun_congr_eventually (I := I) (X x₀) (by
      simpa [zfun, afun] using hpair_ev)
  rw [hderiv_congr]
  have hsum_fun :
      (fun y : M => ∑ j : CoordinateIdx E, zfun j y * afun j y) =
        Finset.univ.sum (fun j : CoordinateIdx E =>
          fun y : M => zfun j y * afun j y) := by
    funext y
    simp
  rw [hsum_fun]
  rw [extDerivFun_finset_sum (I := I) (t := Finset.univ)
    (f := fun j y => zfun j y * afun j y) (x := x₀) (v := X x₀)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [extDerivFun_mul (I := I) (f := zfun j) (g := afun j) (x := x₀)
      (v := X x₀) (hdiff_z j) (hdiff_α j)]
    have hzj : zfun j x₀ = z j := by
      rw [hz j]
      exact coordinateFrame_coeff_at_base_eq_coord (I := I) x₀ (Z x₀) j
    have hdzj : extDerivFun (I := I) (zfun j) x₀ (X x₀) = dz j := by
      exact (hdz j).symm
    have haj :
        afun j x₀ = coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) := by
      simp [afun, coordComponent0SAt, component0S]
    have hdaj :
        extDerivFun (I := I) (afun j) x₀ (X x₀) =
          coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x)
            (fun _ : Fin 1 => j) := by
      change (mfderiv I 𝓘(Real, Real) (afun j) x₀) (X x₀) =
          coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x)
            (fun _ : Fin 1 => j)
      simp [afun, coordDeriv0SAt]
    rw [hzj, hdzj, haj, hdaj]
    ring
  · intro j _
    exact (hdiff_z j).mul (hdiff_α j)

omit [IsManifold I (⊤ : WithTop ℕ∞) M] [CompleteSpace Real] in
omit [IsManifold I 2 M] in
theorem oneForm_covariantDerivative_coordFrame_product_rule
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Z : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 1)
    (x₀ : M) (z dz : CoordinateIdx E -> Real)
    (hz : ∀ j : CoordinateIdx E,
      z j = (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀))
    (hdz : ∀ j : CoordinateIdx E,
      dz j =
        extDerivFun (I := I)
          (fun y : M =>
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
          x₀ (X x₀))
    (hdiff_z : ∀ j : CoordinateIdx E,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀) :
    α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) =
      ∑ j : CoordinateIdx E,
        (dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
          z j *
            (∑ k : CoordinateIdx E,
              christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                x₀ (X x₀) j k *
                coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k))) := by
  classical
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  let frame := coordinateFrameAt (I := I) x₀
  let zfun : CoordinateIdx E -> M -> Real :=
    fun j y => hframe.coeff j y (Z y)
  let term : CoordinateIdx E -> (x : M) -> TangentSpace I x :=
    fun j => zfun j • frame j
  have hframe_diff (j : CoordinateIdx E) : MDiffAt (T% (frame j)) x₀ :=
    (hframe.contMDiffAt (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) j).mdifferentiableAt one_ne_zero
  have hterm_diff : ∀ j ∈ (Finset.univ : Finset (CoordinateIdx E)),
      MDiffAt (T% (term j)) x₀ := by
    intro j _
    exact (hdiff_z j).smul_section (hframe_diff j)
  have hsum_diff :
      MDiffAt (T% ((Finset.univ : Finset (CoordinateIdx E)).sum term)) x₀ := by
    classical
    exact (by
      have hterm_all : ∀ j : CoordinateIdx E, MDiffAt (T% (term j)) x₀ := by
        intro j
        exact hterm_diff j (by simp)
      simpa using MDifferentiableAt.sum_section
        (s := (Finset.univ : Finset (CoordinateIdx E))) (t := term) hterm_all)
  have hZ_diff : MDiffAt (T% (fun y : M => Z y)) x₀ :=
    Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hZ_ev : (fun y : M => Z y) =ᶠ[𝓝 x₀]
      (fun y : M => ∑ j : CoordinateIdx E, term j y) := by
    exact hframe.eventually_eq_sum_coeff_smul (fun y => Z y)
      ((coordinateFrameSet_open (I := I) x₀).mem_nhds
        (coordinateFrameAt_mem (I := I) x₀))
  have hcov_congr :
      cov (fun y : M => Z y) x₀ =
        cov ((Finset.univ : Finset (CoordinateIdx E)).sum term) x₀ :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZ_diff hsum_diff
      (by simp)
      (by simpa [term] using hZ_ev)
  have hcov_sum :
      (cov (fun y : M => Z y) x₀) (X x₀) =
        ∑ j : CoordinateIdx E,
          (dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀)) := by
    calc
      (cov (fun y : M => Z y) x₀) (X x₀)
          = (cov ((Finset.univ : Finset (CoordinateIdx E)).sum term) x₀) (X x₀) := by
            rw [hcov_congr]
      _ = ∑ j : CoordinateIdx E, (cov (term j) x₀) (X x₀) := by
            rw [covariantDerivative_finset_sum (I := I) cov
              (Finset.univ : Finset (CoordinateIdx E)) term (X x₀) (by
                intro j
                exact hterm_diff j (by simp))]
      _ = ∑ j : CoordinateIdx E,
            (dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            have hleib := congr($(cov.isCovariantDerivativeOnUniv.leibniz
              (σ := frame j) (g := zfun j) (x := x₀)
              (hframe_diff j) (hdiff_z j)) (X x₀))
            have hzj : zfun j x₀ = z j := by
              rw [hz j]
              exact coordinateFrame_coeff_at_base_eq_coord (I := I) x₀ (Z x₀) j
            have hdzj : extDerivFun (I := I) (zfun j) x₀ (X x₀) = dz j := by
              exact (hdz j).symm
            simpa [term, zfun, hzj, hdzj, add_comm] using hleib
  rw [hcov_sum]
  rw [tensor0S_one_eval_finset_sum (I := I)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcov_frame :
      (cov (frame j) x₀) (X x₀) =
        ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k • frame k x₀ := by
    exact hframe.coeff_sum_eq
      (fun y => (cov (frame j) y) (X y))
      (coordinateFrameAt_mem (I := I) x₀)
  have h_eval_cov :
      α x₀ (fun _ : Fin 1 => (cov (frame j) x₀) (X x₀)) =
        ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
    rw [hcov_frame]
    rw [tensor0S_one_eval_finset_sum (I := I)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hupdate :
        (fun _ : Fin 1 =>
            christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k • frame k x₀) =
          Function.update (fun _ : Fin 1 => frame k x₀) (0 : Fin 1)
            (christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k • frame k x₀) := by
      funext q
      fin_cases q
      simp
    rw [hupdate]
    have hsmul :
        α x₀ (Function.update (fun _ : Fin 1 => frame k x₀) (0 : Fin 1)
            (christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k • frame k x₀)) =
          christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k •
            α x₀ (Function.update (fun _ : Fin 1 => frame k x₀)
              (0 : Fin 1) (frame k x₀)) :=
      (α x₀).toMultilinearMap.map_update_smul
        (m := fun _ : Fin 1 => frame k x₀) (i := (0 : Fin 1))
        (c := christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k)
        (x := frame k x₀)
    rw [hsmul]
    have hframe_eval :
        α x₀ (fun _ : Fin 1 => frame k x₀) =
          coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
      simp [frame, coordComponent0SAt, component0S]
    have hupdate0 :
        Function.update (fun _ : Fin 1 => frame k x₀) (0 : Fin 1) (frame k x₀) =
          fun _ : Fin 1 => frame k x₀ := by
      funext q
      fin_cases q
      simp
    rw [hupdate0, hframe_eval, smul_eq_mul]
  have h_eval_frame :
      α x₀ (fun _ : Fin 1 => frame j x₀) =
        coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) := by
    simp [frame, coordComponent0SAt, component0S]
  change α x₀ (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀)) =
      dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
        z j *
          (∑ k : CoordinateIdx E,
            christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k *
              coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k))
  have hconst_add :
      (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀)) =
        Function.update
          (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀))
          (0 : Fin 1)
          (dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀)) := by
    funext q
    fin_cases q
    simp
  rw [hconst_add]
  have hadd :
      α x₀ (Function.update
            (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀))
            (0 : Fin 1)
            (dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀))) =
        α x₀ (Function.update
            (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀))
            (0 : Fin 1) (dz j • frame j x₀)) +
          α x₀ (Function.update
            (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀))
            (0 : Fin 1) (z j • (cov (frame j) x₀) (X x₀))) :=
    (α x₀).toMultilinearMap.map_update_add
      (m := fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀))
      (i := (0 : Fin 1))
      (x := dz j • frame j x₀)
      (y := z j • (cov (frame j) x₀) (X x₀))
  rw [hadd]
  have h_up1 :
      Function.update
        (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀))
        (0 : Fin 1) (dz j • frame j x₀) =
        fun _ : Fin 1 => dz j • frame j x₀ := by
    funext q
    fin_cases q
    simp
  have h_up2 :
      Function.update
        (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀))
        (0 : Fin 1) (z j • (cov (frame j) x₀) (X x₀)) =
        fun _ : Fin 1 => z j • (cov (frame j) x₀) (X x₀) := by
    funext q
    fin_cases q
    simp
  rw [h_up1, h_up2]
  rw [show α x₀ (fun _ : Fin 1 => dz j • frame j x₀) =
      dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) by
    have hupdate :
        (fun _ : Fin 1 => dz j • frame j x₀) =
          Function.update (fun _ : Fin 1 => frame j x₀) (0 : Fin 1)
            (dz j • frame j x₀) := by
      funext q
      fin_cases q
      simp
    rw [hupdate]
    have hsmul1 :
        α x₀ (Function.update (fun _ : Fin 1 => frame j x₀) (0 : Fin 1)
            (dz j • frame j x₀)) =
          dz j • α x₀ (Function.update (fun _ : Fin 1 => frame j x₀) (0 : Fin 1)
            (frame j x₀)) :=
      (α x₀).toMultilinearMap.map_update_smul
        (m := fun _ : Fin 1 => frame j x₀) (i := (0 : Fin 1))
        (c := dz j) (x := frame j x₀)
    rw [hsmul1]
    simp [h_eval_frame, smul_eq_mul]]
  rw [show α x₀ (fun _ : Fin 1 => z j • (cov (frame j) x₀) (X x₀)) =
      z j * (∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k)) by
    have hupdate :
        (fun _ : Fin 1 => z j • (cov (frame j) x₀) (X x₀)) =
          Function.update
            (fun _ : Fin 1 => (cov (frame j) x₀) (X x₀))
            (0 : Fin 1)
            (z j • (cov (frame j) x₀) (X x₀)) := by
      funext q
      fin_cases q
      simp
    rw [hupdate]
    have hsmul2 :
        α x₀ (Function.update (fun _ : Fin 1 => (cov (frame j) x₀) (X x₀))
            (0 : Fin 1) (z j • (cov (frame j) x₀) (X x₀))) =
          z j • α x₀ (Function.update (fun _ : Fin 1 => (cov (frame j) x₀) (X x₀))
            (0 : Fin 1) ((cov (frame j) x₀) (X x₀))) :=
      (α x₀).toMultilinearMap.map_update_smul
        (m := fun _ : Fin 1 => (cov (frame j) x₀) (X x₀)) (i := (0 : Fin 1))
        (c := z j) (x := (cov (frame j) x₀) (X x₀))
    rw [hsmul2]
    simp [h_eval_cov, smul_eq_mul]]

omit [IsManifold I ω M] in
theorem nabla0SFun_one_eval_coordFrame_expanded
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (Z : TangentSpace I x₀) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z) =
      ∑ j : CoordinateIdx E,
        (coordinateFrameAt_toBasis (I := I) x₀).coord j Z *
          (coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x)
              (fun _ : Fin 1 => j) -
            ∑ k : CoordinateIdx E,
              christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                x₀ (X x₀) j k *
                coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k)) := by
  classical
  rw [tensor0S_one_eval_coordFrame_sum (I := I)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [nabla0SFun_one_eval_coordFrame (I := I) cov X α x₀ hderiv j]

omit [IsManifold I ω M] in
theorem nabla0SFun_one_eval_of_coordFrame_product
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Z : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (z dz : CoordinateIdx E -> Real)
    (hz : ∀ j : CoordinateIdx E,
      z j = (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀))
    (hpair :
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) =
        ∑ j : CoordinateIdx E,
          (dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
            z j *
              coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x)
                (fun _ : Fin 1 => j)))
    (hcovZ :
      α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) =
        ∑ j : CoordinateIdx E,
          (dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
            z j *
              (∑ k : CoordinateIdx E,
                christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                  x₀ (X x₀) j k *
                  coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k)))) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  classical
  rw [nabla0SFun_one_eval_coordFrame_expanded (I := I) cov X α x₀ hderiv (Z x₀)]
  rw [hpair, hcovZ]
  simp_rw [← hz]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp_rw [Finset.sum_add_distrib]
  ring

omit [IsManifold I ω M] in
theorem nabla0SFun_one_eval_of_coordFrame_product_rule
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Z : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (z dz : CoordinateIdx E -> Real)
    (hz : ∀ j : CoordinateIdx E,
      z j = (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀))
    (hdz : ∀ j : CoordinateIdx E,
      dz j =
        extDerivFun (I := I)
          (fun y : M =>
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
          x₀ (X x₀))
    (hdiff_z : ∀ j : CoordinateIdx E,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀)
    (hdiff_α : ∀ j : CoordinateIdx E,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀)
    (hcovZ :
      α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) =
        ∑ j : CoordinateIdx E,
          (dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
            z j *
              (∑ k : CoordinateIdx E,
                christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                  x₀ (X x₀) j k *
                  coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k)))) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  exact nabla0SFun_one_eval_of_coordFrame_product
    (I := I) cov X Z α x₀ hderiv z dz hz
    (oneForm_pair_coordFrame_product_rule
      (I := I) X Z α x₀ z dz hz hdz hdiff_z hdiff_α)
    hcovZ

omit [IsManifold I ω M] in
theorem nabla0SFun_one_eval_of_coordFrame_product_rules
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Z : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (z dz : CoordinateIdx E -> Real)
    (hz : ∀ j : CoordinateIdx E,
      z j = (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀))
    (hdz : ∀ j : CoordinateIdx E,
      dz j =
        extDerivFun (I := I)
          (fun y : M =>
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
          x₀ (X x₀))
    (hdiff_z : ∀ j : CoordinateIdx E,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀)
    (hdiff_α : ∀ j : CoordinateIdx E,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  exact nabla0SFun_one_eval_of_coordFrame_product_rule
    (I := I) cov X Z α x₀ hderiv z dz hz hdz hdiff_z hdiff_α
    (oneForm_covariantDerivative_coordFrame_product_rule
      (I := I) cov X Z α x₀ z dz hz hdz hdiff_z)

omit [IsManifold I ω M] in
theorem nabla0SFun_one_eval_coordFrame_moving
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Z : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (hdiff_z : ∀ j : CoordinateIdx E,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀)
    (hdiff_α : ∀ j : CoordinateIdx E,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  let z : CoordinateIdx E -> Real :=
    fun j => (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀)
  let dz : CoordinateIdx E -> Real :=
    fun j =>
      extDerivFun (I := I)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
        x₀ (X x₀)
  exact nabla0SFun_one_eval_of_coordFrame_product_rules
    (I := I) cov X Z α x₀ hderiv z dz (by intro j; rfl) (by intro j; rfl)
    hdiff_z hdiff_α

end Coordinates
end DifferentialGeometry
