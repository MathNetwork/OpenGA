import DifferentialGeometry.Geometry.Coordinates.NablaComponents.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.ModelMixed
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase







set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open Bundle Set Tensor0SBundle TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]


theorem nabla0S_one_model_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          1 cov X α x₀)
        (fun _ : Fin 1 => j) =
      modelDeriv0SAt (I := I) X x₀ (fun x => α x) (fun _ : Fin 1 => j) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
  have h := nabla0S_model_coordFrame_slots
    (I := I) cov X α x₀ (fun _ : Fin 1 => j)
  have hupdate (k : CoordinateIdx (𝕜 := 𝕜) E) :
      Function.update (fun _ : Fin 1 => j) 0 k = fun _ : Fin 1 => k := by
    funext q
    fin_cases q
    simp
  simpa only [Fin.sum_univ_one, hupdate] using h



theorem nabla0S_one_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (j : CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          1 cov X α x₀)
        (fun _ : Fin 1 => j) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x) (fun _ : Fin 1 => j) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
  have h := nabla0S_coordFrame_slots
    (I := I) cov X α x₀ hderiv (fun _ : Fin 1 => j)
  have hupdate (k : CoordinateIdx (𝕜 := 𝕜) E) :
      Function.update (fun _ : Fin 1 => j) 0 k = fun _ : Fin 1 => k := by
    funext q
    fin_cases q
    simp
  simpa only [Fin.sum_univ_one, hupdate] using h








theorem nabla0SFun_one_eval_coordFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (j : CoordinateIdx (𝕜 := 𝕜) E) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀)
        (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j x₀) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x) (fun _ : Fin 1 => j) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
  simpa [coordComponent0SAt, component0S] using
    nabla0S_one_coord (I := I) cov X α x₀ hderiv j



omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] in
theorem tensor0S_one_eval_coordFrame_sum
    {x₀ : M}
    (αx : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1 x₀)
    (Z : TangentSpace I x₀) :
    αx (fun _ : Fin 1 => Z) =
      ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
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
    (Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E)) (0 : Fin 1)
    (fun j : CoordinateIdx (𝕜 := 𝕜) E => b.coord j Z • b j) (fun _ : Fin 1 => Z)
  calc
    αx (fun _ : Fin 1 => Z)
        = αx (Function.update (fun _ : Fin 1 => Z) (0 : Fin 1)
            (∑ j : CoordinateIdx (𝕜 := 𝕜) E, b.coord j Z • b j)) := by
          rw [hupdate]
          congr 1
          funext q
          exact (b.sum_repr Z).symm
    _ = ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          b.coord j Z *
            αx (Function.update (fun _ : Fin 1 => Z) (0 : Fin 1) (b j)) := by
          simpa using hmap
    _ = ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          b.coord j Z * αx (fun _ : Fin 1 => b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hupdate]
    _ = ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          (coordinateFrameAt_toBasis (I := I) x₀).coord j Z *
            αx (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j x₀) := by
          simp [b]


omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem tensor0S_one_eval_finset_sum
    {ι : Type*} {x : M}
    (αx : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1 x)
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

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
private theorem mdifferentiableAt_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> 𝕜) {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x) :
    MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using (mdifferentiableAt_const
        (I := I) (I' := 𝓘(𝕜, 𝕜)) (c := (0 : 𝕜)) (x := x))
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x := ih hft
      have hadd : MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i + t.sum f) x := hfi.add hsum
      simpa [Finset.sum_insert, hit] using hadd

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem oneForm_extDerivFun_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> 𝕜)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x) :
    extDerivFun (I := I) (t.sum f) x v =
      t.sum (fun i => extDerivFun (I := I) (f i) x v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x := by
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

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem oneForm_extDerivFun_mul
    {f g : M -> 𝕜} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(𝕜, 𝕜) f x)
    (hg : MDifferentiableAt I 𝓘(𝕜, 𝕜) g x) :
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

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem oneForm_covariantDerivative_finset_sum
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

omit [IsManifold I 1 M] [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] in
theorem oneForm_coordinateFrame_coeff_at_base_eq_coord
    (x₀ : M) (Z : TangentSpace I x₀) (j : CoordinateIdx (𝕜 := 𝕜) E) :
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

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem oneForm_extDerivFun_congr_eventually
    {f g : M -> 𝕜} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[𝓝 x] g) :
    extDerivFun (I := I) f x v = extDerivFun (I := I) g x v := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(𝕜, 𝕜)) h
  have hx : f x = g x := h.eq_of_nhds
  unfold extDerivFun
  rw [hmf, hx]
end DifferentialGeometry.Tensor.Coordinates
