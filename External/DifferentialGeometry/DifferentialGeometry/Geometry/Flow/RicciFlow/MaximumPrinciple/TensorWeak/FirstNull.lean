import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.TensorWeak.BarrierCore


set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle Tensor0SBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]








structure TensorFirstNullData
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) : Type _ where
  t1 : Real
  x1 : M
  v : TangentSpace I x1
  t1_mem : t1 ∈ Set.Ioc t0 (t0 + delta)
  v_ne_zero : v ≠ 0
  unit : (G t1).inner x1 v v = 1
  nonnegative_until :
    ∀ t, t ∈ Set.Icc t0 t1 ->
      ∀ x, TwoTensorNonnegativeAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t) x
  null :
    tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t1 x1 v v = 0



omit [IsManifold I 2 M] in
theorem firstNullKernel_left
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S)
        (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0) :
    ∀ w : TangentSpace I d.x1,
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 d.t1 d.x1 d.v w = 0 := by
  let Bsec : TwoTensorSecFamily (I := I) (M := M) :=
    tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0
  let A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 d.x1 :=
    Bsec d.t1 d.x1
  have ht1_slab : d.t1 ∈ Set.Icc t0 (t0 + delta) :=
    ⟨le_of_lt d.t1_mem.1, d.t1_mem.2⟩
  have hBsym :
      TwoTensorSymmetricAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0 d.t1) d.x1 :=
    barrierSymmAt (I := I) (M := M)
      (G := G) (S := twoTensorSecToFamily (I := I) (M := M) S)
      (epsilon := epsilon) (delta := delta) (t0 := t0)
      (t := d.t1) (x := d.x1)
      (hsym d.t1 ht1_slab d.x1)
  have hAsym :
      ∀ u w : TangentSpace I d.x1,
        eval02 (I := I) (M := M) A u w =
          eval02 (I := I) (M := M) A w u := by
    intro u w
    calc
      eval02 (I := I) (M := M) A u w =
          twoTensorSecToFamily (I := I) (M := M) Bsec d.t1 d.x1 u w := by
            exact eval02_sec_eq (I := I) (M := M) Bsec d.t1 d.x1 u w
      _ =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 u w := by
            exact tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0
              d.t1 d.x1 u w
      _ =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 w u := hBsym u w
      _ =
          twoTensorSecToFamily (I := I) (M := M) Bsec d.t1 d.x1 w u := by
            exact (tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0
              d.t1 d.x1 w u).symm
      _ = eval02 (I := I) (M := M) A w u := by
            exact (eval02_sec_eq (I := I) (M := M) Bsec d.t1 d.x1 w u).symm
  have hApsd : ∀ u : TangentSpace I d.x1,
      0 ≤ quad02 (I := I) (M := M) A u := by
    intro u
    have hraw := d.nonnegative_until d.t1
      ⟨le_of_lt d.t1_mem.1, le_rfl⟩ d.x1 u
    calc
      0 ≤
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 u u := hraw
      _ = quad02 (I := I) (M := M) A u := by
          rw [← tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0
            d.t1 d.x1 u u]
          exact (quad02_sec_eq (I := I) (M := M) Bsec d.t1 d.x1 u).symm
  have hAnull : quad02 (I := I) (M := M) A d.v = 0 := by
    calc
      quad02 (I := I) (M := M) A d.v =
          twoTensorSecToFamily (I := I) (M := M) Bsec d.t1 d.x1 d.v d.v :=
            quad02_sec_eq (I := I) (M := M) Bsec d.t1 d.x1 d.v
      _ =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 d.v d.v :=
            tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0
              d.t1 d.x1 d.v d.v
      _ = 0 := d.null
  have hkernel :=
    psd_null_left (I := I) (M := M) A hAsym hApsd hAnull
  intro w
  calc
    tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 d.t1 d.x1 d.v w =
        twoTensorSecToFamily (I := I) (M := M) Bsec d.t1 d.x1 d.v w := by
          exact (tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0
            d.t1 d.x1 d.v w).symm
    _ = eval02 (I := I) (M := M) A d.v w := by
          exact (eval02_sec_eq (I := I) (M := M) Bsec d.t1 d.x1 d.v w).symm
    _ = 0 := hkernel w


omit [IsManifold I 2 M] in
theorem firstNullKernel_right
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S)
        (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0) :
    ∀ w : TangentSpace I d.x1,
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 d.t1 d.x1 w d.v = 0 := by
  have ht1_slab : d.t1 ∈ Set.Icc t0 (t0 + delta) :=
    ⟨le_of_lt d.t1_mem.1, d.t1_mem.2⟩
  have hBsym :
      TwoTensorSymmetricAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0 d.t1) d.x1 :=
    barrierSymmAt (I := I) (M := M)
      (G := G) (S := twoTensorSecToFamily (I := I) (M := M) S)
      (epsilon := epsilon) (delta := delta) (t0 := t0)
      (t := d.t1) (x := d.x1)
      (hsym d.t1 ht1_slab d.x1)
  intro w
  rw [hBsym w d.v]
  exact firstNullKernel_left (I := I) (M := M) hsym d w



omit [IsManifold I 2 M] in
theorem firstNullFieldKerL
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S)
        (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0)
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    (hB :
      ∀ w : TangentSpace I d.x1,
        B d.x1 (vec2 (I := I) d.v w) =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 d.v w) :
    ∀ w : TangentSpace I d.x1,
      B d.x1 (vec2 (I := I) d.v w) = 0 := by
  intro w
  rw [hB w]
  exact firstNullKernel_left (I := I) (M := M) hsym d w



omit [IsManifold I 2 M] in
theorem firstNullFieldKerR
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S)
        (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0)
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    (hB :
      ∀ w : TangentSpace I d.x1,
        B d.x1 (vec2 (I := I) w d.v) =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 w d.v) :
    ∀ w : TangentSpace I d.x1,
      B d.x1 (vec2 (I := I) w d.v) = 0 := by
  intro w
  rw [hB w]
  exact firstNullKernel_right (I := I) (M := M) hsym d w





private theorem deriv_nonpos_of_nonneg_left
    {phi : Real -> Real} {a b t d : Real}
    (hat : a < t) (htb : t ≤ b)
    (hnonneg : ∀ s : Real, s ∈ Set.Icc a t -> 0 ≤ phi s)
    (hzero : phi t = 0)
    (hderiv : HasDerivWithinAt phi d (Set.Ioc a b) t) :
    d ≤ 0 := by
  let m : Real := (a + t) / 2
  have ham : a < m := by
    dsimp [m]
    linarith
  have hmt : m < t := by
    dsimp [m]
    linarith
  have hsubset : Set.Icc m t ⊆ Set.Ioc a b := by
    intro y hy
    exact ⟨lt_of_lt_of_le ham hy.1, hy.2.trans htb⟩
  have hderiv_m : HasDerivWithinAt phi d (Set.Icc m t) t :=
    hderiv.mono hsubset
  have hmin : IsMinOn phi (Set.Icc m t) t := by
    intro y hy
    rw [hzero]
    exact hnonneg y ⟨(le_of_lt ham).trans hy.1, hy.2⟩
  have hlocal : IsLocalMinOn phi (Set.Icc m t) t := hmin.localize
  have hdir : m - t ∈ posTangentConeAt (Set.Icc m t) t := by
    have hseg : segment Real t m ⊆ Set.Icc m t := by
      rw [segment_symm, segment_eq_Icc (le_of_lt hmt)]
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonneg_deriv :
      0 ≤ (fderivWithin Real phi (Set.Icc m t) t : Real →L[Real] Real) (m - t) :=
    hlocal.fderivWithin_nonneg hdir
  have huniq :
      UniqueDiffWithinAt Real (Set.Icc m t) t :=
    (uniqueDiffOn_Icc hmt).uniqueDiffWithinAt ⟨le_of_lt hmt, le_rfl⟩
  have hderiv_eq : derivWithin phi (Set.Icc m t) t = d :=
    hderiv_m.derivWithin huniq
  have hlin :
      (fderivWithin Real phi (Set.Icc m t) t : Real →L[Real] Real) (m - t) =
        (m - t) * derivWithin phi (Set.Icc m t) t := by
    rw [← fderivWithin_derivWithin (𝕜 := Real) (f := phi)
      (s := Set.Icc m t) (x := t)]
    simpa [smul_eq_mul] using
      ((fderivWithin Real phi (Set.Icc m t) t : Real →L[Real] Real).map_smul
        (m - t) (1 : Real))
  rw [hlin, hderiv_eq] at hnonneg_deriv
  exact nonpos_of_mul_nonneg_right hnonneg_deriv (sub_neg.mpr hmt)


omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem firstNullTime_nonpos
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (timeDeriv : TensorQuadraticFormFamily (I := I) (M := M))
    (hderiv :
      ∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt
            (fun s : Real =>
              tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
                s x v v)
            (timeDeriv t x v) (Set.Ioc t0 (t0 + delta)) t) :
    timeDeriv d.t1 d.x1 d.v ≤ 0 := by
  exact deriv_nonpos_of_nonneg_left
    (a := t0) (b := t0 + delta) (t := d.t1)
    (d := timeDeriv d.t1 d.x1 d.v)
    d.t1_mem.1 d.t1_mem.2
    (fun s hs => d.nonnegative_until s hs d.x1 d.v)
    d.null
    (hderiv d.t1 d.t1_mem d.x1 d.v)





theorem nablaEval_extDeriv
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : ∀ q : Fin 2, V q x = v)
    (hcovV :
      ∀ q : Fin 2, ((cov (fun p : M => V q p) x) (Y x)) = 0) :
    nablaB x (Fin.cons (Y x) (vec2 (I := I) v v)) =
      extDerivFun (I := I) (fun p : M => B p (fun q : Fin 2 => V q p))
        x (Y x) := by
  have hslots : (fun q : Fin 2 => V q x) = vec2 (I := I) v v := by
    funext q
    rw [hV q]
    fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  have h :=
    TotalNabla0SRealizes.eval_smooth_slots (I := I)
      hreal Y V x
  rw [hslots] at h
  rw [h]
  have hsum :
      (∑ a : Fin 2,
        B x
          (Function.update (vec2 (I := I) v v) a
            ((cov (fun p : M => V a p) x) (Y x)))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _ha
    rw [hcovV a]
    exact (B x).map_update_zero (vec2 (I := I) v v) a
  rw [hsum]
  simp









private theorem nablaEval_ker
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : ∀ q : Fin 2, V q x = v)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0) :
    nablaB x (Fin.cons (Y x) (vec2 (I := I) v v)) =
      extDerivFun (I := I) (fun p : M => B p (fun q : Fin 2 => V q p))
        x (Y x) := by
  have hslots : (fun q : Fin 2 => V q x) = vec2 (I := I) v v := by
    funext q
    rw [hV q]
    fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  have h :=
    TotalNabla0SRealizes.eval_smooth_slots (I := I)
      hreal Y V x
  rw [hslots] at h
  rw [h]
  have hsum :
      (∑ a : Fin 2,
        B x
          (Function.update (vec2 (I := I) v v) a
            ((cov (fun p : M => V a p) x) (Y x)))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _ha
    fin_cases a
    · change
        B x
          (Function.update (vec2 (I := I) v v) (0 : Fin 2)
            ((cov (fun p : M => V 0 p) x) (Y x))) = 0
      let A : TangentSpace I x := (cov (fun p : M => V 0 p) x) (Y x)
      have hupdate :
          Function.update (vec2 (I := I) v v) (0 : Fin 2) A =
            vec2 (I := I) A v := by
        funext q
        fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update, A]
      rw [hupdate]
      exact hkerR A
    · change
        B x
          (Function.update (vec2 (I := I) v v) (1 : Fin 2)
            ((cov (fun p : M => V 1 p) x) (Y x))) = 0
      let A : TangentSpace I x := (cov (fun p : M => V 1 p) x) (Y x)
      have hupdate :
          Function.update (vec2 (I := I) v v) (1 : Fin 2) A =
            vec2 (I := I) v A := by
        funext q
        fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update, A]
      rw [hupdate]
      exact hkerL A
  rw [hsum]
  simp







private theorem nablaEval_ker_tangent
    [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (Vsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : Vsec x = v)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0)
    (A : TangentSpace I x) :
    nablaB x (Fin.cons A (vec2 (I := I) v v)) =
      extDerivFun (I := I)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) x A := by
  obtain ⟨Ysec, hYsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A
  let V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun _ => Vsec
  have hV' : ∀ q : Fin 2, V q x = v := by
    intro q
    exact hV
  have hcalc :=
    nablaEval_ker (I := I) (M := M) hreal Ysec V hV' hkerL hkerR
  simpa [V, hYsec, vec2_self_eq_const] using hcalc



private theorem deriv_eval_zero_left
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (X A V : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hA : A x = 0)
    (hV : V x = v)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0) :
    extDerivFun (I := I)
      (fun p : M => B p (vec2 (I := I) (A p) (V p))) x (X x) = 0 := by
  let U : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Fin.cons A (fun _ : Fin 1 => V)
  have hslots : (fun q : Fin 2 => U q x) =
      vec2 (I := I) (0 : TangentSpace I x) v := by
    funext q
    fin_cases q <;> simp [U, hA, hV, vec2, DifferentialGeometry.Integral.Connection.vec2]
  have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) hreal X U x
  rw [hslots] at h
  have hfun :
      (fun p : M => B p (fun a : Fin 2 => U a p)) =
        (fun p : M => B p (vec2 (I := I) (A p) (V p))) := by
    funext p
    congr
    funext q
    fin_cases q <;> simp [U, vec2, DifferentialGeometry.Integral.Connection.vec2]
  rw [hfun] at h
  have hlhs :
      nablaB x (Fin.cons (X x) (vec2 (I := I) (0 : TangentSpace I x) v)) = 0 := by
    exact (nablaB x).map_coord_zero (1 : Fin 3)
      (by
        change (vec2 (I := I) (0 : TangentSpace I x) v) (0 : Fin 2) = 0
        simp [vec2, DifferentialGeometry.Integral.Connection.vec2])
  have hsum :
      (∑ a : Fin 2,
        B x
          (Function.update (vec2 (I := I) (0 : TangentSpace I x) v) a
            ((cov (fun p : M => U a p) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_two]
    have h0 :
        B x
          (Function.update (vec2 (I := I) (0 : TangentSpace I x) v) (0 : Fin 2)
            ((cov (fun p : M => U 0 p) x) (X x))) = 0 := by
      let W : TangentSpace I x := (cov (fun p : M => U 0 p) x) (X x)
      have hupdate :
          Function.update (vec2 (I := I) (0 : TangentSpace I x) v) (0 : Fin 2) W =
            vec2 (I := I) W v := by
        funext q
        fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update, W]
      rw [hupdate]
      exact hkerR W
    have h1 :
        B x
          (Function.update (vec2 (I := I) (0 : TangentSpace I x) v) (1 : Fin 2)
            ((cov (fun p : M => U 1 p) x) (X x))) = 0 := by
      let W : TangentSpace I x := (cov (fun p : M => U 1 p) x) (X x)
      have hupdate :
          Function.update (vec2 (I := I) (0 : TangentSpace I x) v) (1 : Fin 2) W =
            vec2 (I := I) (0 : TangentSpace I x) W := by
        funext q
        fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update, W]
      have hzero :
          B x (vec2 (I := I) (0 : TangentSpace I x) W) = 0 := by
        exact (B x).map_coord_zero (0 : Fin 2)
          (by simp [vec2, DifferentialGeometry.Integral.Connection.vec2])
      rw [hupdate]
      exact hzero
    rw [h0, h1]
    simp
  rw [hlhs, hsum] at h
  simpa using h.symm



private theorem deriv_eval_zero_right
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (X V A : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : V x = v)
    (hA : A x = 0)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0) :
    extDerivFun (I := I)
      (fun p : M => B p (vec2 (I := I) (V p) (A p))) x (X x) = 0 := by
  let U : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Fin.cons V (fun _ : Fin 1 => A)
  have hslots : (fun q : Fin 2 => U q x) =
      vec2 (I := I) v (0 : TangentSpace I x) := by
    funext q
    fin_cases q <;> simp [U, hA, hV, vec2, DifferentialGeometry.Integral.Connection.vec2]
  have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) hreal X U x
  rw [hslots] at h
  have hfun :
      (fun p : M => B p (fun a : Fin 2 => U a p)) =
        (fun p : M => B p (vec2 (I := I) (V p) (A p))) := by
    funext p
    congr
    funext q
    fin_cases q <;> simp [U, vec2, DifferentialGeometry.Integral.Connection.vec2]
  rw [hfun] at h
  have hlhs :
      nablaB x (Fin.cons (X x) (vec2 (I := I) v (0 : TangentSpace I x))) = 0 := by
    exact (nablaB x).map_coord_zero (2 : Fin 3)
      (by
        change (vec2 (I := I) v (0 : TangentSpace I x)) (1 : Fin 2) = 0
        simp [vec2, DifferentialGeometry.Integral.Connection.vec2])
  have hsum :
      (∑ a : Fin 2,
        B x
          (Function.update (vec2 (I := I) v (0 : TangentSpace I x)) a
            ((cov (fun p : M => U a p) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_two]
    have h0 :
        B x
          (Function.update (vec2 (I := I) v (0 : TangentSpace I x)) (0 : Fin 2)
            ((cov (fun p : M => U 0 p) x) (X x))) = 0 := by
      let W : TangentSpace I x := (cov (fun p : M => U 0 p) x) (X x)
      have hupdate :
          Function.update (vec2 (I := I) v (0 : TangentSpace I x)) (0 : Fin 2) W =
            vec2 (I := I) W (0 : TangentSpace I x) := by
        funext q
        fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update, W]
      have hzero :
          B x (vec2 (I := I) W (0 : TangentSpace I x)) = 0 := by
        exact (B x).map_coord_zero (1 : Fin 2)
          (by simp [vec2, DifferentialGeometry.Integral.Connection.vec2])
      rw [hupdate]
      exact hzero
    have h1 :
        B x
          (Function.update (vec2 (I := I) v (0 : TangentSpace I x)) (1 : Fin 2)
            ((cov (fun p : M => U 1 p) x) (X x))) = 0 := by
      let W : TangentSpace I x := (cov (fun p : M => U 1 p) x) (X x)
      have hupdate :
          Function.update (vec2 (I := I) v (0 : TangentSpace I x)) (1 : Fin 2) W =
            vec2 (I := I) v W := by
        funext q
        fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update, W]
      rw [hupdate]
      exact hkerL W
    rw [h0, h1]
    simp
  rw [hlhs, hsum] at h
  simpa using h.symm



private theorem deriv_eval_zero_left_C1
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (X V : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (A : (p : M) -> TangentSpace I p)
    {x : M} {v : TangentSpace I x}
    (hA_at :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M => (⟨p, A p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x)
    (hA : A x = 0)
    (hV : V x = v)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0) :
    extDerivFun (I := I)
      (fun p : M => B p (vec2 (I := I) (A p) (V p))) x (X x) = 0 := by
  let U : Fin 2 -> (p : M) -> TangentSpace I p :=
    Fin.cons A (fun _ : Fin 1 => fun p : M => V p)
  have hV_at :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
    have htop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x :=
      V.contMDiff.contMDiffAt
    exact htop.of_le (by simp)
  have hU_at : ∀ a : Fin 2,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, U a p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
    intro a
    fin_cases a
    · simpa [U] using hA_at
    · simpa [U] using hV_at
  have hslots : (fun q : Fin 2 => U q x) =
      vec2 (I := I) (0 : TangentSpace I x) v := by
    funext q
    fin_cases q <;> simp [U, hA, hV, vec2, DifferentialGeometry.Integral.Connection.vec2]
  have h := TotalNabla0SRealizes.eval_C1_slots (I := I) hreal X U x hU_at
  rw [hslots] at h
  have hfun :
      (fun p : M => B p (fun a : Fin 2 => U a p)) =
        (fun p : M => B p (vec2 (I := I) (A p) (V p))) := by
    funext p
    congr
    funext q
    fin_cases q <;> simp [U, vec2, DifferentialGeometry.Integral.Connection.vec2]
  rw [hfun] at h
  have hlhs :
      nablaB x (Fin.cons (X x) (vec2 (I := I) (0 : TangentSpace I x) v)) = 0 := by
    exact (nablaB x).map_coord_zero (1 : Fin 3)
      (by
        change (vec2 (I := I) (0 : TangentSpace I x) v) (0 : Fin 2) = 0
        simp [vec2, DifferentialGeometry.Integral.Connection.vec2])
  have hsum :
      (∑ a : Fin 2,
        B x
          (Function.update (vec2 (I := I) (0 : TangentSpace I x) v) a
            ((cov (U a) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_two]
    have h0 :
        B x
          (Function.update (vec2 (I := I) (0 : TangentSpace I x) v) (0 : Fin 2)
            ((cov (U 0) x) (X x))) = 0 := by
      let W : TangentSpace I x := (cov (U 0) x) (X x)
      have hupdate :
          Function.update (vec2 (I := I) (0 : TangentSpace I x) v) (0 : Fin 2) W =
            vec2 (I := I) W v := by
        funext q
        fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update, W]
      rw [hupdate]
      exact hkerR W
    have h1 :
        B x
          (Function.update (vec2 (I := I) (0 : TangentSpace I x) v) (1 : Fin 2)
            ((cov (U 1) x) (X x))) = 0 := by
      let W : TangentSpace I x := (cov (U 1) x) (X x)
      have hupdate :
          Function.update (vec2 (I := I) (0 : TangentSpace I x) v) (1 : Fin 2) W =
            vec2 (I := I) (0 : TangentSpace I x) W := by
        funext q
        fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update, W]
      have hzero :
          B x (vec2 (I := I) (0 : TangentSpace I x) W) = 0 := by
        exact (B x).map_coord_zero (0 : Fin 2)
          (by simp [vec2, DifferentialGeometry.Integral.Connection.vec2])
      rw [hupdate]
      exact hzero
    rw [h0, h1]
    simp
  rw [hlhs, hsum] at h
  simpa using h.symm



private theorem deriv_eval_zero_right_C1
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (X V : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (A : (p : M) -> TangentSpace I p)
    {x : M} {v : TangentSpace I x}
    (hA_at :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M => (⟨p, A p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x)
    (hV : V x = v)
    (hA : A x = 0)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0) :
    extDerivFun (I := I)
      (fun p : M => B p (vec2 (I := I) (V p) (A p))) x (X x) = 0 := by
  let U : Fin 2 -> (p : M) -> TangentSpace I p :=
    Fin.cons (fun p : M => V p) (fun _ : Fin 1 => A)
  have hV_at :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
    have htop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x :=
      V.contMDiff.contMDiffAt
    exact htop.of_le (by simp)
  have hU_at : ∀ a : Fin 2,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, U a p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
    intro a
    fin_cases a
    · simpa [U] using hV_at
    · simpa [U] using hA_at
  have hslots : (fun q : Fin 2 => U q x) =
      vec2 (I := I) v (0 : TangentSpace I x) := by
    funext q
    fin_cases q <;> simp [U, hA, hV, vec2, DifferentialGeometry.Integral.Connection.vec2]
  have h := TotalNabla0SRealizes.eval_C1_slots (I := I) hreal X U x hU_at
  rw [hslots] at h
  have hfun :
      (fun p : M => B p (fun a : Fin 2 => U a p)) =
        (fun p : M => B p (vec2 (I := I) (V p) (A p))) := by
    funext p
    congr
    funext q
    fin_cases q <;> simp [U, vec2, DifferentialGeometry.Integral.Connection.vec2]
  rw [hfun] at h
  have hlhs :
      nablaB x (Fin.cons (X x) (vec2 (I := I) v (0 : TangentSpace I x))) = 0 := by
    exact (nablaB x).map_coord_zero (2 : Fin 3)
      (by
        change (vec2 (I := I) v (0 : TangentSpace I x)) (1 : Fin 2) = 0
        simp [vec2, DifferentialGeometry.Integral.Connection.vec2])
  have hsum :
      (∑ a : Fin 2,
        B x
          (Function.update (vec2 (I := I) v (0 : TangentSpace I x)) a
            ((cov (U a) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_two]
    have h0 :
        B x
          (Function.update (vec2 (I := I) v (0 : TangentSpace I x)) (0 : Fin 2)
            ((cov (U 0) x) (X x))) = 0 := by
      let W : TangentSpace I x := (cov (U 0) x) (X x)
      have hupdate :
          Function.update (vec2 (I := I) v (0 : TangentSpace I x)) (0 : Fin 2) W =
            vec2 (I := I) W (0 : TangentSpace I x) := by
        funext q
        fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update, W]
      have hzero :
          B x (vec2 (I := I) W (0 : TangentSpace I x)) = 0 := by
        exact (B x).map_coord_zero (1 : Fin 2)
          (by simp [vec2, DifferentialGeometry.Integral.Connection.vec2])
      rw [hupdate]
      exact hzero
    have h1 :
        B x
          (Function.update (vec2 (I := I) v (0 : TangentSpace I x)) (1 : Fin 2)
            ((cov (U 1) x) (X x))) = 0 := by
      let W : TangentSpace I x := (cov (U 1) x) (X x)
      have hupdate :
          Function.update (vec2 (I := I) v (0 : TangentSpace I x)) (1 : Fin 2) W =
            vec2 (I := I) v W := by
        funext q
        fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update, W]
      rw [hupdate]
      exact hkerL W
    rw [h0, h1]
    simp
  rw [hlhs, hsum] at h
  simpa using h.symm



theorem nabla2Eval_extDeriv
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaB nabla2B)
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : ∀ q : Fin 2, V q x = v)
    (hcovY : ((cov (fun p : M => Y p) x) (X x)) = 0)
    (hcovV :
      ∀ q : Fin 2, ((cov (fun p : M => V q p) x) (X x)) = 0) :
    nabla2B x (Fin.cons (X x) (Fin.cons (Y x) (vec2 (I := I) v v))) =
      extDerivFun (I := I)
        (fun p : M => nablaB p (Fin.cons (Y p) (fun q : Fin 2 => V q p)))
        x (X x) := by
  let W : Fin 3 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Fin.cons Y V
  have hslots :
      (fun q : Fin 3 => W q x) =
        Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
          (Y x) (vec2 (I := I) v v) := by
    funext q
    cases q using Fin.cases with
    | zero =>
        simp [W]
    | succ q =>
        simp [W, hV q, vec2, DifferentialGeometry.Integral.Connection.vec2, Fin.cons_succ]
  have h :=
    TotalNabla0SRealizes.eval_smooth_slots (I := I)
      hreal X W x
  rw [hslots] at h
  rw [h]
  have hsum :
      (∑ a : Fin 3,
        nablaB x
          (Function.update
            (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
              (Y x) (vec2 (I := I) v v))
            a ((cov (fun p : M => W a p) x) (X x)))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _ha
    have hz : ((cov (fun p : M => W a p) x) (X x)) = 0 := by
      cases a using Fin.cases with
      | zero =>
          simpa [W, Fin.cons_zero] using hcovY
      | succ a =>
          simpa [W, Fin.cons_succ] using hcovV a
    rw [hz]
    exact (nablaB x).map_update_zero
      (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
        (Y x) (vec2 (I := I) v v)) a
  have hfun :
      (fun p : M => nablaB p (fun a : Fin 3 => W a p)) =
        (fun p : M => nablaB p (Fin.cons (Y p) (fun q : Fin 2 => V q p))) := by
    funext p
    congr
    funext a
    cases a using Fin.cases with
    | zero =>
        simp [W, Fin.cons_zero]
    | succ a =>
        simp [W, Fin.cons_succ]
  rw [hfun, hsum]
  simp








private theorem nabla2Eval_extDeriv_oneSec_corr
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaB nabla2B)
    (X Y Vsec : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : Vsec x = v)
    (hcovV : ((cov (fun p : M => Vsec p) x) (X x)) = 0) :
    nabla2B x (Fin.cons (X x) (Fin.cons (Y x) (vec2 (I := I) v v))) =
      extDerivFun (I := I)
        (fun p : M => nablaB p (Fin.cons (Y p) (vec2 (I := I) (Vsec p) (Vsec p))))
        x (X x) -
      nablaB x
        (Fin.cons ((cov (fun p : M => Y p) x) (X x)) (vec2 (I := I) v v)) := by
  let W : Fin 3 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Fin.cons Y (fun _ : Fin 2 => Vsec)
  have hslots :
      (fun q : Fin 3 => W q x) =
        Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
          (Y x) (vec2 (I := I) v v) := by
    funext q
    cases q using Fin.cases with
    | zero =>
        simp [W]
    | succ q =>
        simp [W, hV, vec2, DifferentialGeometry.Integral.Connection.vec2, Fin.cons_succ]
  have h :=
    TotalNabla0SRealizes.eval_smooth_slots (I := I)
      hreal X W x
  rw [hslots] at h
  rw [h]
  have hsum :
      (∑ a : Fin 3,
        nablaB x
          (Function.update
            (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
              (Y x) (vec2 (I := I) v v))
            a ((cov (fun p : M => W a p) x) (X x)))) =
      nablaB x
        (Fin.cons ((cov (fun p : M => Y p) x) (X x)) (vec2 (I := I) v v)) := by
    rw [Fin.sum_univ_three]
    have h0 :
        nablaB x
          (Function.update
            (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
              (Y x) (vec2 (I := I) v v))
            0 ((cov (fun p : M => W 0 p) x) (X x))) =
        nablaB x
          (Fin.cons ((cov (fun p : M => Y p) x) (X x)) (vec2 (I := I) v v)) := by
      congr
      funext q
      cases q using Fin.cases with
      | zero =>
          simp [W, Function.update, Fin.cons_zero]
      | succ q =>
          simp [Function.update, Fin.cons_succ]
    have h1 :
        nablaB x
          (Function.update
            (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
              (Y x) (vec2 (I := I) v v))
            1 ((cov (fun p : M => W 1 p) x) (X x))) = 0 := by
      have hz : ((cov (fun p : M => W 1 p) x) (X x)) = 0 := by
        simpa [W, Fin.cons_succ] using hcovV
      rw [hz]
      exact (nablaB x).map_update_zero
        (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
          (Y x) (vec2 (I := I) v v)) 1
    have h2 :
        nablaB x
          (Function.update
            (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
              (Y x) (vec2 (I := I) v v))
            2 ((cov (fun p : M => W 2 p) x) (X x))) = 0 := by
      have hz : ((cov (fun p : M => W 2 p) x) (X x)) = 0 := by
        simpa [W, Fin.cons_succ] using hcovV
      rw [hz]
      exact (nablaB x).map_update_zero
        (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
          (Y x) (vec2 (I := I) v v)) 2
    rw [h0, h1, h2]
    simp
  have hfun :
      (fun p : M => nablaB p (fun a : Fin 3 => W a p)) =
        (fun p : M => nablaB p
          (Fin.cons (Y p) (vec2 (I := I) (Vsec p) (Vsec p)))) := by
    funext p
    congr
    funext a
    cases a using Fin.cases with
    | zero =>
        simp [W, Fin.cons_zero]
    | succ a =>
        simp [W, vec2_self_eq_const, Fin.cons_succ]
  rw [hfun, hsum]









private theorem nabla2Eval_extDeriv_oneSec_corr_phi
    [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4}
    (hreal1 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (hreal2 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaB nabla2B)
    (X Y Vsec : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : Vsec x = v)
    (hcovV : ((cov (fun p : M => Vsec p) x) (X x)) = 0)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0) :
    nabla2B x (Fin.cons (X x) (Fin.cons (Y x) (vec2 (I := I) v v))) =
      extDerivFun (I := I)
        (fun p : M => nablaB p (Fin.cons (Y p) (vec2 (I := I) (Vsec p) (Vsec p))))
        x (X x) -
      extDerivFun (I := I)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) x
        ((cov (fun p : M => Y p) x) (X x)) := by
  let A : TangentSpace I x := (cov (fun p : M => Y p) x) (X x)
  have hA :
      nablaB x (Fin.cons A (vec2 (I := I) v v)) =
        extDerivFun (I := I)
          (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) x A :=
    nablaEval_ker_tangent (I := I) (M := M) hreal1 Vsec hV hkerL hkerR A
  calc
    nabla2B x (Fin.cons (X x) (Fin.cons (Y x) (vec2 (I := I) v v)))
        =
      extDerivFun (I := I)
        (fun p : M => nablaB p (Fin.cons (Y p) (vec2 (I := I) (Vsec p) (Vsec p))))
        x (X x) -
      nablaB x
        (Fin.cons ((cov (fun p : M => Y p) x) (X x)) (vec2 (I := I) v v)) := by
          exact nabla2Eval_extDeriv_oneSec_corr (I := I) (M := M)
            hreal2 X Y Vsec hV hcovV
    _ =
      extDerivFun (I := I)
        (fun p : M => nablaB p (Fin.cons (Y p) (vec2 (I := I) (Vsec p) (Vsec p))))
        x (X x) -
      extDerivFun (I := I)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) x
        ((cov (fun p : M => Y p) x) (X x)) := by
          simpa [A] using congrArg
            (fun z : Real =>
              extDerivFun (I := I)
                (fun p : M =>
                  nablaB p (Fin.cons (Y p) (vec2 (I := I) (Vsec p) (Vsec p))))
                x (X x) - z)
            hA











private theorem nabla2Eval_extDeriv_oneSec_hess
    [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4}
    (hreal1 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (hreal2 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaB nabla2B)
    (X Y V : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : V x = v)
    (hcovVX : ((cov (fun p : M => V p) x) (X x)) = 0)
    (hcovVY : ((cov (fun p : M => V p) x) (Y x)) = 0)
    (hA_at :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, ((cov (fun q : M => V q) p) (Y p))⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0)
    (hdphi :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          extDerivFun (I := I)
            (fun q : M => B q (vec2 (I := I) (V q) (V q))) p (Y p)) x) :
    nabla2B x (Fin.cons (X x) (Fin.cons (Y x) (vec2 (I := I) v v))) =
      extDerivFun (I := I)
        (fun p : M =>
          extDerivFun (I := I)
            (fun q : M => B q (vec2 (I := I) (V q) (V q))) p (Y p))
        x (X x) -
      extDerivFun (I := I)
        (fun p : M => B p (vec2 (I := I) (V p) (V p))) x
        ((cov (fun p : M => Y p) x) (X x)) := by
  let phi : M -> Real := fun p => B p (vec2 (I := I) (V p) (V p))
  let A : (p : M) -> TangentSpace I p := fun p => ((cov (fun q : M => V q) p) (Y p))
  let dphiY : M -> Real := fun p => extDerivFun (I := I) phi p (Y p)
  let corrL : M -> Real := fun p => B p (vec2 (I := I) (A p) (V p))
  let corrR : M -> Real := fun p => B p (vec2 (I := I) (V p) (A p))
  have hV_at :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
    have htop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x :=
      V.contMDiff.contMDiffAt
    exact htop.of_le (by simp)
  have hA_at' :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M => (⟨p, A p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
    simpa [A] using hA_at
  have hcorrL :
      MDifferentiableAt I 𝓘(Real, Real) corrL x := by
    let Slots : Fin 2 -> (p : M) -> TangentSpace I p :=
      Fin.cons A (fun _ : Fin 1 => fun p : M => V p)
    have hSlots : ∀ a : Fin 2,
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, Slots a p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
      intro a
      fin_cases a
      · simpa [Slots] using hA_at'
      · simpa [Slots] using hV_at
    have hraw := tensor0SField_eval_C1_slots_mdiffAt
      (I := I) (M := M) B Slots x hSlots
    have hfun :
        (fun p : M => B p (fun a : Fin 2 => Slots a p)) = corrL := by
      funext p
      congr
      funext a
      fin_cases a <;> simp [Slots, vec2, DifferentialGeometry.Integral.Connection.vec2]
    rw [← hfun]
    exact hraw
  have hcorrR :
      MDifferentiableAt I 𝓘(Real, Real) corrR x := by
    let Slots : Fin 2 -> (p : M) -> TangentSpace I p :=
      Fin.cons (fun p : M => V p) (fun _ : Fin 1 => A)
    have hSlots : ∀ a : Fin 2,
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, Slots a p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
      intro a
      fin_cases a
      · simpa [Slots] using hV_at
      · simpa [Slots] using hA_at'
    have hraw := tensor0SField_eval_C1_slots_mdiffAt
      (I := I) (M := M) B Slots x hSlots
    have hfun :
        (fun p : M => B p (fun a : Fin 2 => Slots a p)) = corrR := by
      funext p
      congr
      funext a
      fin_cases a <;> simp [Slots, vec2, DifferentialGeometry.Integral.Connection.vec2]
    rw [← hfun]
    exact hraw
  have hleft_fun :
      (fun p : M =>
        nablaB p (Fin.cons (Y p) (vec2 (I := I) (V p) (V p)))) =
        (fun p : M => dphiY p - corrL p - corrR p) := by
    funext p
    let Slots : Fin 2 ->
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      fun _ => V
    have hprod :=
      TotalNabla0SRealizes.eval_smooth_slots (I := I) hreal1 Y Slots p
    have hslots : (fun a : Fin 2 => Slots a p) =
        vec2 (I := I) (V p) (V p) := by
      funext a
      fin_cases a <;> simp [Slots, vec2, DifferentialGeometry.Integral.Connection.vec2]
    rw [hslots] at hprod
    have hfun :
        (fun q : M => B q (fun a : Fin 2 => Slots a q)) = phi := by
      funext q
      simp [phi, Slots, vec2_self_eq_const]
    rw [hfun] at hprod
    have hsum :
        (∑ a : Fin 2,
          B p
            (Function.update (vec2 (I := I) (V p) (V p)) a
              ((cov (fun q : M => Slots a q) p) (Y p)))) =
          corrL p + corrR p := by
      rw [Fin.sum_univ_two]
      have h0 :
          B p
            (Function.update (vec2 (I := I) (V p) (V p)) (0 : Fin 2)
              ((cov (fun q : M => Slots 0 q) p) (Y p))) =
            corrL p := by
        have hcov :
            ((cov (fun q : M => Slots 0 q) p) (Y p)) = A p := by
          rfl
        rw [hcov]
        congr
        funext a
        fin_cases a <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update]
      have h1 :
          B p
            (Function.update (vec2 (I := I) (V p) (V p)) (1 : Fin 2)
              ((cov (fun q : M => Slots 1 q) p) (Y p))) =
            corrR p := by
        have hcov :
            ((cov (fun q : M => Slots 1 q) p) (Y p)) = A p := by
          rfl
        rw [hcov]
        congr
        funext a
        fin_cases a <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update]
      rw [h0, h1]
    rw [hprod, hsum]
    ring
  have hleft_deriv :
      extDerivFun (I := I)
        (fun p : M =>
          nablaB p (Fin.cons (Y p) (vec2 (I := I) (V p) (V p)))) x (X x) =
      extDerivFun (I := I) dphiY x (X x) := by
    rw [hleft_fun]
    have hsub1 :
        MDifferentiableAt I 𝓘(Real, Real) (fun p : M => dphiY p - corrL p) x :=
      hdphi.sub hcorrL
    rw [extDerivFun_sub_at (I := I) (x := x) (v := X x) hsub1 hcorrR]
    rw [extDerivFun_sub_at (I := I) (x := x) (v := X x) hdphi hcorrL]
    have hA0 : A x = 0 := by
      simp [A, hcovVY]
    have hcorrL_zero :
        extDerivFun (I := I) corrL x (X x) = 0 := by
      simpa [corrL] using
        deriv_eval_zero_left_C1 (I := I) (M := M)
          hreal1 X V A hA_at' hA0 hV hkerR
    have hcorrR_zero :
        extDerivFun (I := I) corrR x (X x) = 0 := by
      simpa [corrR] using
        deriv_eval_zero_right_C1 (I := I) (M := M)
          hreal1 X V A hA_at' hV hA0 hkerL
    rw [hcorrL_zero, hcorrR_zero]
    ring
  have hcorr_phi :=
    nabla2Eval_extDeriv_oneSec_corr_phi (I := I) (M := M)
      hreal1 hreal2 X Y V hV hcovVX hkerL hkerR
  rw [hleft_deriv] at hcorr_phi
  simpa [phi, dphiY] using hcorr_phi



private theorem nabla2Eval_hess
    [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4}
    {du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1}
    {Hess : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y}
    (hreal1 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (hreal2 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaB nabla2B)
    (X Y V : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : V x = v)
    (hcovVX : ((cov (fun p : M => V p) x) (X x)) = 0)
    (hcovVY : ((cov (fun p : M => V p) x) (Y x)) = 0)
    (hA_at :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, ((cov (fun q : M => V q) p) (Y p))⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0)
    (hdu :
      DuFieldRealizes (I := I)
        (fun p : M => B p (vec2 (I := I) (V p) (V p))) du)
    (hHess :
      HessianRealizesNablaDuAt (I := I) cov du Hess x)
    (hdphi :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          extDerivFun (I := I)
            (fun q : M => B q (vec2 (I := I) (V q) (V q))) p (Y p)) x) :
    nabla2B x (Fin.cons (X x) (Fin.cons (Y x) (vec2 (I := I) v v))) =
      Hess x (vec2 (I := I) (X x) (Y x)) := by
  let phi : M -> Real := fun p => B p (vec2 (I := I) (V p) (V p))
  have hprod :
      nabla2B x (Fin.cons (X x) (Fin.cons (Y x) (vec2 (I := I) v v))) =
        extDerivFun (I := I)
          (fun p : M => extDerivFun (I := I) phi p (Y p)) x (X x) -
        extDerivFun (I := I) phi x ((cov (fun p : M => Y p) x) (X x)) := by
    simpa [phi] using
      nabla2Eval_extDeriv_oneSec_hess (I := I) (M := M)
        hreal1 hreal2 X Y V hV hcovVX hcovVY hA_at hkerL hkerR hdphi
  have hnabla_eval :
      nablaDuAt (I := I) cov X du x (fun _ : Fin 1 => Y x) =
        extDerivFun (I := I) (fun y : M => du y (fun _ : Fin 1 => Y y))
          x (X x) -
        du x (fun _ : Fin 1 => (cov (fun y : M => Y y) x) (X x)) := by
    simpa [nablaDuAt] using
      DifferentialGeometry.Tensor.Coordinates.nabla0SFun_one_eval_smooth_slots (I := I) cov X Y du x
  have hdu_fun :
      (fun y : M => du y (fun _ : Fin 1 => Y y)) =
        (fun y : M => extDerivFun (I := I) phi y (Y y)) := by
    funext y
    rw [hdu y]
    exact differential1FormFun_apply_eq_extDerivFun (I := I) phi y (Y y)
  have hdu_corr :
      du x (fun _ : Fin 1 => (cov (fun y : M => Y y) x) (X x)) =
        extDerivFun (I := I) phi x ((cov (fun y : M => Y y) x) (X x)) := by
    rw [hdu x]
    exact differential1FormFun_apply_eq_extDerivFun
      (I := I) phi x ((cov (fun y : M => Y y) x) (X x))
  have hnabla_phi :
      nablaDuAt (I := I) cov X du x (fun _ : Fin 1 => Y x) =
        extDerivFun (I := I) (fun y : M => extDerivFun (I := I) phi y (Y y))
          x (X x) -
        extDerivFun (I := I) phi x ((cov (fun y : M => Y y) x) (X x)) := by
    rw [hnabla_eval, hdu_fun, hdu_corr]
  calc
    nabla2B x (Fin.cons (X x) (Fin.cons (Y x) (vec2 (I := I) v v)))
        =
      extDerivFun (I := I) (fun y : M => extDerivFun (I := I) phi y (Y y))
        x (X x) -
      extDerivFun (I := I) phi x ((cov (fun y : M => Y y) x) (X x)) := hprod
    _ = nablaDuAt (I := I) cov X du x (fun _ : Fin 1 => Y x) := hnabla_phi.symm
    _ = Hess x (vec2 (I := I) (X x) (Y x)) := (hHess X (Y x)).symm


theorem nabla2Eval_hess_slots
    [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4}
    {du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1}
    {Hess : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y}
    (hreal1 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (hreal2 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaB nabla2B)
    (V : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : V x = v)
    (hcovV :
      ∀ W : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _),
        ((cov (fun p : M => V p) x) (W x)) = 0)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0)
    (hdu :
      DuFieldRealizes (I := I)
        (fun p : M => B p (vec2 (I := I) (V p) (V p))) du)
    (hHess :
      HessianRealizesNablaDuAt (I := I) cov du Hess x)
    (hAreg :
      ∀ Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _),
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, ((cov (fun q : M => V q) p) (Y p))⟩ :
              TotalSpace E (TangentSpace I : M -> Type _))) x) :
    ∀ U W : TangentSpace I x,
      nabla2B x (metricTraceInput (I := I) U W (vec2 (I := I) v v)) =
        Hess x (vec2 (I := I) U W) := by
  let phi : M -> Real := fun p => B p (vec2 (I := I) (V p) (V p))
  have hphi :
      ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) phi := by
    let Slots : Fin 2 ->
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      fun _ => V
    have hraw := TensorMultilinear.contMDiff_tensor0SField_apply
      (I := I) (M := M) B Slots
    simpa [phi, Slots, vec2_self_eq_const] using hraw
  intro U W
  obtain ⟨Xsec, hXsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x U
  obtain ⟨Ysec, hYsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x W
  have hA_at := hAreg Ysec
  have hdphi :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          extDerivFun (I := I)
            (fun q : M => B q (vec2 (I := I) (V q) (V q))) p (Ysec p)) x := by
    simpa [phi] using dphi_apply_mdiffAt (I := I) phi hphi Ysec x
  have hcalc :=
    nabla2Eval_hess (I := I) (M := M)
      hreal1 hreal2 Xsec Ysec V hV (hcovV Xsec) (hcovV Ysec)
      hA_at hkerL hkerR hdu hHess hdphi
  have hinput :
      metricTraceInput (I := I) U W (vec2 (I := I) v v) =
        Fin.cons (Xsec x) (Fin.cons (Ysec x) (vec2 (I := I) v v)) := by
    funext q
    cases q using Fin.cases with
    | zero =>
        change U = Xsec x
        exact hXsec.symm
    | succ q =>
        cases q using Fin.cases with
        | zero =>
            change W = Ysec x
            exact hYsec.symm
        | succ q =>
            cases q using Fin.cases with
            | zero =>
                rfl
            | succ q =>
                fin_cases q
                rfl
  calc
    nabla2B x (metricTraceInput (I := I) U W (vec2 (I := I) v v))
        =
      nabla2B x (Fin.cons (Xsec x) (Fin.cons (Ysec x) (vec2 (I := I) v v))) := by
        rw [hinput]
    _ = Hess x (vec2 (I := I) (Xsec x) (Ysec x)) := hcalc
    _ = Hess x (vec2 (I := I) U W) := by
        rw [hXsec, hYsec]






theorem nablaEval_zero
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : ∀ q : Fin 2, V q x = v)
    (hphi :
      extDerivFun (I := I) (fun p : M => B p (fun q : Fin 2 => V q p))
        x (X x) = 0)
    (hcovV :
      ∀ q : Fin 2, ((cov (fun p : M => V q p) x) (X x)) = 0) :
    nablaB x (Fin.cons (X x) (vec2 (I := I) v v)) = 0 := by
  rw [nablaEval_extDeriv (I := I) (M := M) hreal X V hV hcovV]
  exact hphi




omit [IsManifold I 2 M] in
theorem firstNullLocalMin
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hV : ∀ q : Fin 2, V q d.x1 = d.v)
    (hB :
      ∀ p : M,
        B p (fun q : Fin 2 => V q p) =
          tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
            d.t1 p (V 0 p) (V 0 p)) :
    IsLocalMin (fun p : M => B p (fun q : Fin 2 => V q p)) d.x1 := by
  unfold IsLocalMin IsMinFilter
  filter_upwards [] with p
  have hbase :
      B d.x1 (fun q : Fin 2 => V q d.x1) = 0 := by
    rw [hB d.x1, hV 0]
    exact d.null
  have hp :
      0 ≤ B p (fun q : Fin 2 => V q p) := by
    rw [hB p]
    exact d.nonnegative_until d.t1
      ⟨le_of_lt d.t1_mem.1, le_rfl⟩ p (V 0 p)
  rw [hbase]
  exact hp

end

end DifferentialGeometry.Integral.Connection
