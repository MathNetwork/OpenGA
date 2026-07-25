import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Product

set_option autoImplicit false
set_option linter.style.longLine false









namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem totalNabla0SRealizes_eval_point_vector_smooth_slots
    [T2Space M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {s : Nat} {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov A nablaA)
    {x : M} (W : TangentSpace I x)
    (V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    nablaA x (Fin.cons W (fun q : Fin s => V q x)) =
      extDerivFun (I := I)
        (fun y : M => A y (fun q : Fin s => V q y)) x W -
      ∑ q : Fin s,
        A x
          (Function.update (fun r : Fin s => V r x) q
            ((cov (fun y : M => V q y) x) W)) := by
  obtain ⟨Wsec, hWsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x W
  have h0 := TotalNabla0SRealizes.eval_smooth_slots
    (I := I) hA Wsec V x
  simpa [hWsec] using h0








theorem cotangentSharp_cov_eq_sharp_curry_of_mdiffAt
    [T2Space M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (alpha : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (nablaAlpha : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (hAlpha : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 cov alpha nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M)
    (hSharp : MDiffAt
      (T% (fun y : M => cotangentSharp_gen (I := I) g y (alpha y))) x) :
    cov (fun y : M => cotangentSharp_gen (I := I) g y (alpha y)) x (X x) =
      cotangentSharp_gen (I := I) g x
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
          (nablaAlpha x) (X x)) := by
  classical
  let Ysharp : (y : M) -> TangentSpace I y :=
    fun y => cotangentSharp_gen (I := I) g y (alpha y)
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x)))
      Real (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  apply eq_of_inner_basis_eq_gen (I := I) g x basis
  intro i
  obtain ⟨Zsec, hZsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (basis i)
  have hX : MDiffAt (T% (fun y : M => X y)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hZ : MDiffAt (T% (fun y : M => Zsec y)) x :=
    Zsec.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hmc_apply :=
    DifferentialGeometry.Integral.Connection.metric_compatible_apply (I := I) hmc
      (fun y : M => X y) Ysharp (fun y : M => Zsec y) hX hSharp hZ
  have hpair_fun :
      (fun y : M => g.inner y (Ysharp y) (Zsec y)) =
        fun y : M => alpha y (fun _ : Fin 1 => Zsec y) := by
    funext y
    simp [Ysharp, cotangentSharp_inner_gen, cotangentToDual_apply_gen]
  have hderiv_pair :
      mfderiv I 𝓘(Real, Real)
          (fun y : M => g.inner y (Ysharp y) (Zsec y)) x (X x) =
        extDerivFun (I := I)
          (fun y : M => alpha y (fun _ : Fin 1 => Zsec y)) x (X x) := by
    rw [hpair_fun]
    exact (DifferentialGeometry.extDerivFun_real_eq_mfderiv (I := I)
      (fun y : M => alpha y (fun _ : Fin 1 => Zsec y)) x (X x)).symm
  have hnabla_eval :=
    totalNabla0SRealizes_eval_point_vector_smooth_slots (I := I)
      hAlpha (X x) (fun _ : Fin 1 => Zsec)
  have hnabla_pair :
      g.inner x
          (cotangentSharp_gen (I := I) g x
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
              (nablaAlpha x) (X x))) (Zsec x) =
        extDerivFun (I := I)
          (fun y : M => alpha y (fun _ : Fin 1 => Zsec y)) x (X x) -
          alpha x (fun _ : Fin 1 => (cov (fun y : M => Zsec y) x) (X x)) := by
    rw [cotangentSharp_inner_gen, cotangentToDual_apply_gen]
    rw [tensor0S_curry_apply_cons]
    have hupdate :
        Function.update (fun r : Fin 1 => Zsec x) 0
            ((cov (fun y : M => Zsec y) x) (X x)) =
          fun _ : Fin 1 => (cov (fun y : M => Zsec y) x) (X x) := by
      funext q
      fin_cases q
      simp
    simpa [hupdate] using hnabla_eval
  calc
    g.inner x
        (cov (fun y : M => cotangentSharp_gen (I := I) g y (alpha y)) x (X x))
        (basis i)
        = g.inner x
            (cov Ysharp x (X x)) (Zsec x) := by
          simp [Ysharp, hZsec]
    _ = extDerivFun (I := I)
          (fun y : M => alpha y (fun _ : Fin 1 => Zsec y)) x (X x) -
          alpha x (fun _ : Fin 1 => (cov (fun y : M => Zsec y) x) (X x)) := by
          have hpair_cov :
              g.inner x (cov Ysharp x (X x)) (Zsec x) =
                extDerivFun (I := I)
                  (fun y : M => alpha y (fun _ : Fin 1 => Zsec y)) x (X x) -
                  g.inner x (Ysharp x)
                    ((cov (fun y : M => Zsec y) x) (X x)) := by
            let a := g.inner x (cov Ysharp x (X x)) (Zsec x)
            let b := g.inner x (Ysharp x)
              ((cov (fun y : M => Zsec y) x) (X x))
            let d := mfderiv I 𝓘(Real, Real)
              (fun y : M => g.inner y (Ysharp y) (Zsec y)) x (X x)
            let e := extDerivFun (I := I)
              (fun y : M => alpha y (fun _ : Fin 1 => Zsec y)) x (X x)
            change a = e - b
            have hs : d = a + b := by
              simpa [a, b, d] using hmc_apply
            have hd : d = e := by
              simpa [d, e] using hderiv_pair
            have hsum_eq : a + b = e := hs.symm.trans hd
            calc
              a = a + b - b := by ring
              _ = e - b := by rw [hsum_eq]
          rw [hpair_cov]
          rw [show
            g.inner x (Ysharp x) ((cov (fun y : M => Zsec y) x) (X x)) =
              alpha x (fun _ : Fin 1 => (cov (fun y : M => Zsec y) x) (X x)) by
                simp [Ysharp, cotangentSharp_inner_gen, cotangentToDual_apply_gen]]
    _ = g.inner x
          (cotangentSharp_gen (I := I) g x
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
              (nablaAlpha x) (X x))) (Zsec x) := by
          exact hnabla_pair.symm
    _ = g.inner x
          (cotangentSharp_gen (I := I) g x
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
              (nablaAlpha x) (X x))) (basis i) := by
          simp [hZsec]

private theorem cotangentInner_metricCompatible_extDerivFun_of_sharp_mdiffAt
    [T2Space M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (alpha beta : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1)
    (nablaAlpha nablaBeta :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2)
    (hAlpha : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 cov alpha nablaAlpha)
    (hBeta : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 cov beta nablaBeta)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M)
    (hSharpAlpha : MDiffAt
      (T% (fun y : M => cotangentSharp_gen (I := I) g y (alpha y))) x)
    (hSharpBeta : MDiffAt
      (T% (fun y : M => cotangentSharp_gen (I := I) g y (beta y))) x) :
    extDerivFun (I := I)
        (fun y : M => cotangentInner_gen (I := I) g y (alpha y) (beta y))
        x (X x) =
      cotangentInner_gen (I := I) g x
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
          (nablaAlpha x) (X x)) (beta x) +
        cotangentInner_gen (I := I) g x (alpha x)
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
            (nablaBeta x) (X x)) := by
  let Asharp : (y : M) -> TangentSpace I y :=
    fun y => cotangentSharp_gen (I := I) g y (alpha y)
  let Bsharp : (y : M) -> TangentSpace I y :=
    fun y => cotangentSharp_gen (I := I) g y (beta y)
  have hX : MDiffAt (T% (fun y : M => X y)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hmc_apply :=
    DifferentialGeometry.Integral.Connection.metric_compatible_apply (I := I) hmc
      (fun y : M => X y) Asharp Bsharp hX (by simpa [Asharp] using hSharpAlpha)
      (by simpa [Bsharp] using hSharpBeta)
  have hcovA :
      cov Asharp x (X x) =
        cotangentSharp_gen (I := I) g x
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
            (nablaAlpha x) (X x)) := by
    simpa [Asharp] using
      cotangentSharp_cov_eq_sharp_curry_of_mdiffAt (I := I)
        cov g hmc alpha nablaAlpha hAlpha X x hSharpAlpha
  have hcovB :
      cov Bsharp x (X x) =
        cotangentSharp_gen (I := I) g x
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
            (nablaBeta x) (X x)) := by
    simpa [Bsharp] using
      cotangentSharp_cov_eq_sharp_curry_of_mdiffAt (I := I)
        cov g hmc beta nablaBeta hBeta X x hSharpBeta
  rw [DifferentialGeometry.extDerivFun_real_eq_mfderiv]
  change
    mfderiv I 𝓘(Real, Real)
        (fun y : M => g.inner y (Asharp y) (Bsharp y)) x (X x) =
      _
  rw [hmc_apply]
  rw [hcovA, hcovB]
  rfl


theorem inner0S_two_mdiff
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x : M) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x := by
  classical
  let Idx : Type _ := DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
  let slots : Idx -> Idx -> Fin 2 -> Idx :=
    fun i j q => if q = 0 then i else j
  let U : M -> Idx -> Idx -> Real :=
    fun y i j =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x i j (extChartAt I x y)
  let Ac : M -> Idx -> Idx -> Real :=
    fun y i j => A y (fun q : Fin 2 => if q = 0 then frame i y else frame j y)
  let Bc : M -> Idx -> Idx -> Real :=
    fun y i j => B y (fun q : Fin 2 => if q = 0 then frame i y else frame j y)
  have hx : x ∈ DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) x
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)
  have hUmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => U y i j) x := by
    intro i j
    simpa [U, Idx] using
      DifferentialGeometry.Tensor.Coordinates.gInvComp_mdiffAt (I := I) g x i j
  have hAmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => Ac y i j) x := by
    intro i j
    have h := DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) (𝕜 := Real) A x (slots i j)
    have hfun :
        (fun y : M => A y
          (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
            (slots i j a) y)) =
          fun y : M => Ac y i j := by
      funext y
      exact congrArg (fun f : Fin 2 -> TangentSpace I y => A y f)
        (fin2_apply_ite (fun r : Idx => frame r y) i j)
    exact hfun ▸ h.mdifferentiableAt (by simp)
  have hBmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => Bc y i j) x := by
    intro i j
    have h := DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) (𝕜 := Real) B x (slots i j)
    have hfun :
        (fun y : M => B y
          (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
            (slots i j a) y)) =
          fun y : M => Bc y i j := by
      funext y
      exact congrArg (fun f : Fin 2 -> TangentSpace I y => B y f)
        (fin2_apply_ite (fun r : Idx => frame r y) i j)
    exact hfun ▸ h.mdifferentiableAt (by simp)
  have hlocal :
      (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) =ᶠ[𝓝 x]
        fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U y i k * U y j l * Ac y i j * Bc y k l := by
    filter_upwards
      [(DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open (I := I) x).mem_nhds hx]
      with y hy
    have h := inner0S_two_eq_coord (I := I) g y
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x hy)
      (U y) (DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) g x hy)
      (A y) (B y)
    simpa [U, Ac, Bc, frame, slots,
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply] using h
  have hsum :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U y i k * U y j l * Ac y i j * Bc y k l) x := by
    have hraw : MDifferentiableAt I 𝓘(Real, Real)
        (∑ i : Idx, fun y : M => ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U y i k * U y j l * Ac y i j * Bc y k l) x := by
      refine MDifferentiableAt.sum (𝕜 := Real) (I := I)
        (t := (Finset.univ : Finset Idx)) ?_
      intro i _
      have hraw_j : MDifferentiableAt I 𝓘(Real, Real)
          (∑ j : Idx, fun y : M => ∑ k : Idx, ∑ l : Idx,
            U y i k * U y j l * Ac y i j * Bc y k l) x := by
        refine MDifferentiableAt.sum (𝕜 := Real) (I := I)
          (t := (Finset.univ : Finset Idx)) ?_
        intro j _
        have hraw_k : MDifferentiableAt I 𝓘(Real, Real)
            (∑ k : Idx, fun y : M => ∑ l : Idx,
              U y i k * U y j l * Ac y i j * Bc y k l) x := by
          refine MDifferentiableAt.sum (𝕜 := Real) (I := I)
            (t := (Finset.univ : Finset Idx)) ?_
          intro k _
          have hraw_l : MDifferentiableAt I 𝓘(Real, Real)
              (∑ l : Idx, fun y : M =>
                U y i k * U y j l * Ac y i j * Bc y k l) x := by
            refine MDifferentiableAt.sum (𝕜 := Real) (I := I)
              (t := (Finset.univ : Finset Idx)) ?_
            intro l _
            exact (((hUmdiff i k).mul (hUmdiff j l)).mul (hAmdiff i j)).mul
              (hBmdiff k l)
          exact hraw_l.congr_of_eventuallyEq
            (by filter_upwards with y; simp [Finset.sum_apply])
        exact hraw_k.congr_of_eventuallyEq
          (by filter_upwards with y; simp [Finset.sum_apply])
      exact hraw_j.congr_of_eventuallyEq
        (by filter_upwards with y; simp [Finset.sum_apply])
    exact hraw.congr_of_eventuallyEq
      (by filter_upwards with y; simp [Finset.sum_apply])
  exact hsum.congr_of_eventuallyEq hlocal





theorem inner0S_two_nabla
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
      inner0S (I := I) g x 2
        (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X A x) (B x) +
        inner0S (I := I) g x 2 (A x)
          (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X B x) := by
  classical
  let Idx : Type _ := DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
  let hframe : IsLocalFrameOn I E 1 frame
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x
  let slots : Idx -> Idx -> Fin 2 -> Idx :=
    fun i j q => if q = 0 then i else j
  let U : M -> Idx -> Idx -> Real :=
    fun y i j =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x i j (extChartAt I x y)
  let Ac : M -> Idx -> Idx -> Real :=
    fun y i j => A y (fun q : Fin 2 => if q = 0 then frame i y else frame j y)
  let Bc : M -> Idx -> Idx -> Real :=
    fun y i j => B y (fun q : Fin 2 => if q = 0 then frame i y else frame j y)
  let DA : Idx -> Idx -> Real :=
    fun i j => extDerivFun (I := I) (fun y : M => Ac y i j) x (X x)
  let DB : Idx -> Idx -> Real :=
    fun i j => extDerivFun (I := I) (fun y : M => Bc y i j) x (X x)
  let DU : Idx -> Idx -> Real :=
    fun i j => extDerivFun (I := I) (fun y : M => U y i j) x (X x)
  let Γ : Idx -> Idx -> Real :=
    fun i j =>
      DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov frame hframe x (X x) i j
  let NA : Idx -> Idx -> Real :=
    fun i j =>
      (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X A x) (fun q : Fin 2 => if q = 0 then frame i x else frame j x)
  let NB : Idx -> Idx -> Real :=
    fun i j =>
      (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X B x) (fun q : Fin 2 => if q = 0 then frame i x else frame j x)
  have hx : x ∈ DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) x
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)
  have hUmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => U y i j) x := by
    intro i j
    simpa [U, Idx] using
      DifferentialGeometry.Tensor.Coordinates.gInvComp_mdiffAt (I := I) g x i j
  have hAmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => Ac y i j) x := by
    intro i j
    have h := DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) (𝕜 := Real) A x (slots i j)
    have hfun :
        (fun y : M => A y
          (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
            (slots i j a) y)) =
          fun y : M => Ac y i j := by
      funext y
      exact congrArg (fun f : Fin 2 -> TangentSpace I y => A y f)
        (fin2_apply_ite (fun r : Idx => frame r y) i j)
    exact hfun ▸ h.mdifferentiableAt (by simp)
  have hBmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => Bc y i j) x := by
    intro i j
    have h := DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) (𝕜 := Real) B x (slots i j)
    have hfun :
        (fun y : M => B y
          (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
            (slots i j a) y)) =
          fun y : M => Bc y i j := by
      funext y
      exact congrArg (fun f : Fin 2 -> TangentSpace I y => B y f)
        (fin2_apply_ite (fun r : Idx => frame r y) i j)
    exact hfun ▸ h.mdifferentiableAt (by simp)
  have hlocal :
      (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) =ᶠ[𝓝 x]
        fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U y i k * U y j l * Ac y i j * Bc y k l := by
    filter_upwards
      [(DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open (I := I) x).mem_nhds hx]
      with y hy
    have h := inner0S_two_eq_coord (I := I) g y
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x hy)
      (U y) (DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) g x hy)
      (A y) (B y)
    simpa [U, Ac, Bc, frame, slots,
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply] using h
  have hDU : ∀ p q : Idx,
      DU p q =
        - ((∑ a : Idx, Γ a p * U x a q) + (∑ a : Idx, Γ a q * U x p a)) := by
    intro p q
    have hzero := DifferentialGeometry.Tensor.Coordinates.gInvCovZeroAt
      (I := I) g cov X hmc x p q
    unfold DifferentialGeometry.Tensor.Coordinates.inverseMetricCovDerivForMetricCompAlongInFrame at hzero
    have hzero' :
        DU p q +
          (∑ a : Idx, Γ a p * U x a q) +
          (∑ a : Idx, Γ a q * U x p a) = 0 := by
      simpa [DU, U, Γ, frame, hframe, Idx] using hzero
    linarith
  have hDA_coord (p q : Idx) :
      DA p q =
        DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I)
          (fun y : M => X y) x (fun y : M => A y) (slots p q) := by
    have hfun :
        (fun y : M => Ac y p q) =
          fun y : M => A y
            (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
              (slots p q a) y) := by
      funext y
      exact (congrArg (fun f : Fin 2 -> TangentSpace I y => A y f)
        (fin2_apply_ite (fun r : Idx => frame r y) p q)).symm
    calc
      DA p q =
          extDerivFun (I := I) (fun y : M => Ac y p q) x (X x) := rfl
      _ =
          extDerivFun (I := I)
            (fun y : M => A y
              (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (slots p q a) y)) x (X x) := by
            rw [hfun]
      _ =
          DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I)
            (fun y : M => X y) x (fun y : M => A y) (slots p q) := by
            simp [DifferentialGeometry.extDerivFun_real_eq_mfderiv,
              DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt]
  have hDB_coord (p q : Idx) :
      DB p q =
        DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I)
          (fun y : M => X y) x (fun y : M => B y) (slots p q) := by
    have hfun :
        (fun y : M => Bc y p q) =
          fun y : M => B y
            (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
              (slots p q a) y) := by
      funext y
      exact (congrArg (fun f : Fin 2 -> TangentSpace I y => B y f)
        (fin2_apply_ite (fun r : Idx => frame r y) p q)).symm
    calc
      DB p q =
          extDerivFun (I := I) (fun y : M => Bc y p q) x (X x) := rfl
      _ =
          extDerivFun (I := I)
            (fun y : M => B y
              (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (slots p q a) y)) x (X x) := by
            rw [hfun]
      _ =
          DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I)
            (fun y : M => X y) x (fun y : M => B y) (slots p q) := by
            simp [DifferentialGeometry.extDerivFun_real_eq_mfderiv,
              DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt]
  have hNA : ∀ p q : Idx,
      NA p q =
        DA p q - (∑ a : Idx, Γ p a * Ac x a q) -
          (∑ a : Idx, Γ q a * Ac x p a) := by
    intro p q
    have hcoord := DifferentialGeometry.Tensor.Coordinates.nabla0SFun_two_eval_coordFrame
      (I := I) cov X A x
      (DifferentialGeometry.Tensor.Coordinates.modelDeriv_eq_coordDeriv0SAt (I := I) X x A)
      p q
    have hs1 :
        (∑ a : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
              x (X x) p a *
            A x (fun r : Fin 2 =>
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then a else q) x)) =
          ∑ a : Idx, Γ p a * Ac x a q := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hslot :
          (fun r : Fin 2 =>
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then a else q) x) =
            (fun r : Fin 2 => if r = 0 then frame a x else frame q x) :=
        fin2_apply_ite (fun r : Idx => frame r x) a q
      rw [hslot]
    have hs2 :
        (∑ a : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
              x (X x) q a *
            A x (fun r : Fin 2 =>
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then p else a) x)) =
          ∑ a : Idx, Γ q a * Ac x p a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hslot :
          (fun r : Fin 2 =>
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then p else a) x) =
            (fun r : Fin 2 => if r = 0 then frame p x else frame a x) :=
        fin2_apply_ite (fun r : Idx => frame r x) p a
      rw [hslot]
    have hcoord' :
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X A x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x) =
          DA p q - (∑ a : Idx, Γ p a * Ac x a q) -
            (∑ a : Idx, Γ q a * Ac x p a) := by
      calc
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X A x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x)
            =
          (DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I)
              (fun y : M => X y) x (fun y : M => A y) (slots p q) -
              ∑ a : Idx,
                DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
                    x (X x) p a *
                  A x (fun r : Fin 2 =>
                    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                      (if r = 0 then a else q) x)) -
              ∑ a : Idx,
                DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
                    x (X x) q a *
                  A x (fun r : Fin 2 =>
                    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                      (if r = 0 then p else a) x) := by
            simpa [frame, slots] using hcoord
        _ = DA p q - (∑ a : Idx, Γ p a * Ac x a q) -
            (∑ a : Idx, Γ q a * Ac x p a) := by
            rw [← hDA_coord p q, hs1, hs2]
    simpa [NA] using hcoord'
  have hNB : ∀ p q : Idx,
      NB p q =
        DB p q - (∑ a : Idx, Γ p a * Bc x a q) -
          (∑ a : Idx, Γ q a * Bc x p a) := by
    intro p q
    have hcoord := DifferentialGeometry.Tensor.Coordinates.nabla0SFun_two_eval_coordFrame
      (I := I) cov X B x
      (DifferentialGeometry.Tensor.Coordinates.modelDeriv_eq_coordDeriv0SAt (I := I) X x B)
      p q
    have hs1 :
        (∑ a : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
              x (X x) p a *
            B x (fun r : Fin 2 =>
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then a else q) x)) =
          ∑ a : Idx, Γ p a * Bc x a q := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hslot :
          (fun r : Fin 2 =>
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then a else q) x) =
            (fun r : Fin 2 => if r = 0 then frame a x else frame q x) :=
        fin2_apply_ite (fun r : Idx => frame r x) a q
      rw [hslot]
    have hs2 :
        (∑ a : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
              x (X x) q a *
            B x (fun r : Fin 2 =>
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then p else a) x)) =
          ∑ a : Idx, Γ q a * Bc x p a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hslot :
          (fun r : Fin 2 =>
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then p else a) x) =
            (fun r : Fin 2 => if r = 0 then frame p x else frame a x) :=
        fin2_apply_ite (fun r : Idx => frame r x) p a
      rw [hslot]
    have hcoord' :
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X B x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x) =
          DB p q - (∑ a : Idx, Γ p a * Bc x a q) -
            (∑ a : Idx, Γ q a * Bc x p a) := by
      calc
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X B x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x)
            =
          (DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I)
              (fun y : M => X y) x (fun y : M => B y) (slots p q) -
              ∑ a : Idx,
                DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
                    x (X x) p a *
                  B x (fun r : Fin 2 =>
                    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                      (if r = 0 then a else q) x)) -
              ∑ a : Idx,
                DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
                    x (X x) q a *
                  B x (fun r : Fin 2 =>
                    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                      (if r = 0 then p else a) x) := by
            simpa [frame, slots] using hcoord
        _ = DB p q - (∑ a : Idx, Γ p a * Bc x a q) -
            (∑ a : Idx, Γ q a * Bc x p a) := by
            rw [← hDB_coord p q, hs1, hs2]
    simpa [NB] using hcoord'
  have hleft_deriv :
      extDerivFun (I := I)
          (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (((DU i k * U x j l + U x i k * DU j l) * Ac x i j * Bc x k l +
            U x i k * U x j l * (DA i j * Bc x k l + Ac x i j * DB k l))) := by
    calc
      extDerivFun (I := I)
          (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
        extDerivFun (I := I)
          (fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            U y i k * U y j l * Ac y i j * Bc y k l) x (X x) := by
          exact DifferentialGeometry.Tensor.Coordinates.deriv_congr_nhds (I := I)
            (x := x) (X x) hlocal
      _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (((DU i k * U x j l + U x i k * DU j l) * Ac x i j * Bc x k l +
            U x i k * U x j l * (DA i j * Bc x k l + Ac x i j * DB k l))) := by
          simpa [U, Ac, Bc, DA, DB, DU] using
            deriv4sum (I := I) (U := U) (A := Ac) (B := Bc)
              (x := x) (v := X x) hUmdiff hAmdiff hBmdiff
  have halg :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (((DU i k * U x j l + U x i k * DU j l) * Ac x i j * Bc x k l +
            U x i k * U x j l * (DA i j * Bc x k l + Ac x i j * DB k l)))) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l + Ac x i j * NB k l) :=
    inner0S_two_metricCompatible_coord_algebra
      (U := U x) (Γ := Γ) (A := Ac x) (B := Bc x)
      (DA := DA) (DB := DB) (NA := NA) (NB := NB) (DU := DU)
      hDU hNA hNB
  have hsplit :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l + Ac x i j * NB k l)) =
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l)) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (Ac x i j * NB k l)) := by
    calc
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l + Ac x i j * NB k l)) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (U x i k * U x j l * (NA i j * Bc x k l) +
            U x i k * U x j l * (Ac x i j * NB k l)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
      _ = _ := by
          simp [Finset.sum_add_distrib]
  have hRhsA :
      inner0S (I := I) g x 2
        (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X A x) (B x) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l) := by
    have h := inner0S_two_eq_coord (I := I) g x
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x hx)
      (U x) (DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) g x hx)
      (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X A x) (B x)
    calc
      inner0S (I := I) g x 2
          (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X A x) (B x) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * NA i j * Bc x k l := by
          simpa [U, Bc, NA, frame,
            DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply] using h
      _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
  have hRhsB :
      inner0S (I := I) g x 2 (A x)
        (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X B x) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (Ac x i j * NB k l) := by
    have h := inner0S_two_eq_coord (I := I) g x
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x hx)
      (U x) (DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) g x hx)
      (A x)
      (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X B x)
    calc
      inner0S (I := I) g x 2 (A x)
          (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X B x) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * Ac x i j * NB k l := by
          simpa [U, Ac, NB, frame,
            DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply] using h
      _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (Ac x i j * NB k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
  calc
    extDerivFun (I := I)
        (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (((DU i k * U x j l + U x i k * DU j l) * Ac x i j * Bc x k l +
          U x i k * U x j l * (DA i j * Bc x k l + Ac x i j * DB k l))) :=
        hleft_deriv
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l + Ac x i j * NB k l) := halg
    _ = inner0S (I := I) g x 2
          (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X A x) (B x) +
        inner0S (I := I) g x 2 (A x)
          (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X B x) := by
          rw [hsplit, ← hRhsA, ← hRhsB]














theorem inner0S_two_metricCompatible_extDerivFun
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (nablaA nablaB :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov A nablaA)
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov B nablaB)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
      inner0S (I := I) g x 2
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
          (nablaA x) (X x)) (B x) +
        inner0S (I := I) g x 2 (A x)
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
            (nablaB x) (X x)) := by
  classical
  let Idx : Type _ := DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
  let hframe : IsLocalFrameOn I E 1 frame
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x
  let slots : Idx -> Idx -> Fin 2 -> Idx :=
    fun i j q => if q = 0 then i else j
  let U : M -> Idx -> Idx -> Real :=
    fun y i j =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x i j (extChartAt I x y)
  let Ac : M -> Idx -> Idx -> Real :=
    fun y i j => A y (fun q : Fin 2 => if q = 0 then frame i y else frame j y)
  let Bc : M -> Idx -> Idx -> Real :=
    fun y i j => B y (fun q : Fin 2 => if q = 0 then frame i y else frame j y)
  let DA : Idx -> Idx -> Real :=
    fun i j => extDerivFun (I := I) (fun y : M => Ac y i j) x (X x)
  let DB : Idx -> Idx -> Real :=
    fun i j => extDerivFun (I := I) (fun y : M => Bc y i j) x (X x)
  let DU : Idx -> Idx -> Real :=
    fun i j => extDerivFun (I := I) (fun y : M => U y i j) x (X x)
  let Γ : Idx -> Idx -> Real :=
    fun i j =>
      DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov frame hframe x (X x) i j
  let NA : Idx -> Idx -> Real :=
    fun i j =>
      (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
        (nablaA x) (X x)) (fun q : Fin 2 => if q = 0 then frame i x else frame j x)
  let NB : Idx -> Idx -> Real :=
    fun i j =>
      (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
        (nablaB x) (X x)) (fun q : Fin 2 => if q = 0 then frame i x else frame j x)
  have hx : x ∈ DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) x
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)
  have hUmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => U y i j) x := by
    intro i j
    simpa [U, Idx] using
      DifferentialGeometry.Tensor.Coordinates.gInvComp_mdiffAt (I := I) g x i j
  have hAmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => Ac y i j) x := by
    intro i j
    have h := DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) (𝕜 := Real) A x (slots i j)
    have hfun :
        (fun y : M => A y
          (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
            (slots i j a) y)) =
          fun y : M => Ac y i j := by
      funext y
      exact congrArg (fun f : Fin 2 -> TangentSpace I y => A y f)
        (fin2_apply_ite (fun r : Idx => frame r y) i j)
    exact hfun ▸ h.mdifferentiableAt (by simp)
  have hBmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => Bc y i j) x := by
    intro i j
    have h := DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) (𝕜 := Real) B x (slots i j)
    have hfun :
        (fun y : M => B y
          (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
            (slots i j a) y)) =
          fun y : M => Bc y i j := by
      funext y
      exact congrArg (fun f : Fin 2 -> TangentSpace I y => B y f)
        (fin2_apply_ite (fun r : Idx => frame r y) i j)
    exact hfun ▸ h.mdifferentiableAt (by simp)
  have hlocal :
      (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) =ᶠ[𝓝 x]
        fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U y i k * U y j l * Ac y i j * Bc y k l := by
    filter_upwards
      [(DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open (I := I) x).mem_nhds hx]
      with y hy
    have h := inner0S_two_eq_coord (I := I) g y
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x hy)
      (U y) (DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) g x hy)
      (A y) (B y)
    simpa [U, Ac, Bc, frame, slots,
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply] using h
  have hDU : ∀ p q : Idx,
      DU p q =
        - ((∑ a : Idx, Γ a p * U x a q) + (∑ a : Idx, Γ a q * U x p a)) := by
    intro p q
    have hzero := DifferentialGeometry.Tensor.Coordinates.gInvCovZeroAt
      (I := I) g cov X hmc x p q
    unfold DifferentialGeometry.Tensor.Coordinates.inverseMetricCovDerivForMetricCompAlongInFrame at hzero
    have hzero' :
        DU p q +
          (∑ a : Idx, Γ a p * U x a q) +
          (∑ a : Idx, Γ a q * U x p a) = 0 := by
      simpa [DU, U, Γ, frame, hframe, Idx] using hzero
    linarith
  have hDA_coord (p q : Idx) :
      DA p q =
        DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I)
          (fun y : M => X y) x (fun y : M => A y) (slots p q) := by
    have hfun :
        (fun y : M => Ac y p q) =
          fun y : M => A y
            (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
              (slots p q a) y) := by
      funext y
      exact (congrArg (fun f : Fin 2 -> TangentSpace I y => A y f)
        (fin2_apply_ite (fun r : Idx => frame r y) p q)).symm
    calc
      DA p q =
          extDerivFun (I := I) (fun y : M => Ac y p q) x (X x) := rfl
      _ =
          extDerivFun (I := I)
            (fun y : M => A y
              (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (slots p q a) y)) x (X x) := by
            rw [hfun]
      _ =
          DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I)
            (fun y : M => X y) x (fun y : M => A y) (slots p q) := by
            simp [DifferentialGeometry.extDerivFun_real_eq_mfderiv,
              DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt]
  have hDB_coord (p q : Idx) :
      DB p q =
        DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I)
          (fun y : M => X y) x (fun y : M => B y) (slots p q) := by
    have hfun :
        (fun y : M => Bc y p q) =
          fun y : M => B y
            (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
              (slots p q a) y) := by
      funext y
      exact (congrArg (fun f : Fin 2 -> TangentSpace I y => B y f)
        (fin2_apply_ite (fun r : Idx => frame r y) p q)).symm
    calc
      DB p q =
          extDerivFun (I := I) (fun y : M => Bc y p q) x (X x) := rfl
      _ =
          extDerivFun (I := I)
            (fun y : M => B y
              (fun a : Fin 2 => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (slots p q a) y)) x (X x) := by
            rw [hfun]
      _ =
          DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I)
            (fun y : M => X y) x (fun y : M => B y) (slots p q) := by
            simp [DifferentialGeometry.extDerivFun_real_eq_mfderiv,
              DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt]
  have hNA : ∀ p q : Idx,
      NA p q =
        DA p q - (∑ a : Idx, Γ p a * Ac x a q) -
          (∑ a : Idx, Γ q a * Ac x p a) := by
    intro p q
    have happ := TotalNabla0SRealizes.apply (I := I) hA X x
      (fun r : Fin 2 => if r = 0 then frame p x else frame q x)
    have hcoord := DifferentialGeometry.Tensor.Coordinates.nabla0SFun_two_eval_coordFrame
      (I := I) cov X A x
      (DifferentialGeometry.Tensor.Coordinates.modelDeriv_eq_coordDeriv0SAt (I := I) X x A)
      p q
    have hs1 :
        (∑ a : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
              x (X x) p a *
            A x (fun r : Fin 2 =>
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then a else q) x)) =
          ∑ a : Idx, Γ p a * Ac x a q := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hslot :
          (fun r : Fin 2 =>
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then a else q) x) =
            (fun r : Fin 2 => if r = 0 then frame a x else frame q x) :=
        fin2_apply_ite (fun r : Idx => frame r x) a q
      rw [hslot]
    have hs2 :
        (∑ a : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
              x (X x) q a *
            A x (fun r : Fin 2 =>
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then p else a) x)) =
          ∑ a : Idx, Γ q a * Ac x p a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hslot :
          (fun r : Fin 2 =>
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then p else a) x) =
            (fun r : Fin 2 => if r = 0 then frame p x else frame a x) :=
        fin2_apply_ite (fun r : Idx => frame r x) p a
      rw [hslot]
    have hcoord' :
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X A x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x) =
          DA p q - (∑ a : Idx, Γ p a * Ac x a q) -
            (∑ a : Idx, Γ q a * Ac x p a) := by
      calc
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X A x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x)
            =
          (DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I)
              (fun y : M => X y) x (fun y : M => A y) (slots p q) -
              ∑ a : Idx,
                DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
                    x (X x) p a *
                  A x (fun r : Fin 2 =>
                    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                      (if r = 0 then a else q) x)) -
              ∑ a : Idx,
                DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
                    x (X x) q a *
                  A x (fun r : Fin 2 =>
                    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                      (if r = 0 then p else a) x) := by
            simpa [frame, slots] using hcoord
        _ = DA p q - (∑ a : Idx, Γ p a * Ac x a q) -
            (∑ a : Idx, Γ q a * Ac x p a) := by
            rw [← hDA_coord p q, hs1, hs2]
    calc
      NA p q =
          nablaA x (Fin.cons (X x)
            (fun r : Fin 2 => if r = 0 then frame p x else frame q x)) := by
            simp [NA, tensor0S_curry_apply_cons]
      _ =
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X A x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x) := happ
      _ =
          DA p q - (∑ a : Idx, Γ p a * Ac x a q) -
            (∑ a : Idx, Γ q a * Ac x p a) := hcoord'
  have hNB : ∀ p q : Idx,
      NB p q =
        DB p q - (∑ a : Idx, Γ p a * Bc x a q) -
          (∑ a : Idx, Γ q a * Bc x p a) := by
    intro p q
    have happ := TotalNabla0SRealizes.apply (I := I) hB X x
      (fun r : Fin 2 => if r = 0 then frame p x else frame q x)
    have hcoord := DifferentialGeometry.Tensor.Coordinates.nabla0SFun_two_eval_coordFrame
      (I := I) cov X B x
      (DifferentialGeometry.Tensor.Coordinates.modelDeriv_eq_coordDeriv0SAt (I := I) X x B)
      p q
    have hs1 :
        (∑ a : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
              x (X x) p a *
            B x (fun r : Fin 2 =>
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then a else q) x)) =
          ∑ a : Idx, Γ p a * Bc x a q := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hslot :
          (fun r : Fin 2 =>
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then a else q) x) =
            (fun r : Fin 2 => if r = 0 then frame a x else frame q x) :=
        fin2_apply_ite (fun r : Idx => frame r x) a q
      rw [hslot]
    have hs2 :
        (∑ a : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
              x (X x) q a *
            B x (fun r : Fin 2 =>
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then p else a) x)) =
          ∑ a : Idx, Γ q a * Bc x p a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hslot :
          (fun r : Fin 2 =>
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then p else a) x) =
            (fun r : Fin 2 => if r = 0 then frame p x else frame a x) :=
        fin2_apply_ite (fun r : Idx => frame r x) p a
      rw [hslot]
    have hcoord' :
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X B x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x) =
          DB p q - (∑ a : Idx, Γ p a * Bc x a q) -
            (∑ a : Idx, Γ q a * Bc x p a) := by
      calc
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X B x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x)
            =
          (DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I)
              (fun y : M => X y) x (fun y : M => B y) (slots p q) -
              ∑ a : Idx,
                DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
                    x (X x) p a *
                  B x (fun r : Fin 2 =>
                    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                      (if r = 0 then a else q) x)) -
              ∑ a : Idx,
                DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame cov
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
                    x (X x) q a *
                  B x (fun r : Fin 2 =>
                    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
                      (if r = 0 then p else a) x) := by
            simpa [frame, slots] using hcoord
        _ = DB p q - (∑ a : Idx, Γ p a * Bc x a q) -
            (∑ a : Idx, Γ q a * Bc x p a) := by
            rw [← hDB_coord p q, hs1, hs2]
    calc
      NB p q =
          nablaB x (Fin.cons (X x)
            (fun r : Fin 2 => if r = 0 then frame p x else frame q x)) := by
            simp [NB, tensor0S_curry_apply_cons]
      _ =
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X B x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x) := happ
      _ =
          DB p q - (∑ a : Idx, Γ p a * Bc x a q) -
            (∑ a : Idx, Γ q a * Bc x p a) := hcoord'
  have hleft_deriv :
      extDerivFun (I := I)
          (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (((DU i k * U x j l + U x i k * DU j l) * Ac x i j * Bc x k l +
            U x i k * U x j l * (DA i j * Bc x k l + Ac x i j * DB k l))) := by
    calc
      extDerivFun (I := I)
          (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
        extDerivFun (I := I)
          (fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            U y i k * U y j l * Ac y i j * Bc y k l) x (X x) := by
          exact DifferentialGeometry.Tensor.Coordinates.deriv_congr_nhds (I := I)
            (x := x) (X x) hlocal
      _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (((DU i k * U x j l + U x i k * DU j l) * Ac x i j * Bc x k l +
            U x i k * U x j l * (DA i j * Bc x k l + Ac x i j * DB k l))) := by
          simpa [U, Ac, Bc, DA, DB, DU] using
            deriv4sum (I := I) (U := U) (A := Ac) (B := Bc)
              (x := x) (v := X x) hUmdiff hAmdiff hBmdiff
  have halg :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (((DU i k * U x j l + U x i k * DU j l) * Ac x i j * Bc x k l +
            U x i k * U x j l * (DA i j * Bc x k l + Ac x i j * DB k l)))) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l + Ac x i j * NB k l) :=
    inner0S_two_metricCompatible_coord_algebra
      (U := U x) (Γ := Γ) (A := Ac x) (B := Bc x)
      (DA := DA) (DB := DB) (NA := NA) (NB := NB) (DU := DU)
      hDU hNA hNB
  have hsplit :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l + Ac x i j * NB k l)) =
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l)) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (Ac x i j * NB k l)) := by
    calc
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l + Ac x i j * NB k l)) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (U x i k * U x j l * (NA i j * Bc x k l) +
            U x i k * U x j l * (Ac x i j * NB k l)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
      _ = _ := by
          simp [Finset.sum_add_distrib]
  have hRhsA :
      inner0S (I := I) g x 2
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
          (nablaA x) (X x)) (B x) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l) := by
    have h := inner0S_two_eq_coord (I := I) g x
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x hx)
      (U x) (DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) g x hx)
      (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
        (nablaA x) (X x)) (B x)
    calc
      inner0S (I := I) g x 2
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
            (nablaA x) (X x)) (B x) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * NA i j * Bc x k l := by
          simpa [U, Bc, NA, frame,
            DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply] using h
      _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
  have hRhsB :
      inner0S (I := I) g x 2 (A x)
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
          (nablaB x) (X x)) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (Ac x i j * NB k l) := by
    have h := inner0S_two_eq_coord (I := I) g x
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x hx)
      (U x) (DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) g x hx)
      (A x)
      (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
        (nablaB x) (X x))
    calc
      inner0S (I := I) g x 2 (A x)
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
            (nablaB x) (X x)) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * Ac x i j * NB k l := by
          simpa [U, Ac, NB, frame,
            DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply] using h
      _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (Ac x i j * NB k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
  calc
    extDerivFun (I := I)
        (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (((DU i k * U x j l + U x i k * DU j l) * Ac x i j * Bc x k l +
          U x i k * U x j l * (DA i j * Bc x k l + Ac x i j * DB k l))) :=
        hleft_deriv
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l + Ac x i j * NB k l) := halg
    _ = inner0S (I := I) g x 2
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
            (nablaA x) (X x)) (B x) +
        inner0S (I := I) g x 2 (A x)
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
            (nablaB x) (X x)) := by
          rw [hsplit, ← hRhsA, ← hRhsB]


end

end Tensor0SBundle
