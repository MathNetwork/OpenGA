import DifferentialGeometry.Tensor.RicciIdentity.Tensor0S.Realization

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false








noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.SlotAlgebra
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]








private theorem tensor0S_commutator_expansion_from_realizes
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {s : ℕ}
    (alphaSec : Tensor0SSection (I := I) (M := M) s)
    (nablaAlphaSec : Tensor0SSection (I := I) (M := M) (s + 1))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (Xsec Ysec : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (Vsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (halpha : alphaSec x = alpha)
    (hnablaAlpha : nablaAlphaSec x = nablaAlpha)
    (hnabla2 : Nabla20SRealizesAt (I := I) s cov alphaSec nablaAlphaSec x
      nabla2Alpha) :
    let X : TangentSpace I x := Xsec x
    let Y : TangentSpace I x := Ysec x
    let slots : Fin s → TangentSpace I x := fun q => Vsec q x
    nabla2Alpha (metricTraceInput (I := I) X Y slots) -
        nabla2Alpha (metricTraceInput (I := I) Y X slots) =
      curvatureAction0SAt (I := I) Rm13 alpha X Y slots -
        torsionCorrection0SAt (I := I) nablaAlpha (cov.torsion x X Y) slots := by
  classical
  dsimp only
  let Xf : (p : M) → TangentSpace I p := fun p => Xsec p
  let Yf : (p : M) → TangentSpace I p := fun p => Ysec p
  let Vfield : Fin s → (p : M) → TangentSpace I p := fun q p => Vsec q p
  let slots : Fin s → TangentSpace I x := fun q => Vsec q x
  let WY :
      Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
    Fin.cons Ysec Vsec
  let WX :
      Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
    Fin.cons Xsec Vsec
  have hXY :
      nabla2Alpha (Fin.cons (Xsec x) (fun a : Fin (s + 1) => WY a x)) =
        extDerivFun (I := I)
            (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WY a p))
            x (Xsec x) -
          ∑ a : Fin (s + 1),
            nablaAlphaSec x
              (Function.update
                (fun b : Fin (s + 1) => WY b x) a
                ((cov (fun p : M => WY a p) x) (Xsec x))) := by
    have h := Nabla20SRealizesAt.eval_smooth_slots
      (I := I) hnabla2 Xsec WY
    simpa using h
  have hYX :
      nabla2Alpha (Fin.cons (Ysec x) (fun a : Fin (s + 1) => WX a x)) =
        extDerivFun (I := I)
            (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WX a p))
            x (Ysec x) -
          ∑ a : Fin (s + 1),
            nablaAlphaSec x
              (Function.update
                (fun b : Fin (s + 1) => WX b x) a
                ((cov (fun p : M => WX a p) x) (Ysec x))) := by
    have h := Nabla20SRealizesAt.eval_smooth_slots
      (I := I) hnabla2 Ysec WX
    simpa using h
  have hFY (p : M) :
      nablaAlphaSec p
          (Fin.cons (Ysec p) (fun q : Fin s => Vsec q p)) =
        extDerivFun (I := I)
            (fun y : M => alphaSec y (fun q : Fin s => Vsec q y))
            p (Ysec p) -
          ∑ q : Fin s,
            alphaSec p
              (Function.update (fun r : Fin s => Vsec r p) q
                ((cov (fun y : M => Vsec q y) p) (Ysec p))) := by
    have h := Nabla0SSectionRealizes.eval_smooth_slots
      (I := I) hnabla2.1 Ysec Vsec p
    simpa using h
  have hFX (p : M) :
      nablaAlphaSec p
          (Fin.cons (Xsec p) (fun q : Fin s => Vsec q p)) =
        extDerivFun (I := I)
            (fun y : M => alphaSec y (fun q : Fin s => Vsec q y))
            p (Xsec p) -
          ∑ q : Fin s,
            alphaSec p
              (Function.update (fun r : Fin s => Vsec r p) q
                ((cov (fun y : M => Vsec q y) p) (Xsec p))) := by
    have h := Nabla0SSectionRealizes.eval_smooth_slots
      (I := I) hnabla2.1 Xsec Vsec p
    simpa using h
  let YV : Fin s → (p : M) → TangentSpace I p :=
    fun q p => (cov (fun y : M => Vsec q y) p) (Ysec p)
  let XV : Fin s → (p : M) → TangentSpace I p :=
    fun q p => (cov (fun y : M => Vsec q y) p) (Xsec p)
  have hYV_C1 (q : Fin s) :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, YV q p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x := by
    simpa [YV] using
      CovariantDerivative.smoothSections_cov_contMDiffAt_one
        (𝕜 := ℝ) cov hcov Ysec (Vsec q) x
  have hXV_C1 (q : Fin s) :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, XV q p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x := by
    simpa [XV] using
      CovariantDerivative.smoothSections_cov_contMDiffAt_one
        (𝕜 := ℝ) cov hcov Xsec (Vsec q) x
  let VYq : Fin s → Fin s → (p : M) → TangentSpace I p :=
    fun q => Function.update Vfield q (YV q)
  let VXq : Fin s → Fin s → (p : M) → TangentSpace I p :=
    fun q => Function.update Vfield q (XV q)
  have hVYq_C1 (q a : Fin s) :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, VYq q a p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x := by
    by_cases ha : a = q
    · subst a
      simpa [VYq, Vfield] using hYV_C1 q
    · simpa [VYq, Vfield, ha] using
        ((Vsec a).contMDiff.contMDiffAt.of_le
          (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞)))
  have hVXq_C1 (q a : Fin s) :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, VXq q a p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x := by
    by_cases ha : a = q
    · subst a
      simpa [VXq, Vfield] using hXV_C1 q
    · simpa [VXq, Vfield, ha] using
        ((Vsec a).contMDiff.contMDiffAt.of_le
          (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞)))
  have hDX_corrY (q : Fin s) :
      extDerivFun (I := I)
          (fun p : M => alphaSec p (fun a : Fin s => VYq q a p))
          x (Xsec x) =
        nablaAlphaSec x
            (Fin.cons (Xsec x) (fun a : Fin s => VYq q a x)) +
          ∑ a : Fin s,
            alphaSec x
              (Function.update (fun b : Fin s => VYq q b x) a
                ((cov (fun p : M => VYq q a p) x) (Xsec x))) := by
    have h := Nabla0SSectionRealizes.eval_C1_slots
      (I := I) hnabla2.1 Xsec (VYq q) x (hVYq_C1 q)
    rw [h]
    abel
  have hDY_corrX (q : Fin s) :
      extDerivFun (I := I)
          (fun p : M => alphaSec p (fun a : Fin s => VXq q a p))
          x (Ysec x) =
        nablaAlphaSec x
            (Fin.cons (Ysec x) (fun a : Fin s => VXq q a x)) +
          ∑ a : Fin s,
            alphaSec x
              (Function.update (fun b : Fin s => VXq q b x) a
                ((cov (fun p : M => VXq q a p) x) (Ysec x))) := by
    have h := Nabla0SSectionRealizes.eval_C1_slots
      (I := I) hnabla2.1 Ysec (VXq q) x (hVXq_C1 q)
    rw [h]
    abel
  have hcurvAction :
      curvatureAction0SAt (I := I) Rm13 alpha (Xsec x) (Ysec x)
          (fun q : Fin s => Vsec q x) =
        curvatureAction0SAtSlots (I := I) alpha
          (fun q : Fin s => Vsec q x)
          (fun q : Fin s =>
            (connectionRiemannCurvatureField (I := I) cov Xf Yf
              (fun p : M => Vsec q p)) x) := by
    simpa [Xf, Yf] using
      curvatureAction0SAt_eq_slots_connectionRiemannCurvature
        (I := I) (cov := cov) (Rm13 := Rm13)
        alpha Xsec Ysec Vsec hRm13
  have hcurvActionSlots :
      curvatureAction0SAtSlots (I := I) alpha
          (fun q : Fin s => Vsec q x)
          (fun q : Fin s =>
            (connectionRiemannCurvatureField (I := I) cov Xf Yf
              (fun p : M => Vsec q p)) x) =
        -∑ q : Fin s,
          alpha
            (Function.update (fun r : Fin s => Vsec r x) q
              ((connectionRiemannCurvatureField (I := I) cov Xf Yf
                (fun p : M => Vsec q p)) x)) := by
    rfl
  have hX_mdiff : MDiffAt (T% Xf) x := by
    simpa [Xf] using
      (Xsec.contMDiff.contMDiffAt.mdifferentiableAt
        (by simp))
  have hY_mdiff : MDiffAt (T% Yf) x := by
    simpa [Yf] using
      (Ysec.contMDiff.contMDiffAt.mdifferentiableAt
        (by simp))
  have htorsion_apply :
      cov.torsion x (Xsec x) (Ysec x) =
        (cov Yf x) (Xsec x) - (cov Xf x) (Ysec x) -
          VectorField.mlieBracket I Xf Yf x := by
    simpa [Xf, Yf] using
      cov.torsion_apply hX_mdiff hY_mdiff
  have htorsionFirstSlot :
      nablaAlpha
          (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) -
          nablaAlpha
            (Fin.cons ((cov Yf x) (Xsec x)) slots) +
          nablaAlpha
            (Fin.cons ((cov Xf x) (Ysec x)) slots) =
        -torsionCorrection0SAt (I := I) nablaAlpha
          (cov.torsion x (Xsec x) (Ysec x)) slots := by
    have h := first_slot_torsionCorrection_eq
      (I := I) nablaAlpha ((cov Yf x) (Xsec x))
      ((cov Xf x) (Ysec x)) (VectorField.mlieBracket I Xf Yf x) slots
    simpa [htorsion_apply] using h
  have hExpanded :
      nabla2Alpha
          (metricTraceInput (I := I) (Xsec x) (Ysec x)
            (fun q : Fin s => Vsec q x)) -
        nabla2Alpha
          (metricTraceInput (I := I) (Ysec x) (Xsec x)
            (fun q : Fin s => Vsec q x))
        =
        (-∑ q : Fin s,
          alpha
            (Function.update (fun r : Fin s => Vsec r x) q
              ((connectionRiemannCurvatureField (I := I) cov Xf Yf
                (fun p : M => Vsec q p)) x)))
        +
        (nablaAlpha
            (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) -
          nablaAlpha
            (Fin.cons ((cov Yf x) (Xsec x)) slots) +
          nablaAlpha
            (Fin.cons ((cov Xf x) (Ysec x)) slots)) := by




    rw [metricTraceInput_eq_finCons (I := I) (Xsec x) (Ysec x)
      (fun q : Fin s => Vsec q x)]
    rw [metricTraceInput_eq_finCons (I := I) (Ysec x) (Xsec x)
      (fun q : Fin s => Vsec q x)]
    have hWYx :
        (fun a : Fin (s + 1) => WY a x) =
          Fin.cons (Ysec x) (fun q : Fin s => Vsec q x) := by
      funext a
      refine Fin.cases ?_ ?_ a
      · simp [WY]
      · intro q
        simp [WY]
    have hWXx :
        (fun a : Fin (s + 1) => WX a x) =
          Fin.cons (Xsec x) (fun q : Fin s => Vsec q x) := by
      funext a
      refine Fin.cases ?_ ?_ a
      · simp [WX]
      · intro q
        simp [WX]
    have hcorrWY :
        (∑ a : Fin (s + 1),
          nablaAlphaSec x
            (Function.update (fun b : Fin (s + 1) => WY b x) a
              ((cov (fun p : M => WY a p) x) (Xsec x)))) =
          nablaAlphaSec x
            (Fin.cons ((cov Yf x) (Xsec x))
              (fun q : Fin s => Vsec q x)) +
            ∑ q : Fin s,
              nablaAlphaSec x
                (Fin.cons (Ysec x)
                  (Function.update (fun r : Fin s => Vsec r x) q
                    (XV q x))) := by
      rw [hWYx]
      simpa [WY, Xf, Yf, XV] using
        sum_update_finCons_raw
          (F := fun slots' : Fin (s + 1) → TangentSpace I x =>
            nablaAlphaSec x slots')
          (head := Ysec x)
          (tail := fun q : Fin s => Vsec q x)
          (d := fun a : Fin (s + 1) =>
            (cov (fun p : M =>
              ((Fin.cons Ysec Vsec :
                Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                  (TangentSpace I : M → Type _)) a) p) x) (Xsec x))
    have hcorrWX :
        (∑ a : Fin (s + 1),
          nablaAlphaSec x
            (Function.update (fun b : Fin (s + 1) => WX b x) a
              ((cov (fun p : M => WX a p) x) (Ysec x)))) =
          nablaAlphaSec x
            (Fin.cons ((cov Xf x) (Ysec x))
              (fun q : Fin s => Vsec q x)) +
            ∑ q : Fin s,
              nablaAlphaSec x
                (Fin.cons (Xsec x)
                  (Function.update (fun r : Fin s => Vsec r x) q
                    (YV q x))) := by
      rw [hWXx]
      simpa [WX, Xf, Yf, YV] using
        sum_update_finCons_raw
          (F := fun slots' : Fin (s + 1) → TangentSpace I x =>
            nablaAlphaSec x slots')
          (head := Xsec x)
          (tail := fun q : Fin s => Vsec q x)
          (d := fun a : Fin (s + 1) =>
            (cov (fun p : M =>
              ((Fin.cons Xsec Vsec :
                Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                  (TangentSpace I : M → Type _)) a) p) x) (Ysec x))
    let baseScalar : M → Real :=
      fun p : M => alphaSec p (fun q : Fin s => Vsec q p)
    have hbaseSmooth :
        ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞) baseScalar x := by
      simpa [baseScalar] using
        Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          alphaSec Vsec x
    have hbase2 :
        ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) baseScalar x :=
      hbaseSmooth.of_le
        (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hX2 :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
          (T% Xf) x := by
      simpa [Xf] using
        (Xsec.contMDiff.contMDiffAt.of_le
          (by
            exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
    have hY2 :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
          (T% Yf) x := by
      simpa [Yf] using
        (Ysec.contMDiff.contMDiffAt.of_le
          (by
            exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
    have hYbase_mdiff :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => extDerivFun (I := I) baseScalar p (Ysec p)) x := by
      exact
        (DifferentialGeometry.extDerivFun_apply_contMDiffAt
          (I := I) hbaseSmooth Ysec).mdifferentiableAt (by simp)
    have hXbase_mdiff :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => extDerivFun (I := I) baseScalar p (Xsec p)) x := by
      exact
        (DifferentialGeometry.extDerivFun_apply_contMDiffAt
          (I := I) hbaseSmooth Xsec).mdifferentiableAt (by simp)
    have hCY_mdiff (q : Fin s) :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => alphaSec p (fun a : Fin s => VYq q a p)) x := by
      exact
        Tensor0SBundle.tensor0SField_eval_C1_slots_mdiffAt
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          alphaSec (VYq q) x (hVYq_C1 q)
    have hCX_mdiff (q : Fin s) :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => alphaSec p (fun a : Fin s => VXq q a p)) x := by
      exact
        Tensor0SBundle.tensor0SField_eval_C1_slots_mdiffAt
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          alphaSec (VXq q) x (hVXq_C1 q)
    have hCY_sum_mdiff :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M =>
            ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p)) x :=
      by
        have hfun :
            (fun p : M =>
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p)) =
              Finset.univ.sum (fun q : Fin s => fun p : M =>
                alphaSec p (fun a : Fin s => VYq q a p)) := by
          funext p
          simp
        rw [hfun]
        exact
          mdiffAt_finset_sum (I := I) Finset.univ
            (fun q : Fin s => fun p : M =>
              alphaSec p (fun a : Fin s => VYq q a p))
            (by intro q hq; exact hCY_mdiff q)
    have hCX_sum_mdiff :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M =>
            ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p)) x :=
      by
        have hfun :
            (fun p : M =>
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p)) =
              Finset.univ.sum (fun q : Fin s => fun p : M =>
                alphaSec p (fun a : Fin s => VXq q a p)) := by
          funext p
          simp
        rw [hfun]
        exact
          mdiffAt_finset_sum (I := I) Finset.univ
            (fun q : Fin s => fun p : M =>
              alphaSec p (fun a : Fin s => VXq q a p))
            (by intro q hq; exact hCX_mdiff q)
    have hFY_fun :
        (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WY a p)) =
          fun p : M =>
            extDerivFun (I := I) baseScalar p (Ysec p) -
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p) := by
      funext p
      have hWYp :
          (fun a : Fin (s + 1) => WY a p) =
            Fin.cons (Ysec p) (fun q : Fin s => Vsec q p) := by
        funext a
        refine Fin.cases ?_ ?_ a
        · simp [WY]
        · intro q
          simp [WY]
      have hsum :
          (∑ q : Fin s,
            alphaSec p
              (Function.update (fun r : Fin s => Vsec r p) q
                ((cov (fun y : M => Vsec q y) p) (Ysec p)))) =
            ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p) := by
        refine Finset.sum_congr rfl ?_
        intro q hq
        congr 1
        funext a
        by_cases ha : a = q
        · subst a
          simp [VYq, Vfield, YV]
        · simp [VYq, Vfield, YV, ha]
      calc
        nablaAlphaSec p (fun a : Fin (s + 1) => WY a p)
            = nablaAlphaSec p
                (Fin.cons (Ysec p) (fun q : Fin s => Vsec q p)) := by
              rw [hWYp]
        _ =
            extDerivFun (I := I) baseScalar p (Ysec p) -
              ∑ q : Fin s,
                alphaSec p
                  (Function.update (fun r : Fin s => Vsec r p) q
                    ((cov (fun y : M => Vsec q y) p) (Ysec p))) := by
              simpa [baseScalar] using hFY p
        _ =
            extDerivFun (I := I) baseScalar p (Ysec p) -
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p) := by
              rw [hsum]
    have hFX_fun :
        (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WX a p)) =
          fun p : M =>
            extDerivFun (I := I) baseScalar p (Xsec p) -
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p) := by
      funext p
      have hWXp :
          (fun a : Fin (s + 1) => WX a p) =
            Fin.cons (Xsec p) (fun q : Fin s => Vsec q p) := by
        funext a
        refine Fin.cases ?_ ?_ a
        · simp [WX]
        · intro q
          simp [WX]
      have hsum :
          (∑ q : Fin s,
            alphaSec p
              (Function.update (fun r : Fin s => Vsec r p) q
                ((cov (fun y : M => Vsec q y) p) (Xsec p)))) =
            ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p) := by
        refine Finset.sum_congr rfl ?_
        intro q hq
        congr 1
        funext a
        by_cases ha : a = q
        · subst a
          simp [VXq, Vfield, XV]
        · simp [VXq, Vfield, XV, ha]
      calc
        nablaAlphaSec p (fun a : Fin (s + 1) => WX a p)
            = nablaAlphaSec p
                (Fin.cons (Xsec p) (fun q : Fin s => Vsec q p)) := by
              rw [hWXp]
        _ =
            extDerivFun (I := I) baseScalar p (Xsec p) -
              ∑ q : Fin s,
                alphaSec p
                  (Function.update (fun r : Fin s => Vsec r p) q
                    ((cov (fun y : M => Vsec q y) p) (Xsec p))) := by
              simpa [baseScalar] using hFX p
        _ =
            extDerivFun (I := I) baseScalar p (Xsec p) -
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p) := by
              rw [hsum]
    have hFY_deriv :
        extDerivFun (I := I)
            (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WY a p))
            x (Xsec x) =
          extDerivFun (I := I)
              (fun p : M => extDerivFun (I := I) baseScalar p (Ysec p))
              x (Xsec x) -
            ∑ q : Fin s,
              extDerivFun (I := I)
                (fun p : M => alphaSec p (fun a : Fin s => VYq q a p))
                x (Xsec x) := by
      rw [hFY_fun]
      rw [extDerivFun_sub_at (I := I) (x := x) (v := Xsec x)
        hYbase_mdiff hCY_sum_mdiff]
      have hsum :
          extDerivFun (I := I)
              (fun p : M =>
                ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p))
              x (Xsec x) =
            ∑ q : Fin s,
              extDerivFun (I := I)
                (fun p : M => alphaSec p (fun a : Fin s => VYq q a p))
                x (Xsec x) := by
        have hfun :
            (fun p : M =>
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p)) =
              Finset.univ.sum (fun q : Fin s => fun p : M =>
                alphaSec p (fun a : Fin s => VYq q a p)) := by
          funext p
          simp
        rw [hfun]
        exact
          extDerivFun_finset_sum_at (I := I) Finset.univ
            (fun q : Fin s => fun p : M =>
              alphaSec p (fun a : Fin s => VYq q a p))
            (x := x) (v := Xsec x)
            (by intro q hq; exact hCY_mdiff q)
      rw [hsum]
    have hFX_deriv :
        extDerivFun (I := I)
            (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WX a p))
            x (Ysec x) =
          extDerivFun (I := I)
              (fun p : M => extDerivFun (I := I) baseScalar p (Xsec p))
              x (Ysec x) -
            ∑ q : Fin s,
              extDerivFun (I := I)
                (fun p : M => alphaSec p (fun a : Fin s => VXq q a p))
                x (Ysec x) := by
      rw [hFX_fun]
      rw [extDerivFun_sub_at (I := I) (x := x) (v := Ysec x)
        hXbase_mdiff hCX_sum_mdiff]
      have hsum :
          extDerivFun (I := I)
              (fun p : M =>
                ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p))
              x (Ysec x) =
            ∑ q : Fin s,
              extDerivFun (I := I)
                (fun p : M => alphaSec p (fun a : Fin s => VXq q a p))
                x (Ysec x) := by
        have hfun :
            (fun p : M =>
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p)) =
              Finset.univ.sum (fun q : Fin s => fun p : M =>
                alphaSec p (fun a : Fin s => VXq q a p)) := by
          funext p
          simp
        rw [hfun]
        exact
          extDerivFun_finset_sum_at (I := I) Finset.univ
            (fun q : Fin s => fun p : M =>
              alphaSec p (fun a : Fin s => VXq q a p))
            (x := x) (v := Ysec x)
            (by intro q hq; exact hCX_mdiff q)
      rw [hsum]
    haveI : CompleteSpace E := FiniteDimensional.complete Real E
    haveI : IsManifold I 3 M := by
      exact IsManifold.of_le (I := I) (M := M)
        (by exact WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hbracket :
        extDerivFun (I := I) baseScalar x
            (VectorField.mlieBracket I Xf Yf x) =
          extDerivFun (I := I)
              (fun p : M => extDerivFun (I := I) baseScalar p (Ysec p))
              x (Xsec x) -
            extDerivFun (I := I)
              (fun p : M => extDerivFun (I := I) baseScalar p (Xsec p))
              x (Ysec x) := by
      simpa [Xf, Yf] using
        DifferentialGeometry.extDerivFun_apply_mlieBracket
          (I := I) Xf Yf baseScalar x hX2 hY2 hbase2
    have hbracket_eval :
        extDerivFun (I := I) baseScalar x
            (VectorField.mlieBracket I Xf Yf x) =
          nablaAlpha
            (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) +
            ∑ q : Fin s,
              alpha
                (Function.update slots q
                  ((cov (fun y : M => Vsec q y) x)
                    (VectorField.mlieBracket I Xf Yf x))) := by
      have h0 := Nabla0SSectionRealizes.eval_point_vector_smooth_slots
        (I := I) hnabla2.1
        (VectorField.mlieBracket I Xf Yf x) Vsec
      rw [hnablaAlpha, halpha] at h0
      linarith
    have hbaseComm :
        extDerivFun (I := I)
            (fun p : M => extDerivFun (I := I) baseScalar p (Ysec p))
            x (Xsec x) -
          extDerivFun (I := I)
            (fun p : M => extDerivFun (I := I) baseScalar p (Xsec p))
            x (Ysec x) =
          nablaAlpha
            (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) +
            ∑ q : Fin s,
              alpha
                (Function.update slots q
                  ((cov (fun y : M => Vsec q y) x)
                    (VectorField.mlieBracket I Xf Yf x))) := by
      rw [← hbracket]
      exact hbracket_eval
    have hbaseComm_left :
        extDerivFun (I := I)
            (fun p : M => extDerivFun (I := I) baseScalar p (Ysec p))
            x (Xsec x) =
          (nablaAlpha
            (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) +
            ∑ q : Fin s,
              alpha
                (Function.update slots q
                  ((cov (fun y : M => Vsec q y) x)
                    (VectorField.mlieBracket I Xf Yf x)))) +
            extDerivFun (I := I)
              (fun p : M => extDerivFun (I := I) baseScalar p (Xsec p))
              x (Ysec x) := by
      linarith
    rw [← hWYx, ← hWXx]
    rw [hXY, hYX]
    rw [hcorrWY, hcorrWX]
    rw [hFY_deriv, hFX_deriv]
    rw [hbaseComm_left]
    simp_rw [hDX_corrY, hDY_corrX]
    rw [hnablaAlpha, halpha]
    have hVYq_at (q : Fin s) :
        (fun a : Fin s => VYq q a x) =
          Function.update slots q (YV q x) := by
      funext a
      by_cases ha : a = q
      · subst a
        simp [VYq, Vfield, slots]
      · simp [VYq, Vfield, slots, ha]
    have hVXq_at (q : Fin s) :
        (fun a : Fin s => VXq q a x) =
          Function.update slots q (XV q x) := by
      funext a
      by_cases ha : a = q
      · subst a
        simp [VXq, Vfield, slots]
      · simp [VXq, Vfield, slots, ha]
    have hFinConsVY (q : Fin s) :
        (Fin.cons (Xsec x) (fun a : Fin s => VYq q a x) :
            Fin (s + 1) → TangentSpace I x) =
          Function.update
            (Fin.cons (Xsec x) slots : Fin (s + 1) → TangentSpace I x)
            q.succ (YV q x) := by
      rw [hVYq_at q]
      exact finCons_update_tail_eq_update_finCons_succ
        (Xsec x) slots q (YV q x)
    have hFinConsVX (q : Fin s) :
        (Fin.cons (Ysec x) (fun a : Fin s => VXq q a x) :
            Fin (s + 1) → TangentSpace I x) =
          Function.update
            (Fin.cons (Ysec x) slots : Fin (s + 1) → TangentSpace I x)
            q.succ (XV q x) := by
      rw [hVXq_at q]
      exact finCons_update_tail_eq_update_finCons_succ
        (Ysec x) slots q (XV q x)
    have hDoubleY :
        (∑ q : Fin s, ∑ a : Fin s,
          alpha
            (Function.update (fun b : Fin s => VYq q b x) a
              ((cov (fun p : M => VYq q a p) x) (Xsec x)))) =
        ∑ q : Fin s, ∑ a : Fin s,
          alpha
            (Function.update (Function.update slots q (YV q x)) a
              (if a = q then
                (cov (fun p : M => YV q p) x) (Xsec x)
              else
                XV a x)) := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      refine Finset.sum_congr rfl ?_
      intro a ha
      have hderiv :
          ((cov (fun p : M => VYq q a p) x) (Xsec x)) =
            (if a = q then
              (cov (fun p : M => YV q p) x) (Xsec x)
            else
              XV a x) := by
        by_cases haq : a = q
        · subst a
          simp [VYq, Vfield, YV, XV]
        · simp [VYq, Vfield, YV, XV, haq]
      rw [hVYq_at q, hderiv]
    have hDoubleX :
        (∑ q : Fin s, ∑ a : Fin s,
          alpha
            (Function.update (fun b : Fin s => VXq q b x) a
              ((cov (fun p : M => VXq q a p) x) (Ysec x)))) =
        ∑ q : Fin s, ∑ a : Fin s,
          alpha
            (Function.update (Function.update slots q (XV q x)) a
              (if a = q then
                (cov (fun p : M => XV q p) x) (Ysec x)
              else
                YV a x)) := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      refine Finset.sum_congr rfl ?_
      intro a ha
      have hderiv :
          ((cov (fun p : M => VXq q a p) x) (Ysec x)) =
            (if a = q then
              (cov (fun p : M => XV q p) x) (Ysec x)
            else
              YV a x) := by
        by_cases haq : a = q
        · subst a
          simp [VXq, Vfield, YV, XV]
        · simp [VXq, Vfield, YV, XV, haq]
      rw [hVXq_at q, hderiv]
    have hDoubleCancel :
        - (∑ q : Fin s, ∑ a : Fin s,
          alpha
            (Function.update (fun b : Fin s => VYq q b x) a
              ((cov (fun p : M => VYq q a p) x) (Xsec x)))) +
          (∑ q : Fin s, ∑ a : Fin s,
            alpha
              (Function.update (fun b : Fin s => VXq q b x) a
                ((cov (fun p : M => VXq q a p) x) (Ysec x)))) =
        - (∑ q : Fin s,
          alpha
            (Function.update slots q
              ((cov (fun p : M => YV q p) x) (Xsec x)))) +
          (∑ q : Fin s,
            alpha
              (Function.update slots q
                ((cov (fun p : M => XV q p) x) (Ysec x)))) := by
      rw [hDoubleY, hDoubleX]
      exact double_update_sum_cancel_diag
        (eval := fun slots' : Fin s → TangentSpace I x => alpha slots')
        (slots := slots)
        (X := fun q : Fin s => XV q x)
        (Y := fun q : Fin s => YV q x)
        (XY := fun q : Fin s => (cov (fun p : M => YV q p) x) (Xsec x))
        (YX := fun q : Fin s => (cov (fun p : M => XV q p) x) (Ysec x))
    have hDiagCurv :
        - (∑ q : Fin s,
          alpha
            (Function.update slots q
              ((cov (fun p : M => YV q p) x) (Xsec x)))) +
          (∑ q : Fin s,
            alpha
              (Function.update slots q
                ((cov (fun p : M => XV q p) x) (Ysec x)))) +
          (∑ q : Fin s,
            alpha
              (Function.update slots q
                ((cov (fun y : M => Vsec q y) x)
                  (VectorField.mlieBracket I Xf Yf x)))) =
        -∑ q : Fin s,
          alpha
            (Function.update slots q
              ((connectionRiemannCurvatureField (I := I) cov Xf Yf
                (fun p : M => Vsec q p)) x)) := by
      let A : Fin s → Real := fun q =>
        alpha (Function.update slots q
          ((cov (fun p : M => YV q p) x) (Xsec x)))
      let B : Fin s → Real := fun q =>
        alpha (Function.update slots q
          ((cov (fun p : M => XV q p) x) (Ysec x)))
      let C : Fin s → Real := fun q =>
        alpha (Function.update slots q
          ((cov (fun y : M => Vsec q y) x)
            (VectorField.mlieBracket I Xf Yf x)))
      let D : Fin s → Real := fun q =>
        alpha (Function.update slots q
          ((connectionRiemannCurvatureField (I := I) cov Xf Yf
            (fun p : M => Vsec q p)) x))
      change - (∑ q : Fin s, A q) + (∑ q : Fin s, B q) +
          (∑ q : Fin s, C q) = -∑ q : Fin s, D q
      calc
        - (∑ q : Fin s, A q) + (∑ q : Fin s, B q) +
            (∑ q : Fin s, C q)
            = ∑ q : Fin s, (-A q + B q + C q) := by
              simp [Finset.sum_neg_distrib, Finset.sum_add_distrib]
        _ = ∑ q : Fin s, -D q := by
              refine Finset.sum_congr rfl ?_
              intro q hq
              have hdiag :=
                tensor0S_update_curvature_diag
                  (I := I) alpha slots q
                  ((cov (fun p : M => YV q p) x) (Xsec x))
                  ((cov (fun p : M => XV q p) x) (Ysec x))
                  ((cov (fun y : M => Vsec q y) x)
                    (VectorField.mlieBracket I Xf Yf x))
              calc
                -A q + B q + C q =
                    -alpha
                      (Function.update slots q
                        (((cov (fun p : M => YV q p) x) (Xsec x)) -
                          ((cov (fun p : M => XV q p) x) (Ysec x)) -
                          ((cov (fun y : M => Vsec q y) x)
                            (VectorField.mlieBracket I Xf Yf x)))) := by
                  simpa [A, B, C] using hdiag
                _ = -D q := by
                  have hvec :
                      ((cov (fun p : M => YV q p) x) (Xsec x)) -
                          ((cov (fun p : M => XV q p) x) (Ysec x)) -
                          ((cov (fun y : M => Vsec q y) x)
                            (VectorField.mlieBracket I Xf Yf x)) =
                        (connectionRiemannCurvatureField (I := I) cov Xf Yf
                          (fun p : M => Vsec q p)) x := by
                    rfl
                  dsimp [D]
                  rw [hvec]
        _ = -∑ q : Fin s, D q := by
              simp [Finset.sum_neg_distrib]
    simp_rw [hFinConsVY, hFinConsVX]
    simp_rw [finCons_update_tail_eq_update_finCons_succ]
    repeat rw [Finset.sum_add_distrib]
    linarith [hDoubleCancel, hDiagCurv]

  calc
    nabla2Alpha
        (metricTraceInput (I := I) (Xsec x) (Ysec x)
          (fun q : Fin s => Vsec q x)) -
      nabla2Alpha
        (metricTraceInput (I := I) (Ysec x) (Xsec x)
          (fun q : Fin s => Vsec q x))
        =
        (-∑ q : Fin s,
          alpha
            (Function.update (fun r : Fin s => Vsec r x) q
              ((connectionRiemannCurvatureField (I := I) cov Xf Yf
                (fun p : M => Vsec q p)) x)))
        +
        (nablaAlpha
            (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) -
          nablaAlpha
            (Fin.cons ((cov Yf x) (Xsec x)) slots) +
          nablaAlpha
            (Fin.cons ((cov Xf x) (Ysec x)) slots)) := hExpanded
    _ =
        curvatureAction0SAtSlots (I := I) alpha
          (fun q : Fin s => Vsec q x)
          (fun q : Fin s =>
            (connectionRiemannCurvatureField (I := I) cov Xf Yf
              (fun p : M => Vsec q p)) x)
        +
        (-torsionCorrection0SAt (I := I) nablaAlpha
          ((cov.torsion x) (Xsec x) (Ysec x))
          (fun q : Fin s => Vsec q x)) := by
          rw [← hcurvActionSlots]
          simpa [slots] using congrArg
            (fun z =>
              curvatureAction0SAtSlots (I := I) alpha
                (fun q : Fin s => Vsec q x)
                (fun q : Fin s =>
                  (connectionRiemannCurvatureField (I := I) cov Xf Yf
                    (fun p : M => Vsec q p)) x) + z)
            htorsionFirstSlot
    _ =
        curvatureAction0SAt (I := I) Rm13 alpha (Xsec x) (Ysec x)
          (fun q : Fin s => Vsec q x)
        +
        (-torsionCorrection0SAt (I := I) nablaAlpha
          ((cov.torsion x) (Xsec x) (Ysec x))
          (fun q : Fin s => Vsec q x)) := by
          rw [← hcurvAction]
    _ =
        curvatureAction0SAt (I := I) Rm13 alpha (Xsec x) (Ysec x)
          (fun q : Fin s => Vsec q x) -
        torsionCorrection0SAt (I := I) nablaAlpha
          ((cov.torsion x) (Xsec x) (Ysec x))
          (fun q : Fin s => Vsec q x) := by
          ring




theorem tensor0S_ricciIdentity_with_torsion
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {s : ℕ}
    (alphaSec : Tensor0SSection (I := I) (M := M) s)
    (nablaAlphaSec : Tensor0SSection (I := I) (M := M) (s + 1))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (halpha : alphaSec x = alpha)
    (hnablaAlpha : nablaAlphaSec x = nablaAlpha)
    (hnabla2 : Nabla20SRealizesAt (I := I) s cov alphaSec nablaAlphaSec x
      nabla2Alpha) :
    Tensor0SRicciIdentityWithTorsionAt (I := I) Rm13 alpha nablaAlpha
      nabla2Alpha (fun X Y => cov.torsion x X Y) := by
  classical
  intro X Y slots
  obtain ⟨Xsec, hXx⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  obtain ⟨Ysec, hYx⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y
  let Vsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    fun q =>
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
        (slots q)).choose
  have hVx (q : Fin s) : Vsec q x = slots q :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
      (slots q)).choose_spec
  have hslots : (fun q : Fin s => Vsec q x) = slots := by
    funext q
    exact hVx q
  have hmain :=
    tensor0S_commutator_expansion_from_realizes
      (I := I) cov hcov Rm13 alphaSec nablaAlphaSec alpha nablaAlpha
      nabla2Alpha Xsec Ysec Vsec hRm13 halpha hnablaAlpha hnabla2
  simpa [Tensor0SRicciIdentityWithTorsionAt, hXx, hYx, hslots] using hmain

theorem tensor0S_ricciIdentity_of_torsionFree
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {s : ℕ}
    (alphaSec : Tensor0SSection (I := I) (M := M) s)
    (nablaAlphaSec : Tensor0SSection (I := I) (M := M) (s + 1))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (halpha : alphaSec x = alpha)
    (hnablaAlpha : nablaAlphaSec x = nablaAlpha)
    (hnabla2 : Nabla20SRealizesAt (I := I) s cov alphaSec nablaAlphaSec x
      nabla2Alpha)
    (htor : cov.torsion x = 0) :
    Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha := by
  intro X Y slots
  have h := tensor0S_ricciIdentity_with_torsion
    (I := I) cov hcov Rm13 alphaSec nablaAlphaSec alpha nablaAlpha
    nabla2Alpha hRm13 halpha hnablaAlpha hnabla2 X Y slots
  have hzero : cov.torsion x X Y = 0 := by
    simpa using congrArg (fun T => T X Y) htor
  have ht : nablaAlpha (Fin.cons (0 : TangentSpace I x) slots) = 0 := by
    exact nablaAlpha.map_coord_zero (0 : Fin (s + 1)) rfl
  simp [hzero, torsionCorrection0SAt, ht] at h
  simpa using h




def RicciIdentity0SAt {x : M} {s : ℕ}
    (comm curvatureAction :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x) :
    Prop :=
  comm = curvatureAction

omit [FiniteDimensional ℝ E] in
theorem ricci_identity_0s {x : M} {s : ℕ}
    (comm curvatureAction :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (h : RicciIdentity0SAt (I := I) comm curvatureAction) :
    comm = curvatureAction :=
  h

end DifferentialGeometry.Integral.Connection
