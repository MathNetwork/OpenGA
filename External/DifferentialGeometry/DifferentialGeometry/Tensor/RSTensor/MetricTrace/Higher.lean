import DifferentialGeometry.Tensor.RSTensor.MetricTrace.NablaTrace02

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

private theorem headFreezeNabla
    [T2Space M] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3)
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M}
    (hYzero : ((cov (fun p : M => Y p) x) (X x)) = 0)
    (U V : TangentSpace I x) :
    let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2 :=
      freezeHead03Field (I := I) (M := M) A Y
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B x (vec3 (I := I) (X x) U V) =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov A x (vec4 (I := I) (X x) (Y x) U V) := by
  classical
  let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    freezeHead03Field (I := I) (M := M) A Y
  obtain ⟨Usec, hUsec, hUcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x U
  obtain ⟨Vsec, hVsec, hVcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x V
  let V2 : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)
    | ⟨0, _⟩ => Usec
    | ⟨1, _⟩ => Vsec
  let V3 : Fin 3 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)
    | ⟨0, _⟩ => Y
    | ⟨1, _⟩ => Usec
    | ⟨2, _⟩ => Vsec
  have hBtot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov X B x (vec2 (I := I) U V)
  have hAtot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov X A x (vec3 (I := I) (Y x) U V)
  have hBeval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V2 B x
  have hAeval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V3 A x
  have hderiv :
      extDerivFun (I := I)
          (fun p : M => B p (fun a : Fin 2 => V2 a p)) x (X x) =
        extDerivFun (I := I)
          (fun p : M => A p (fun a : Fin 3 => V3 a p)) x (X x) := by
    have hfun :
        (fun p : M => B p (fun a : Fin 2 => V2 a p)) =
          fun p : M => A p (fun a : Fin 3 => V3 a p) := by
      funext p
      have hV2p :
          (fun a : Fin 2 => V2 a p) =
            vec2 (I := I) (Usec p) (Vsec p) := by
        funext a
        fin_cases a <;> rfl
      have hV3p :
          (fun a : Fin 3 => V3 a p) =
            vec3 (I := I) (Y p) (Usec p) (Vsec p) := by
        funext a
        fin_cases a <;> rfl
      rw [hV2p, hV3p]
      simp [B, metricTrace_tensor0S_curry_apply_cons, metricTrace_finCons_vec2_eq_vec3]
    rw [hfun]
  have hBcorr :
      (∑ a : Fin 2,
        B x
          (Function.update (fun b : Fin 2 => V2 b x) a
            ((cov (fun p : M => V2 a p) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_two]
    simp [V2, hUcov X, hVcov X, metricTrace_tensor0S_update_zero]
  have hAcorr :
      (∑ a : Fin 3,
        A x
          (Function.update (fun b : Fin 3 => V3 b x) a
            ((cov (fun p : M => V3 a p) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_three]
    simp [V3, hYzero, hUcov X, hVcov X, metricTrace_tensor0S_update_zero]
  calc
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B x (vec3 (I := I) (X x) U V)
        =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov X B x (vec2 (I := I) U V) := by
        simpa [metricTrace_finCons_vec2_eq_vec3 (I := I), hUsec, hVsec] using hBtot
    _ =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov X A x (vec3 (I := I) (Y x) U V) := by
        have hV2x :
            (fun a : Fin 2 => V2 a x) = vec2 (I := I) U V := by
          funext a
          fin_cases a <;> simp [V2, hUsec, hVsec, DifferentialGeometry.Integral.Connection.vec2]
        have hV3x :
            (fun a : Fin 3 => V3 a x) =
              vec3 (I := I) (Y x) U V := by
          funext a
          fin_cases a <;> simp [V3, hUsec, hVsec, DifferentialGeometry.Integral.Connection.vec3]
        rw [← hV2x, ← hV3x]
        rw [hBeval, hAeval, hderiv, hBcorr, hAcorr]
    _ =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov A x (vec4 (I := I) (X x) (Y x) U V) := by
        simpa [metricTrace_finCons_vec3_eq_vec4 (I := I)] using hAtot.symm







theorem nabla2Trace02
    [T2Space M] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv)
    (X Y : TangentSpace I x) :
    let traceA : M -> Real := fun y => metricTracePair0SAt (I := I) g (A y)
    let htrace : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) traceA :=
      trace02_smooth (I := I) g A
    let HessTrace := hessianSec (I := I) cov hcov traceA htrace
    let nablaA :=
      totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov A (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 cov hcov A)
    let nabla2A :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaA x
    HessTrace x (vec2 (I := I) X Y) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * nabla2A (vec4 (I := I) X Y (basis i) (basis j)) := by
  classical
  let traceA : M -> Real := fun y => metricTracePair0SAt (I := I) g (A y)
  let htrace : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) traceA :=
    trace02_smooth (I := I) g A
  let HessTrace := hessianSec (I := I) cov hcov traceA htrace
  let nablaA :=
    totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov A (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        2 cov hcov A)
  let nabla2A :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 cov nablaA x
  obtain ⟨Xsec, hXsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x X
  obtain ⟨Ysec, hYsec, hYcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov1 x Y
  let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    freezeHead03Field (I := I) (M := M) nablaA Ysec
  have hfirst :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov A nablaA := by
    simpa [nablaA] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov A
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 cov hcov A))
  have hB_eq_nabla (p : M) :
      B p =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov Ysec A p := by
    let basisp := coordinateFrameAt_toBasis (I := I) p
    apply ext0S_basis (I := I) basisp
    intro slots
    have hslots :
        (fun a : Fin 2 => basisp (slots a)) =
          vec2 (I := I) (basisp (slots 0)) (basisp (slots 1)) := by
      funext a
      fin_cases a <;> rfl
    simp only [component0S_apply]
    rw [hslots]
    have hreal := hfirst Ysec p
      (vec2 (I := I) (basisp (slots 0)) (basisp (slots 1)))
    have hcurry :
        B p (vec2 (I := I) (basisp (slots 0)) (basisp (slots 1))) =
          nablaA p (vec3 (I := I) (Ysec p)
            (basisp (slots 0)) (basisp (slots 1))) := by
      simp [B, metricTrace_tensor0S_curry_apply_cons, metricTrace_finCons_vec2_eq_vec3]
    rw [hcurry]
    simpa [metricTrace_finCons_vec2_eq_vec3 (I := I)] using hreal
  have hdu_fun :
      (fun p : M =>
          duSec (I := I) traceA htrace p (fun _ : Fin 1 => Ysec p)) =
        fun p : M => metricTracePair0SAt (I := I) g (B p) := by
    funext p
    have hd := dTrace02_eq (I := I) (M := M) cov g hmc A Ysec p
    dsimp [traceA] at hd
    rw [duSec_apply]
    change differential1FormFun (I := I)
        (fun y : M => metricTracePair0SAt (I := I) g (A y)) p
        (fun _ : Fin 1 => Ysec p) =
      metricTracePair0SAt (I := I) g (B p)
    rw [hd]
    rw [hB_eq_nabla p]
    rfl
  have hHessEval :=
    hessianSec_nabla (I := I) cov hcov traceA htrace x Xsec (Ysec x)
  let V1 : Fin 1 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)
    | _ => Ysec
  have heval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov Xsec V1 (duSec (I := I) traceA htrace) x
  have hcorr :
      (∑ a : Fin 1,
        duSec (I := I) traceA htrace x
          (Function.update (fun b : Fin 1 => V1 b x) a
            ((cov (fun p : M => V1 a p) x) (Xsec x)))) = 0 := by
    rw [Fin.sum_univ_one]
    simp [V1, hYcov Xsec, metricTrace_tensor0S_update_zero]
  have hleft :
      HessTrace x (vec2 (I := I) X Y) =
        differential1FormFun (I := I)
          (fun y : M => metricTracePair0SAt (I := I) g (B y)) x
          (fun _ : Fin 1 => X) := by
    calc
      HessTrace x (vec2 (I := I) X Y)
          = HessTrace x (vec2 (I := I) (Xsec x) (Ysec x)) := by
              rw [hXsec, hYsec]
      _ =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          1 cov Xsec (duSec (I := I) traceA htrace) x
          (fun _ : Fin 1 => Ysec x) := by
          simpa [HessTrace] using hHessEval
      _ =
        extDerivFun (I := I)
            (fun p : M =>
              duSec (I := I) traceA htrace p (fun a : Fin 1 => V1 a p))
            x (Xsec x) := by
          have hV1x :
              (fun a : Fin 1 => V1 a x) = fun _ : Fin 1 => Ysec x := by
            funext a
            fin_cases a
            rfl
          rw [← hV1x]
          rw [heval, hcorr]
          ring
      _ =
        extDerivFun (I := I)
            (fun y : M => metricTracePair0SAt (I := I) g (B y))
            x (Xsec x) := by
          rw [hdu_fun]
      _ =
        differential1FormFun (I := I)
          (fun y : M => metricTracePair0SAt (I := I) g (B y)) x
          (fun _ : Fin 1 => X) := by
          simp [differential1FormFun_apply_eq_extDerivFun, hXsec]
  have htraceB := dTrace02_eq (I := I) (M := M) cov g hmc B Xsec x
  have htraceB_sum :
      metricTracePair0SAt (I := I) g
          (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov Xsec B x) =
        ∑ i : Idx, ∑ j : Idx,
          gInv i j *
            nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 cov Xsec B x (vec2 (I := I) (basis i) (basis j)) := by
    exact metricTracePair0SAt_eq_sum_basis
      (I := I) g basis gInv hinv
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov Xsec B x)
  calc
    HessTrace x (vec2 (I := I) X Y)
        =
      differential1FormFun (I := I)
        (fun y : M => metricTracePair0SAt (I := I) g (B y)) x
        (fun _ : Fin 1 => X) := hleft
    _ =
      metricTracePair0SAt (I := I) g
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov Xsec B x) := by
        simpa [hXsec] using htraceB
    _ =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov Xsec B x (vec2 (I := I) (basis i) (basis j)) :=
        htraceB_sum
    _ =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * nabla2A (vec4 (I := I) X Y (basis i) (basis j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        have hfreeze :=
          headFreezeNabla (I := I) (M := M) cov hcov1 nablaA Xsec Ysec
            (hYcov Xsec) (basis i) (basis j)
        have hBtot :=
          totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) 2 cov Xsec B x
            (vec2 (I := I) (basis i) (basis j))
        have hBtot' :
            nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                2 cov Xsec B x (vec2 (I := I) (basis i) (basis j)) =
              totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I)
                (M := M) 2 cov B x
                (vec3 (I := I) (Xsec x) (basis i) (basis j)) := by
          simpa [metricTrace_finCons_vec2_eq_vec3 (I := I)] using hBtot.symm
        have h := hBtot'.trans hfreeze
        simpa [B, nabla2A, hXsec, hYsec, metricTrace_finCons_vec2_eq_vec3 (I := I)] using h

private theorem tailFreezeNabla
    [T2Space M] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M}
    (hYzero : ((cov (fun p : M => Y p) x) (X x)) = 0)
    (hZzero : ((cov (fun p : M => Z p) x) (X x)) = 0)
    (U V : TangentSpace I x) :
    let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2 :=
      freezeTail04Field (I := I) (M := M) A Y Z
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B x (vec3 (I := I) (X x) U V) =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov A x (Fin.cons (X x) (vec4 (I := I) U V (Y x) (Z x))) := by
  classical
  let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    freezeTail04Field (I := I) (M := M) A Y Z
  obtain ⟨Usec, hUsec, hUcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x U
  obtain ⟨Vsec, hVsec, hVcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x V
  let V2 : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)
    | ⟨0, _⟩ => Usec
    | ⟨1, _⟩ => Vsec
  let V4 : Fin 4 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)
    | ⟨0, _⟩ => Usec
    | ⟨1, _⟩ => Vsec
    | ⟨2, _⟩ => Y
    | ⟨3, _⟩ => Z
  have hBtot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov X B x (vec2 (I := I) U V)
  have hAtot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 cov X A x
      (vec4 (I := I) U V (Y x) (Z x))
  have hBeval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V2 B x
  have hAeval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V4 A x
  have hderiv :
      extDerivFun (I := I)
          (fun p : M => B p (fun a : Fin 2 => V2 a p)) x (X x) =
        extDerivFun (I := I)
          (fun p : M => A p (fun a : Fin 4 => V4 a p)) x (X x) := by
    have hfun :
        (fun p : M => B p (fun a : Fin 2 => V2 a p)) =
          fun p : M => A p (fun a : Fin 4 => V4 a p) := by
      funext p
      have hV2p :
          (fun a : Fin 2 => V2 a p) =
            vec2 (I := I) (Usec p) (Vsec p) := by
        funext a
        fin_cases a <;> rfl
      have hV4p :
          (fun a : Fin 4 => V4 a p) =
            vec4 (I := I) (Usec p) (Vsec p) (Y p) (Z p) := by
        funext a
        fin_cases a <;> rfl
      rw [hV2p, hV4p]
      simp [B, metricTrace_input_vec2_eq_vec4]
    rw [hfun]
  have hBcorr :
      (∑ a : Fin 2,
        B x
          (Function.update (fun b : Fin 2 => V2 b x) a
            ((cov (fun p : M => V2 a p) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_two]
    simp [V2, hUcov X, hVcov X, metricTrace_tensor0S_update_zero]
  have hAcorr :
      (∑ a : Fin 4,
        A x
          (Function.update (fun b : Fin 4 => V4 b x) a
            ((cov (fun p : M => V4 a p) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_four]
    simp [V4, hUcov X, hVcov X, hYzero, hZzero, metricTrace_tensor0S_update_zero]
  calc
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B x (vec3 (I := I) (X x) U V)
        =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov X B x (vec2 (I := I) U V) := by
        simpa [metricTrace_finCons_vec2_eq_vec3 (I := I), hUsec, hVsec] using hBtot
    _ =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov X A x (vec4 (I := I) U V (Y x) (Z x)) := by
        have hV2x :
            (fun a : Fin 2 => V2 a x) = vec2 (I := I) U V := by
          funext a
          fin_cases a <;> simp [V2, hUsec, hVsec, DifferentialGeometry.Integral.Connection.vec2]
        have hV4x :
            (fun a : Fin 4 => V4 a x) =
              vec4 (I := I) U V (Y x) (Z x) := by
          funext a
          fin_cases a <;> simp [V4, hUsec, hVsec, DifferentialGeometry.Integral.Connection.vec4]
        rw [← hV2x, ← hV4x]
        rw [hBeval, hAeval, hderiv, hBcorr, hAcorr]
    _ =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov A x (Fin.cons (X x) (vec4 (I := I) U V (Y x) (Z x))) := by
        simpa [hUsec, hVsec] using hAtot.symm

private theorem middleFreezeNabla
    [T2Space M] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M}
    (hYzero : ((cov (fun p : M => Y p) x) (X x)) = 0)
    (hZzero : ((cov (fun p : M => Z p) x) (X x)) = 0)
    (U V : TangentSpace I x) :
    let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2 :=
      freezeMiddle04Field (I := I) (M := M) A Y Z
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B x (vec3 (I := I) (X x) U V) =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov A x (Fin.cons (X x) (vec4 (I := I) U (Y x) (Z x) V)) := by
  classical
  let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    freezeMiddle04Field (I := I) (M := M) A Y Z
  obtain ⟨Usec, hUsec, hUcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x U
  obtain ⟨Vsec, hVsec, hVcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x V
  let V2 : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)
    | ⟨0, _⟩ => Usec
    | ⟨1, _⟩ => Vsec
  let V4 : Fin 4 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)
    | ⟨0, _⟩ => Usec
    | ⟨1, _⟩ => Y
    | ⟨2, _⟩ => Z
    | ⟨3, _⟩ => Vsec
  have hBtot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov X B x (vec2 (I := I) U V)
  have hAtot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 cov X A x
      (vec4 (I := I) U (Y x) (Z x) V)
  have hBeval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V2 B x
  have hAeval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V4 A x
  have hderiv :
      extDerivFun (I := I)
          (fun p : M => B p (fun a : Fin 2 => V2 a p)) x (X x) =
        extDerivFun (I := I)
          (fun p : M => A p (fun a : Fin 4 => V4 a p)) x (X x) := by
    have hfun :
        (fun p : M => B p (fun a : Fin 2 => V2 a p)) =
          fun p : M => A p (fun a : Fin 4 => V4 a p) := by
      funext p
      have hV2p :
          (fun a : Fin 2 => V2 a p) =
            vec2 (I := I) (Usec p) (Vsec p) := by
        funext a
        fin_cases a <;> rfl
      have hV4p :
          (fun a : Fin 4 => V4 a p) =
            vec4 (I := I) (Usec p) (Y p) (Z p) (Vsec p) := by
        funext a
        fin_cases a <;> rfl
      rw [hV2p, hV4p]
      simp only [B, freezeMiddle04Field_apply, freezeFirstTwo0S_apply]
      rw [metricTrace_input_vec2_eq_vec4]
      change (A p) (fun i =>
        vec4 (I := I) (Usec p) (Vsec p) (Y p) (Z p) (trace04Perm i)) = _
      apply congrArg (A p)
      funext q
      fin_cases q <;> simp [trace04Perm, DifferentialGeometry.Integral.Connection.vec4]
    rw [hfun]
  have hBcorr :
      (∑ a : Fin 2,
        B x
          (Function.update (fun b : Fin 2 => V2 b x) a
            ((cov (fun p : M => V2 a p) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_two]
    simp [V2, hUcov X, hVcov X, metricTrace_tensor0S_update_zero]
  have hAcorr :
      (∑ a : Fin 4,
        A x
          (Function.update (fun b : Fin 4 => V4 b x) a
            ((cov (fun p : M => V4 a p) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_four]
    simp [V4, hUcov X, hYzero, hZzero, hVcov X, metricTrace_tensor0S_update_zero]
  calc
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B x (vec3 (I := I) (X x) U V)
        =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov X B x (vec2 (I := I) U V) := by
        simpa [metricTrace_finCons_vec2_eq_vec3 (I := I), hUsec, hVsec] using hBtot
    _ =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov X A x (vec4 (I := I) U (Y x) (Z x) V) := by
        have hV2x :
            (fun a : Fin 2 => V2 a x) = vec2 (I := I) U V := by
          funext a
          fin_cases a <;> simp [V2, hUsec, hVsec, DifferentialGeometry.Integral.Connection.vec2]
        have hV4x :
            (fun a : Fin 4 => V4 a x) =
              vec4 (I := I) U (Y x) (Z x) V := by
          funext a
          fin_cases a <;> simp [V4, hUsec, hVsec, DifferentialGeometry.Integral.Connection.vec4]
        rw [← hV2x, ← hV4x]
        rw [hBeval, hAeval, hderiv, hBcorr, hAcorr]
    _ =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov A x (Fin.cons (X x) (vec4 (I := I) U (Y x) (Z x) V)) := by
        simpa [hUsec, hVsec] using hAtot.symm



theorem nablaTrace04
    [T2Space M] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv)
    (X Y Z : TangentSpace I x) :
    let traceA := trace04Field (I := I) (M := M) g A
    let nablaA :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov A x
    let nablaTraceA :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov traceA x
    nablaTraceA (vec3 (I := I) X Y Z) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * nablaA (Fin.cons X (vec4 (I := I) (basis i) Y Z (basis j))) := by
  classical
  let traceA := trace04Field (I := I) (M := M) g A
  let nablaA :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 cov A x
  let nablaTraceA :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov traceA x
  obtain ⟨Xsec, hXsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x X
  obtain ⟨Ysec, hYsec, hYcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x Y
  obtain ⟨Zsec, hZsec, hZcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x Z
  let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    freezeMiddle04Field (I := I) (M := M) A Ysec Zsec
  let traceB : M -> Real := fun y => metricTracePair0SAt (I := I) g (B y)
  let dTraceB := differential1FormFun (I := I) traceB x
  let V2 : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)
    | ⟨0, _⟩ => Ysec
    | ⟨1, _⟩ => Zsec
  have htot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov Xsec traceA x (vec2 (I := I) Y Z)
  have heval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov Xsec V2 traceA x
  have hfun :
      (fun p : M => traceA p (fun a : Fin 2 => V2 a p)) = traceB := by
    funext p
    have hV2p :
        (fun a : Fin 2 => V2 a p) = vec2 (I := I) (Ysec p) (Zsec p) := by
      funext a
      fin_cases a <;> rfl
    rw [hV2p]
    simp [traceA, traceB, B, metricTraceFirstTwo0SAt]
  have hcorr :
      (∑ a : Fin 2,
        traceA x
          (Function.update (fun b : Fin 2 => V2 b x) a
            ((cov (fun p : M => V2 a p) x) (Xsec x)))) = 0 := by
    rw [Fin.sum_univ_two]
    simp [traceA, V2, hYcov Xsec, hZcov Xsec, metricTrace_tensor0S_update_zero]
  have hleft :
      nablaTraceA (vec3 (I := I) X Y Z) =
        dTraceB (fun _ : Fin 1 => X) := by
    calc
      nablaTraceA (vec3 (I := I) X Y Z)
          =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov Xsec traceA x (vec2 (I := I) Y Z) := by
          simpa [nablaTraceA, hXsec, metricTrace_finCons_vec2_eq_vec3 (I := I)] using htot
      _ = extDerivFun (I := I) traceB x (Xsec x) := by
          have hV2x :
              (fun a : Fin 2 => V2 a x) = vec2 (I := I) Y Z := by
            funext a
            fin_cases a <;> simp [V2, hYsec, hZsec, DifferentialGeometry.Integral.Connection.vec2]
          rw [← hV2x]
          rw [heval, hcorr]
          rw [hfun]
          ring
      _ = dTraceB (fun _ : Fin 1 => X) := by
          simp [dTraceB, differential1FormFun_apply_eq_extDerivFun, hXsec]
  have htrace02 :
      dTraceB (fun _ : Fin 1 => X) =
        ∑ i : Idx, ∑ j : Idx,
          gInv i j *
            (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 cov B x) (vec3 (I := I) X (basis i) (basis j)) := by
    simpa [B, traceB, dTraceB] using
      nablaTrace02 (I := I) (M := M) cov g hmc B basis gInv hinv X
  dsimp
  rw [hleft, htrace02]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hfreeze :=
    middleFreezeNabla (I := I) (M := M) cov hcov A Xsec Ysec Zsec
      (hYcov Xsec) (hZcov Xsec) (basis i) (basis j)
  simpa [B, nablaA, hXsec, hYsec, hZsec] using hfreeze


end

end DifferentialGeometry.Integral.Connection
