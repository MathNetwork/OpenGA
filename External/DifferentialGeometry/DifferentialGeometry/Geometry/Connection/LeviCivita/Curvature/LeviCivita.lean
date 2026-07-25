import DifferentialGeometry.Geometry.Curvature.Components.Basic
import DifferentialGeometry.Geometry.Curvature.Components.Lowering
import DifferentialGeometry.Geometry.Curvature.Components.TraceOneForm
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Curvature.Components.LocalFrame
import DifferentialGeometry.Geometry.Curvature.Components.Christoffel
import DifferentialGeometry.Geometry.Curvature.Components.RicciIdentity
import DifferentialGeometry.Geometry.Curvature.Realized.CurvatureProducers
import DifferentialGeometry.Geometry.Curvature.Bianchi
import DifferentialGeometry.Geometry.Connection.LeviCivita.Hessian
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricFlatBasis
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Connection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricCoord
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Model
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Christoffel
import DifferentialGeometry.Geometry.Connection.LeviCivita.Torsion
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Basic
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Pairing
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.ConnectionProduct
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Moving
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Smoothness
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.Tensor0S
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Smooth
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Tangent
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Endomorphism
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.OneJet
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Connection
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Trace04
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.NablaTrace02
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Higher
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.ModelMixed
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
variable [SigmaCompactSpace M] [T2Space M]







omit [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] in
private theorem directionalDeriv_congr_nhds
    {X : (p : M) -> TangentSpace I p} {f h : M -> Real} {x : M}
    (hfh : f =ᶠ[𝓝 x] h) :
    directionalDerivAlong (I := I) X f x = directionalDerivAlong (I := I) X h x := by
  have hx : f x = h x := hfh.self_of_nhds
  unfold directionalDerivAlong extDerivFun
  rw [hfh.mfderiv_eq]
  rw [hx]

omit [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] in
private theorem directionalDeriv_add_fun
    (X : (p : M) -> TangentSpace I p) {f h : M -> Real} (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    directionalDerivAlong (I := I) X (fun y : M => f y + h y) x =
        directionalDerivAlong (I := I) X f x +
        directionalDerivAlong (I := I) X h x := by
  unfold directionalDerivAlong
  change (extDerivFun (I := I) (f + h) x) (X x) =
    (extDerivFun (I := I) f x) (X x) + (extDerivFun (I := I) h x) (X x)
  rw [extDerivFun_add hf hh]
  rw [ContinuousLinearMap.add_apply]

omit [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] in
private theorem directionalDeriv_sub_fun
    (X : (p : M) -> TangentSpace I p) {f h : M -> Real} (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    directionalDerivAlong (I := I) X (fun y : M => f y - h y) x =
        directionalDerivAlong (I := I) X f x -
        directionalDerivAlong (I := I) X h x := by
  unfold directionalDerivAlong
  change (extDerivFun (I := I) (f - h) x) (X x) =
    (extDerivFun (I := I) f x) (X x) - (extDerivFun (I := I) h x) (X x)
  have hsub :
      extDerivFun (I := I) (f - h) x =
        extDerivFun (I := I) f x - extDerivFun (I := I) h x := by
    unfold extDerivFun
    ext v
    simp [mfderiv_sub hf hh, NormedSpace.fromTangentSpace]
    rfl
  rw [hsub]
  rw [ContinuousLinearMap.sub_apply]

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] in
private theorem oneForm_eval_const_add {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (A B : TangentSpace I x) :
    alpha (fun _ : Fin 1 => A + B) =
      alpha (fun _ : Fin 1 => A) + alpha (fun _ : Fin 1 => B) := by
  rw [← cotangentToDual_apply_gen (I := I) alpha (A + B)]
  rw [← cotangentToDual_apply_gen (I := I) alpha A]
  rw [← cotangentToDual_apply_gen (I := I) alpha B]
  exact map_add (cotangentToDual_gen (I := I) alpha) A B

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] in
private theorem oneForm_eval_const_sub {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (A B : TangentSpace I x) :
    alpha (fun _ : Fin 1 => A - B) =
      alpha (fun _ : Fin 1 => A) - alpha (fun _ : Fin 1 => B) := by
  rw [← cotangentToDual_apply_gen (I := I) alpha (A - B)]
  rw [← cotangentToDual_apply_gen (I := I) alpha A]
  rw [← cotangentToDual_apply_gen (I := I) alpha B]
  exact map_sub (cotangentToDual_gen (I := I) alpha) A B

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] in
private theorem oneForm_eval_const_neg {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (A : TangentSpace I x) :
    alpha (fun _ : Fin 1 => -A) = -alpha (fun _ : Fin 1 => A) := by
  rw [← cotangentToDual_apply_gen (I := I) alpha (-A)]
  rw [← cotangentToDual_apply_gen (I := I) alpha A]
  exact map_neg (cotangentToDual_gen (I := I) alpha) A

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] in
private theorem oneForm_eval_const_smul {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (c : Real) (A : TangentSpace I x) :
    alpha (fun _ : Fin 1 => c • A) = c * alpha (fun _ : Fin 1 => A) := by
  rw [← cotangentToDual_apply_gen (I := I) alpha (c • A)]
  rw [← cotangentToDual_apply_gen (I := I) alpha A]
  simp [smul_eq_mul]

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] in
private theorem oneForm_eval_const_sub_add_sub {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (A B C D : TangentSpace I x) :
    alpha (fun _ : Fin 1 => A - B + C - D) =
      alpha (fun _ : Fin 1 => A) - alpha (fun _ : Fin 1 => B) +
        alpha (fun _ : Fin 1 => C) - alpha (fun _ : Fin 1 => D) := by
  rw [oneForm_eval_const_sub (I := I) alpha (A - B + C) D]
  rw [oneForm_eval_const_add (I := I) alpha (A - B) C]
  rw [oneForm_eval_const_sub (I := I) alpha A B]

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] in
private theorem mdifferentiableAt_metric_inner
    (g : SmoothRiemannianMetric I M)
    {X Y : (p : M) -> TangentSpace I p} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    MDiffAt (fun y : M => g.inner y (X y) (Y y)) x := by
  have hg :
      MDifferentiableAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real))
        (fun y : M =>
          TotalSpace.mk' (E →L[Real] E →L[Real] Real)
            (E := fun y : M =>
              TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
            y (g.inner y)) x :=
    g.contMDiff.mdifferentiableAt (by simp)
  have htotal :
      MDifferentiableAt I (I.prod 𝓘(Real, Real))
        (fun y : M =>
          TotalSpace.mk' Real (E := Bundle.Trivial M Real) y
            (g.inner y (X y) (Y y))) x := by
    exact MDifferentiableAt.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) hg hX hY
  rw [mdifferentiableAt_totalSpace] at htotal
  exact htotal.2

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] in
private theorem contMDiffAt_metric_inner
    (g : SmoothRiemannianMetric I M)
    {X Y : (p : M) -> TangentSpace I p} {x : M} {n : WithTop ℕ∞}
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) n (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(Real, E)) n (T% Y) x)
    (hn : n ≤ ∞) :
    ContMDiffAt I 𝓘(Real, Real) n
      (fun y : M => g.inner y (X y) (Y y)) x := by
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) n
        (fun y : M =>
          TotalSpace.mk' (E →L[Real] E →L[Real] Real)
            (E := fun y : M =>
              TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
            y (g.inner y)) x :=
    (g.contMDiff.contMDiffAt).of_le hn
  have htotal :
      ContMDiffAt I (I.prod 𝓘(Real, Real)) n
        (fun y : M =>
          TotalSpace.mk' Real (E := Bundle.Trivial M Real) y
            (g.inner y (X y) (Y y))) x := by
    exact ContMDiffAt.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) hg hX hY
  rw [contMDiffAt_totalSpace] at htotal
  exact htotal.2


omit [CompleteSpace E] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem nabla0SFun_two_eval_smooth_slots
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (A : TwoTensorSection (I := I) (M := M)) (x : M) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov X A x) (vec2 (Y x) (Z x)) =
      extDerivFun (I := I)
          (fun p : M => A p (vec2 (Y p) (Z p))) x (X x) -
        (A x) (vec2 ((cov (fun p : M => Y p) x) (X x)) (Z x)) -
        (A x) (vec2 (Y x) ((cov (fun p : M => Z p) x) (X x))) := by
  classical
  let Vsec : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a => if a = 0 then Y else Z
  let V : Fin 2 -> (p : M) -> TangentSpace I p := fun a p => Vsec a p
  have hslots : (fun a : Fin 2 => V a x) = vec2 (Y x) (Z x) := by
    funext a
    fin_cases a <;> simp [V, Vsec, vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hpair : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => A p (fun a : Fin 2 => V a p)) x := by
    have hEval := TensorMultilinear.contMDiff_tensor0SField_apply
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := 2)
      A Vsec
    exact (by
      simpa [V] using hEval.contMDiffAt.mdifferentiableAt (by simp))
  have hV : ∀ a : Fin 2, MDiffAt (T% (V a)) x := by
    intro a
    exact (Vsec a).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hVmodel : ∀ a : Fin 2,
      DifferentiableWithinAt Real
        (TensorLieDeriv.tangentFieldModelInChart (𝕜 := Real) (I := I) x (V a))
        (Set.range I) (extChartAt I x x) := by
    intro a
    exact
      tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
        (I := I) (V a) x (Vsec a).contMDiff.contMDiffAt
  have hcoord : ∀ a : Fin 2, ∀ i : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord i
            (TensorLieDeriv.tangentFieldModelInChart (𝕜 := Real) (I := I) x (V a)
              (extChartAt I x p))) x := by
    intro a i
    exact
      tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
        (I := I) (V a) x (Vsec a).contMDiff.contMDiffAt i
  have h := Tensor0SBundle.nabla0SFun_eval_coordFrame_moving_raw
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (s := 2) cov X V A x hpair hV hVmodel hcoord
  have hsum :
      (∑ a : Fin 2,
          A x
            (Function.update (fun b : Fin 2 => V b x) a
              ((cov (V a) x) (X x)))) =
        A x (vec2 ((cov (fun p : M => Y p) x) (X x)) (Z x)) +
          A x (vec2 (Y x) ((cov (fun p : M => Z p) x) (X x))) := by
    have h0 :
        Function.update (fun b : Fin 2 => V b x) 0
            ((cov (V 0) x) (X x)) =
          vec2 ((cov (fun p : M => Y p) x) (X x)) (Z x) := by
      funext q
      fin_cases q <;> simp [V, Vsec, vec2, DifferentialGeometry.Integral.Connection.vec2]
    have h1 :
        Function.update (fun b : Fin 2 => V b x) 1
            ((cov (V 1) x) (X x)) =
          vec2 (Y x) ((cov (fun p : M => Z p) x) (X x)) := by
      funext q
      fin_cases q <;> simp [V, Vsec, vec2, DifferentialGeometry.Integral.Connection.vec2]
    rw [Fin.sum_univ_two]
    rw [h0, h1]
  have hscalar :
      (fun p : M => A p (fun a : Fin 2 => V a p)) =
        fun p : M => A p (vec2 (Y p) (Z p)) := by
    funext p
    congr 1
    funext a
    fin_cases a <;> simp [V, Vsec, vec2, DifferentialGeometry.Integral.Connection.vec2]
  calc
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov X A x) (vec2 (Y x) (Z x))
        = (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X A x) (fun a : Fin 2 => V a x) := by rw [hslots]
    _ = extDerivFun (I := I) (fun p : M => A p (fun a : Fin 2 => V a p))
          x (X x) -
        ∑ a : Fin 2,
          A x
            (Function.update (fun b : Fin 2 => V b x) a
              ((cov (V a) x) (X x))) := h
    _ = extDerivFun (I := I)
          (fun p : M => A p (vec2 (Y p) (Z p))) x (X x) -
        (A x) (vec2 ((cov (fun p : M => Y p) x) (X x)) (Z x)) -
        (A x) (vec2 (Y x) ((cov (fun p : M => Z p) x) (X x))) := by
      rw [hscalar, hsum]
      ring

omit [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
private theorem cov_smoothSections_apply_contMDiffAt_one
    [IsManifold I 2 M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, (cov (fun q : M => Y q) p) (X p)⟩ :
          TotalSpace E (TangentSpace I : M -> Type _))) x := by
  haveI : IsManifold I ((1 : WithTop ℕ∞) + 1) M := by
    have h : ((1 : WithTop ℕ∞) + 1) = (2 : WithTop ℕ∞) := by
      norm_num
    exact h.symm ▸ (inferInstance : IsManifold I 2 M)
  have hY :
      ContMDiffOn I (I.prod 𝓘(Real, E)) ((1 : WithTop ℕ∞) + 1)
        (fun p : M =>
          (⟨p, Y p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) Set.univ :=
    (Y.contMDiff.of_le
      (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.2 le_top)).contMDiffOn
  have hcovY :
      ContMDiffOn I (I.prod 𝓘(Real, E →L[Real] E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (fun q : M => Y q) p⟩ :
            TotalSpace (E →L[Real] E)
              (fun p : M =>
                TangentSpace I p →L[Real] TangentSpace I p))) Set.univ :=
    (hcov isOpen_univ).contMDiff hY
  have hX :
      ContMDiffOn I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, X p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) Set.univ :=
    (X.contMDiff.of_le
      (by
        change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.2 le_top)).contMDiffOn
  exact (hcovY.clm_bundle_apply hX).contMDiffAt (by simp)

omit [CompleteSpace E] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem coordinateFrame_coeff_mdiffAt_of_contMDiffAt_one
    (Z : (x : M) -> TangentSpace I x) {x₀ : M}
    (hZ : ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
      (fun y : M => (⟨y, Z y⟩ :
        TotalSpace E (TangentSpace I : M -> Type _))) x₀)
    (j : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀ := by
  let e := coordinateTrivializationAt (I := I) x₀
  have hx : x₀ ∈ e.baseSet := by
    simp [e, coordinateTrivializationAt]
  have hcoeff :
      ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀ := by
    have hraw :=
      contMDiffAt_localFrame_coeff
        (I := I) (V := TangentSpace I) (e := e)
        (b := Module.finBasis Real E) (s := Z)
        (k := (1 : WithTop ℕ∞)) hx hZ j
    simpa [e, coordinateTrivializationAt, coordinateFrameAt_isLocalFrame_one,
      coordinateFrameAt] using hraw
  exact hcoeff.mdifferentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)

omit [CompleteSpace E] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem oneForm_eval_moving_C1_slot_mdiffAt
    (alpha : OneFormSection (I := I) (M := M))
    (Z : (x : M) -> TangentSpace I x) {x₀ : M}
    (hZ : ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
      (fun y : M =>
        (⟨y, Z y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => alpha y (fun _ : Fin 1 => Z y)) x₀ := by
  classical
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  let zfun : CoordinateIdx (𝕜 := Real) E -> M -> Real :=
    fun j y => hframe.coeff j y (Z y)
  let afun : CoordinateIdx (𝕜 := Real) E -> M -> Real :=
    fun j y => alpha y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)
  have hsum :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          ∑ j : CoordinateIdx (𝕜 := Real) E, zfun j y * afun j y) x₀ := by
    have hraw :=
      (MDifferentiableAt.sum (t := Finset.univ)
        (f := fun j : CoordinateIdx (𝕜 := Real) E =>
          fun y : M => zfun j y * afun j y)
        (fun j _ =>
          (coordinateFrame_coeff_mdiffAt_of_contMDiffAt_one (I := I) Z hZ j).mul
            ((DifferentialGeometry.Tensor.Coordinates.oneForm_eval_coordinateFrame_contMDiffAt
              (I := I) alpha x₀ j).mdifferentiableAt (by simp))))
    have hfun :
        (fun y : M =>
          ∑ j : CoordinateIdx (𝕜 := Real) E, zfun j y * afun j y) =
        Finset.univ.sum (fun j : CoordinateIdx (𝕜 := Real) E =>
          fun y : M => zfun j y * afun j y) := by
      funext y
      simp
    rw [hfun]
    exact hraw
  refine hsum.congr_of_eventuallyEq ?_
  simpa [zfun, afun, hframe] using
    (DifferentialGeometry.Tensor.Coordinates.oneForm_pair_coordFrame_eventually
      (I := I) Z alpha x₀)

omit [CompleteSpace E] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem nablaOneFormSectionRealizes_eval_moving_C1_slot
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (hnabla : NablaOneFormSectionRealizes (I := I) cov alpha nablaAlpha)
    (Z : (x : M) -> TangentSpace I x)
    (x : M)
    (hZ : ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
      (fun y : M =>
        (⟨y, Z y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x) :
    nablaAlpha x (vec2 (X x) (Z x)) =
      extDerivFun (I := I) (fun y : M => alpha y (fun _ : Fin 1 => Z y)) x (X x) -
        alpha x (fun _ : Fin 1 => (cov Z x) (X x)) := by
  have hraw := nabla0SFun_one_eval_coordFrame_moving_raw
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    cov X Z alpha x
    (modelDeriv_eq_coordDeriv0SAt (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) X x alpha)
    (fun j => coordinateFrame_coeff_mdiffAt_of_contMDiffAt_one
      (I := I) Z hZ j)
    (fun j => (DifferentialGeometry.Tensor.Coordinates.oneForm_eval_coordinateFrame_contMDiffAt
      (I := I) alpha x j).mdifferentiableAt (by simp))
    (hZ.mdifferentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0))
  have hreal := hnabla x X (Z x)
  calc
    nablaAlpha x (vec2 (X x) (Z x))
        = (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            1 cov X alpha x) (fun _ : Fin 1 => Z x) := hreal
    _ = extDerivFun (I := I) (fun y : M => alpha y (fun _ : Fin 1 => Z y)) x (X x) -
        alpha x (fun _ : Fin 1 => (cov Z x) (X x)) := hraw

omit [CompleteSpace E] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] in
private theorem mdifferentiableAt_tangentConstAt_of_mem
    (x₀ : M) (v : TangentSpace I x₀) {p : M}
    (hp : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    MDiffAt
      (T% (tangentConstAt (I := I) x₀ v :
        (p : M) -> TangentSpace I p)) p := by
  unfold tangentConstAt
  exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
    (𝕜 := Real) (I := I) (x₀ := x₀) (p := p) v hp

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
private theorem contMDiffAt_tangentConstAt_self_minTwo
    (x₀ : M) (v : TangentSpace I x₀) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
      (T% (tangentConstAt (I := I) x₀ v :
        (p : M) -> TangentSpace I p)) x₀ := by
  haveI : IsManifold I (minSmoothness Real 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (inferInstance : IsManifold I 2 M)
  haveI : IsManifold I ((minSmoothness Real 2 : WithTop ℕ∞) + 1) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    have h : ((2 : WithTop ℕ∞) + 1) = (3 : WithTop ℕ∞) := by
      norm_num
    exact h.symm ▸ (inferInstance : IsManifold I 3 M)
  have h_on :
      ContMDiffOn I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
        (T% (tangentConstAt (I := I) x₀ v :
          (p : M) -> TangentSpace I p))
        (trivializationAt E (TangentSpace I) x₀).baseSet := by
    simpa [tangentConstAt] using
      (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
        (𝕜 := Real) (I := I) (M := M)
        (n := minSmoothness Real 2) x₀ v)
  exact (h_on x₀ (mem_baseSet_trivializationAt E (TangentSpace I) x₀)).contMDiffAt
    ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x₀))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem cov_tangentConstAt_apply_contMDiffOn_baseSet
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (x₀ : M) (v w : TangentSpace I x₀) :
    ContMDiffOn I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
      (T% (fun p : M =>
        (cov (tangentConstAt (I := I) x₀ w) p)
          ((tangentConstAt (I := I) x₀ v) p)))
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  let e := trivializationAt E (TangentSpace I) x₀
  haveI : IsManifold I ((1 : WithTop ℕ∞) + 1) M := by
    have h : ((1 : WithTop ℕ∞) + 1) = (2 : WithTop ℕ∞) := by
      norm_num
    exact h.symm ▸ (inferInstance : IsManifold I 2 M)
  haveI : IsManifold I (((1 : WithTop ℕ∞) + 1) + 1) M := by
    have h : (((1 : WithTop ℕ∞) + 1) + 1) = (3 : WithTop ℕ∞) := by
      norm_num
    exact h.symm ▸ (inferInstance : IsManifold I 3 M)
  have hw :
      ContMDiffOn I (I.prod 𝓘(Real, E)) ((1 : WithTop ℕ∞) + 1)
        (T% (tangentConstAt (I := I) x₀ w :
          (p : M) -> TangentSpace I p)) e.baseSet := by
    simpa [e, tangentConstAt] using
      (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
        (𝕜 := Real) (I := I) (M := M)
        (n := (1 : WithTop ℕ∞) + 1) x₀ w)
  have hcovw :
      ContMDiffOn I (I.prod 𝓘(Real, E →L[Real] E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (tangentConstAt (I := I) x₀ w) p⟩ :
            TotalSpace (E →L[Real] E)
              (fun p : M =>
                TangentSpace I p →L[Real] TangentSpace I p)))
        e.baseSet := by
    exact (hcov e.open_baseSet).contMDiff hw
  have hv :
      ContMDiffOn I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (T% (tangentConstAt (I := I) x₀ v :
          (p : M) -> TangentSpace I p)) e.baseSet := by
    simpa [e, tangentConstAt] using
      (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
        (𝕜 := Real) (I := I) (M := M)
        (n := (1 : WithTop ℕ∞)) x₀ v)
  simpa [e] using hcovw.clm_bundle_apply hv

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem cov_tangentConstAt_apply_mdiffAt_of_mem
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (x₀ : M) (v w : TangentSpace I x₀) {p : M}
    (hp : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    MDiffAt
      (T% (fun q : M =>
        (cov (tangentConstAt (I := I) x₀ w) q)
          ((tangentConstAt (I := I) x₀ v) q))) p := by
  let e := trivializationAt E (TangentSpace I) x₀
  have h_on :=
    cov_tangentConstAt_apply_contMDiffOn_baseSet (I := I) cov hcov x₀ v w
  exact ((h_on p (by simpa [e] using hp)).contMDiffAt
    (e.open_baseSet.mem_nhds hp)).mdifferentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)

omit [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] in
private theorem cov_smooth_apply_mdiffAt_one
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    MDiffAt (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) x := by
  exact (CovariantDerivative.smoothSections_cov_contMDiffAt_one
    (𝕜 := Real) (I := I) cov hcov X Y x).mdifferentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)

omit [IsManifold I 2 M] [IsManifold I 3 M] in
omit [CompleteSpace E] [SigmaCompactSpace M] in
private theorem exists_contMDiffSection_eventuallyEq_tangentConstAt
    (x : M) (v : TangentSpace I x) :
    ∃ V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
      (fun p : M => V p) =ᶠ[𝓝 x] tangentConstAt (I := I) x v ∧ V x = v := by
  classical
  let e := trivializationAt E (TangentSpace I) x
  let b := Module.finBasis Real E
  have he : x ∈ e.baseSet := by
    simp [e]
  have hframe := e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) b
  obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he
  let V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ∑ i, (b.repr v i) • s' i
  have hV : (fun p : M => V p) =ᶠ[𝓝 x] tangentConstAt (I := I) x v := by
    filter_upwards [hs', e.open_baseSet.mem_nhds he] with p hs'p hp
    have hbasis :
        (∑ i, (b.repr v i) • e.localFrame b i p) =
          tangentConstAt (I := I) x v p := by
      have hframe_apply (i) :
          e.localFrame b i p = e.symmL Real p (b i) := by
        rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
          (e := e) (b := b) (i := i) hp]
        simp [e, Bundle.Trivialization.basisAt, Trivialization.symmL_apply]
      calc
        (∑ i, (b.repr v i) • e.localFrame b i p)
            = ∑ i, (b.repr v i) • e.symmL Real p (b i) := by
              exact Finset.sum_congr rfl (fun i _ => by rw [hframe_apply i])
        _ = e.symmL Real p (∑ i, (b.repr v i) • b i) := by
              rw [map_sum]
              simp
        _ = tangentConstAt (I := I) x v p := by
              rw [b.sum_repr]
              rfl
    calc
      V p = ∑ i, (b.repr v i) • s' i p := by
        simp [V, ContMDiffSection.finset_sum_apply_gen]
      _ = ∑ i, (b.repr v i) • e.localFrame b i p := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hs'p i]
      _ = tangentConstAt (I := I) x v p := hbasis
  refine ⟨V, hV, ?_⟩
  exact hV.self_of_nhds.trans (tangentConstAt_self (I := I) x v)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {x : M} (X Y Z : TangentSpace I x)
    (Xs Ys Zs :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hX : (fun p : M => Xs p) =ᶠ[𝓝 x] tangentConstAt (I := I) x X)
    (hY : (fun p : M => Ys p) =ᶠ[𝓝 x] tangentConstAt (I := I) x Y)
    (hZ : (fun p : M => Zs p) =ᶠ[𝓝 x] tangentConstAt (I := I) x Z) :
    connectionRiemannCurvatureField (I := I) cov
        (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x =
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => Xs p) (fun p : M => Ys p) (fun p : M => Zs p) x := by
  classical
  let Xc : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x Z
  have hX' : Xc =ᶠ[𝓝 x] fun p : M => Xs p := by
    simpa [Xc] using hX.symm
  have hY' : Yc =ᶠ[𝓝 x] fun p : M => Ys p := by
    simpa [Yc] using hY.symm
  have hZ' : Zc =ᶠ[𝓝 x] fun p : M => Zs p := by
    simpa [Zc] using hZ.symm
  have hXx : Xc x = Xs x := hX'.self_of_nhds
  have hYx : Yc x = Ys x := hY'.self_of_nhds
  have hbr :
      VectorField.mlieBracket I Xc Yc x =
        VectorField.mlieBracket I (fun p : M => Xs p) (fun p : M => Ys p) x := by
    exact hX'.mlieBracket_vectorField_eq (I := I) hY'
  have hZ_at :
      cov Zc x = cov (fun p : M => Zs p) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (by simpa [Zc] using mdifferentiableAt_tangentConstAt_self (I := I) x Z)
      (Zs.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      (by simp) hZ'
  let e := trivializationAt E (TangentSpace I) x
  have he : x ∈ e.baseSet := by
    simp [e]
  have hinnerY :
      (fun p : M => (cov Zc p) (Yc p)) =ᶠ[𝓝 x]
        (fun p : M => (cov (fun q : M => Zs q) p) (Ys p)) := by
    rcases mem_nhds_iff.mp (hZ' : {p : M | Zc p = Zs p} ∈ 𝓝 x) with
      ⟨U, hUsub, hUopen, hxU⟩
    filter_upwards [hUopen.mem_nhds hxU, hY', e.open_baseSet.mem_nhds he] with
      p hpU hYp hpE
    have hZp : Zc =ᶠ[𝓝 p] fun q : M => Zs q :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpU) fun q hq => hUsub hq
    have hZc_md : MDiffAt (T% Zc) p := by
      exact mdifferentiableAt_tangentConstAt_of_mem (I := I) x Z (by simpa [e] using hpE)
    have hcovp :
        cov Zc p = cov (fun q : M => Zs q) p := by
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        hZc_md (Zs.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (by simp) hZp
    rw [hcovp, hYp]
  have hinnerX :
      (fun p : M => (cov Zc p) (Xc p)) =ᶠ[𝓝 x]
        (fun p : M => (cov (fun q : M => Zs q) p) (Xs p)) := by
    rcases mem_nhds_iff.mp (hZ' : {p : M | Zc p = Zs p} ∈ 𝓝 x) with
      ⟨U, hUsub, hUopen, hxU⟩
    filter_upwards [hUopen.mem_nhds hxU, hX', e.open_baseSet.mem_nhds he] with
      p hpU hXp hpE
    have hZp : Zc =ᶠ[𝓝 p] fun q : M => Zs q :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpU) fun q hq => hUsub hq
    have hZc_md : MDiffAt (T% Zc) p := by
      exact mdifferentiableAt_tangentConstAt_of_mem (I := I) x Z (by simpa [e] using hpE)
    have hcovp :
        cov Zc p = cov (fun q : M => Zs q) p := by
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        hZc_md (Zs.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (by simp) hZp
    rw [hcovp, hXp]
  have hcovZY :
      cov (fun p : M => (cov Zc p) (Yc p)) x =
        cov (fun p : M => (cov (fun q : M => Zs q) p) (Ys p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (by
        simpa [Zc, Yc] using
          cov_tangentConstAt_apply_mdiffAt_of_mem (I := I) cov hcov x Y Z he)
      (cov_smooth_apply_mdiffAt_one (I := I) cov hcov Ys Zs x)
      (by simp) hinnerY
  have hcovZX :
      cov (fun p : M => (cov Zc p) (Xc p)) x =
        cov (fun p : M => (cov (fun q : M => Zs q) p) (Xs p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (by
        simpa [Zc, Xc] using
          cov_tangentConstAt_apply_mdiffAt_of_mem (I := I) cov hcov x X Z he)
      (cov_smooth_apply_mdiffAt_one (I := I) cov hcov Xs Zs x)
      (by simp) hinnerX
  have hXval : tangentConstAt (I := I) x X x = Xs x := by
    simpa [Xc] using hXx
  have hYval : tangentConstAt (I := I) x Y x = Ys x := by
    simpa [Yc] using hYx
  simp only [connectionRiemannCurvatureField, DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField]
  rw [hcovZY, hcovZX, hZ_at, hbr]
  rw [hXval, hYval]

omit [CompleteSpace E] [SigmaCompactSpace M] in
private theorem rm04_tconst_eval
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm04 : Rm04RealizesConnection (I := I) g cov Rm04)
    {x : M} (X Y Z W : TangentSpace I x) :
    Rm04 x (vec4 X Y Z W) =
      g.inner x W
        ((connectionRiemannCurvatureField (I := I) cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z)) x) := by
  obtain ⟨Wsec, hWnear, hWx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x W
  obtain ⟨Xsec, hXnear, hXx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x X
  obtain ⟨Ysec, hYnear, hYx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x Y
  obtain ⟨Zsec, hZnear, hZx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x Z
  have hcurv :
      connectionRiemannCurvatureField (I := I) cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x =
        connectionRiemannCurvatureField (I := I) cov
          (fun p : M => Xsec p) (fun p : M => Ysec p) (fun p : M => Zsec p) x :=
    connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst
      (I := I) cov hcov X Y Z Xsec Ysec Zsec hXnear hYnear hZnear
  have hRm := hRm04 Xsec Ysec Zsec Wsec x
  calc
    Rm04 x (vec4 X Y Z W)
        = Rm04 x (vec4 (Xsec x) (Ysec x) (Zsec x) (Wsec x)) := by
          simp [hWx, hXx, hYx, hZx]
    _ = g.inner x (Wsec x)
        ((connectionRiemannCurvatureField (I := I) cov
          (fun p : M => Xsec p) (fun p : M => Ysec p) (fun p : M => Zsec p)) x) := hRm
    _ = g.inner x W
        ((connectionRiemannCurvatureField (I := I) cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z)) x) := by
          rw [hWx, ← hcurv]





omit [SigmaCompactSpace M] [T2Space M] in
theorem directionalDeriv_directionalDeriv_sub_commutator
    (X Y : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Y) x)
    (hf : ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) f x) :
    directionalDerivAlong (I := I) X (fun y : M => directionalDerivAlong (I := I) Y f y) x -
        directionalDerivAlong (I := I) Y (fun y : M => directionalDerivAlong (I := I) X f y) x -
          directionalDerivAlong (I := I) (VectorField.mlieBracket I X Y) f x = 0 := by
  have h := vderiv_mlieBracket (I := I) X Y f x hX hY hf
  unfold directionalDerivAlong
  unfold vderiv at h
  rw [h]
  ring








omit [SigmaCompactSpace M] [T2Space M] in
private theorem connectionRiemannCurvatureField_metric_skew_at_of_metricCompatible
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (hmc : IsMetricCompatible_gen (I := I) cov g)
    {x : M} (W X Y Z : TangentSpace I x) :
    g.inner x W
        ((connectionRiemannCurvatureField (I := I) cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z)) x) =
      -g.inner x Z
        ((connectionRiemannCurvatureField (I := I) cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x W)) x) := by
  let Xc : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x Z
  let Wc : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x W
  let YZc : (p : M) -> TangentSpace I p := fun p => (cov Zc p) (Yc p)
  let YWc : (p : M) -> TangentSpace I p := fun p => (cov Wc p) (Yc p)
  let XZc : (p : M) -> TangentSpace I p := fun p => (cov Zc p) (Xc p)
  let XWc : (p : M) -> TangentSpace I p := fun p => (cov Wc p) (Xc p)
  let Bc : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Xc Yc
  let f : M -> Real := fun p => g.inner p (Zc p) (Wc p)
  have hX : MDiffAt (T% Xc) x := by
    simpa [Xc] using mdifferentiableAt_tangentConstAt_self (I := I) x X
  have hY : MDiffAt (T% Yc) x := by
    simpa [Yc] using mdifferentiableAt_tangentConstAt_self (I := I) x Y
  have hZ : MDiffAt (T% Zc) x := by
    simpa [Zc] using mdifferentiableAt_tangentConstAt_self (I := I) x Z
  have hW : MDiffAt (T% Wc) x := by
    simpa [Wc] using mdifferentiableAt_tangentConstAt_self (I := I) x W
  have hX2 : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Xc) x := by
    simpa [Xc] using contMDiffAt_tangentConstAt_self_minTwo (I := I) x X
  have hY2 : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Yc) x := by
    simpa [Yc] using contMDiffAt_tangentConstAt_self_minTwo (I := I) x Y
  have hZ2 : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Zc) x := by
    simpa [Zc] using contMDiffAt_tangentConstAt_self_minTwo (I := I) x Z
  have hW2 : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Wc) x := by
    simpa [Wc] using contMDiffAt_tangentConstAt_self_minTwo (I := I) x W
  have hf2 : ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) f x := by
    simpa [f] using contMDiffAt_metric_inner (I := I) g hZ2 hW2
      (by
        simpa [minSmoothness_of_isRCLikeNormedField] using
          (by decide : (2 : WithTop ℕ∞) <= ∞))
  haveI : IsManifold I (minSmoothness Real 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (inferInstance : IsManifold I 2 M)
  have hYZ : MDiffAt (T% YZc) x := by
    simpa [YZc, Yc, Zc, tangentConstAt] using
      CovariantDerivative.tangentConst_cov_mdiffAt
        (𝕜 := Real) (I := I) cov hcov (x := x) (v := Y) (w := Z)
  have hYW : MDiffAt (T% YWc) x := by
    simpa [YWc, Yc, Wc, tangentConstAt] using
      CovariantDerivative.tangentConst_cov_mdiffAt
        (𝕜 := Real) (I := I) cov hcov (x := x) (v := Y) (w := W)
  have hXZ : MDiffAt (T% XZc) x := by
    simpa [XZc, Xc, Zc, tangentConstAt] using
      CovariantDerivative.tangentConst_cov_mdiffAt
        (𝕜 := Real) (I := I) cov hcov (x := x) (v := X) (w := Z)
  have hXW : MDiffAt (T% XWc) x := by
    simpa [XWc, Xc, Wc, tangentConstAt] using
      CovariantDerivative.tangentConst_cov_mdiffAt
        (𝕜 := Real) (I := I) cov hcov (x := x) (v := X) (w := W)
  have hX2nat : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : ℕ∞) (T% Xc) x := by
    simpa [minSmoothness_of_isRCLikeNormedField] using hX2
  have hY2nat : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : ℕ∞) (T% Yc) x := by
    simpa [minSmoothness_of_isRCLikeNormedField] using hY2
  haveI : IsManifold I (((2 : ℕ∞) : WithTop ℕ∞) + 1) M := by
    change IsManifold I (3 : WithTop ℕ∞) M
    exact (inferInstance : IsManifold I 3 M)
  have hB1 : ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : ℕ∞) (T% Bc) x := by
    simpa [Bc] using
      (ContMDiffAt.mlieBracket_vectorField (I := I) (m := (1 : ℕ∞)) (n := (2 : ℕ∞))
        hX2nat hY2nat (by
          rw [minSmoothness_of_isRCLikeNormedField]
          norm_num))
  have hB : MDiffAt (T% Bc) x :=
    hB1.mdifferentiableAt (by norm_num : ((1 : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have hYf_eq :
      (fun p : M => directionalDerivAlong (I := I) Yc f p) =ᶠ[𝓝 x]
        fun p => g.inner p (YZc p) (Wc p) + g.inner p (Zc p) (YWc p) := by
    let e := trivializationAt E (TangentSpace I) x
    filter_upwards [e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x)] with p hp
    have hYp : MDiffAt (T% Yc) p := by
      simpa [Yc] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x Y hp
    have hZp : MDiffAt (T% Zc) p := by
      simpa [Zc] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x Z hp
    have hWp : MDiffAt (T% Wc) p := by
      simpa [Wc] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x W hp
    have hmetric := DifferentialGeometry.Integral.Connection.metric_compatible_apply (I := I) hmc
      (x := p) Yc Zc Wc hYp hZp hWp
    simpa [directionalDerivAlong, extDerivFun, NormedSpace.fromTangentSpace, f, YZc, YWc]
      using hmetric
  have hXf_eq :
      (fun p : M => directionalDerivAlong (I := I) Xc f p) =ᶠ[𝓝 x]
        fun p => g.inner p (XZc p) (Wc p) + g.inner p (Zc p) (XWc p) := by
    let e := trivializationAt E (TangentSpace I) x
    filter_upwards [e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x)] with p hp
    have hXp : MDiffAt (T% Xc) p := by
      simpa [Xc] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x X hp
    have hZp : MDiffAt (T% Zc) p := by
      simpa [Zc] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x Z hp
    have hWp : MDiffAt (T% Wc) p := by
      simpa [Wc] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x W hp
    have hmetric := DifferentialGeometry.Integral.Connection.metric_compatible_apply (I := I) hmc
      (x := p) Xc Zc Wc hXp hZp hWp
    simpa [directionalDerivAlong, extDerivFun, NormedSpace.fromTangentSpace, f, XZc, XWc]
      using hmetric
  have hYZ_W : MDiffAt (fun p : M => g.inner p (YZc p) (Wc p)) x :=
    mdifferentiableAt_metric_inner (I := I) g hYZ hW
  have hZ_YW : MDiffAt (fun p : M => g.inner p (Zc p) (YWc p)) x :=
    mdifferentiableAt_metric_inner (I := I) g hZ hYW
  have hXZ_W : MDiffAt (fun p : M => g.inner p (XZc p) (Wc p)) x :=
    mdifferentiableAt_metric_inner (I := I) g hXZ hW
  have hZ_XW : MDiffAt (fun p : M => g.inner p (Zc p) (XWc p)) x :=
    mdifferentiableAt_metric_inner (I := I) g hZ hXW
  have hXYf :
      directionalDerivAlong (I := I) Xc
          (fun y : M => directionalDerivAlong (I := I) Yc f y) x =
        (g.inner x ((cov YZc x) (Xc x)) (Wc x) +
          g.inner x (YZc x) ((cov Wc x) (Xc x))) +
        (g.inner x ((cov Zc x) (Xc x)) (YWc x) +
          g.inner x (Zc x) ((cov YWc x) (Xc x))) := by
    have h1 := DifferentialGeometry.Integral.Connection.metric_compatible_apply (I := I) hmc
      (x := x) Xc YZc Wc hX hYZ hW
    have h1' :
        directionalDerivAlong (I := I) Xc (fun p : M => g.inner p (YZc p) (Wc p)) x =
          g.inner x ((cov YZc x) (Xc x)) (Wc x) +
            g.inner x (YZc x) ((cov Wc x) (Xc x)) := by
      simpa [directionalDerivAlong, extDerivFun, NormedSpace.fromTangentSpace] using h1
    have h2 := DifferentialGeometry.Integral.Connection.metric_compatible_apply (I := I) hmc
      (x := x) Xc Zc YWc hX hZ hYW
    have h2' :
        directionalDerivAlong (I := I) Xc (fun p : M => g.inner p (Zc p) (YWc p)) x =
          g.inner x ((cov Zc x) (Xc x)) (YWc x) +
            g.inner x (Zc x) ((cov YWc x) (Xc x)) := by
      simpa [directionalDerivAlong, extDerivFun, NormedSpace.fromTangentSpace] using h2
    calc
      directionalDerivAlong (I := I) Xc
          (fun y : M => directionalDerivAlong (I := I) Yc f y) x
          = directionalDerivAlong (I := I) Xc
              (fun p : M => g.inner p (YZc p) (Wc p) +
                g.inner p (Zc p) (YWc p)) x :=
            directionalDeriv_congr_nhds (I := I) (X := Xc) hYf_eq
      _ = directionalDerivAlong (I := I) Xc
              (fun p : M => g.inner p (YZc p) (Wc p)) x +
            directionalDerivAlong (I := I) Xc
              (fun p : M => g.inner p (Zc p) (YWc p)) x :=
            directionalDeriv_add_fun (I := I) Xc x hYZ_W hZ_YW
      _ = _ := by rw [h1', h2']
  have hYXf :
      directionalDerivAlong (I := I) Yc
          (fun y : M => directionalDerivAlong (I := I) Xc f y) x =
        (g.inner x ((cov XZc x) (Yc x)) (Wc x) +
          g.inner x (XZc x) ((cov Wc x) (Yc x))) +
        (g.inner x ((cov Zc x) (Yc x)) (XWc x) +
          g.inner x (Zc x) ((cov XWc x) (Yc x))) := by
    have h1 := DifferentialGeometry.Integral.Connection.metric_compatible_apply (I := I) hmc
      (x := x) Yc XZc Wc hY hXZ hW
    have h1' :
        directionalDerivAlong (I := I) Yc (fun p : M => g.inner p (XZc p) (Wc p)) x =
          g.inner x ((cov XZc x) (Yc x)) (Wc x) +
            g.inner x (XZc x) ((cov Wc x) (Yc x)) := by
      simpa [directionalDerivAlong, extDerivFun, NormedSpace.fromTangentSpace] using h1
    have h2 := DifferentialGeometry.Integral.Connection.metric_compatible_apply (I := I) hmc
      (x := x) Yc Zc XWc hY hZ hXW
    have h2' :
        directionalDerivAlong (I := I) Yc (fun p : M => g.inner p (Zc p) (XWc p)) x =
          g.inner x ((cov Zc x) (Yc x)) (XWc x) +
            g.inner x (Zc x) ((cov XWc x) (Yc x)) := by
      simpa [directionalDerivAlong, extDerivFun, NormedSpace.fromTangentSpace] using h2
    calc
      directionalDerivAlong (I := I) Yc
          (fun y : M => directionalDerivAlong (I := I) Xc f y) x
          = directionalDerivAlong (I := I) Yc
              (fun p : M => g.inner p (XZc p) (Wc p) +
                g.inner p (Zc p) (XWc p)) x :=
            directionalDeriv_congr_nhds (I := I) (X := Yc) hXf_eq
      _ = directionalDerivAlong (I := I) Yc
              (fun p : M => g.inner p (XZc p) (Wc p)) x +
            directionalDerivAlong (I := I) Yc
              (fun p : M => g.inner p (Zc p) (XWc p)) x :=
            directionalDeriv_add_fun (I := I) Yc x hXZ_W hZ_XW
      _ = _ := by rw [h1', h2']
  have hBf :
      directionalDerivAlong (I := I) Bc f x =
        g.inner x ((cov Zc x) (Bc x)) (Wc x) +
          g.inner x (Zc x) ((cov Wc x) (Bc x)) := by
    have hmetric := DifferentialGeometry.Integral.Connection.metric_compatible_apply (I := I) hmc
      (x := x) Bc Zc Wc hB hZ hW
    simpa [directionalDerivAlong, extDerivFun, NormedSpace.fromTangentSpace, f] using hmetric
  have hcomm :=
    directionalDeriv_directionalDeriv_sub_commutator
      (I := I) Xc Yc f x hX2 hY2 hf2
  rw [hXYf, hYXf, hBf] at hcomm
  have hXc_self : Xc x = X := by
    simpa [Xc] using tangentConstAt_self (I := I) x X
  have hYc_self : Yc x = Y := by
    simpa [Yc] using tangentConstAt_self (I := I) x Y
  have hZc_self : Zc x = Z := by
    simpa [Zc] using tangentConstAt_self (I := I) x Z
  have hWc_self : Wc x = W := by
    simpa [Wc] using tangentConstAt_self (I := I) x W
  have hcurv_zero :
      g.inner x ((cov YZc x) X) W +
        g.inner x Z ((cov YWc x) X) -
        g.inner x ((cov XZc x) Y) W -
        g.inner x Z ((cov XWc x) Y) -
        g.inner x ((cov Zc x) (Bc x)) W -
        g.inner x Z ((cov Wc x) (Bc x)) = 0 := by
    have h := hcomm
    dsimp [YZc, YWc, XZc, XWc] at h
    rw [hXc_self, hYc_self, hZc_self, hWc_self] at h
    ring_nf at h
    change
      g.inner x ((cov YZc x) X) W +
        g.inner x Z ((cov YWc x) X) -
        g.inner x ((cov XZc x) Y) W -
        g.inner x Z ((cov XWc x) Y) -
        g.inner x ((cov Zc x) (Bc x)) W -
        g.inner x Z ((cov Wc x) (Bc x)) = 0 at h
    exact h
  have hsum :
      g.inner x W
          ((cov YZc x) X - (cov XZc x) Y - (cov Zc x) (Bc x)) +
        g.inner x Z
          ((cov YWc x) X - (cov XWc x) Y - (cov Wc x) (Bc x)) = 0 := by
    rw [g.symm x W
      ((cov YZc x) X - (cov XZc x) Y - (cov Zc x) (Bc x))]
    simp only [map_add, map_neg, sub_eq_add_neg, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply]
    ring_nf at hcurv_zero ⊢
    exact hcurv_zero
  have hgoal :
      g.inner x W
          ((cov YZc x) X - (cov XZc x) Y - (cov Zc x) (Bc x)) =
        -g.inner x Z
          ((cov YWc x) X - (cov XWc x) Y - (cov Wc x) (Bc x)) := by
    linarith
  change g.inner x W ((connectionRiemannCurvatureField (I := I) cov Xc Yc Zc) x) =
      -g.inner x Z ((connectionRiemannCurvatureField (I := I) cov Xc Yc Wc) x)
  simpa [connectionRiemannCurvatureField,
    DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField, YZc, YWc, XZc, XWc, Bc,
    hXc_self, hYc_self] using hgoal



omit [IsManifold I 2 M] [IsManifold I 3 M] in
omit [SigmaCompactSpace M] in
theorem rm04InputSkewAt_of_leviCivita_realizes
    (g : SmoothRiemannianMetric I M)
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm04 : Rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04)
    {x : M} :
    forall X Y Z W : TangentSpace I x,
      Rm04 x (vec4 Y X Z W) = -Rm04 x (vec4 X Y Z W) := by
  intro X Y Z W
  obtain ⟨Wsec, hWsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := (⊤ : ℕ∞)) x W
  obtain ⟨Xsec, hXsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := (⊤ : ℕ∞)) x X
  obtain ⟨Ysec, hYsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := (⊤ : ℕ∞)) x Y
  obtain ⟨Zsec, hZsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := (⊤ : ℕ∞)) x Z
  have hleft := hRm04 Ysec Xsec Zsec Wsec x
  have hright := hRm04 Xsec Ysec Zsec Wsec x
  have hswap :=
    DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField_swap
      (I := I) (leviCivitaConnectionOfMetric (I := I) g)
      Xsec Ysec Zsec x
  have hinner :
      g.inner x (Wsec x)
          (connectionRiemannCurvatureField (I := I)
            (leviCivitaConnectionOfMetric (I := I) g)
            (fun p : M => Ysec p) (fun p : M => Xsec p)
            (fun p : M => Zsec p) x) =
        -g.inner x (Wsec x)
          (connectionRiemannCurvatureField (I := I)
            (leviCivitaConnectionOfMetric (I := I) g)
            (fun p : M => Xsec p) (fun p : M => Ysec p)
            (fun p : M => Zsec p) x) := by
    simpa using
      congrArg (fun V : TangentSpace I x => g.inner x (Wsec x) V) hswap
  simpa [hWsec, hXsec, hYsec, hZsec] using
    hleft.trans (hinner.trans (congrArg Neg.neg hright.symm))



omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
theorem rm04InputSkew_ofRealizes
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm04 : Rm04RealizesConnection (I := I) g cov Rm04)
    {x : M} :
    forall X Y Z W : TangentSpace I x,
      Rm04 x (vec4 Y X Z W) = -Rm04 x (vec4 X Y Z W) := by
  intro X Y Z W
  obtain ⟨Wsec, hWsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := (⊤ : ℕ∞)) x W
  obtain ⟨Xsec, hXsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := (⊤ : ℕ∞)) x X
  obtain ⟨Ysec, hYsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := (⊤ : ℕ∞)) x Y
  obtain ⟨Zsec, hZsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := (⊤ : ℕ∞)) x Z
  have hleft := hRm04 Ysec Xsec Zsec Wsec x
  have hright := hRm04 Xsec Ysec Zsec Wsec x
  have hswap :=
    DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField_swap
      (I := I) cov Xsec Ysec Zsec x
  have hinner :
      g.inner x (Wsec x)
          (connectionRiemannCurvatureField (I := I) cov
            (fun p : M => Ysec p) (fun p : M => Xsec p)
            (fun p : M => Zsec p) x) =
        -g.inner x (Wsec x)
          (connectionRiemannCurvatureField (I := I) cov
            (fun p : M => Xsec p) (fun p : M => Ysec p)
            (fun p : M => Zsec p) x) := by
    simpa using
      congrArg (fun V : TangentSpace I x => g.inner x (Wsec x) V) hswap
  simpa [hWsec, hXsec, hYsec, hZsec] using
    hleft.trans (hinner.trans (congrArg Neg.neg hright.symm))



omit [SigmaCompactSpace M] in
theorem firstBianchi_ofTF
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (htf : IsTorsionFree (I := I) cov)
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm04 : Rm04RealizesConnection (I := I) g cov Rm04)
    {x : M} :
    FirstBianchiAt (I := I) (Rm04 x) := by
  intro X Y Z W
  have hXYZ := rm04_tconst_eval (I := I) g cov hcov Rm04 hRm04 X Y Z W
  have hYZX := rm04_tconst_eval (I := I) g cov hcov Rm04 hRm04 Y Z X W
  have hZXY := rm04_tconst_eval (I := I) g cov hcov Rm04 hRm04 Z X Y W
  have hBianchi :=
    DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField_tangentConst_first_bianchi_of_torsionFree
      (I := I) cov hcov htf x X Y Z
  have hinner := congrArg (fun V : TangentSpace I x => g.inner x W V) hBianchi
  rw [hXYZ, hYZX, hZXY]
  simpa [map_add, map_zero] using hinner


omit [IsManifold I 1 M] in
omit [SigmaCompactSpace M] in
theorem firstBianchiAt_of_leviCivita_realizes
    (g : SmoothRiemannianMetric I M)
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm04 : Rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04)
    {x : M} :
    FirstBianchiAt (I := I) (Rm04 x) := by
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (leviCivitaConnectionOfMetric (I := I) g) (1 : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one (I := I) g
  intro X Y Z W
  have hXYZ :=
    rm04_tconst_eval (I := I) g (leviCivitaConnectionOfMetric (I := I) g)
      hcov Rm04 hRm04 X Y Z W
  have hYZX :=
    rm04_tconst_eval (I := I) g (leviCivitaConnectionOfMetric (I := I) g)
      hcov Rm04 hRm04 Y Z X W
  have hZXY :=
    rm04_tconst_eval (I := I) g (leviCivitaConnectionOfMetric (I := I) g)
      hcov Rm04 hRm04 Z X Y W
  have hBianchi :=
    DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField_tangentConst_first_bianchi_of_torsionFree
      (I := I) (leviCivitaConnectionOfMetric (I := I) g) hcov
      (leviCivitaConnectionOfMetric_isTorsionFree (I := I) g) x X Y Z
  have hinner :=
    congrArg (fun V : TangentSpace I x => g.inner x W V) hBianchi
  rw [hXYZ, hYZX, hZXY]
  simpa [map_add, map_zero] using hinner

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] in
private theorem rm04_pair_symm_of_input_output_first
    {x : M}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    (hinput : forall X Y Z W : TangentSpace I x,
      Rm04 (vec4 Y X Z W) = -Rm04 (vec4 X Y Z W))
    (houtput : Rm04OutputSkewAt (I := I) Rm04)
    (hfirst : FirstBianchiAt (I := I) Rm04) :
    forall X Y Z W : TangentSpace I x,
      Rm04 (vec4 X Y Z W) = Rm04 (vec4 Z W X Y) := by
  intro W X Y Z
  have hB0 := hfirst W X Y Z
  have hB1 := hfirst X Y Z W
  have hB2 := hfirst X Z Y W
  have hB3 := hfirst W X Z Y
  have hB4 := hfirst W Y Z X
  have hO1 := houtput X Y Z W
  have hO2 := houtput W X Z Y
  have hO3 := houtput W Y Z X
  have hO4 := houtput W Z Y X
  have hO5 := houtput X Z Y W
  have hO6 := houtput Y Z X W
  have hI1 := hinput W Y X Z
  have hI2 := hinput W Z X Y
  have hI3 := hinput W Z Y X
  have hI4 := hinput X Z Y W
  linarith



omit [IsManifold I 1 M] in
omit [SigmaCompactSpace M] in
theorem rm04OutputSkewAt_of_leviCivita_realizes
    (g : SmoothRiemannianMetric I M)
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm04 : Rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04)
    {x : M} :
    Rm04OutputSkewAt (I := I) (Rm04 x) := by
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (leviCivitaConnectionOfMetric (I := I) g) (1 : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one (I := I) g
  intro X Y Z W
  have hleft :=
    rm04_tconst_eval (I := I) g (leviCivitaConnectionOfMetric (I := I) g)
      hcov Rm04 hRm04 X Y Z W
  have hright :=
    rm04_tconst_eval (I := I) g (leviCivitaConnectionOfMetric (I := I) g)
      hcov Rm04 hRm04 X Y W Z
  have hskew :=
    connectionRiemannCurvatureField_metric_skew_at_of_metricCompatible
      (I := I) g (leviCivitaConnectionOfMetric (I := I) g) hcov
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g) W X Y Z
  exact hleft.trans (hskew.trans (congrArg (fun r : Real => -r) hright.symm))



omit [SigmaCompactSpace M] in
theorem rm04OutputSkew_ofMC
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (hmc : IsMetricCompatible_gen (I := I) cov g)
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm04 : Rm04RealizesConnection (I := I) g cov Rm04)
    {x : M} :
    Rm04OutputSkewAt (I := I) (Rm04 x) := by
  intro X Y Z W
  have hleft := rm04_tconst_eval (I := I) g cov hcov Rm04 hRm04 X Y Z W
  have hright := rm04_tconst_eval (I := I) g cov hcov Rm04 hRm04 X Y W Z
  have hskew :=
    connectionRiemannCurvatureField_metric_skew_at_of_metricCompatible
      (I := I) g cov hcov hmc W X Y Z
  exact hleft.trans (hskew.trans (congrArg (fun r : Real => -r) hright.symm))



omit [SigmaCompactSpace M] in
theorem rm04PairSymm_ofLC
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (hLC : IsLeviCivita (I := I) cov g)
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm04 : Rm04RealizesConnection (I := I) g cov Rm04)
    {x : M} :
    forall X Y Z W : TangentSpace I x,
      Rm04 x (vec4 X Y Z W) = Rm04 x (vec4 Z W X Y) :=
  rm04_pair_symm_of_input_output_first (I := I)
    (rm04InputSkew_ofRealizes (I := I) g cov Rm04 hRm04)
    (rm04OutputSkew_ofMC (I := I) g cov hcov
      (metricCompatible_of_isLeviCivita (I := I) hLC) Rm04 hRm04)
    (firstBianchi_ofTF (I := I) g cov hcov
      (torsionFree_of_isLeviCivita (I := I) hLC) Rm04 hRm04)


omit [SigmaCompactSpace M] in
theorem rm04PairSymmAt_of_leviCivita_realizes
    (g : SmoothRiemannianMetric I M)
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm04 : Rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04)
    {x : M} :
    forall X Y Z W : TangentSpace I x,
      Rm04 x (vec4 X Y Z W) = Rm04 x (vec4 Z W X Y) :=
  rm04_pair_symm_of_input_output_first (I := I)
    (rm04InputSkewAt_of_leviCivita_realizes (I := I) g Rm04 hRm04)
    (rm04OutputSkewAt_of_leviCivita_realizes (I := I) g Rm04 hRm04)
    (firstBianchiAt_of_leviCivita_realizes (I := I) g Rm04 hRm04)



omit [IsManifold I 1 M] in
theorem rm13MetricSkewAt_of_leviCivita_realizes
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm13 : Rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04)
    {x : M} :
    Rm13MetricSkewAt (I := I) g x (Rm13 x) :=
  rm13MetricSkewAt_of_realizes_outputSkew (I := I) g
    (leviCivitaConnectionOfMetric (I := I) g) Rm13 Rm04 hRm13 hRm04
    (rm04OutputSkewAt_of_leviCivita_realizes (I := I) g Rm04 hRm04)

omit [SigmaCompactSpace M] in
private theorem oneFormThirdCovDerivCommAt_of_leviCivita_higherOrder
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13Section (I := I) (M := M))
    (alphaSec : OneFormSection (I := I) (M := M))
    (nablaAlphaSec : TwoTensorSection (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (halpha : alphaSec x = alpha)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) alphaSec nablaAlphaSec x
      nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha := by
  classical
  intro X Y Z
  let cov := leviCivitaConnectionOfMetric (I := I) g
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      cov (1 : WithTop ℕ∞) := by
    simpa [cov] using
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one (I := I) g
  obtain ⟨Xsec, hXx⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  obtain ⟨Ysec, hYx⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y
  obtain ⟨Zsec, hZx⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Z
  let Xf : (p : M) -> TangentSpace I p := fun p => Xsec p
  let Yf : (p : M) -> TangentSpace I p := fun p => Ysec p
  let Zf : (p : M) -> TangentSpace I p := fun p => Zsec p
  let YZc : (p : M) -> TangentSpace I p := fun p => (cov Zf p) (Yf p)
  let XZc : (p : M) -> TangentSpace I p := fun p => (cov Zf p) (Xf p)
  let XYv : TangentSpace I x := (cov Yf x) (Xf x)
  let YXv : TangentSpace I x := (cov Xf x) (Yf x)
  let bracket : TangentSpace I x := VectorField.mlieBracket I Xf Yf x
  let f : M -> Real := fun p => alphaSec p (fun _ : Fin 1 => Zf p)
  let gYZ : M -> Real := fun p => alphaSec p (fun _ : Fin 1 => YZc p)
  let gXZ : M -> Real := fun p => alphaSec p (fun _ : Fin 1 => XZc p)
  have hnabla := nabla2OneFormRealizesAt_first (I := I) cov alphaSec
    nablaAlphaSec x nabla2Alpha hnabla2
  have hXmd : MDiffAt (T% Xf) x :=
    Xsec.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYmd : MDiffAt (T% Yf) x :=
    Ysec.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hX2 :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
        (T% Xf) x := by
    exact Xsec.contMDiff.contMDiffAt.of_le (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hY2 :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
        (T% Yf) x := by
    exact Ysec.contMDiff.contMDiffAt.of_le (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hZ1_at (p : M) :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M =>
          (⟨y, Zf y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) p := by
    exact Zsec.contMDiff.contMDiffAt.of_le (by
      change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.2 le_top)
  have hYZc1 :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, YZc p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
    simpa [YZc, cov, Yf, Zf] using
      cov_smoothSections_apply_contMDiffAt_one (I := I) cov hcov Ysec Zsec x
  have hXZc1 :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, XZc p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
    simpa [XZc, cov, Xf, Zf] using
      cov_smoothSections_apply_contMDiffAt_one (I := I) cov hcov Xsec Zsec x
  have hf_smooth : ContMDiff I 𝓘(Real, Real) ∞ f := by
    let Zslot : Fin 1 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) := fun _ => Zsec
    simpa [f, Zf, Zslot] using
      TensorMultilinear.contMDiff_tensor0SField_apply
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := 1) alphaSec Zslot
  have hf2 : ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) f x := by
    exact hf_smooth.contMDiffAt.of_le (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hYf_mdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => directionalDerivAlong (I := I) Yf f p) x := by
    simpa [directionalDerivAlong, Yf] using
      (extDerivFun_apply_contMDiffAt I hf_smooth.contMDiffAt Ysec).mdifferentiableAt
        (by simp)
  have hXf_mdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => directionalDerivAlong (I := I) Xf f p) x := by
    simpa [directionalDerivAlong, Xf] using
      (extDerivFun_apply_contMDiffAt I hf_smooth.contMDiffAt Xsec).mdifferentiableAt
        (by simp)
  have hgYZ_mdiff : MDifferentiableAt I 𝓘(Real, Real) gYZ x := by
    simpa [gYZ] using
      oneForm_eval_moving_C1_slot_mdiffAt (I := I) alphaSec YZc hYZc1
  have hgXZ_mdiff : MDifferentiableAt I 𝓘(Real, Real) gXZ x := by
    simpa [gXZ] using
      oneForm_eval_moving_C1_slot_mdiffAt (I := I) alphaSec XZc hXZc1
  have hFYZ :
      (fun p : M => nablaAlphaSec p (vec2 (I := I) (Yf p) (Zf p))) =
        fun p : M => directionalDerivAlong (I := I) Yf f p - gYZ p := by
    funext p
    have h := nablaOneFormSectionRealizes_eval_moving_C1_slot
      (I := I) cov Ysec alphaSec nablaAlphaSec hnabla Zf p (hZ1_at p)
    simpa [directionalDerivAlong, f, gYZ, YZc, Yf, Zf, cov] using h
  have hFXZ :
      (fun p : M => nablaAlphaSec p (vec2 (I := I) (Xf p) (Zf p))) =
        fun p : M => directionalDerivAlong (I := I) Xf f p - gXZ p := by
    funext p
    have h := nablaOneFormSectionRealizes_eval_moving_C1_slot
      (I := I) cov Xsec alphaSec nablaAlphaSec hnabla Zf p (hZ1_at p)
    simpa [directionalDerivAlong, f, gXZ, XZc, Xf, Zf, cov] using h
  have hDX_FYZ :
      directionalDerivAlong (I := I) Xf
          (fun p : M => nablaAlphaSec p (vec2 (I := I) (Yf p) (Zf p))) x =
        directionalDerivAlong (I := I) Xf
          (fun p : M => directionalDerivAlong (I := I) Yf f p) x -
          directionalDerivAlong (I := I) Xf gYZ x := by
    rw [hFYZ]
    exact directionalDeriv_sub_fun (I := I) Xf x hYf_mdiff hgYZ_mdiff
  have hDY_FXZ :
      directionalDerivAlong (I := I) Yf
          (fun p : M => nablaAlphaSec p (vec2 (I := I) (Xf p) (Zf p))) x =
        directionalDerivAlong (I := I) Yf
          (fun p : M => directionalDerivAlong (I := I) Xf f p) x -
          directionalDerivAlong (I := I) Yf gXZ x := by
    rw [hFXZ]
    exact directionalDeriv_sub_fun (I := I) Yf x hXf_mdiff hgXZ_mdiff
  have hA_X_YZ :
      nablaAlphaSec x (vec2 (I := I) (Xf x) (YZc x)) =
        directionalDerivAlong (I := I) Xf gYZ x -
          alphaSec x (fun _ : Fin 1 => (cov YZc x) (Xf x)) := by
    simpa [directionalDerivAlong, gYZ, Xf, cov] using
      nablaOneFormSectionRealizes_eval_moving_C1_slot
        (I := I) cov Xsec alphaSec nablaAlphaSec hnabla YZc x hYZc1
  have hA_Y_XZ :
      nablaAlphaSec x (vec2 (I := I) (Yf x) (XZc x)) =
        directionalDerivAlong (I := I) Yf gXZ x -
          alphaSec x (fun _ : Fin 1 => (cov XZc x) (Yf x)) := by
    simpa [directionalDerivAlong, gXZ, Yf, cov] using
      nablaOneFormSectionRealizes_eval_moving_C1_slot
        (I := I) cov Ysec alphaSec nablaAlphaSec hnabla XZc x hXZc1
  obtain ⟨XYsec, hXYsecx⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x XYv
  obtain ⟨YXsec, hYXsecx⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x YXv
  let XYf : (p : M) -> TangentSpace I p := fun p => XYsec p
  let YXf : (p : M) -> TangentSpace I p := fun p => YXsec p
  have hA_XY_Z :
      nablaAlphaSec x (vec2 (I := I) XYv (Zf x)) =
        directionalDerivAlong (I := I) XYf f x -
          alphaSec x (fun _ : Fin 1 => (cov Zf x) (XYf x)) := by
    have h := nablaOneFormSectionRealizes_eval_moving_C1_slot
      (I := I) cov XYsec alphaSec nablaAlphaSec hnabla Zf x (hZ1_at x)
    simpa [directionalDerivAlong, f, XYf, Zf, cov, hXYsecx] using h
  have hA_YX_Z :
      nablaAlphaSec x (vec2 (I := I) YXv (Zf x)) =
        directionalDerivAlong (I := I) YXf f x -
          alphaSec x (fun _ : Fin 1 => (cov Zf x) (YXf x)) := by
    have h := nablaOneFormSectionRealizes_eval_moving_C1_slot
      (I := I) cov YXsec alphaSec nablaAlphaSec hnabla Zf x (hZ1_at x)
    simpa [directionalDerivAlong, f, YXf, Zf, cov, hYXsecx] using h
  have hXYZ :
      nabla2Alpha (vec3 (I := I) X Y Z) =
        directionalDerivAlong (I := I) Xf
            (fun p : M => nablaAlphaSec p (vec2 (I := I) (Yf p) (Zf p))) x -
          nablaAlphaSec x (vec2 (I := I) XYv (Zf x)) -
          nablaAlphaSec x (vec2 (I := I) (Yf x) (XZc x)) := by
    have h2 := nabla2OneFormRealizesAt_apply (I := I) cov alphaSec
      nablaAlphaSec x nabla2Alpha hnabla2 Xsec Y Z
    have hraw := nabla0SFun_two_eval_smooth_slots
      (I := I) cov Xsec Ysec Zsec nablaAlphaSec x
    calc
      nabla2Alpha (vec3 (I := I) X Y Z)
          = nabla2Alpha (vec3 (I := I) (Xsec x) Y Z) := by
              simp [hXx]
      _ = directionalDerivAlong (I := I) Xf
              (fun p : M => nablaAlphaSec p (vec2 (I := I) (Yf p) (Zf p))) x -
            nablaAlphaSec x (vec2 (I := I) XYv (Zf x)) -
            nablaAlphaSec x (vec2 (I := I) (Yf x) (XZc x)) := by
              rw [h2]
              simpa [directionalDerivAlong, Xf, Yf, Zf, XZc, XYv, hYx, hZx, cov] using hraw
  have hYXZ :
      nabla2Alpha (vec3 (I := I) Y X Z) =
        directionalDerivAlong (I := I) Yf
            (fun p : M => nablaAlphaSec p (vec2 (I := I) (Xf p) (Zf p))) x -
          nablaAlphaSec x (vec2 (I := I) YXv (Zf x)) -
          nablaAlphaSec x (vec2 (I := I) (Xf x) (YZc x)) := by
    have h2 := nabla2OneFormRealizesAt_apply (I := I) cov alphaSec
      nablaAlphaSec x nabla2Alpha hnabla2 Ysec X Z
    have hraw := nabla0SFun_two_eval_smooth_slots
      (I := I) cov Ysec Xsec Zsec nablaAlphaSec x
    calc
      nabla2Alpha (vec3 (I := I) Y X Z)
          = nabla2Alpha (vec3 (I := I) (Ysec x) X Z) := by
              simp [hYx]
      _ = directionalDerivAlong (I := I) Yf
              (fun p : M => nablaAlphaSec p (vec2 (I := I) (Xf p) (Zf p))) x -
            nablaAlphaSec x (vec2 (I := I) YXv (Zf x)) -
            nablaAlphaSec x (vec2 (I := I) (Xf x) (YZc x)) := by
              rw [h2]
              simpa [directionalDerivAlong, Xf, Yf, Zf, YZc, YXv, hXx, hZx, cov] using hraw
  have hcomm :=
    directionalDeriv_directionalDeriv_sub_commutator
      (I := I) Xf Yf f x hX2 hY2 hf2
  have htf := leviCivitaConnectionOfMetric_isTorsionFree (I := I) g
  have htorsion : XYv - YXv = bracket := by
    simpa [cov, XYv, YXv, bracket, Xf, Yf] using
      torsion_free_apply (I := I) htf (x := x) (X := Xf) (Y := Yf)
        hXmd hYmd
  have hdir_XY_YX :
      directionalDerivAlong (I := I) XYf f x -
          directionalDerivAlong (I := I) YXf f x =
        directionalDerivAlong (I := I)
          (fun p : M => VectorField.mlieBracket I Xf Yf p) f x := by
    change (extDerivFun (I := I) f x) (XYf x) -
        (extDerivFun (I := I) f x) (YXf x) =
      (extDerivFun (I := I) f x) (VectorField.mlieBracket I Xf Yf x)
    change (extDerivFun (I := I) f x) (XYsec x) -
        (extDerivFun (I := I) f x) (YXsec x) =
      (extDerivFun (I := I) f x) (VectorField.mlieBracket I Xf Yf x)
    rw [hXYsecx, hYXsecx]
    rw [← map_sub (extDerivFun (I := I) f x) XYv YXv]
    rw [htorsion]
  have hcurv :
      connectionRiemannCurvatureField (I := I) cov Xf Yf Zf x =
        (cov YZc x) (Xf x) - (cov XZc x) (Yf x) - (cov Zf x) bracket := by
    rfl
  have hcurv_alpha :
      alphaSec x (fun _ : Fin 1 => (cov Zf x) (XYf x)) -
          alphaSec x (fun _ : Fin 1 => (cov Zf x) (YXf x)) +
          alphaSec x (fun _ : Fin 1 => (cov XZc x) (Yf x)) -
          alphaSec x (fun _ : Fin 1 => (cov YZc x) (Xf x)) =
        -Rm13 x alpha (vec3 (I := I) X Y Z) := by
    let A : TangentSpace I x := (cov Zf x) (XYf x)
    let B : TangentSpace I x := (cov Zf x) (YXf x)
    let C : TangentSpace I x := (cov XZc x) (Yf x)
    let D : TangentSpace I x := (cov YZc x) (Xf x)
    let R : TangentSpace I x :=
      connectionRiemannCurvatureField (I := I) cov Xf Yf Zf x
    have hfour :
        alphaSec x (fun _ : Fin 1 => A - B + C - D) =
          alphaSec x (fun _ : Fin 1 => A) - alphaSec x (fun _ : Fin 1 => B) +
            alphaSec x (fun _ : Fin 1 => C) - alphaSec x (fun _ : Fin 1 => D) := by
      rw [halpha]
      exact oneForm_eval_const_sub_add_sub (I := I) alpha A B C D
    have hAB : A - B = (cov Zf x) bracket := by
      dsimp [A, B, XYf, YXf]
      rw [hXYsecx, hYXsecx, ← map_sub, htorsion]
    have hnegR : A - B + C - D = -R := by
      dsimp [R, A, B, C, D]
      rw [hcurv]
      dsimp [A, B, C, D] at hAB
      rw [hAB]
      abel
    have hRm := hRm13 Xsec Ysec Zsec x alpha
    calc
      alphaSec x (fun _ : Fin 1 => A) - alphaSec x (fun _ : Fin 1 => B) +
          alphaSec x (fun _ : Fin 1 => C) - alphaSec x (fun _ : Fin 1 => D)
          = alphaSec x (fun _ : Fin 1 => A - B + C - D) := hfour.symm
      _ = alpha (fun _ : Fin 1 => -R) := by
            rw [hnegR]
            rw [halpha]
      _ = -cotangentToDual_gen (I := I) alpha R := by
            rw [oneForm_eval_const_neg (I := I) alpha R]
            rw [← cotangentToDual_apply_gen (I := I) alpha R]
      _ = -Rm13 x alpha (vec3 (I := I) X Y Z) := by
            simpa [R, cov, Xf, Yf, Zf, hXx, hYx, hZx] using
              congrArg Neg.neg hRm.symm
  rw [hXYZ, hYXZ, hDX_FYZ, hDY_FXZ, hA_XY_Z, hA_YX_Z,
    hA_Y_XZ, hA_X_YZ]
  have hcomm' :
      directionalDerivAlong (I := I) Xf
          (fun y : M => directionalDerivAlong (I := I) Yf f y) x -
        directionalDerivAlong (I := I) Yf
          (fun y : M => directionalDerivAlong (I := I) Xf f y) x =
        directionalDerivAlong (I := I)
          (fun p : M => VectorField.mlieBracket I Xf Yf p) f x := by
    linarith
  linarith



omit [SigmaCompactSpace M] in
theorem oneFormThirdCovDerivCommAt_of_leviCivita
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13Section (I := I) (M := M))
    (alphaSec : OneFormSection (I := I) (M := M))
    (nablaAlphaSec : TwoTensorSection (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (halpha : alphaSec x = alpha)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) alphaSec nablaAlphaSec x
      nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha :=
  oneFormThirdCovDerivCommAt_of_leviCivita_higherOrder
    (I := I) g Rm13 alphaSec nablaAlphaSec alpha nabla2Alpha hRm13
    halpha hnabla2





omit [IsManifold I 3 M] in
omit [SigmaCompactSpace M] in
theorem tensor0S_ricciIdentity_of_leviCivita
    (g : SmoothRiemannianMetric I M)
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
    (hRm13 : Rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (halpha : alphaSec x = alpha)
    (hnablaAlpha : nablaAlphaSec x = nablaAlpha)
    (hnabla2 : Nabla20SRealizesAt (I := I) s
      (leviCivitaConnectionOfMetric (I := I) g) alphaSec nablaAlphaSec x
      nabla2Alpha) :
    Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha := by
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (leviCivitaConnectionOfMetric (I := I) g) (1 : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one (I := I) g
  refine tensor0S_ricciIdentity_of_torsionFree
    (I := I) (leviCivitaConnectionOfMetric (I := I) g) hcov Rm13
    alphaSec nablaAlphaSec alpha nablaAlpha nabla2Alpha hRm13 halpha
    hnablaAlpha hnabla2 ?_
  have htf := leviCivitaConnectionOfMetric_isTorsionFree (I := I) g
  simpa [IsTorsionFreeAt] using htf x


end DifferentialGeometry.Integral.Connection
