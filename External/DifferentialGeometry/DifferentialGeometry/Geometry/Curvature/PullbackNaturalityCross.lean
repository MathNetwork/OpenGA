import DifferentialGeometry.Geometry.Curvature.PullbackNaturality
import DifferentialGeometry.Geometry.Metric.PullbackCross

set_option autoImplicit false
set_option linter.style.longLine false


















noncomputable section

namespace DifferentialGeometry.Integral.Connection

open scoped Manifold ContDiff
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F] [NeZero (Module.finrank ℝ F)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

private lemma infty_ne_zeroC : (∞ : WithTop ℕ∞) ≠ 0 := by
  decide

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [FiniteDimensional ℝ F] [CompleteSpace F] [NeZero (Module.finrank ℝ F)] [IsManifold I ∞ M] [IsManifold J ∞ N] in
private theorem mfderiv_eq_cle_applyCross
    (Phi : M ≃ₘ⟮I, J⟯ N) (x : M) (v : TangentSpace I x) :
    Diffeomorph.mfderivToContinuousLinearEquiv Phi infty_ne_zeroC x v =
      mfderiv I J Phi x v := by
  have h :=
    Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Phi) (x := x) infty_ne_zeroC
  exact congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace J (Phi x) => f v) h

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [FiniteDimensional ℝ F] [CompleteSpace F] [NeZero (Module.finrank ℝ F)] [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem mpullback_symm_applyCross
    (Phi : M ≃ₘ⟮I, J⟯ N) (X : (p : M) -> TangentSpace I p) (x : M) :
    VectorField.mpullback J I (Phi.symm : N -> M) X (Phi x) =
      mfderiv I J (Phi : M -> N) x (X x) := by
  unfold VectorField.mpullback
  rw [Diffeomorph.symm_apply_apply Phi x]
  let e := Diffeomorph.mfderivToContinuousLinearEquiv Phi infty_ne_zeroC x
  have he_apply : e (X x) = mfderiv I J (Phi : M -> N) x (X x) := by
    simpa [e] using mfderiv_eq_cle_applyCross (I := I) (J := J) (Phi := Phi) x (X x)
  rw [← he_apply]
  conv_lhs =>
    rw [← ContinuousLinearEquiv.symm_apply_apply e (X x)]
  change (mfderiv J I (Phi.symm : N -> M) (Phi x)).inverse (e.symm (e (X x))) = e (X x)
  have hInv :
      (mfderiv J I (Phi.symm : N -> M) (Phi x)).IsInvertible := by
    rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe
      (Φ := Phi.symm) (x := Phi x) infty_ne_zeroC]
    exact ContinuousLinearMap.isInvertible_equiv
  rw [ContinuousLinearMap.IsInvertible.inverse_apply_eq hInv]
  change e.symm (e (X x)) =
    (mfderiv J I (Phi.symm : N -> M) (Phi x)) (e (X x))
  rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe
    (Φ := Phi.symm) (x := Phi x) infty_ne_zeroC]
  have hlocal :
      ((Phi.isLocalDiffeomorph x).localInverse : N -> M)
        =ᶠ[nhds (Phi x)] (Phi.symm : N -> M) := by
    filter_upwards [(Phi.isLocalDiffeomorph x).localInverse_eventuallyEq_right] with y hy
    calc
      (Phi.isLocalDiffeomorph x).localInverse y =
          Phi.symm (Phi ((Phi.isLocalDiffeomorph x).localInverse y)) := by
            rw [Diffeomorph.symm_apply_apply]
      _ = Phi.symm y := by
            have hy' : Phi ((Phi.isLocalDiffeomorph x).localInverse y) = y := by
              simpa [Function.comp_def] using hy
            rw [hy']
  simp [e, Diffeomorph.mfderivToContinuousLinearEquiv,
    IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv, hlocal.mfderiv_eq]
  rfl



private abbrev pushFwdFieldCross
    (Phi : M ≃ₘ⟮I, J⟯ N) (X : (p : M) -> TangentSpace I p) :
    (q : N) -> TangentSpace J q :=
  VectorField.mpullback J I (Phi.symm : N -> M) X

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [FiniteDimensional ℝ F] [CompleteSpace F] [NeZero (Module.finrank ℝ F)] [IsManifold I ∞ M] [IsManifold J ∞ N] in
@[simp] private theorem pushFwdFieldCross_apply_at_image
    (Phi : M ≃ₘ⟮I, J⟯ N) (X : (p : M) -> TangentSpace I p) (x : M) :
    pushFwdFieldCross (I := I) (J := J) Phi X (Phi x) =
      mfderiv I J (Phi : M -> N) x (X x) :=
  mpullback_symm_applyCross (I := I) (J := J) Phi X x


noncomputable def pushFwdSectionCross
    [IsManifold I 1 M] [IsManifold J 1 N]
    (Phi : M ≃ₘ⟮I, J⟯ N)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    ContMDiffSection J F (∞ : WithTop ℕ∞) (TangentSpace J : N -> Type _) where
  toFun := pushFwdFieldCross (I := I) (J := J) Phi (fun p : M => X p)
  contMDiff_toFun := by
    refine ContMDiff.mpullback_vectorField
      (I := J) (I' := I) (f := (Phi.symm : N -> M))
      (V := fun p : M => X p) (m := ∞) (n := ∞)
      X.contMDiff Phi.symm.contMDiff ?_ ?_
    · intro q
      rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe
        (Φ := Phi.symm) (x := q) infty_ne_zeroC]
      exact ContinuousLinearMap.isInvertible_equiv
    · simp

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ F)] [IsManifold I ∞ M] [IsManifold J ∞ N] in
@[simp] theorem pushFwdSectionCross_apply_at_image
    [IsManifold I 1 M] [IsManifold J 1 N]
    (Phi : M ≃ₘ⟮I, J⟯ N)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) (x : M) :
    pushFwdSectionCross (I := I) (J := J) Phi X (Phi x) =
      mfderiv I J (Phi : M -> N) x (X x) := by
  simp [pushFwdSectionCross]



omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ F)] in
theorem directionalDeriv_pullbackCross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold J 1 N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (A P Q : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) (x : M) :
    DifferentialGeometry.Integral.Connection.directionalDerivAlong (I := I) (fun p : M => A p)
        (fun y : M =>
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi).inner y (P y) (Q y)) x =
      DifferentialGeometry.Integral.Connection.directionalDerivAlong (I := J)
        (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi A q)
        (fun q : N =>
          g.inner q (pushFwdSectionCross (I := I) (J := J) Phi P q)
            (pushFwdSectionCross (I := I) (J := J) Phi Q q)) (Phi x) := by
  have hfun :
      (fun y : M =>
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi).inner y (P y) (Q y)) =
        fun y : M =>
          (fun q : N =>
            g.inner q (pushFwdSectionCross (I := I) (J := J) Phi P q)
              (pushFwdSectionCross (I := I) (J := J) Phi Q q)) (Phi y) := by
    funext y
    rw [Diffeomorph.pullbackMetricCross_inner]
    simp only [pushFwdSectionCross_apply_at_image]
  rw [hfun]
  unfold DifferentialGeometry.Integral.Connection.directionalDerivAlong
  dsimp only
  rw [pushFwdSectionCross_apply_at_image]
  rw [extDerivFun_real_eq_mfderiv, extDerivFun_real_eq_mfderiv]
  have hG_diff :
      MDifferentiableAt J 𝓘(ℝ, ℝ)
        (fun q : N =>
          g.inner q (pushFwdSectionCross (I := I) (J := J) Phi P q)
            (pushFwdSectionCross (I := I) (J := J) Phi Q q)) (Phi x) :=
    (DifferentialGeometry.Integral.Connection.CovariantDerivative.metric_inner_contMDiffAt (I := J) (M := N) g
      (pushFwdSectionCross (I := I) (J := J) Phi P).contMDiff.contMDiffAt
      (pushFwdSectionCross (I := I) (J := J) Phi Q).contMDiff.contMDiffAt
      (by simp)).mdifferentiableAt (by simp)
  have hPhi_diff : MDifferentiableAt I J (Phi : M -> N) x :=
    Phi.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hcomp :=
    mfderiv_comp_apply (I := I) (I' := J) (I'' := 𝓘(ℝ, ℝ))
      (g := fun q : N =>
        g.inner q (pushFwdSectionCross (I := I) (J := J) Phi P q)
          (pushFwdSectionCross (I := I) (J := J) Phi Q q))
      (f := (Phi : M -> N)) (x := x) hG_diff hPhi_diff (A x)
  simpa [Function.comp_def] using hcomp


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ F)] in
private theorem inner_bracket_pullback_pushFwdCross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold J 1 N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (A P Q : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) (x : M) :
    (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi).inner x (A x)
        (VectorField.mlieBracket I (fun p : M => P p) (fun p : M => Q p) x) =
      g.inner (Phi x) (pushFwdSectionCross (I := I) (J := J) Phi A (Phi x))
        (VectorField.mlieBracket J
          (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi P q)
          (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Q q) (Phi x)) := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    exact IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  haveI : IsManifold J (minSmoothness ℝ 2) N := by
    exact IsManifold.of_le (I := J) (M := N) (n := ∞)
      (by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hbr :
      VectorField.mpullback J I (Phi.symm : N -> M)
          (VectorField.mlieBracket I (fun p : M => P p) (fun p : M => Q p))
          (Phi x) =
        VectorField.mlieBracket J
          (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi P q)
          (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Q q) (Phi x) := by
    have hbr' :=
      VectorField.mpullback_mlieBracket
        (I := J) (I' := I) (f := (Phi.symm : N -> M))
        (V := fun p : M => P p) (W := fun p : M => Q p) (x₀ := Phi x)
        (by simpa using P.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (by simpa using Q.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        Phi.symm.contMDiff.contMDiffAt
        (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    simpa [pushFwdSectionCross, pushFwdFieldCross] using hbr'
  rw [← hbr]
  rw [mpullback_symm_applyCross]
  rw [Diffeomorph.pullbackMetricCross_inner]
  rw [pushFwdSectionCross_apply_at_image]


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ F)] in
private theorem koszulScalar_pullback_pushFwdCross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold J 1 N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (A B C : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) (x : M) :
    DifferentialGeometry.Integral.Connection.koszulScalar (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
        (fun p : M => A p) (fun p : M => B p) (fun p : M => C p) x =
      DifferentialGeometry.Integral.Connection.koszulScalar (I := J) g
        (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi A q)
        (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi B q)
        (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi C q) (Phi x) := by
  unfold DifferentialGeometry.Integral.Connection.koszulScalar
  dsimp only
  rw [directionalDeriv_pullbackCross (I := I) (J := J) g Phi A B C x,
    directionalDeriv_pullbackCross (I := I) (J := J) g Phi B C A x,
    directionalDeriv_pullbackCross (I := I) (J := J) g Phi C A B x,
    inner_bracket_pullback_pushFwdCross (I := I) (J := J) g Phi A B C x,
    inner_bracket_pullback_pushFwdCross (I := I) (J := J) g Phi B C A x,
    inner_bracket_pullback_pushFwdCross (I := I) (J := J) g Phi C A B x]


omit [NeZero (Module.finrank ℝ E)] [NeZero (Module.finrank ℝ F)] in
theorem metricCov_pullbackCross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) (x : M) (v : TangentSpace I x) :
    mfderiv I J (Phi : M -> N) x
        ((metricCov (I := I) (M := M) (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
          (fun p : M => Y p) x) v)
      =
      (metricCov (I := J) (M := N) g
        (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Y q) (Phi x))
        (mfderiv I J (Phi : M -> N) x v) := by
  apply tangentFlatLinear_injective_gen (I := J) g (Phi x)
  ext u
  simp only [tangentFlatLinear_apply_gen]
  set e := Diffeomorph.mfderivToContinuousLinearEquiv Phi infty_ne_zeroC x with he
  set w : TangentSpace I x := e.symm u with hw_def
  have hdw : mfderiv I J (Phi : M -> N) x w = u := by
    rw [← mfderiv_eq_cle_applyCross (I := I) (J := J) Phi x w, hw_def]
    exact e.apply_symm_apply u
  obtain ⟨Xv, hXv⟩ :=
    ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x v
  obtain ⟨Zw, hZw⟩ :=
    ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x w
  have hu : pushFwdSectionCross (I := I) (J := J) Phi Zw (Phi x) = u := by
    rw [pushFwdSectionCross_apply_at_image, hZw]; exact hdw
  have hv : pushFwdSectionCross (I := I) (J := J) Phi Xv (Phi x) = mfderiv I J (Phi : M -> N) x v := by
    rw [pushFwdSectionCross_apply_at_image, hXv]
  have hkoszul_h :
      g.inner (Phi x)
          (mfderiv I J (Phi : M -> N) x
            (metricCov (I := I) (M := M) (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
              (fun p : M => Y p) x v)) u
        = (1 / 2 : ℝ) *
            DifferentialGeometry.Integral.Connection.koszulScalar (I := I)
              (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
              (fun p : M => Xv p) (fun p : M => Y p) (fun p : M => Zw p) x := by
    rw [← hdw, ← Diffeomorph.pullbackMetricCross_inner, ← hXv, ← hZw]
    exact DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_inner_eq_koszulScalar
      (I := I) (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
      (fun p : M => Xv p) (fun p : M => Y p) (fun p : M => Zw p) x
      (Xv.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      (Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      (Zw.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have hkoszul_g :
      g.inner (Phi x)
          (metricCov (I := J) (M := N) g
            (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Y q) (Phi x)
            (mfderiv I J (Phi : M -> N) x v)) u
        = (1 / 2 : ℝ) *
            DifferentialGeometry.Integral.Connection.koszulScalar (I := J) g
              (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Xv q)
              (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Y q)
              (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Zw q) (Phi x) := by
    rw [← hu, ← hv]
    exact DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_inner_eq_koszulScalar
      (I := J) g
      (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Xv q)
      (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Y q)
      (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Zw q) (Phi x)
      ((pushFwdSectionCross (I := I) (J := J) Phi Xv).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      ((pushFwdSectionCross (I := I) (J := J) Phi Y).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      ((pushFwdSectionCross (I := I) (J := J) Phi Zw).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  rw [hkoszul_h, hkoszul_g, koszulScalar_pullback_pushFwdCross (I := I) (J := J) g Phi Xv Y Zw x]



omit [NeZero (Module.finrank ℝ E)] [NeZero (Module.finrank ℝ F)] in
private theorem connectionRiemannCurvatureField_pullback_pushFwdCross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) (x : M) :
    mfderiv I J (Phi : M -> N) x
        (DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField
          (I := I)
          (metricCov (I := I) (M := M) (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi))
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x)
      =
      DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField
        (I := J) (metricCov (I := J) (M := N) g)
        (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi X q)
        (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Y q)
        (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Z q) (Phi x) := by
  let h : SmoothRiemannianMetric I M := Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi
  let covh : CovariantDerivative I E (TangentSpace I : M -> Type _) :=
    metricCov (I := I) (M := M) h
  let covg : CovariantDerivative J F (TangentSpace J : N -> Type _) :=
    metricCov (I := J) (M := N) g
  let ZYh : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => (covh (fun q : M => Z q) p) (Y p),
      fun p => DifferentialGeometry.Integral.Connection.CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) covh (metricCov_smooth (I := I) (M := M) h) Y Z p⟩
  let ZXh : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => (covh (fun q : M => Z q) p) (X p),
      fun p => DifferentialGeometry.Integral.Connection.CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) covh (metricCov_smooth (I := I) (M := M) h) X Z p⟩
  have hZY :
      (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi ZYh q) =
        (fun q : N => (covg (fun r : N => pushFwdSectionCross (I := I) (J := J) Phi Z r) q)
          (pushFwdSectionCross (I := I) (J := J) Phi Y q)) := by
    funext q
    let p : M := Phi.symm q
    have hp : Phi p = q := by
      simp [p]
    have hmid :
        pushFwdSectionCross (I := I) (J := J) Phi ZYh q =
          (metricCov (I := J) (M := N) g
            (fun r : N => pushFwdSectionCross (I := I) (J := J) Phi Z r) (Phi p))
            (pushFwdSectionCross (I := I) (J := J) Phi Y (Phi p)) := by
      calc
        pushFwdSectionCross (I := I) (J := J) Phi ZYh q =
            pushFwdSectionCross (I := I) (J := J) Phi ZYh (Phi p) := by rw [hp]
        _ = mfderiv I J (Phi : M -> N) p (ZYh p) := by simp
        _ =
            (metricCov (I := J) (M := N) g
              (fun r : N => pushFwdSectionCross (I := I) (J := J) Phi Z r) (Phi p))
              (mfderiv I J (Phi : M -> N) p (Y p)) := by
              simpa [h, covh, covg, ZYh] using
                metricCov_pullbackCross
                  (I := I) (J := J) g Phi Z p (Y p)
        _ =
            (metricCov (I := J) (M := N) g
              (fun r : N => pushFwdSectionCross (I := I) (J := J) Phi Z r) (Phi p))
              (pushFwdSectionCross (I := I) (J := J) Phi Y (Phi p)) := by
              rw [pushFwdSectionCross_apply_at_image]
    rw [← hp]
    rw [← hp] at hmid
    simpa [covg] using hmid
  have hZX :
      (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi ZXh q) =
        (fun q : N => (covg (fun r : N => pushFwdSectionCross (I := I) (J := J) Phi Z r) q)
          (pushFwdSectionCross (I := I) (J := J) Phi X q)) := by
    funext q
    let p : M := Phi.symm q
    have hp : Phi p = q := by
      simp [p]
    have hmid :
        pushFwdSectionCross (I := I) (J := J) Phi ZXh q =
          (metricCov (I := J) (M := N) g
            (fun r : N => pushFwdSectionCross (I := I) (J := J) Phi Z r) (Phi p))
            (pushFwdSectionCross (I := I) (J := J) Phi X (Phi p)) := by
      calc
        pushFwdSectionCross (I := I) (J := J) Phi ZXh q =
            pushFwdSectionCross (I := I) (J := J) Phi ZXh (Phi p) := by rw [hp]
        _ = mfderiv I J (Phi : M -> N) p (ZXh p) := by simp
        _ =
            (metricCov (I := J) (M := N) g
              (fun r : N => pushFwdSectionCross (I := I) (J := J) Phi Z r) (Phi p))
              (mfderiv I J (Phi : M -> N) p (X p)) := by
              simpa [h, covh, covg, ZXh] using
                metricCov_pullbackCross
                  (I := I) (J := J) g Phi Z p (X p)
        _ =
            (metricCov (I := J) (M := N) g
              (fun r : N => pushFwdSectionCross (I := I) (J := J) Phi Z r) (Phi p))
              (pushFwdSectionCross (I := I) (J := J) Phi X (Phi p)) := by
              rw [pushFwdSectionCross_apply_at_image]
    rw [← hp]
    rw [← hp] at hmid
    simpa [covg] using hmid
  have hbr :
      mfderiv I J (Phi : M -> N) x
          (VectorField.mlieBracket I (fun p : M => X p) (fun p : M => Y p) x) =
        VectorField.mlieBracket J
          (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi X q)
          (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Y q) (Phi x) := by
    haveI : IsManifold I (minSmoothness ℝ 2) M := by
      exact IsManifold.of_le (I := I) (M := M) (n := ∞)
        (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    haveI : IsManifold J (minSmoothness ℝ 2) N := by
      exact IsManifold.of_le (I := J) (M := N) (n := ∞)
        (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hbr' :=
      VectorField.mpullback_mlieBracket
        (I := J) (I' := I) (f := (Phi.symm : N -> M))
        (V := fun p : M => X p) (W := fun p : M => Y p)
        (x₀ := Phi x)
        (by
          simpa using
            X.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (by
          simpa using
            Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        Phi.symm.contMDiff.contMDiffAt
        (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    simpa [pushFwdSectionCross, pushFwdFieldCross] using hbr'
  simp only [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField]
  change
    mfderiv I J (Phi : M -> N) x
      ((covh (fun p : M => ZYh p) x) (X x) -
        (covh (fun p : M => ZXh p) x) (Y x) -
        (covh (fun p : M => Z p) x)
          (VectorField.mlieBracket I (fun p : M => X p) (fun p : M => Y p) x))
      =
      (covg (fun q : N =>
          (covg (fun r : N => pushFwdSectionCross (I := I) (J := J) Phi Z r) q)
            (pushFwdSectionCross (I := I) (J := J) Phi Y q)) (Phi x))
        (pushFwdSectionCross (I := I) (J := J) Phi X (Phi x)) -
        (covg (fun q : N =>
          (covg (fun r : N => pushFwdSectionCross (I := I) (J := J) Phi Z r) q)
            (pushFwdSectionCross (I := I) (J := J) Phi X q)) (Phi x))
          (pushFwdSectionCross (I := I) (J := J) Phi Y (Phi x)) -
        (covg (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Z q) (Phi x))
          (VectorField.mlieBracket J
            (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi X q)
            (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Y q) (Phi x))
  rw [map_sub, map_sub]
  rw [metricCov_pullbackCross (I := I) (J := J) g Phi ZYh x (X x)]
  rw [metricCov_pullbackCross (I := I) (J := J) g Phi ZXh x (Y x)]
  rw [metricCov_pullbackCross
    (I := I) (J := J) g Phi Z x
    (VectorField.mlieBracket I (fun p : M => X p) (fun p : M => Y p) x)]
  rw [hZY, hZX, hbr]
  simp [covg]

omit [NeZero (Module.finrank ℝ E)] [NeZero (Module.finrank ℝ F)] in
theorem metricRm04Std_pullbackCross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (x : M) (X Y Z W : TangentSpace I x) :
    metricRm04StdAt (I := I) (M := M)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x X Y Z W =
      metricRm04StdAt (I := J) (M := N) g (Phi x)
        (mfderiv I J (Phi : M -> N) x X)
        (mfderiv I J (Phi : M -> N) x Y)
        (mfderiv I J (Phi : M -> N) x Z)
        (mfderiv I J (Phi : M -> N) x W) := by
  obtain ⟨Xs, hXs⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  obtain ⟨Ys, hYs⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y
  obtain ⟨Zs, hZs⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Z
  obtain ⟨Ws, hWs⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x W
  rw [metricRm04StdAt_apply, metricRm04StdAt_apply]
  unfold metricRm04At
  have hleft :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At_apply_smooth
      (I := I)
      (g := Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
      (cov := metricCov (I := I) (M := M)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi))
      (hcov := metricCov_smooth (I := I) (M := M)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi))
      Xs Ys Zs Ws x
  have hright :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At_apply_smooth
      (I := J)
      (g := g)
      (cov := metricCov (I := J) (M := N) g)
      (hcov := metricCov_smooth (I := J) (M := N) g)
      (pushFwdSectionCross (I := I) (J := J) Phi Xs)
      (pushFwdSectionCross (I := I) (J := J) Phi Ys)
      (pushFwdSectionCross (I := I) (J := J) Phi Zs)
      (pushFwdSectionCross (I := I) (J := J) Phi Ws) (Phi x)
  rw [show DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
        (metricCov (I := I) (M := M) (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi))
        (metricCov_smooth (I := I) (M := M)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi))
        x (vec4 X Y Z W) =
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi).inner x W
        (DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField
          (I := I)
          (metricCov (I := I) (M := M) (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi))
          (fun p : M => Xs p) (fun p : M => Ys p) (fun p : M => Zs p) x) by
        simpa [hXs, hYs, hZs, hWs] using hleft]
  rw [show DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
        g (metricCov (I := J) (M := N) g)
        (metricCov_smooth (I := J) (M := N) g)
        (Phi x)
        (vec4 (mfderiv I J (Phi : M -> N) x X)
          (mfderiv I J (Phi : M -> N) x Y)
          (mfderiv I J (Phi : M -> N) x Z)
          (mfderiv I J (Phi : M -> N) x W)) =
      g.inner (Phi x) (mfderiv I J (Phi : M -> N) x W)
        (DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField
          (I := J) (metricCov (I := J) (M := N) g)
          (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Xs q)
          (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Ys q)
          (fun q : N => pushFwdSectionCross (I := I) (J := J) Phi Zs q) (Phi x)) by
        simpa [hXs, hYs, hZs, hWs] using hright]
  rw [Diffeomorph.pullbackMetricCross_inner]
  rw [connectionRiemannCurvatureField_pullback_pushFwdCross
    (I := I) (J := J) g Phi Xs Ys Zs x]

end DifferentialGeometry.Integral.Connection
