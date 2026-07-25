import DifferentialGeometry.Geometry.Curvature.Metric
import DifferentialGeometry.Geometry.Metric.OpenSubtype
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartLieBracket

set_option autoImplicit false
set_option linter.style.longLine false








noncomputable section

namespace DifferentialGeometry.Integral.Connection

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

private lemma infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by
  decide




omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem SmoothRiemannianMetric.eq_of_inner_eq_gen
    (g : SmoothRiemannianMetric I M) {x : M} {v w : TangentSpace I x}
    (h : ∀ ζ : TangentSpace I x, g.inner x v ζ = g.inner x w ζ) : v = w := by
  have hpair : ∀ ζ : TangentSpace I x, g.inner x (v - w) ζ = 0 := by
    intro ζ
    have hsub : g.inner x (v - w) ζ = g.inner x v ζ - g.inner x w ζ := by
      simp [map_sub, ContinuousLinearMap.sub_apply]
    rw [hsub, h ζ, sub_self]
  have hself : g.inner x (v - w) (v - w) = 0 := hpair (v - w)
  by_contra hne
  have hne' : v - w ≠ 0 := sub_ne_zero.mpr hne
  exact (lt_irrefl (0 : Real)) (hself ▸ g.pos x _ hne')




omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] in
theorem extDerivFun_restrictOpen
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    (f : M -> Real) (x : U) (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f (x : M)) :
    extDerivFun (I := I) (fun y : U => f (y : M)) x v =
      extDerivFun (I := I) f (x : M) v := by
  have hval :
      MDifferentiableAt I I (fun y : U => (y : M)) x := by
    exact ((contMDiff_subtype_val (I := I) (U := U)).contMDiffAt).mdifferentiableAt
      infty_ne_zero
  rw [extDerivFun_real_eq_mfderiv, extDerivFun_real_eq_mfderiv]
  simpa [Function.comp_def, mfderiv_subtype_val_apply (I := I) U x v] using
    mfderiv_comp_apply (I := I) (I' := I) (I'' := 𝓘(Real, Real))
      x hf hval v




noncomputable def restrictOpenTangentField
    (U : TopologicalSpace.Opens M)
    (Y : (p : M) -> TangentSpace I p) : (y : U) -> TangentSpace I y :=
  VectorField.mpullback I I (Subtype.val : U -> M) Y

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] in
@[simp]
theorem restrictOpenTangentField_apply
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    (Y : (p : M) -> TangentSpace I p) (x : U) :
    restrictOpenTangentField (I := I) U Y x = Y (x : M) := by
  unfold restrictOpenTangentField VectorField.mpullback
  have hval_inv : (mfderiv% (Subtype.val : U -> M) x).IsInvertible := by
    rw [mfderiv_subtype_val (I := I) U x]
    change (ContinuousLinearMap.id Real E).IsInvertible
    exact (ContinuousLinearMap.isInvertible_equiv
      (f := ContinuousLinearEquiv.refl Real E))
  rw [ContinuousLinearMap.IsInvertible.inverse_apply_eq hval_inv]
  rw [mfderiv_subtype_val (I := I) U x]
  rfl



omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem mdiffAt_restrictOpen_section
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : U) :
    MDiffAt (T% (restrictOpenTangentField (I := I) U (fun y : M => Y y))) x := by
  have hY : MDiffAt (T% (fun y : M => Y y)) (x : M) :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt infty_ne_zero
  have hval : ContMDiffAt I I (∞ : WithTop ℕ∞) (Subtype.val : U -> M) x :=
    (contMDiff_subtype_val (I := I) (U := U)).contMDiffAt
  have hval_inv : (mfderiv% (Subtype.val : U -> M) x).IsInvertible := by
    rw [mfderiv_subtype_val (I := I) U x]
    change (ContinuousLinearMap.id Real E).IsInvertible
    exact (ContinuousLinearMap.isInvertible_equiv
      (f := ContinuousLinearEquiv.refl Real E))
  have hmn : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h1 : (2 : ℕ∞) ≤ ⊤ := le_top
    have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_le_coe.mpr h1
    convert h2 using 1
  exact MDifferentiableAt.mpullback_vectorField
    (I := I) (I' := I) (f := (Subtype.val : U -> M)) (V := fun y : M => Y y)
    (x₀ := x) (n := (∞ : WithTop ℕ∞)) hY hval hval_inv hmn



omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem contMDiff_restrictOpen_section
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)) :
    ContMDiff I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
      (T% (restrictOpenTangentField (I := I) U (fun y : M => Y y))) := by
  refine ContMDiff.mpullback_vectorField
    (I := I) (I' := I) (f := (Subtype.val : U -> M))
    (V := fun y : M => Y y) (m := ∞) (n := ∞)
    Y.contMDiff (contMDiff_subtype_val (I := I) (U := U)) ?_ ?_
  · intro x
    rw [mfderiv_subtype_val (I := I) U x]
    change (ContinuousLinearMap.id Real E).IsInvertible
    exact (ContinuousLinearMap.isInvertible_equiv
      (f := ContinuousLinearEquiv.refl Real E))
  · simp



noncomputable def restrictOpenTangentSection
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : U -> Type _) where
  toFun := restrictOpenTangentField (I := I) U (fun y : M => Y y)
  contMDiff_toFun := contMDiff_restrictOpen_section (I := I) U Y

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
@[simp]
theorem restrictOpenTangentSection_apply
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : U) :
    restrictOpenTangentSection (I := I) U Y x = Y (x : M) := by
  simp [restrictOpenTangentSection]



omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem mlieBracket_restrictOpen
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : U) :
    restrictOpenTangentField (I := I) U
        (fun y : M => VectorField.mlieBracket I (fun z : M => X z) (fun z : M => Y z) y) x =
      VectorField.mlieBracket I
        (restrictOpenTangentField (I := I) U (fun y : M => X y))
        (restrictOpenTangentField (I := I) U (fun y : M => Y y)) x := by
  haveI : IsManifold I (minSmoothness Real 2) M := by
    exact IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  haveI : IsManifold I (minSmoothness Real 2) U := by
    exact IsManifold.of_le (I := I) (M := U) (n := ∞)
      (by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hval : ContMDiffAt I I (∞ : WithTop ℕ∞) (Subtype.val : U -> M) x :=
    (contMDiff_subtype_val (I := I) (U := U)).contMDiffAt
  have hmin : minSmoothness Real 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))
  have hbr :=
    VectorField.mpullback_mlieBracket
      (I := I) (I' := I) (f := (Subtype.val : U -> M))
      (V := fun y : M => X y) (W := fun y : M => Y y) (x₀ := x)
      (by
        simpa using
          X.contMDiff.contMDiffAt.mdifferentiableAt infty_ne_zero)
      (by
        simpa using
          Y.contMDiff.contMDiffAt.mdifferentiableAt infty_ne_zero)
      hval hmin
  simpa [restrictOpenTangentField] using hbr



omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem directionalDeriv_restrictOpen_inner
    (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : U) :
    directionalDerivAlong (I := I)
        (restrictOpenTangentField (I := I) U (fun y : M => X y))
        (fun y : U => (g.restrictOpen (I := I) U).inner y
          (restrictOpenTangentField (I := I) U (fun z : M => Y z) y)
          (restrictOpenTangentField (I := I) U (fun z : M => Z z) y)) x =
      directionalDerivAlong (I := I)
        (fun y : M => X y)
        (fun y : M => g.inner y (Y y) (Z y)) (x : M) := by
  have hf :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => g.inner y (Y y) (Z y)) (x : M) :=
    (DifferentialGeometry.Integral.Connection.CovariantDerivative.metric_inner_contMDiffAt
      (I := I) (M := M) g
      Y.contMDiff.contMDiffAt Z.contMDiff.contMDiffAt
      (by simp)).mdifferentiableAt (by simp)
  simpa [directionalDerivAlong] using
    extDerivFun_restrictOpen (I := I) U
      (fun y : M => g.inner y (Y y) (Z y)) x (X (x : M)) hf



omit [T2Space M] [SigmaCompactSpace M] in
theorem koszulScalar_restrictOpen
    (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : U) :
    koszulScalar (I := I) (g.restrictOpen (I := I) U)
        (restrictOpenTangentField (I := I) U (fun y : M => X y))
        (restrictOpenTangentField (I := I) U (fun y : M => Y y))
        (restrictOpenTangentField (I := I) U (fun y : M => Z y)) x =
      koszulScalar (I := I) g
        (fun y : M => X y) (fun y : M => Y y) (fun y : M => Z y) (x : M) := by
  unfold koszulScalar
  rw [directionalDeriv_restrictOpen_inner (I := I) g U X Y Z x,
    directionalDeriv_restrictOpen_inner (I := I) g U Y Z X x,
    directionalDeriv_restrictOpen_inner (I := I) g U Z X Y x]
  rw [← mlieBracket_restrictOpen (I := I) U Y Z x,
    ← mlieBracket_restrictOpen (I := I) U Z X x,
    ← mlieBracket_restrictOpen (I := I) U X Y x]
  simp




omit [SigmaCompactSpace M] in
theorem metricCov_restrictOpen_apply_section
    (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : U) :
    (metricCov (I := I) (M := U) (g.restrictOpen (I := I) U)
        (restrictOpenTangentField (I := I) U (fun y : M => Y y)) x)
        (restrictOpenTangentField (I := I) U (fun y : M => X y) x) =
      (metricCov (I := I) (M := M) g (fun y : M => Y y) (x : M)) (X (x : M)) := by
  apply SmoothRiemannianMetric.eq_of_inner_eq_gen (g.restrictOpen (I := I) U)
  intro ζ
  obtain ⟨Z, hZx⟩ :=
    ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) (x : M) ζ
  have hZrestrict :
      restrictOpenTangentField (I := I) U (fun y : M => Z y) x = ζ := by
    simp [hZx]
  have hleft :
      (g.restrictOpen (I := I) U).inner x
          ((metricCov (I := I) (M := U) (g.restrictOpen (I := I) U)
            (restrictOpenTangentField (I := I) U (fun y : M => Y y)) x)
            (restrictOpenTangentField (I := I) U (fun y : M => X y) x))
          ζ =
        (1 / 2 : Real) *
          koszulScalar (I := I) (g.restrictOpen (I := I) U)
            (restrictOpenTangentField (I := I) U (fun y : M => X y))
            (restrictOpenTangentField (I := I) U (fun y : M => Y y))
            (restrictOpenTangentField (I := I) U (fun y : M => Z y)) x := by
    rw [← hZrestrict]
    exact leviCivitaConnectionOfMetric_inner_eq_koszulScalar
      (I := I) (g.restrictOpen (I := I) U)
      (restrictOpenTangentField (I := I) U (fun y : M => X y))
      (restrictOpenTangentField (I := I) U (fun y : M => Y y))
      (restrictOpenTangentField (I := I) U (fun y : M => Z y)) x
      (mdiffAt_restrictOpen_section (I := I) U X x)
      (mdiffAt_restrictOpen_section (I := I) U Y x)
      (mdiffAt_restrictOpen_section (I := I) U Z x)
  have hright :
      (g.restrictOpen (I := I) U).inner x
          ((metricCov (I := I) (M := M) g (fun y : M => Y y) (x : M)) (X (x : M)))
          ζ =
        (1 / 2 : Real) *
          koszulScalar (I := I) g
            (fun y : M => X y) (fun y : M => Y y) (fun y : M => Z y) (x : M) := by
    rw [SmoothRiemannianMetric.restrictOpen_inner, ← hZx]
    exact leviCivitaConnectionOfMetric_inner_eq_koszulScalar
      (I := I) g (fun y : M => X y) (fun y : M => Y y) (fun y : M => Z y) (x : M)
      (X.contMDiff.contMDiffAt.mdifferentiableAt infty_ne_zero)
      (Y.contMDiff.contMDiffAt.mdifferentiableAt infty_ne_zero)
      (Z.contMDiff.contMDiffAt.mdifferentiableAt infty_ne_zero)
  rw [hleft, hright, koszulScalar_restrictOpen (I := I) g U X Y Z x]



omit [SigmaCompactSpace M] in
theorem metricCov_restrictOpen_globalSection
    (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : U) (v : TangentSpace I x) :
    (metricCov (I := I) (M := U) (g.restrictOpen (I := I) U)
        (restrictOpenTangentField (I := I) U (fun y : M => Y y)) x) v =
      (metricCov (I := I) (M := M) g (fun y : M => Y y) (x : M)) v := by
  obtain ⟨X, hXx⟩ :=
    ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) (x : M) v
  calc
    (metricCov (I := I) (M := U) (g.restrictOpen (I := I) U)
        (restrictOpenTangentField (I := I) U (fun y : M => Y y)) x) v
        =
      (metricCov (I := I) (M := U) (g.restrictOpen (I := I) U)
        (restrictOpenTangentField (I := I) U (fun y : M => Y y)) x)
        (restrictOpenTangentField (I := I) U (fun y : M => X y) x) := by
          simp [hXx]
    _ =
      (metricCov (I := I) (M := M) g (fun y : M => Y y) (x : M)) (X (x : M)) := by
        exact metricCov_restrictOpen_apply_section (I := I) g U X Y x
    _ = (metricCov (I := I) (M := M) g (fun y : M => Y y) (x : M)) v := by
      rw [hXx]

end DifferentialGeometry.Integral.Connection
