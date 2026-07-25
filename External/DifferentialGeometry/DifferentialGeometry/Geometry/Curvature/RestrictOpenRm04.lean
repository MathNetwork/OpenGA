import DifferentialGeometry.Geometry.Curvature.OpenSubtypeNaturality
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections

set_option autoImplicit false
set_option linter.style.longLine false


















noncomputable section

namespace DifferentialGeometry.Integral.Connection

open scoped Manifold ContDiff Topology
open DifferentialGeometry.Integral.Connection.CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]






omit [SigmaCompactSpace M] in
theorem connectionRiemannCurvatureField_restrictOpen
    (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    (Xs Ys Zs : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : U) :
    connectionRiemannCurvatureField (I := I)
        (metricCov (I := I) (M := U) (g.restrictOpen (I := I) U))
        (restrictOpenTangentField (I := I) U (fun p : M => Xs p))
        (restrictOpenTangentField (I := I) U (fun p : M => Ys p))
        (restrictOpenTangentField (I := I) U (fun p : M => Zs p)) x =
      connectionRiemannCurvatureField (I := I) (metricCov (I := I) (M := M) g)
        (fun p : M => Xs p) (fun p : M => Ys p) (fun p : M => Zs p) (x : M) := by

  let ZYs : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ⟨fun p : M => (metricCov (I := I) (M := M) g (fun q : M => Zs q) p) (Ys p),
      cov_smooth_apply_contMDiffAt (I := I) (metricCov (I := I) (M := M) g)
        (metricCov_smooth (I := I) (M := M) g) Ys Zs⟩
  let ZXs : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ⟨fun p : M => (metricCov (I := I) (M := M) g (fun q : M => Zs q) p) (Xs p),
      cov_smooth_apply_contMDiffAt (I := I) (metricCov (I := I) (M := M) g)
        (metricCov_smooth (I := I) (M := M) g) Xs Zs⟩


  have hZY :
      (fun y : U =>
          (metricCov (I := I) (M := U) (g.restrictOpen (I := I) U)
            (restrictOpenTangentField (I := I) U (fun p : M => Zs p)) y)
            (restrictOpenTangentField (I := I) U (fun p : M => Ys p) y)) =
        restrictOpenTangentField (I := I) U (fun p : M => ZYs p) := by
    funext y
    rw [restrictOpenTangentField_apply (I := I) U (fun p : M => ZYs p) y,
      restrictOpenTangentField_apply (I := I) U (fun p : M => Ys p) y]
    exact metricCov_restrictOpen_globalSection (I := I) g U Zs y (Ys (y : M))
  have hZX :
      (fun y : U =>
          (metricCov (I := I) (M := U) (g.restrictOpen (I := I) U)
            (restrictOpenTangentField (I := I) U (fun p : M => Zs p)) y)
            (restrictOpenTangentField (I := I) U (fun p : M => Xs p) y)) =
        restrictOpenTangentField (I := I) U (fun p : M => ZXs p) := by
    funext y
    rw [restrictOpenTangentField_apply (I := I) U (fun p : M => ZXs p) y,
      restrictOpenTangentField_apply (I := I) U (fun p : M => Xs p) y]
    exact metricCov_restrictOpen_globalSection (I := I) g U Zs y (Xs (y : M))

  have hbr :
      VectorField.mlieBracket I
          (restrictOpenTangentField (I := I) U (fun p : M => Xs p))
          (restrictOpenTangentField (I := I) U (fun p : M => Ys p)) x =
        VectorField.mlieBracket I (fun p : M => Xs p) (fun p : M => Ys p) (x : M) := by
    rw [← mlieBracket_restrictOpen (I := I) U Xs Ys x]
    rw [restrictOpenTangentField_apply (I := I) U
      (fun p : M => VectorField.mlieBracket I (fun q : M => Xs q) (fun q : M => Ys q) p) x]
  simp only [connectionRiemannCurvatureField]
  rw [hZY, hZX, hbr,
    restrictOpenTangentField_apply (I := I) U (fun p : M => Xs p) x,
    restrictOpenTangentField_apply (I := I) U (fun p : M => Ys p) x,
    metricCov_restrictOpen_globalSection (I := I) g U ZYs x (Xs (x : M)),
    metricCov_restrictOpen_globalSection (I := I) g U ZXs x (Ys (x : M)),
    metricCov_restrictOpen_globalSection (I := I) g U Zs x
      (VectorField.mlieBracket I (fun p : M => Xs p) (fun p : M => Ys p) (x : M))]
  rfl




omit [SigmaCompactSpace M] in
theorem metricRm04StdAt_restrictOpen
    (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (x : U) (X Y Z W : TangentSpace I x) :
    metricRm04StdAt (I := I) (M := U) (g.restrictOpen (I := I) U) x X Y Z W =
      metricRm04StdAt (I := I) (M := M) g (x : M) X Y Z W := by
  obtain ⟨Xs, hXs⟩ :=
    ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) (x : M) X
  obtain ⟨Ys, hYs⟩ :=
    ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) (x : M) Y
  obtain ⟨Zs, hZs⟩ :=
    ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) (x : M) Z
  obtain ⟨Ws, hWs⟩ :=
    ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) (x : M) W

  have hR :
      metricRm04StdAt (I := I) (M := M) g (x : M) X Y Z W =
        g.inner (x : M) W
          (connectionRiemannCurvatureField (I := I) (metricCov (I := I) (M := M) g)
            (fun p : M => Xs p) (fun p : M => Ys p) (fun p : M => Zs p) (x : M)) := by
    have hvec :
        (vec4 (I := I) (x := (x : M)) X Y Z W) =
          vec4 (I := I) (x := (x : M)) (Xs (x : M)) (Ys (x : M)) (Zs (x : M)) (Ws (x : M)) := by
      rw [hXs, hYs, hZs, hWs]
    rw [metricRm04StdAt_apply, hvec,
      show metricRm04At (I := I) (M := M) g (x : M) =
          riemannCurvature04At (I := I) g (metricCov (I := I) (M := M) g)
            (metricCov_smooth (I := I) (M := M) g) (x : M) from rfl,
      riemannCurvature04At_apply_smooth (I := I) g (metricCov (I := I) (M := M) g)
        (metricCov_smooth (I := I) (M := M) g) Xs Ys Zs Ws (x : M), hWs]

  have hL :
      metricRm04StdAt (I := I) (M := U) (g.restrictOpen (I := I) U) x X Y Z W =
        g.inner (x : M) W
          (connectionRiemannCurvatureField (I := I) (metricCov (I := I) (M := M) g)
            (fun p : M => Xs p) (fun p : M => Ys p) (fun p : M => Zs p) (x : M)) := by
    have hvec :
        (vec4 (I := I) (x := x) X Y Z W) =
          vec4 (I := I) (x := x)
            (restrictOpenTangentSection (I := I) U Xs x)
            (restrictOpenTangentSection (I := I) U Ys x)
            (restrictOpenTangentSection (I := I) U Zs x)
            (restrictOpenTangentSection (I := I) U Ws x) := by
      rw [restrictOpenTangentSection_apply, restrictOpenTangentSection_apply,
        restrictOpenTangentSection_apply, restrictOpenTangentSection_apply,
        hXs, hYs, hZs, hWs]
    rw [metricRm04StdAt_apply, hvec,
      show metricRm04At (I := I) (M := U) (g.restrictOpen (I := I) U) x =
          riemannCurvature04At (I := I) (g.restrictOpen (I := I) U)
            (metricCov (I := I) (M := U) (g.restrictOpen (I := I) U))
            (metricCov_smooth (I := I) (M := U) (g.restrictOpen (I := I) U)) x from rfl,
      riemannCurvature04At_apply_smooth (I := I) (g.restrictOpen (I := I) U)
        (metricCov (I := I) (M := U) (g.restrictOpen (I := I) U))
        (metricCov_smooth (I := I) (M := U) (g.restrictOpen (I := I) U))
        (restrictOpenTangentSection (I := I) U Xs)
        (restrictOpenTangentSection (I := I) U Ys)
        (restrictOpenTangentSection (I := I) U Zs)
        (restrictOpenTangentSection (I := I) U Ws) x,
      SmoothRiemannianMetric.restrictOpen_inner,
      restrictOpenTangentSection_apply, hWs]
    exact congrArg (fun v => g.inner (x : M) W v)
      (connectionRiemannCurvatureField_restrictOpen (I := I) g U Xs Ys Zs x)
  rw [hL, hR]

end DifferentialGeometry.Integral.Connection
