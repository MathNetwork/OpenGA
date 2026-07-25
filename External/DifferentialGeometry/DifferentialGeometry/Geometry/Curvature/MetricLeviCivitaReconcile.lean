import DifferentialGeometry.Geometry.Connection.LeviCivita.Reconcile
import DifferentialGeometry.Geometry.Curvature.Basic
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections
import DifferentialGeometry.Geometry.Curvature.Metric












namespace DifferentialGeometry

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in






omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivita_contMDiffCovariantDerivativeLocally (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally (LeviCivita (I := I) g) ∞ := by
  simpa [LeviCivita, metricCov] using (metricCov_smooth (I := I) g)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in





omit [SigmaCompactSpace M] [T2Space M] in
theorem connectionRiemannCurvatureField_lcOfMetric_eq_leviCivita
    (g : SmoothRiemannianMetric I M)
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    connectionRiemannCurvatureField (I := I) (leviCivitaConnectionOfMetric (I := I) g)
        (fun p => X p) (fun p => Y p) (fun p => Z p) x
      = connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g)
        (fun p => X p) (fun p => Y p) (fun p => Z p) x := by
  simp [LeviCivita]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in




omit [SigmaCompactSpace M] in
theorem riemannCurvatureAt_lcOfMetric_eq_leviCivita
    (g : SmoothRiemannianMetric I M)
    (x : M) :
    riemannCurvatureAt (leviCivitaConnectionOfMetric (I := I) g)
        (metricCov_smooth (I := I) g) x
      = riemannCurvatureAt (LeviCivita (I := I) g)
        (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g) x := by
  classical
  have hcov₁ := metricCov_smooth (I := I) g
  have hcov₂ := leviCivita_contMDiffCovariantDerivativeLocally (I := I) g
  apply tensorRSSpace_ext (𝕜 := ℝ) 1 3 x
  intro α
  apply ContinuousMultilinearMap.ext
  intro v
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (v 0)
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (v 1)
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (v 2)
  have hv : v = vec3 (X x) (Y x) (Z x) := by
    funext i; fin_cases i <;> simp_all [vec3]
  rw [hv]
  change riemannCurvatureAt (leviCivitaConnectionOfMetric (I := I) g) hcov₁ x α
      (vec3 (X x) (Y x) (Z x)) =
    riemannCurvatureAt (LeviCivita (I := I) g) hcov₂ x α
      (vec3 (X x) (Y x) (Z x))
  rw [riemannCurvatureAt_apply_smooth (I := I) (leviCivitaConnectionOfMetric (I := I) g)
      hcov₁ X Y Z α,
    riemannCurvatureAt_apply_smooth (I := I) (LeviCivita (I := I) g) hcov₂ X Y Z α]
  exact congrArg _
    (connectionRiemannCurvatureField_lcOfMetric_eq_leviCivita (I := I) g X Y Z x)

omit [NeZero (Module.finrank ℝ E)] in









omit [SigmaCompactSpace M] in
theorem riemannCurvatureAux_tangentConst_eq_riemannOp
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (X Y Z : TangentSpace I x) :
    riemannCurvatureAux cov (CovariantDerivative.tangentConstAt (I := I) x X)
        (CovariantDerivative.tangentConstAt (I := I) x Y)
        (CovariantDerivative.tangentConstAt (I := I) x Z) x
      = riemannOp cov x X Y Z := by
  obtain ⟨Xc, hXc, hXcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x X
  obtain ⟨Yc, hYc, hYcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x Y
  obtain ⟨Zc, hZc, hZcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x Z
  rw [riemannCurvatureAux_eq_connectionRiemannCurvatureField,
    connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst
      (I := I) cov hcov X Y Z Xc Yc Zc hXc hYc hZc]
  have hsec :
      connectionRiemannCurvatureField cov
          (fun p : M => Xc p) (fun p : M => Yc p) (fun p : M => Zc p) x
        = riemannSec cov (fun p : M => Xc p) (fun p : M => Yc p)
            (fun p : M => Zc p) x := rfl
  rw [hsec, ← riemannOp_apply_smooth (cov := cov) Xc.contMDiff Yc.contMDiff Zc.contMDiff,
    hXcx, hYcx, hZcx]







omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciCurvatureAt_leviCivita_apply_eq_ricciTensor
    (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ricciCurvatureAt (LeviCivita (I := I) g)
        (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g) x (vec2 v w)
      = ricciTensor (I := I) g x v w := by
  classical
  have hcov₂ := leviCivita_contMDiffCovariantDerivativeLocally (I := I) g
  rw [ricciCurvatureAt_eq_trace,
    ricciFromRm13At_apply_basis_trace (chartModelBasis E)
      (riemannCurvatureAt (LeviCivita (I := I) g) hcov₂ x) v w,
    ricciTensor_apply_basisSum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [riemannCurvatureAt_apply_const,
    riemannCurvatureAux_tangentConst_eq_riemannOp (cov := LeviCivita (I := I) g) (hcov := hcov₂),
    cotangentToDual_dualToCotangent_gen, Module.Basis.coord_apply]
  rfl







omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricRicciAt_apply_eq_ricciTensor
    (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    metricRicciAt (I := I) g x (vec2 v w) = ricciTensor (I := I) g x v w := by
  have hcov₂ := leviCivita_contMDiffCovariantDerivativeLocally (I := I) g
  have key : riemannCurvatureAt (metricCov (I := I) g) (metricCov_smooth (I := I) g) x
           = riemannCurvatureAt (LeviCivita (I := I) g) hcov₂ x :=
    riemannCurvatureAt_lcOfMetric_eq_leviCivita (I := I) g x
  rw [metricRicciAt, ricciCurvatureAt_eq_trace, key, ← ricciCurvatureAt_eq_trace]
  exact ricciCurvatureAt_leviCivita_apply_eq_ricciTensor (I := I) g x v w

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in




omit [SigmaCompactSpace M] in
theorem metricRm13At_eq_riemannCurvatureAt
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm13At (I := I) g x
      = riemannCurvatureAt (LeviCivita (I := I) g)
          (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g) x := by
  change riemannCurvatureAt (metricCov (I := I) g) (metricCov_smooth (I := I) g) x
     = riemannCurvatureAt (LeviCivita (I := I) g)
          (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g) x
  exact riemannCurvatureAt_lcOfMetric_eq_leviCivita (I := I) g x

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in





omit [SigmaCompactSpace M] in
theorem metricRm04At_eq_riemannCurvature04At
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm04At (I := I) g x
      = riemannCurvature04At (I := I) g (LeviCivita (I := I) g)
          (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g) x := by
  have hcov₂ := leviCivita_contMDiffCovariantDerivativeLocally (I := I) g
  have key : riemannCurvatureAt (metricCov (I := I) g) (metricCov_smooth (I := I) g) x
           = riemannCurvatureAt (LeviCivita (I := I) g) hcov₂ x :=
    riemannCurvatureAt_lcOfMetric_eq_leviCivita (I := I) g x
  change riemannCurvature04At (I := I) g (metricCov (I := I) g) (metricCov_smooth (I := I) g) x
     = riemannCurvature04At (I := I) g (LeviCivita (I := I) g) hcov₂ x
  unfold riemannCurvature04At
  rw [key]

end DifferentialGeometry
