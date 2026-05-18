import OpenGALib.Riemannian.Connection.LeviCivita

/-!
# `covDeriv` / `covDerivAt` simp bridges

Engineering `@[simp]` rfl bridges between the structural form
`(leviCivitaConnection.toFun Y x) (X x)`, the section-level
`covDeriv X Y x`, and the direction-CLM form `covDerivAt Y x (X x)`.

Tagged `@[simp]` so proofs working with the raw structural form get
rewritten into the notation-form headline (`∇[X] Y`) and into the
direction-CLM form for CLM-style algebra, automatically.
-/

open scoped ContDiff Manifold Topology Riemannian

namespace Riemannian

section CovDerivBridges

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-- **Eng.** Bridge: `(leviCivitaConnection.toFun Y x) (X x) = (∇[X] Y) x` by
definition. Rewrites raw structural form into the `∇` notation form. -/
@[simp] theorem leviCivitaConnection_toFun_eq_covDeriv
    (X Y : VectorFieldSection I M) (x : M) :
    (leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun Y x (X x)
      = (∇[X] Y) x := rfl

/-- **Eng.** `covDeriv X Y x = covDerivAt Y x (X x)`: section-level
`covDeriv` factors through the pointwise continuous linear map `covDerivAt`. -/
@[simp]
theorem covDeriv_eq_covDerivAt
    (X Y : VectorFieldSection I M) (x : M) :
    covDeriv HasMetric.metric X Y x = covDerivAt HasMetric.metric Y x (X x) :=
  rfl

/-- **Eng.** Constant-section specialization:
`covDeriv (fun _ => v) Y x = covDerivAt Y x v`. -/
@[simp]
theorem covDeriv_const_eq_covDerivAt
    (v : E) (Y : VectorFieldSection I M) (x : M) :
    covDeriv HasMetric.metric (fun _ : M => v) Y x
      = covDerivAt HasMetric.metric Y x v :=
  rfl

end CovDerivBridges

end Riemannian
