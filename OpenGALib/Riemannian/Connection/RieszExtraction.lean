import OpenGALib.Riemannian.Connection.Koszul

/-!
# Riesz extraction of the Levi-Civita pointwise value

Builds $\nabla_X Y(x) \in T_xM$ as the Riesz representative of the
half-Koszul functional $Z \mapsto \tfrac12 K(X, Y; Z)(x)$. The
$C^\infty(M)$-tensoriality in $Z$ (`koszulFunctional_tensorialAt`) packages
the half-Koszul as a `TangentSpace I x →L[ℝ] ℝ` via
`TensorialAt.mkHom`; framework-owned `metricRiesz` then extracts the
unique tangent vector.

The output `koszulCovDeriv X Y x hX hY : TangentSpace I x` and its
defining identity `koszulCovDeriv_inner_eq` feed the Levi-Civita
construction in `Connection.lean`.

**Ground truth**: do Carmo, *Riemannian Geometry*, §2 Theorem 3.6,
existence proof Step 3.
-/

open Bundle VectorField
open scoped ContDiff Manifold Topology Riemannian

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [hm : HasMetric I M]

omit [CompleteSpace E] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] in
/-- **Math.** **Riesz extraction existence**: under smoothness of $X, Y$
at $x$, the half-Koszul functional $Z \mapsto \tfrac12 K(X, Y; Z)(x)$
admits a unique tangent-space representative for smooth $Z$.

Closed via `TensorialAt.mkHom` on `koszulFunctional_tensorialAt`.

**Ground truth**: do Carmo 1992 §2 Theorem 3.6 existence proof, Step 3. -/
theorem koszulLinearFunctional_exists
    [IsLocallyConstantChartedSpace H M]
    (X Y : VectorFieldSection I M) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x) :
    ∃ φ : (TangentSpace I x) →L[ℝ] ℝ,
      ∀ Z : VectorFieldSection I M,
        TangentSmoothAt Z x →
        φ (Z x) = (1/2 : ℝ) * koszulFunctional X Y Z x := by
  refine ⟨TensorialAt.mkHom _ x (koszulFunctional_tensorialAt X Y x hX hY),
          fun Z hZ => ?_⟩
  exact TensorialAt.mkHom_apply (koszulFunctional_tensorialAt X Y x hX hY) hZ

omit [CompleteSpace E] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] in
/-- **Math.** Riesz-extracted tangent vector `v ∈ T_xM` satisfying
$\langle v, Z(x)\rangle = \tfrac12 K(X, Y; Z)(x)$ for all smooth $Z$.
The Levi-Civita value $\nabla_X Y(x)$. -/
theorem koszulCovDeriv_exists
    [IsLocallyConstantChartedSpace H M]
    (X Y : VectorFieldSection I M) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x) :
    ∃ v : TangentSpace I x, ∀ Z : VectorFieldSection I M,
      TangentSmoothAt Z x →
      metricInner x v (Z x) = (1/2 : ℝ) * koszulFunctional X Y Z x := by
  obtain ⟨φ, hφ⟩ := koszulLinearFunctional_exists X Y x hX hY
  refine ⟨metricRiesz x φ, fun Z hZ => ?_⟩
  rw [metricRiesz_inner]
  exact hφ Z hZ

/-- **Math.** **Levi-Civita via Koszul + Riesz** (explicit construction):
$\nabla_X Y(x) \in T_xM$ is the unique vector with
$$\langle \nabla_X Y(x), Z(x)\rangle = \tfrac12 K(X, Y; Z)(x)$$
for all smooth $Z$, extracted via Riesz over the framework-owned
`metricInner`. -/
noncomputable def koszulCovDeriv
    [IsLocallyConstantChartedSpace H M]
    (X Y : VectorFieldSection I M) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x) : TangentSpace I x :=
  Classical.choose (koszulCovDeriv_exists X Y x hX hY)

omit [CompleteSpace E] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] in
/-- **Math.** **Riesz defining property**:
$\langle \nabla_X Y(x), Z(x)\rangle = \tfrac12 K(X, Y; Z)(x)$ for smooth
$X, Y, Z$, with `metricInner` as the framework-owned inner product. -/
theorem koszulCovDeriv_inner_eq
    [IsLocallyConstantChartedSpace H M]
    (X Y Z : VectorFieldSection I M) (x : M)
    (hX : TangentSmoothAt X x) (hY : TangentSmoothAt Y x)
    (hZ : TangentSmoothAt Z x) :
    metricInner x (koszulCovDeriv X Y x hX hY) (Z x)
      = (1/2 : ℝ) * koszulFunctional X Y Z x :=
  Classical.choose_spec (koszulCovDeriv_exists X Y x hX hY) Z hZ

end Riemannian
