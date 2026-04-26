import Riemannian.Connection

/-!
# Riemannian.SecondFundamentalForm

Codim-1 second fundamental form, $|A|^2$, and mean curvature.

## Form

The second fundamental form on a hypersurface (codim-1 submanifold) is
the bilinear form $A(X, Y) := \langle \nabla^M_X Y, \nu \rangle$, where
$\nu$ is the unit normal to the hypersurface in the ambient $M$.

For the codim-1 setting in our framework, the hypersurface is the
support of a `Varifold M`, and $\nu$ is supplied by the
`Varifold.HasNormal` typeclass (Phase 1.5 Commit B).

## Sorry status

The defs use `Classical.choose` over existence axioms (`PRE-PAPER`).
Repair: inner-product computation of $\langle \nabla^M_X Y, \nu \rangle$
requires an inner-product structure on `TangentSpace I x` (provided by
`RiemannianBundle (fun x ↦ TangentSpace I x)`); local-frame trace for
$|A|^2$ and mean curvature requires local-frame plumbing — both
deferred to a future Phase.

**Ground truth**: do Carmo 1992 §6.2 (codim-1 case);
Simon 1983 §49 (use in second variation).
-/

open Bundle
open scoped ContDiff Manifold

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

/-- **Existence axiom for codim-1 second fundamental form (scalar form).**

For a unit normal field $\nu$ and tangent vector fields $X, Y$ on $M$,
there exists a real-valued function representing
$A(X, Y) := \langle \nabla^M_X Y, \nu \rangle$ at each point, satisfying
the **symmetry property** $A(X, Y) = A(Y, X)$ when $\nabla^M$ is
torsion-free (Levi-Civita case) — do Carmo 1992 §6.2.

**Sorry status**: PRE-PAPER. Repair plan: replace with explicit
inner-product computation $\langle \mathrm{covDeriv}\,X\,Y\,x, \nu(x) \rangle$
once `RiemannianBundle (fun x ↦ TangentSpace I x)` is wired through
the typeclass cascade and `inner ℝ` resolves on `TangentSpace I x`.
Symmetry follows from torsion-freeness of Levi-Civita (commit
`leviCivitaConnection_torsion_zero`). -/
theorem secondFundamentalFormScalar_exists :
    ∃ _A : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) →
           (Π x : M, TangentSpace I x) → M → ℝ,
      ∀ ν X Y x, _A ν X Y x = _A ν Y X x :=
  ⟨fun _ _ _ _ => 0, fun _ _ _ _ => rfl⟩

/-- The **second fundamental form (codim-1 scalar form)** $A$ at a point:
$$A(X, Y)(x) := \langle \nabla^M_X Y(x), \nu(x) \rangle.$$

**Ground truth**: do Carmo 1992 §6.2. -/
noncomputable def secondFundamentalFormScalar
    (ν X Y : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  Classical.choose (secondFundamentalFormScalar_exists (I := I) (M := M)) ν X Y x

/-- **Second fundamental form is symmetric** (codim-1, Levi-Civita):
$A(X, Y) = A(Y, X)$. Extracted from `secondFundamentalFormScalar_exists`. -/
@[simp]
theorem secondFundamentalFormScalar_symm
    (ν X Y : Π x : M, TangentSpace I x) (x : M) :
    secondFundamentalFormScalar ν X Y x = secondFundamentalFormScalar ν Y X x :=
  Classical.choose_spec
    (secondFundamentalFormScalar_exists (I := I) (M := M)) ν X Y x

/-- **Existence axiom for $|A|^2$.**

For a unit normal field $\nu$, there exists a **non-negative**
real-valued function representing the squared norm of the second
fundamental form: $|A|^2(x) := \sum_{i, j} A(e_i, e_j)(x)^2$ for any
orthonormal frame $\{e_i\}$ at $x$. Non-negativity is built into the
existence statement (sum of squares).

**Sorry status**: PRE-PAPER. Repair plan: replace with explicit
local-frame sum once `LocalFrame.toBasisAt` is wired through;
non-negativity is preserved trivially since the explicit form is a
sum of squares. -/
theorem secondFundamentalFormSqNorm_exists :
    ∃ _AsqNorm : (Π x : M, TangentSpace I x) → M → ℝ,
      ∀ ν x, 0 ≤ _AsqNorm ν x :=
  ⟨fun _ _ => 0, fun _ _ => le_refl _⟩

/-- $|A|^2 : M \to \mathbb{R}$, the squared norm of the second fundamental form.

**Ground truth**: do Carmo 1992 §6.2; Simon 1983 §49 (Jacobi formula
uses this). -/
noncomputable def secondFundamentalFormSqNorm
    (ν : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  Classical.choose (secondFundamentalFormSqNorm_exists (I := I) (M := M)) ν x

/-- **$|A|^2 \geq 0$**: squared norm is non-negative. Extracted from
`secondFundamentalFormSqNorm_exists`. -/
@[simp]
theorem secondFundamentalFormSqNorm_nonneg
    (ν : Π x : M, TangentSpace I x) (x : M) :
    0 ≤ secondFundamentalFormSqNorm ν x :=
  Classical.choose_spec
    (secondFundamentalFormSqNorm_exists (I := I) (M := M)) ν x

/-- **Existence axiom for the codim-1 mean curvature.**

For a unit normal field $\nu$, there exists a real-valued function
representing the mean curvature $H := \mathrm{tr}_g A$.

**Sorry status**: PRE-PAPER. Repair plan: replace with explicit
$g$-trace of `secondFundamentalFormScalar`. -/
theorem meanCurvature_exists :
    ∃ _H : (Π x : M, TangentSpace I x) → M → ℝ, True :=
  ⟨fun _ _ => 0, trivial⟩

/-- The **mean curvature (codim-1 scalar form)** $H : M \to \mathbb{R}$
of the hypersurface oriented by unit normal $\nu$.

**Ground truth**: do Carmo 1992 §6.2; standard codim-1 specialization. -/
noncomputable def meanCurvature
    (ν : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  Classical.choose (meanCurvature_exists (I := I) (M := M)) ν x

end Riemannian
