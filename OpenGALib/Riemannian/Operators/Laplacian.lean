import OpenGALib.Riemannian.Operators.Hessian

/-!
# Laplace–Beltrami operator

For a smooth scalar $f : M \to \mathbb{R}$ on a Riemannian manifold $(M, g)$,
the **Laplace–Beltrami operator** is the trace of the Hessian:
$$\Delta_g f(x) = \operatorname{tr}_g (\operatorname{Hess} f)(x).$$

This file defines $\Delta_g$ on a user-supplied pointwise bilinear-form
Hessian `B : Bilin I M`, computed against the canonical basis of $E$, and
records its basic algebraic properties.

The Voss–Weyl chart formula and the divergence-of-gradient identity belong
with the chart machinery and are out of scope here.

## Main definitions

* `laplacian B x` — the trace of `B` against the canonical basis.

## Main results

* `laplacian_add`, `laplacian_smul` — linearity in `B`.
* `laplacian_sq_le_dim_mul_frobeniusSq` — Cauchy-Schwarz bound
  $(\Delta_g B(x))^2 \le n \cdot \operatorname{frobeniusSq} B(x)$.

Reference: do Carmo §3.6.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle
open scoped ContDiff Manifold Bundle Riemannian

namespace Riemannian
namespace Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hm : HasMetric I M]

/-- The **Laplace–Beltrami operator** $\Delta_g$ acting on a pointwise Hessian
bilinear form $B$:
$$\Delta_g B(x) = \sum_i B(x)(e_i, e_i).$$ -/
noncomputable def laplacian
    (B : Bilin (M := M) I) (x : M) : ℝ :=
  trace B x

@[simp] lemma laplacian_def
    (B : Bilin (M := M) I) (x : M) :
    laplacian (I := I) (M := M) B x = trace B x := rfl

/-- $\Delta_g (B + C) = \Delta_g B + \Delta_g C$. -/
theorem laplacian_add
    (B C : Bilin (M := M) I) (x : M) :
    laplacian (I := I) (M := M) (B + C) x =
      laplacian (I := I) (M := M) B x + laplacian (I := I) (M := M) C x := by
  simp only [laplacian, trace]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (B x + C x) ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) i) =
    B x ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) i) +
      C x ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) i)
  rfl

/-- $\Delta_g (c \cdot B) = c \cdot \Delta_g B$. -/
theorem laplacian_smul
    (c : ℝ) (B : Bilin (M := M) I) (x : M) :
    laplacian (I := I) (M := M) (c • B) x =
      c * laplacian (I := I) (M := M) B x := by
  simp only [laplacian, trace]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (c • B x) ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) i) =
    c * B x ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) i)
  simp [LinearMap.smul_apply]

/-- $(\Delta_g B(x))^2 \le n \cdot \operatorname{frobeniusSq} B(x)$, the
Cauchy-Schwarz bound used downstream of the Bochner identity. -/
theorem laplacian_sq_le_dim_mul_frobeniusSq
    (B : Bilin (M := M) I) (x : M) :
    (laplacian (I := I) (M := M) B x)^2 ≤
      (Module.finrank ℝ E : ℝ) * frobeniusSq (I := I) (M := M) B x := by
  simpa [laplacian] using trace_sq_le_dim_mul_frobeniusSq (I := I) (M := M) B x

/-! ## Function Laplacian

The **scalar Laplacian** $\Delta_g f$ of a smooth function $f : M \to \mathbb{R}$,
as the trace of the Hessian. Used in the Bochner identity. -/

variable [IsLocallyConstantChartedSpace H M]

/-- The **scalar Laplacian** $\Delta_g f(x)$ of a smooth function
$f : M \to \mathbb{R}$ at $x$: the trace of the Hessian over the
canonical basis of $E$. -/
noncomputable def scalarLaplacian (f : M → ℝ) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    hessian (I := I) (M := M) f
      (fun (_ : M) => ((Module.finBasis ℝ E) i : TangentSpace I x))
      (fun (_ : M) => ((Module.finBasis ℝ E) i : TangentSpace I x))
      x

/-- The scalar Laplacian `Δ_g[I] f : M → ℝ` ($= \mathrm{tr}_g(\mathrm{Hess}\,f)$).
`I` is bracketed because `f : M → ℝ` does not expose the model with corners. -/
scoped[Riemannian] notation:max "Δ_g[" I "] " f:max =>
  Operators.scalarLaplacian (I := I) f

end Operators
end Riemannian
