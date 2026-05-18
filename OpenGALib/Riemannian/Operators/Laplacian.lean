import OpenGALib.Riemannian.Operators.Hessian
import Mathlib.Analysis.InnerProductSpace.PiL2
import OpenGALib.Riemannian.Util.CovDerivBridges

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
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [hm : HasMetric I M]

/-- **Math.** The **Laplace–Beltrami operator** $\Delta_g$ acting on a
pointwise Hessian bilinear form $B$:
$$\Delta_g B(x) = \sum_i B(x)(e_i, e_i).$$ -/
noncomputable def laplacian
    (B : Bilin (M := M) I) (x : M) : ℝ :=
  trace B x

@[simp] lemma laplacian_def
    (B : Bilin (M := M) I) (x : M) :
    laplacian (I := I) (M := M) B x = trace B x := rfl

/-- **Math.** $\Delta_g (B + C) = \Delta_g B + \Delta_g C$. -/
theorem laplacian_add
    (B C : Bilin (M := M) I) (x : M) :
    laplacian (I := I) (M := M) (B + C) x =
      laplacian (I := I) (M := M) B x + laplacian (I := I) (M := M) C x := by
  simp only [laplacian, trace_def]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (B x + C x) _ _ = B x _ _ + C x _ _
  rfl

/-- **Math.** $\Delta_g (c \cdot B) = c \cdot \Delta_g B$. -/
theorem laplacian_smul
    (c : ℝ) (B : Bilin (M := M) I) (x : M) :
    laplacian (I := I) (M := M) (c • B) x =
      c * laplacian (I := I) (M := M) B x := by
  simp only [laplacian, trace_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (c • B x) _ _ = c * B x _ _
  simp [LinearMap.smul_apply]

/-- **Math.** $(\Delta_g B(x))^2 \le n \cdot \operatorname{frobeniusSq} B(x)$,
the Cauchy-Schwarz bound used downstream of the Bochner identity. -/
theorem laplacian_sq_le_dim_mul_frobeniusSq
    (B : Bilin (M := M) I) (x : M) :
    (laplacian (I := I) (M := M) B x)^2 ≤
      (Module.finrank ℝ E : ℝ) * frobeniusSq (I := I) (M := M) B x := by
  simpa [laplacian] using trace_sq_le_dim_mul_frobeniusSq (I := I) (M := M) B x

/-! ## Function Laplacian

The **scalar Laplacian** $\Delta_g f$ of a smooth function $f : M \to \mathbb{R}$,
as the trace of the Hessian. Used in the Bochner identity. -/

variable [IsLocallyConstantChartedSpace H M]

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** The **scalar Laplacian** $\Delta_g f(x)$ of a smooth function
$f : M \to \mathbb{R}$ at $x$, the geometric trace of the Hessian:
$\Delta_g f(x) = \sum_i \operatorname{Hess} f(x)(\varepsilon_i, \varepsilon_i)$
in the $g$-orthonormal frame `stdOrthonormalBasis`. Basis-independent. -/
noncomputable def scalarLaplacian (g : RiemannianMetric I M) (f : M → ℝ) (x : M) : ℝ :=
  let e : OrthonormalBasis _ ℝ (TangentSpace I x) :=
    stdOrthonormalBasis ℝ (TangentSpace I x)
  ∑ i, hessian (I := I) (M := M) g f
    (fun (_ : M) => (e i : TangentSpace I x))
    (fun (_ : M) => (e i : TangentSpace I x))
    x


/-- **Math.** **Scalar Laplacian as Bilin-trace of the Hessian section.**
Both unfold to $\sum_i \langle \nabla_{\varepsilon_i} \nabla f,\,
\varepsilon_i\rangle_g$ in the same $g$-orthonormal frame
`stdOrthonormalBasis`. -/
theorem scalarLaplacian_eq_laplacian_hessianBilin
    (g : RiemannianMetric I M) (f : M → ℝ) (x : M) :
    scalarLaplacian (I := I) g f x =
      laplacian (I := I) (M := M) (hessianBilin (I := I) g f) x := by
  unfold scalarLaplacian
  simp only [laplacian, trace_def, hessian, hessianBilin, LinearMap.mk₂_apply,
             covDeriv_const_eq_covDerivAt]

end Operators
end Riemannian
