import Riemannian.Foundations.HessianLie.Flat
import Riemannian.Foundations.HessianLie.ChartHelpers
import Riemannian.Foundations.HessianLie.Manifold

/-!
# Scalar Hessian–Lie identity (facade)

The fundamental algebraic property of the Lie bracket as a derivation
on `C^∞(M, ℝ)`:

  $$X(Y(f))(x) - Y(X(f))(x) = [X, Y](f)(x).$$

## Module organisation

* **`Flat.lean`** — flat (`E_M = E`) version on a normed space, in two
  forms: `flat_hessianLie_apply` (univ) and `flat_hessianLieWithin_apply`
  (Within a unique-diff set). The latter is what chart-pullback consumes
  on `s = range I`.

* **`ChartHelpers.lean`** — three chart-bridge lemmas connecting manifold
  `mfderiv` to flat `fderivWithin (range I)`:
  - `mfderiv_extChartAt_eq_id_eventually` (Helper #1)
  - `mfderiv_chart_compose_apply` (Helper #2)
  - `mfderivWithin_extChartAt_symm_eq_id_eventually` (Helper #3)

* **`Manifold.lean`** — manifold version `mfderiv_iterate_sub_eq_mlieBracket_apply`,
  using the chart helpers + `flat_hessianLieWithin_apply` to lift from
  the chart-pulled-back identity to a manifold equation. Also exports
  `mDirDeriv` (an `F`-typed `@[reducible]` wrapper for `mfderiv`) and
  bridge lemmas reusable elsewhere.

## Used by

  * `Riemannian.Curvature` — `riemannCurvature_inner_diagonal_zero`
    (skew-symmetry of Riemann endomorphism), feeding `ricci_symm` via
    `bianchi_first` (`Riemannian.Connection.Bianchi`).

**Ground truth**: do Carmo 1992 §0 Lemma 5.2; Lee 2013 *Smooth Manifolds*
Proposition 8.30. -/
