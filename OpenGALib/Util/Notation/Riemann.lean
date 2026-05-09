import OpenGALib.Riemannian.Connection.Bianchi

/-!
# Riemannian notation — Riemann curvature tier

Single notation declaration: `Riem(X, Y) Z` for the Riemann curvature
operator. Lives in its own dep tier (post-Bianchi, pre-Curvature)
because:

  * `riemannCurvature` is defined in `Connection/Bianchi.lean`, so
    this notation file must import Bianchi.
  * `Curvature.lean` (which defines `ricci`, `scalarCurvature`) needs
    `Riem(X, Y) Z` to state `riemannCurvature_antisymm`, so the
    notation must be importable BY `Curvature.lean` — which requires
    the notation file to live strictly upstream of `Curvature.lean`.

The "post-curvature" notations (`Ric`, `scal_g`, `II`, `H_g`, `grad_g`)
live in `Util/Notation/Curvature.lean`, which imports `Curvature.lean`
and thus cannot be imported back into it.

`scoped` to `Riemannian`. Activate via `open scoped Riemannian`.
-/

namespace Riemannian

/-- The Riemann curvature $R(X, Y) Z$ as a section. Pointwise:
$(Riem(X, Y) Z)(x) = R(X, Y) Z(x) = $ `riemannCurvature X Y Z x`. -/
scoped notation:max "Riem(" X ", " Y ") " Z:max => riemannCurvature X Y Z

end Riemannian
