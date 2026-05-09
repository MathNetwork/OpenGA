import OpenGALib.Riemannian.Curvature
import OpenGALib.Riemannian.Gradient
import OpenGALib.Riemannian.SecondFundamentalForm

/-!
# Riemannian notation — post-Curvature tier

Notations for quantities defined in `Curvature.lean`, `Gradient.lean`,
`SecondFundamentalForm.lean`. This file imports those math files and
must therefore NOT be imported back by them — it sits strictly
downstream of the curvature math layer.

  * `Ric(X, Y)`    — `ricci X Y` as a section
  * `scal_g`       — `scalarCurvature` (function $M \to \mathbb{R}$)
  * `II(X, Y)`     — `secondFundamentalFormScalar X Y` (codim-1)
  * `H_g`          — `meanCurvature` (function $M \to \mathbb{R}$)
  * `grad_g f`     — `manifoldGradient f` as a section

The Riemann curvature notation `Riem(X, Y) Z` lives in
`Util/Notation/Riemann.lean` (post-Bianchi, pre-Curvature) so that
`Curvature.lean` itself can use it.

All `scoped` to `Riemannian`. Eta-reduced for simp-friendly elaboration.

**Ground truth**: do Carmo 1992 §4 (Ricci), §6.2 (second fundamental
form, mean curvature).
-/

namespace Riemannian

/-- The Ricci curvature $\mathrm{Ric}(X, Y)$ as a scalar function on
the manifold: $(Ric(X, Y))(x) = $ `ricci X Y x`. -/
scoped notation:max "Ric(" X ", " Y ")" => ricci X Y

/-- The scalar curvature $\mathrm{scal}_g : M \to \mathbb{R}$. -/
scoped notation "scal_g" => scalarCurvature

/-- The codim-1 second fundamental form scalar $\mathrm{II}(X, Y) :
M \to \mathbb{R}$. -/
scoped notation:max "II(" X ", " Y ")" => secondFundamentalFormScalar X Y

/-- The mean curvature $H_g : M \to \mathbb{R}$. -/
scoped notation "H_g" => meanCurvature

/-- The manifold gradient $\mathrm{grad}_g f$ as a section
$x \mapsto \nabla^M f(x)$. -/
scoped notation:max "grad_g " f:max => manifoldGradient f

end Riemannian
