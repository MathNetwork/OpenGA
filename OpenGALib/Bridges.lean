import OpenGALib.Bridges.RiemannianToLength

/-!
# OpenGA Bridges (Layer 5)

Bridge instances connecting OpenGA's Layer 1 metric-side primitives with the
Riemannian (Layer 3a) and synthetic-curvature (Layer 2) layers. Each bridge
records a mathematical theorem of the form "every X is a Y" as a typeclass
instance, so that the synthesis lattice automatically transports
length-space / metric-measure structure across the layer boundaries.

Current bridges:
* `Bridges/RiemannianToLength.lean` — every `IsRiemannianManifold I M` is a
  `LengthSpace M`.
-/
