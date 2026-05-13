import OpenGALib.Tensor.Alternating.Basis
import OpenGALib.Tensor.Alternating.Bundle
import OpenGALib.Tensor.Alternating.Comp
import OpenGALib.Tensor.Alternating.Congr
import OpenGALib.Tensor.Alternating.Curry
import OpenGALib.Tensor.Alternating.FDeriv
import OpenGALib.Tensor.Alternating.Flip
import OpenGALib.Tensor.Alternating.Wedge
import OpenGALib.Tensor.DifferentialForm.Basic
import OpenGALib.Tensor.DifferentialForm.Congr
import OpenGALib.Tensor.DifferentialForm.Defs
import OpenGALib.Tensor.DifferentialForm.Rough
import OpenGALib.Tensor.Multilinear.Basis
import OpenGALib.Tensor.Multilinear.Bundle
import OpenGALib.Tensor.Multilinear.Comp
import OpenGALib.Tensor.Multilinear.Curry
import OpenGALib.Tensor.Multilinear.Fiber
import OpenGALib.Tensor.Multilinear.Field
import OpenGALib.Tensor.Multilinear.Flip
import OpenGALib.Tensor.Product.Basis
import OpenGALib.Tensor.Product.Bundle
import OpenGALib.Tensor.Product.Defs
import OpenGALib.Tensor.Product.Fiber
import OpenGALib.Tensor.Product.HomEquiv
import OpenGALib.Tensor.Product.Pretrivialization
import OpenGALib.Tensor.Product.Section

/-!
# Tensor — vector-bundle algebra

Tensor algebra over arbitrary `C^n` vector bundles: continuous multilinear
maps, alternating forms, tensor products, differential forms.

Independent of `OpenGALib/Riemannian/`. Riemannian specialisations (lower
indices via metric, inner product on `(r,s)`-sections) live under
`Riemannian/Tensor/` and consume this layer.

```
Algebraic/Auxiliary  ←  Tensor/Multilinear  ←  Tensor/Alternating
                                            ←  Tensor/Product
                                            ←  Tensor/DifferentialForm
```
-/
