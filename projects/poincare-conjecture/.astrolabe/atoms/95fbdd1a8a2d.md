---
chapter: 14
generator: tools/poincare_tex_extract.py
label: spacetime
labels:
- spacetime
mtref: '14.2'
ref:
- 95fbdd1a8a2d
sort: definition
source: tex
src: morgan-tian
tex_file: surgery
---
A *surgery space-time* is a
space-time ${\mathcal M}$ equipped with a maximal atlas of charts
covering ${\mathcal M}$, each chart being of one of the three types
listed above, with the overlap functions being diffeomorphisms
preserving the functions $\mathbf{t}$ and the vector fields $\chi$. The
points with neighborhoods of the first type are called *smooth
points*, those with neighborhoods of the second type but not the
first type are called *exposed points*,
and all the other points are called *singular
points*. Notice that the union of
the set of smooth points and the set of exposed points forms a
smooth manifold with boundary (possibly disconnected). Each
component of the boundary of this manifold is contained in a single
time-slice. The union of those components contained in a time
distinct from the initial time and the final time is called the *exposed region*. and the boundary points of
the closure of the exposed region form the set of the singular
points of ${\mathcal M}$. (Technically, the exposed points are
singular, but we reserve this word for the most singular points.) An
$(n+1)$-dimensional surgery space-time is by definition of
homogeneous dimension $n+1$.

By construction, the local smooth functions $\mathbf{t}$ are compatible
on the overlaps and hence fit together to define a global smooth
function $\mathbf{t}\colon {\mathcal M}\to \Ar$, called the *time*
function. The level sets of this function are called the *time-slices* of the space-time, and $\mathbf{t}^{-1}(t)$ is denoted
$M_t$. Similarly, the tangent bundles of the various charts are
compatible under the overlap diffeomorphisms and hence glue together
to give a global smooth tangent bundle on space-time. The smooth
sections of this vector bundle, the smooth vector fields on space
time, act as derivations on the smooth functions on space-time. The
tangent bundle of an $(n+1)$-dimensional surgery space-time is a
vector bundle of dimension $(n+1)$. Also, by construction the local
vector fields $\chi$ are compatible and hence glue together to
define a global vector field, denoted $\chi$. The vector field and
time function satisfy

$$
\chi(\mathbf{t})=1.
$$

At the manifold points (including the exposed points) it is a usual
vector field. Along the exposed region and the initial time-slice
the vector field points into the manifold; along the final
time-slice it points out of the manifold.
