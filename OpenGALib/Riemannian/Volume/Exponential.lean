/-!
# Exponential-map bridge: `vol_g|_U = exp_{p,*}(det(d exp_p) · dx)`

Phase 4 of the `riemannian-volume` Layer 3a sub-project: identification of
the local Riemannian volume measure around `p ∈ M` with the pushforward
under the exponential map of `det(d exp_p) · Lebesgue|_{T_pM}`.

Mathematically:
For a Riemannian manifold `(M, g)`, a base point `p ∈ M`, and a normal
neighborhood `U ⊆ M` (image of an open star-shaped neighborhood
`V ⊆ T_pM` of `0_p` under `exp_p : T_pM → M`):

  `vol_g|_U = (exp_p)_* (det(d exp_p) · Lebesgue|_V)`

where `Lebesgue|_V` is the Lebesgue measure on `T_pM` (a real inner-product
space of dimension `n_M`) and `det(d exp_p)` is the Jacobian of the
exponential map at each `v ∈ V` (a positive smooth function on `V`).

**Significance for comparison geometry.** This is the bridge that
expresses `vol_g` in terms of Jacobi fields. Concretely, in polar
coordinates `(t, ξ) ∈ ℝ_{>0} × S^{n-1} ⊂ T_pM`, the Jacobian factors as

  `det(d exp_p(t·ξ)) = t^{n-1} · J_ξ(t)`

where `J_ξ(t)` is the determinant of the (n-1)-Jacobi-field matrix along
the geodesic `γ_ξ(t) = exp_p(t·ξ)`. The Bishop–Gromov / Rauch / Cheeger–
Colding chain of comparison theorems all live on this bridge: comparing
`J_ξ(t)` (the manifold Jacobi field) with `s_K(t)^{n-1}` (the space-form
Jacobi field) is exactly the Riccati / Hessian comparison step.

Ground truth:
* do Carmo, *Riemannian Geometry*, Ch. 10 §1 Proposition 1.1 (Jacobian of
  the exponential map).
* Petersen, *Riemannian Geometry*, Ch. 6 §3 (Jacobi-field volume element).
* Sakai, *Riemannian Geometry*, §III.4.
* Chavel, *Riemannian Geometry: A Modern Introduction*, §III.1.
* Cheeger–Ebin, *Comparison Theorems in Riemannian Geometry*, §1.4
  (Bishop comparison entry point).

## Status — Mathlib gap

This file is **declaration-empty** in Phase 4 of the
`riemannian-volume` branch.

Mathlib provides the *metric-side* exponential via `riemannianEDist`
(infimum of `C^1`-path lengths, `Mathlib.Geometry.Manifold.Riemannian.
PathELength`), but the *smooth-side* exponential map
`Riemannian.expMap : (p : M) → TangentSpace I p → M` (defined via geodesic
ODE flow, smooth on a normal neighborhood, with `d exp_p(0) = id` and
`det(d exp_p) > 0` near `0_p`) is **not yet in Mathlib**. Building it
needs the geodesic equation `∇_{γ'} γ' = 0` integrated to second order
as an ODE in a chart, plus a Picard–Lindelöf-style local existence /
uniqueness / smoothness argument. Estimated 600-1000 LOC of new
Mathlib-style infrastructure if framework self-built.

**Phase 4 deferred until either**:
* Mathlib upstream lands `Riemannian.expMap` and the Jacobian smoothness
  lemmas (possible via Sébastien Gouëzel's ongoing Riemannian geometry
  push in `Mathlib.Geometry.Manifold.Riemannian.*`), or
* OpenGA Layer 3a builds `Riemannian/Exp.lean` as a framework self-build
  on top of `riemannianEDist` + chart-pullback ODE.

**Theorem skeleton (to be declared in follow-up commit):**

```lean
theorem volumeMeasure_eq_pushforward_expMap
    (g : RiemannianMetric I M) (p : M) (V : Set (TangentSpace I p))
    (hV : IsOpen V) (hV_inj : InjOn (Riemannian.expMap g p) V) :
    volumeMeasure g (Riemannian.expMap g p '' V) =
      (Riemannian.expMap g p).map (... |det(d expMap_p)| · Lebesgue|_V)
```

with two further companion lemmas:
* `Riemannian.det_dExpMap_pos`: Jacobian positivity near `0_p`
* `Riemannian.det_dExpMap_jacobiField_decomp`: polar-coordinate
  decomposition `det(d exp_p(t·ξ)) = t^{n-1} · J_ξ(t)`

The latter is what feeds the Riccati comparison in Bishop–Gromov's
proper proof.

## Downstream consumers

When Phase 4 lands, the following proofs can target real proofs (not
sorry'd) at OpenGA Comparison layer:

* `Comparison/BishopGromov/RiccatiComparison.lean` — Petersen Lemma 27.1
* `Comparison/BishopGromov/LaplacianComparison.lean` — do Carmo Ch.10 §1
  Thm 1.4
* `Comparison/BishopGromov/VolumeComparison.lean` — closes the headline
  `bishopGromov_volume_comparison` sorry.

Plus Cheeger–Colding splitting, Toponogov comparison, Rauch comparison,
and the broader Layer 3b machinery.
-/

-- (no declarations; placeholder for the future exp-pullback infrastructure)
