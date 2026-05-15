import OpenGALib.Comparison.BishopGromov.VolumeComparison

/-!
# Bishop–Gromov volume comparison — concept folder

The north-star theorem of Layer 3b comparison geometry. See
`Comparison/BishopGromov/VolumeComparison.lean` for the headline
statement (currently a sorry'd PRE-PAPER north-star) and the layered
repair plan.

Sibling files (pending) will house the supporting infrastructure as the
proof develops:

* `Comparison/BishopGromov/Util/SpaceFormGeometry.lean` — derivatives and
  identities for `snakeFunction`, derivative-quotient lemmas
  `s_K' / s_K`, integration-by-parts setup for the antitone argument.
* `Comparison/BishopGromov/RiccatiComparison.lean` — Riccati comparison
  inequality `u' + u^2/(n-1) ≤ -K ⟹ u ≤ (n-1) s_K'/s_K` (Petersen
  Lemma 27.1).
* `Comparison/BishopGromov/LaplacianComparison.lean` — pointwise
  `Δ_g r ≤ (n-1) s_K'(r)/s_K(r)` on `M ∖ Cut(p)` (do Carmo Ch.10 §1
  Thm 1.4).
-/
