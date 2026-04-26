import AltRegularity.Basic

/-!
# AltRegularity.Regularity.ChordBeatsArc

The plane-trigonometric inequality at the heart of Section 7 Step 1 of the
paper (`paper/chapters/part2/6-regularity.tex`, line 38):

> "In each two-dimensional cross-section normal to $L$, the two half-lines
> $P_j^+ \cap \partial B_r$ and $P_{j+1}^+ \cap \partial B_r$ have total
> length $2r$, while the chord connecting their endpoints has length
> $2r\sin(\theta_j/2) < 2r$."

This file isolates the inequality $2r \sin(\theta/2) < 2r$ for
$0 < \theta < \pi$ as a self-contained, fully formalized real-trigonometric
fact. The chord-beats-arc surgery in the paper invokes this inequality in
each 2D cross-section normal to the edge $L$ where the two adjacent
half-hyperplanes meet at angle $\theta_j \in (0, 2\pi/N] \subset (0, \pi)$.
-/

namespace AltRegularity

namespace Regularity

/-- **Strict bound on `sin` on $(0, \pi/2)$.** For $0 < x < \pi/2$,
$\sin x < 1$. The strict inequality follows from $\cos x > 0$ on this
interval combined with $\sin^2 x + \cos^2 x = 1$. -/
theorem sin_lt_one_of_pos_of_lt_pi_div_two
    {x : ℝ} (hpos : 0 < x) (hlt : x < Real.pi / 2) :
    Real.sin x < 1 := by
  -- $\cos x > 0$ on $(-\pi/2, \pi/2)$.
  have hcos_pos : 0 < Real.cos x := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos]
    · exact hlt
  -- From $\sin^2 + \cos^2 = 1$ and $\cos x > 0$, deduce $\sin x < 1$.
  nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_le_one x, sq_nonneg (Real.cos x)]

/-- **Chord beats arc (Section 7 Step 1, paper line 38).**

For any radius $r > 0$ and any angle $\theta \in (0, \pi)$, the chord of
length $2r \sin(\theta/2)$ connecting the two endpoints of two unit radii
at angular separation $\theta$ on a circle of radius $r$ is strictly
shorter than the sum $2r$ of the two radii.

This is the **exact inequality** stated in
`paper/chapters/part2/6-regularity.tex` line 38, providing the strict
area saving of the chord-beats-arc surgery in each 2D cross-section
normal to the singular edge $L$. -/
theorem chord_lt_arc (r θ : ℝ) (hr : 0 < r) (hpos : 0 < θ) (hltπ : θ < Real.pi) :
    2 * r * Real.sin (θ / 2) < 2 * r := by
  -- $\theta/2 \in (0, \pi/2)$, hence $\sin(\theta/2) < 1$.
  have h_sin_lt : Real.sin (θ / 2) < 1 :=
    sin_lt_one_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  -- Multiply by $2r > 0$ (strict).
  nlinarith

/-- The angle bound from the pigeonhole on $N \ge 3$ half-hyperplanes:
the smallest gap satisfies $\theta_j \le 2\pi/N$, which is $< \pi$ for
$N \ge 3$. -/
theorem angle_gap_lt_pi {N : ℕ} (hN : 3 ≤ N) :
    (2 * Real.pi) / (N : ℝ) < Real.pi := by
  have hN_ge_three : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN_pos : (0 : ℝ) < N := by linarith
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [div_lt_iff₀ hN_pos]
  nlinarith

/-- **Pigeonhole + chord-beats-arc combined.** From $N \ge 3$ half-hyperplanes
meeting at the singular edge with at least one adjacent pair at angle
$\theta \in (0, 2\pi/N]$, the chord on the unit sphere has strictly less
length than the two radii. This is the precise content of Section 7
Step 1's "$\theta_j \le 2\pi/N < \pi$" combined with the chord inequality. -/
theorem chord_lt_arc_of_pigeonhole
    {N : ℕ} (hN : 3 ≤ N) (r θ : ℝ) (hr : 0 < r)
    (hpos : 0 < θ) (hangle : θ ≤ 2 * Real.pi / N) :
    2 * r * Real.sin (θ / 2) < 2 * r := by
  have h_θ_lt_pi : θ < Real.pi := lt_of_le_of_lt hangle (angle_gap_lt_pi hN)
  exact chord_lt_arc r θ hr hpos h_θ_lt_pi

end Regularity

end AltRegularity
