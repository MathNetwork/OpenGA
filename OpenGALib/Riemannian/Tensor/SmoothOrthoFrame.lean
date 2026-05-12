import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import OpenGALib.Riemannian.Metric
import OpenGALib.Riemannian.TangentBundle

/-!
# Smooth orthonormal local frame from the chart frame

For a smooth Riemannian manifold $(M, g)$ and a base point $\alpha : M$,
this file constructs:

* `chartBasisVecFiber α i b` — the $i$-th tangent vector at $b$ obtained
  by transporting the $i$-th model-space basis vector through the inverse
  of the tangent trivialization centred at $\alpha$ (smooth on the
  trivialization base set, junk off it);
* `chartFrameNormFiber g α b i` — the fiberwise $g$-Gram-Schmidt
  orthonormalisation of the chart-basis family
  `chartBasisVecFiber α · b`, by well-founded recursion on `i.val`;
* `smoothOrthoFrame g α i` — a globally-smooth tangent-bundle section,
  obtained by multiplying `chartFrameNorm g α i` by a smooth bump
  function `chartBumpAt α` whose support lies in the chart source.

The output `smoothOrthoFrame g α i` is identically zero off the chart
source and equals the un-bumped Gram-Schmidt frame on the smaller
neighbourhood `smoothOrthoFrameNbhd α` where `chartBumpAt α = 1`.

Downstream consumer: heart-of-Bochner sum identity, where the smooth
orthonormal frame plays the role of the basis along which the trace
of $\nabla^2(\nabla f)$ is identified with $\Delta_g f$.

## Sub-phase scope (Phase A.2)

This file ports Stages 1–2 of
`external/differential-geometry/.../RicciIdentitySmoothFrame.lean`:
the construction itself plus the `smoothOrthoFrameNbhd` set and basic
membership facts. Orthonormality at base-set points (Stage 3) and
smoothness of the global section (Stage 6) are deferred to follow-up
sub-phases — they are mechanical strong-induction proofs over `i.val`
totalling several hundred LOC each.

**Ground truth**: external's `smoothOrthoFrame` construction; do Carmo
§1 (chart-frame trivialization); Lee §3 (smooth bump functions);
Petersen §1 (Gram-Schmidt on a Riemannian frame).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set FiberBundle Filter
open scoped Manifold Topology ContDiff Bundle

namespace Riemannian
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Stage 1: chart-basis tangent sections -/

/-- The $i$-th pointwise tangent vector of the chart-local frame attached
to $\alpha$. For $b$ in the trivialization base set, this is the image
of the $i$-th model-space basis vector under
`(trivializationAt E (TangentSpace I) α).symm b`; off that set it is a
default (junk) value still well-typed in the fiber.

Smooth on `(trivializationAt E (TangentSpace I) α).baseSet` (=
`(chartAt H α).source`); see `chartBasisVec_contMDiffOn`. -/
def chartBasisVecFiber (α : M) (i : Fin (Module.finrank ℝ E)) (b : M) :
    TangentSpace I b :=
  (trivializationAt E (TangentSpace I) α).symm b ((Module.finBasis ℝ E) i)

/-- The $i$-th tangent-bundle section form of the chart-local frame
attached to $\alpha$, packaged as a function `M → TotalSpace E _`.
Smooth on the trivialization base set. -/
def chartBasisVec (α : M) (i : Fin (Module.finrank ℝ E)) :
    M → TotalSpace E (TangentSpace I : M → Type _) :=
  fun b => TotalSpace.mk' E b (chartBasisVecFiber (I := I) α i b)

@[simp] lemma chartBasisVec_proj
    (α : M) (i : Fin (Module.finrank ℝ E)) (b : M) :
    (chartBasisVec (I := I) α i b).proj = b := rfl

@[simp] lemma chartBasisVec_snd
    (α : M) (i : Fin (Module.finrank ℝ E)) (b : M) :
    (chartBasisVec (I := I) α i b).2 = chartBasisVecFiber (I := I) α i b := rfl

/-- On the base set of the trivialization at $\alpha$, applying the
trivialization to the chart-basis vector recovers the constant
model-basis vector. -/
lemma trivializationAt_chartBasisVec_snd
    (α : M) (i : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (trivializationAt E (TangentSpace I) α
        ⟨b, chartBasisVecFiber (I := I) α i b⟩).2
      = (Module.finBasis ℝ E) i := by
  have h := (trivializationAt E (TangentSpace I) α).apply_mk_symm hb
    ((Module.finBasis ℝ E) i)
  simpa [chartBasisVecFiber] using congrArg Prod.snd h

/-- The chart-basis tangent-bundle section is smooth on the base set of
the trivialization at $\alpha$. -/
lemma chartBasisVec_contMDiffOn
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (chartBasisVec (I := I) α i)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hiff :=
    ((trivializationAt E (TangentSpace I) α)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞) (s := fun b => chartBasisVecFiber (I := I) α i b)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun _ : M => (Module.finBasis ℝ E) i)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    contMDiffOn_const
  refine hconst.congr ?_
  intro b hb
  exact (trivializationAt_chartBasisVec_snd (I := I) α i hb)

/-- The chart-basis family at a point $b \in \mathrm{baseSet}$ is a
basis of `TangentSpace I b`, obtained by transporting the fixed
model-space basis through the continuous linear equivalence given by
the trivialization. -/
def chartBasisFamily (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I b) :=
  (Module.finBasis ℝ E).map
    (ContinuousLinearEquiv.toLinearEquiv
      ((trivializationAt E (TangentSpace I) α).continuousLinearEquivAt ℝ b hb).symm)

lemma chartBasisFamily_apply (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisFamily (I := I) α hb i =
      chartBasisVecFiber (I := I) α i b := by
  unfold chartBasisFamily chartBasisVecFiber
  rw [Module.Basis.map_apply]
  rfl

/-- The chart-basis family is linearly independent at each base-set
point. -/
lemma chartBasisFamily_linearIndependent (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        chartBasisVecFiber (I := I) α i b) := by
  have h := (chartBasisFamily (I := I) α hb).linearIndependent
  have hcongr :
      (chartBasisFamily (I := I) α hb : Fin (Module.finrank ℝ E) → TangentSpace I b)
        = fun i => chartBasisVecFiber (I := I) α i b := by
    funext i
    exact chartBasisFamily_apply (I := I) α hb i
  rw [← hcongr]
  exact h

/-! ## Stage 2: hand-rolled $g$-Gram-Schmidt of the chart frame, fiberwise

For a fixed point $b : M$, we recursively build the orthonormalised
basis `chartFrameNormFiber g α b i ∈ T_bM`, with
$i : \mathrm{Fin}\,(\mathrm{Module.finrank}\,\mathbb{R}\,E)$.

The recursion uses Lean's well-founded recursion on `i.val`: each step
references earlier fiber-values, and termination is by strict decrease
of the index. -/

/-- The normalised Gram-Schmidt vector for the chart frame, in a fixed
fiber $b$. Defined by well-founded recursion on `i.val`. -/
private noncomputable def chartFrameNormFiber
    (g : RiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) : TangentSpace I b :=
  let v : TangentSpace I b := chartBasisVecFiber (I := I) α i b
  let raw : TangentSpace I b :=
    v - ∑ j : Fin i.val,
      (g.inner b v
          (chartFrameNormFiber g α b
            ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
        chartFrameNormFiber g α b
          ⟨j.val, lt_trans j.isLt i.isLt⟩
  (Real.sqrt (g.inner b raw raw))⁻¹ • raw
termination_by i.val
decreasing_by exact j.isLt

/-- The normalised Gram-Schmidt vector for the chart frame as a section
in $b$: `chartFrameNorm g α i b ∈ T_bM`. -/
noncomputable def chartFrameNorm
    (g : RiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (b : M) : TangentSpace I b :=
  chartFrameNormFiber (I := I) g α b i

/-- The unnormalised Gram-Schmidt vector at index $i$, in a fixed fiber
$b$:
$$\mathrm{raw}_i(b) := v_i(b) - \sum_{j < i} \langle v_i(b), e_j(b)\rangle_g \, e_j(b),$$
where $v_i(b) = \mathrm{chartBasisVecFiber}\,\alpha\,i\,b$ and
$e_j(b) = \mathrm{chartFrameNormFiber}\,g\,\alpha\,b\,j$. -/
private noncomputable def chartFrameRawFiber
    (g : RiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) : TangentSpace I b :=
  chartBasisVecFiber (I := I) α i b -
    ∑ j : Fin i.val,
      (g.inner b (chartBasisVecFiber (I := I) α i b)
          (chartFrameNormFiber (I := I) g α b
            ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
        chartFrameNormFiber (I := I) g α b
          ⟨j.val, lt_trans j.isLt i.isLt⟩

/-- Recursive expansion of `chartFrameNormFiber`: at index $i$, the
normalised vector is `(Real.sqrt (g.inner b raw raw))⁻¹ • raw`. -/
private lemma chartFrameNormFiber_eq
    (g : RiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    chartFrameNormFiber (I := I) g α b i =
      (Real.sqrt (g.inner b
          (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i)))⁻¹ •
        chartFrameRawFiber (I := I) g α b i := by
  unfold chartFrameNormFiber chartFrameRawFiber
  rfl

/-- At the zeroth index, the unnormalised Gram-Schmidt vector reduces to
the chart-basis vector itself (the empty sum vanishes). -/
private lemma chartFrameRawFiber_at_zero
    (g : RiemannianMetric I M) (α : M) (b : M) :
    chartFrameRawFiber (I := I) g α b ⟨0, NeZero.pos _⟩ =
      chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b := by
  unfold chartFrameRawFiber
  simp

/-- At the zeroth index, the normalised Gram-Schmidt vector is the
chart-basis vector divided by its $g$-norm. -/
private lemma chartFrameNormFiber_at_zero
    (g : RiemannianMetric I M) (α : M) (b : M) :
    chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩ =
      (Real.sqrt
          (g.inner b
            (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
            (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)))⁻¹ •
        chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b := by
  rw [chartFrameNormFiber_eq, chartFrameRawFiber_at_zero]

/-- Generic normalisation calculation: for a vector $v$ in a fiber
with positive $g$-self-inner-product $N$, scaling $v$ by
$(\sqrt N)^{-1}$ gives a unit-norm vector. Pure CLM/ring algebra in
the inner-product slot; isolated as a helper to keep
`chartFrameNormFiber_at_zero_norm` from re-elaborating CLM types
inside `set`-chains. -/
private lemma g_inner_normalised
    (g : RiemannianMetric I M) (b : M) (v : TangentSpace I b)
    (hpos : 0 < g.inner b v v) :
    g.inner b ((Real.sqrt (g.inner b v v))⁻¹ • v)
              ((Real.sqrt (g.inner b v v))⁻¹ • v) = 1 := by
  set s : ℝ := Real.sqrt (g.inner b v v) with hs_def
  have hs_sq : s * s = g.inner b v v := Real.mul_self_sqrt hpos.le
  -- Bilinearity of `g.inner b`: pull `s⁻¹` out of each slot via `map_smul`
  -- on the appropriate CLM. The first-slot pull yields a CLM equality
  -- (smul of CLMs); evaluating at `s⁻¹ • v` then re-applies smul to extract
  -- the second factor. Final shape: `s⁻¹ * (s⁻¹ * g.inner b v v)`.
  have h_left : g.inner b (s⁻¹ • v) = s⁻¹ • g.inner b v := map_smul _ _ _
  have h_right : g.inner b v (s⁻¹ • v) = s⁻¹ * g.inner b v v := by
    rw [map_smul]; rfl
  calc g.inner b (s⁻¹ • v) (s⁻¹ • v)
      = (s⁻¹ • g.inner b v) (s⁻¹ • v) := by rw [h_left]
    _ = s⁻¹ * g.inner b v (s⁻¹ • v) := by
        rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    _ = s⁻¹ * (s⁻¹ * g.inner b v v) := by rw [h_right]
    _ = (s * s)⁻¹ * g.inner b v v := by rw [mul_inv]; ring
    _ = (g.inner b v v)⁻¹ * g.inner b v v := by rw [hs_sq]
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- At a base-set point and at the zeroth index, the normalised
Gram-Schmidt vector is $g$-unit-norm. -/
lemma chartFrameNormFiber_at_zero_norm
    (g : RiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    g.inner b
        (chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩)
        (chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩) = 1 := by
  rw [chartFrameNormFiber_at_zero]
  have hv_ne :
      chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b ≠ 0 :=
    (chartBasisFamily_linearIndependent (I := I) α hb).ne_zero _
  exact g_inner_normalised (I := I) g b _ (g.pos b _ hv_ne)

/-! ## Stage 3a: orthonormality of the un-bumped Gram-Schmidt frame

The inductive Gram-Schmidt step preserves orthogonality and unit length
on the trivialization base set. The proof is by strong induction on the
index $i.\mathrm{val}$; the bundled IH carries three facts at every
$i$: $\mathrm{raw}_i \ne 0$, $\langle e_j, e_i\rangle = 0$ for $j < i$,
and $\langle e_i, e_i\rangle = 1$.

The non-degeneracy step $\mathrm{raw}_i \ne 0$ uses linear independence
of the chart-basis family (`chartBasisFamily_linearIndependent`) and
the inductive span identity
$e_0, \ldots, e_{i-1} \in \mathrm{span}(v_0, \ldots, v_{i-1})$. -/

/-- Bilinear distribution of `g.inner b u (·)` over a finite sum. -/
private lemma g_inner_sum_right
    (g : RiemannianMetric I M) (b : M) (v : TangentSpace I b)
    {ι : Type*} (s : Finset ι) (w : ι → TangentSpace I b)
    (c : ι → ℝ) :
    g.inner b v (∑ k ∈ s, c k • w k) = ∑ k ∈ s, c k * g.inner b v (w k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has]
    rw [show ((g.inner b) v) (c a • w a + ∑ x ∈ s, c x • w x) =
        ((g.inner b) v) (c a • w a) + ((g.inner b) v) (∑ x ∈ s, c x • w x) from by
      rw [map_add]]
    rw [show ((g.inner b) v) (c a • w a) = c a * ((g.inner b) v) (w a) from by
      rw [map_smul]; rfl]
    rw [ih]

/-- Bilinear distribution of `g.inner b (·) w` over a finite sum. -/
private lemma g_inner_sum_left
    (g : RiemannianMetric I M) (b : M)
    {ι : Type*} (s : Finset ι) (v : ι → TangentSpace I b)
    (c : ι → ℝ) (w : TangentSpace I b) :
    g.inner b (∑ k ∈ s, c k • v k) w = ∑ k ∈ s, c k * g.inner b (v k) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has]
    rw [show ((g.inner b) (c a • v a + ∑ x ∈ s, c x • v x)) =
        ((g.inner b) (c a • v a)) + ((g.inner b) (∑ x ∈ s, c x • v x)) from by
      rw [map_add]]
    rw [ContinuousLinearMap.add_apply]
    rw [show ((g.inner b) (c a • v a)) w = c a * ((g.inner b) (v a)) w from by
      rw [map_smul]; rfl]
    rw [ih]

/-- Generic normalisation: scaling a positive-norm vector by
$(\sqrt{\langle v, v\rangle})^{-1}$ in the **second** slot equals the
analogous left-slot scaling, factored through the same helper. Used
twice (orthogonality + unit-norm) in the strong-induction succ step,
where `v` is `chartFrameRawFiber g α b i`. -/
private lemma g_inner_smul_right_normalised
    (g : RiemannianMetric I M) (b : M) (v u : TangentSpace I b) (s : ℝ) :
    g.inner b u (s⁻¹ • v) = s⁻¹ * g.inner b u v := by
  rw [map_smul]; rfl

set_option maxHeartbeats 800000 in
/-- The strong-induction package for the orthonormality of
`chartFrameNormFiber`. The conclusion bundles three facts at every
$i \le k$:

1. $\mathrm{chartFrameRawFiber}\,g\,\alpha\,b\,i \ne 0$;
2. for all $j < i$, $\langle e_j, e_i\rangle_g = 0$;
3. $\langle e_i, e_i\rangle_g = 1$.

We package them together to thread the strong-induction hypothesis
cleanly. -/
private theorem chartFrameNormFiber_orth_strong_aux
    (g : RiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∀ k : ℕ, ∀ i : Fin (Module.finrank ℝ E), i.val ≤ k →
      chartFrameRawFiber (I := I) g α b i ≠ 0 ∧
      (∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
        g.inner b
            (chartFrameNormFiber (I := I) g α b j)
            (chartFrameNormFiber (I := I) g α b i) = 0) ∧
      g.inner b
          (chartFrameNormFiber (I := I) g α b i)
          (chartFrameNormFiber (I := I) g α b i) = 1 := by
  classical
  have hLI : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        chartBasisVecFiber (I := I) α i b) :=
    chartBasisFamily_linearIndependent (I := I) α hb
  intro k
  induction k with
  | zero =>
    intro i hi_le
    have hi_val : i.val = 0 := Nat.le_zero.mp hi_le
    have hi_eq : i = ⟨0, NeZero.pos _⟩ := Fin.ext hi_val
    subst hi_eq
    refine ⟨?_, ?_, ?_⟩
    · rw [chartFrameRawFiber_at_zero]
      exact hLI.ne_zero ⟨0, NeZero.pos _⟩
    · intro j hj
      simp at hj
    · exact chartFrameNormFiber_at_zero_norm (I := I) g α hb
  | succ k ih =>
    intro i hi_le
    by_cases hi_lt : i.val ≤ k
    · exact ih i hi_lt
    · -- i.val = k + 1
      have ih_below : ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
          chartFrameRawFiber (I := I) g α b j ≠ 0 ∧
          (∀ j' : Fin (Module.finrank ℝ E), j'.val < j.val →
            g.inner b
                (chartFrameNormFiber (I := I) g α b j')
                (chartFrameNormFiber (I := I) g α b j) = 0) ∧
          g.inner b
              (chartFrameNormFiber (I := I) g α b j)
              (chartFrameNormFiber (I := I) g α b j) = 1 := by
        intro j hj
        have hj_le : j.val ≤ k := by omega
        exact ih j hj_le
      -- Step 1: orthogonality of `raw_i` to each `e_j` with `j.val < i.val`.
      -- Bilinear unfold: ⟨e_j, raw_i⟩ = ⟨e_j, v_i⟩ - ∑_{m<i.val} ⟨v_i, e_m⟩ ⟨e_j, e_m⟩.
      -- Only m = j survives (orthonormality of e's by IH); the surviving
      -- term equals ⟨e_j, v_i⟩ by `g.symm`. Net: 0.
      have horth_raw : ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
          g.inner b
              (chartFrameNormFiber (I := I) g α b j)
              (chartFrameRawFiber (I := I) g α b i) = 0 := by
        intro j hj_lt
        -- Local notation for the recurring index-coerced normalised vector.
        set e := fun (j' : Fin i.val) =>
          chartFrameNormFiber (I := I) g α b
            ⟨j'.val, lt_trans j'.isLt i.isLt⟩ with he_def
        set vi := chartBasisVecFiber (I := I) α i b with hvi_def
        set ej := chartFrameNormFiber (I := I) g α b j with hej_def
        -- Coefficient function for the Gram-Schmidt sum.
        set c : Fin i.val → ℝ := fun j' => g.inner b vi (e j') with hc_def
        -- Unfold raw_i to the explicit subtraction form.
        change g.inner b ej (vi - ∑ j' : Fin i.val, c j' • e j') = 0
        rw [show (g.inner b) ej (vi - ∑ j' : Fin i.val, c j' • e j') =
            (g.inner b) ej vi - (g.inner b) ej (∑ j' : Fin i.val, c j' • e j') from
          map_sub _ _ _]
        rw [g_inner_sum_right (I := I) g b ej Finset.univ e c]
        -- The sum: only j' = ⟨j.val, hj_lt⟩ survives (by IH orthonormality of e's).
        set j_inFin : Fin i.val := ⟨j.val, hj_lt⟩ with hj_inFin_def
        have hj_eq_inFin : (⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩ :
            Fin (Module.finrank ℝ E)) = j := Fin.ext rfl
        have hsingleton :
            ∑ j' ∈ (Finset.univ : Finset (Fin i.val)),
                c j' * g.inner b ej (e j') =
              c j_inFin * g.inner b ej (e j_inFin) := by
          refine Finset.sum_eq_single j_inFin ?_ ?_
          · intro j' _ hj'_ne
            -- For j' ≠ j_inFin, j'.val ≠ j.val ⇒ ⟨e_j, e_⟨j'.val,_⟩⟩ = 0.
            have hj'_ne_val : j'.val ≠ j.val := fun h => hj'_ne (Fin.ext h)
            by_cases hcompare : j'.val < j.val
            · -- Use IH on j (size j.val ≤ k): ⟨e_j', e_j⟩ = 0, then symm.
              have hIH_j := ih_below j hj_lt
              have hzero := hIH_j.2.1 ⟨j'.val, lt_trans hcompare j.isLt⟩ hcompare
              have h_symm : g.inner b ej (e j') =
                  g.inner b
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans hcompare j.isLt⟩)
                    ej := by
                show g.inner b ej (chartFrameNormFiber (I := I) g α b
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩) = _
                rw [g.symm]
              rw [h_symm, hzero, mul_zero]
            · -- j.val < j'.val: use IH on ⟨j'.val,_⟩ (size j'.val ≤ k).
              have hcompare_le : j.val ≤ j'.val := Nat.le_of_not_lt hcompare
              have hcompare' : j.val < j'.val :=
                lt_of_le_of_ne hcompare_le hj'_ne_val.symm
              have hj'_in : (⟨j'.val, lt_trans j'.isLt i.isLt⟩ :
                Fin (Module.finrank ℝ E)).val < i.val := j'.isLt
              have hIH_j' := ih_below ⟨j'.val, lt_trans j'.isLt i.isLt⟩ hj'_in
              have hzero := hIH_j'.2.1 j hcompare'
              show c j' * g.inner b ej (chartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩) = 0
              rw [hzero, mul_zero]
          · intro h
            exact absurd (Finset.mem_univ j_inFin) h
        rw [hsingleton]
        -- Now c j_inFin * ⟨e_j, e_j_inFin⟩ = ⟨v_i, e_j⟩ * 1 = ⟨v_i, e_j⟩ = ⟨e_j, v_i⟩.
        have hej_eq : e j_inFin = ej := by
          show chartFrameNormFiber (I := I) g α b
              ⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩ = ej
          rw [hj_eq_inFin]
        rw [hej_eq]
        have hjj_unit : g.inner b ej ej = 1 := (ih_below j hj_lt).2.2
        rw [hjj_unit, mul_one]
        -- Target: g.inner b ej vi - c j_inFin = 0.
        -- c j_inFin = g.inner b vi (e j_inFin) = g.inner b vi ej (by hej_eq).
        -- So target ≡ g.inner b ej vi - g.inner b vi ej = 0, which holds by g.symm.
        have hc_eq : c j_inFin = g.inner b vi ej := by
          show g.inner b vi (e j_inFin) = g.inner b vi ej
          rw [hej_eq]
        rw [hc_eq, g.symm]
        ring
      -- Step 2: `raw_i ≠ 0`. Argument: if raw_i = 0, then v_i is in
      -- span(e_0,…,e_{i-1}); by induction on the recursion, each e_j is
      -- in span(v_0,…,v_j), so v_i ∈ span(v_0,…,v_{i-1}), contradicting LI.
      have hraw_ne : chartFrameRawFiber (I := I) g α b i ≠ 0 := by
        intro hraw_zero
        have hv_eq : chartBasisVecFiber (I := I) α i b =
            ∑ j' : Fin i.val,
              (g.inner b (chartBasisVecFiber (I := I) α i b)
                (chartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                chartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := by
          have h_eq : chartBasisVecFiber (I := I) α i b -
              ∑ j' : Fin i.val,
                (g.inner b (chartBasisVecFiber (I := I) α i b)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                  chartFrameNormFiber (I := I) g α b
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩ = 0 := by
            simpa [chartFrameRawFiber] using hraw_zero
          exact sub_eq_zero.mp h_eq
        -- Each e_m (m.val < i.val) is in span(v_0,…,v_{i-1}) by induction on m.val.
        have h_e_in_span_v : ∀ kk : ℕ, ∀ m : Fin (Module.finrank ℝ E),
            m.val ≤ kk → m.val < i.val →
            chartFrameNormFiber (I := I) g α b m ∈
              Submodule.span ℝ
                ((fun n : Fin i.val =>
                  chartBasisVecFiber (I := I) α
                    ⟨n.val, lt_trans n.isLt i.isLt⟩ b) ''
                  Set.univ) := by
          intro kk
          induction kk with
          | zero =>
            intro m hm_le hm_lt
            have hm_val : m.val = 0 := Nat.le_zero.mp hm_le
            have hm_eq : m = ⟨0, NeZero.pos _⟩ := Fin.ext hm_val
            subst hm_eq
            rw [chartFrameNormFiber_at_zero]
            apply Submodule.smul_mem
            apply Submodule.subset_span
            refine ⟨⟨0, hm_lt⟩, Set.mem_univ _, rfl⟩
          | succ kk ih_kk =>
            intro m hm_le hm_lt
            by_cases hcase : m.val ≤ kk
            · exact ih_kk m hcase hm_lt
            · rw [chartFrameNormFiber_eq]
              apply Submodule.smul_mem
              unfold chartFrameRawFiber
              apply Submodule.sub_mem
              · apply Submodule.subset_span
                exact ⟨⟨m.val, hm_lt⟩, Set.mem_univ _, rfl⟩
              · apply Submodule.sum_mem
                intro j _
                apply Submodule.smul_mem
                have hj_in_fin : j.val < i.val := lt_trans j.isLt hm_lt
                have hj_le_kk : j.val ≤ kk := by
                  have : j.val < m.val := j.isLt
                  omega
                have hj_lt_total : j.val < Module.finrank ℝ E :=
                  lt_trans hj_in_fin i.isLt
                exact ih_kk ⟨j.val, hj_lt_total⟩ hj_le_kk hj_in_fin
        -- v_i is in span(v_0,…,v_{i-1}) by hv_eq + h_e_in_span_v.
        have hvi_in_span : chartBasisVecFiber (I := I) α i b ∈
            Submodule.span ℝ
              ((fun n : Fin i.val =>
                chartBasisVecFiber (I := I) α
                  ⟨n.val, lt_trans n.isLt i.isLt⟩ b) ''
                Set.univ) := by
          rw [hv_eq]
          apply Submodule.sum_mem
          intro j' _
          apply Submodule.smul_mem
          have hj'_lt : j'.val < i.val := j'.isLt
          have hj'_le_k : j'.val ≤ k := by
            have : j'.val < i.val := j'.isLt
            omega
          exact h_e_in_span_v k ⟨j'.val, lt_trans j'.isLt i.isLt⟩ hj'_le_k hj'_lt
        -- Contradiction via `LinearIndependent.notMem_span_image`.
        have hset_eq :
            ((fun n : Fin i.val =>
              chartBasisVecFiber (I := I) α
                ⟨n.val, lt_trans n.isLt i.isLt⟩ b) ''
              Set.univ) =
            ((fun n : Fin (Module.finrank ℝ E) =>
              chartBasisVecFiber (I := I) α n b) ''
              {n : Fin (Module.finrank ℝ E) | n.val < i.val}) := by
          ext v
          constructor
          · rintro ⟨n, _, rfl⟩
            refine ⟨⟨n.val, lt_trans n.isLt i.isLt⟩, n.isLt, rfl⟩
          · rintro ⟨n, hn, rfl⟩
            refine ⟨⟨n.val, hn⟩, Set.mem_univ _, rfl⟩
        rw [hset_eq] at hvi_in_span
        have hi_notin : i ∉ {n : Fin (Module.finrank ℝ E) | n.val < i.val} := by
          simp [Set.mem_setOf_eq]
        exact hLI.notMem_span_image hi_notin hvi_in_span
      -- Step 3: orthogonality and unit norm of e_i = (1/sqrt N) • raw_i.
      have hgpos : 0 < g.inner b
          (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i) :=
        g.pos b (chartFrameRawFiber (I := I) g α b i) hraw_ne
      refine ⟨hraw_ne, ?_, ?_⟩
      · -- Orthogonality: ⟨e_j, e_i⟩ = (1/√N) ⟨e_j, raw_i⟩ = 0.
        intro j hj_lt
        -- Rewrite ONLY the second slot (e_i) to its (1/√N) • raw_i form;
        -- a bare `rw [chartFrameNormFiber_eq]` would fire on e_j first.
        conv_lhs => rw [show chartFrameNormFiber (I := I) g α b i =
            (Real.sqrt (g.inner b
                (chartFrameRawFiber (I := I) g α b i)
                (chartFrameRawFiber (I := I) g α b i)))⁻¹ •
              chartFrameRawFiber (I := I) g α b i from
          chartFrameNormFiber_eq (I := I) g α b i]
        rw [g_inner_smul_right_normalised (I := I) g b _ _ _]
        rw [horth_raw j hj_lt, mul_zero]
      · -- Unit norm: ⟨(1/√N) raw_i, (1/√N) raw_i⟩ = 1 by `g_inner_normalised`.
        rw [chartFrameNormFiber_eq]
        exact g_inner_normalised (I := I) g b
          (chartFrameRawFiber (I := I) g α b i) hgpos

/-- **Inductive orthonormality** of `chartFrameNormFiber` on the
trivialization base set. For $b \in \mathrm{baseSet}$ and indices
$i, j$, the inner product
$g.\mathrm{inner}\,b\,(e_i\,b)\,(e_j\,b)$ equals $1$ if $i = j$, and
$0$ otherwise. -/
theorem chartFrameNormFiber_orthonormal
    (g : RiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        (chartFrameNormFiber (I := I) g α b i)
        (chartFrameNormFiber (I := I) g α b j) =
      if i = j then 1 else 0 := by
  classical
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · have h := chartFrameNormFiber_orth_strong_aux (I := I) g α hb j.val j (le_refl _)
    have horth := h.2.1 i hlt
    have hne : i ≠ j := fun h_eq => by rw [h_eq] at hlt; omega
    rw [if_neg hne, horth]
  · have hi_eq_j : i = j := Fin.ext heq
    rw [if_pos hi_eq_j, ← hi_eq_j]
    exact (chartFrameNormFiber_orth_strong_aux (I := I) g α hb i.val i (le_refl _)).2.2
  · have h := chartFrameNormFiber_orth_strong_aux (I := I) g α hb i.val i (le_refl _)
    have horth_ji := h.2.1 j hgt
    have hne : i ≠ j := fun h_eq => by rw [h_eq] at hgt; omega
    rw [if_neg hne, g.symm]
    exact horth_ji

/-- **Orthonormality** of `chartFrameNorm` (the section form) on the
trivialization base set. -/
theorem chartFrameNorm_orthonormal
    (g : RiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        (chartFrameNorm (I := I) g α i b)
        (chartFrameNorm (I := I) g α j b) =
      if i = j then 1 else 0 :=
  chartFrameNormFiber_orthonormal (I := I) g α hb i j

/-! ## Stage 3: bump-cutoff to produce a global section

The chart-frame normalised Gram-Schmidt is $C^\infty$ only on the chart
source. To produce a globally smooth tangent-bundle section, we
multiply by a smooth bump function centred at $\alpha$ whose support
lies inside the chart source. -/

/-- A canonical smooth bump function centred at $\alpha$. It is $1$ on
a neighbourhood of $\alpha$ and supported in `(chartAt H α).source`
(the trivialization base set at $\alpha$). The existence is guaranteed
by `SmoothBumpFunction.instNonempty`. -/
private noncomputable def chartBumpAt (α : M) : SmoothBumpFunction I α :=
  Classical.arbitrary (SmoothBumpFunction I α)

/-- **Smooth orthonormal frame**. The $i$-th tangent-bundle section of a
smooth $g$-orthonormal local frame attached to the base point $\alpha$.
On the neighbourhood of $\alpha$ where the chart bump function
`chartBumpAt α` equals $1$, this section equals the $g$-Gram-Schmidt
orthonormalisation of the chart basis frame. Off the support of the
bump (which is contained in the chart source), the section is zero.

The fiber-by-fiber definition uses the chart bump function multiplied
by the chart-frame normalised Gram-Schmidt step. -/
noncomputable def smoothOrthoFrame
    (g : RiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Π b : M, TangentSpace I b :=
  fun b => (chartBumpAt (I := I) (M := M) α : M → ℝ) b •
    chartFrameNorm (I := I) g α i b

/-- The open subset of $M$ on which `smoothOrthoFrame g α` is guaranteed
to be a $g$-orthonormal smooth basis: the (open) set where the chart
bump function equals $1$. -/
noncomputable def smoothOrthoFrameNbhd (α : M) : Set M :=
  {b : M | (chartBumpAt (I := I) (M := M) α : M → ℝ) b = 1}

/-- The neighbourhood `smoothOrthoFrameNbhd α` is in the filter `𝓝 α`. -/
lemma smoothOrthoFrameNbhd_mem_nhds (α : M) :
    smoothOrthoFrameNbhd (I := I) (M := M) α ∈ 𝓝 α := by
  classical
  exact (chartBumpAt (I := I) (M := M) α).eventuallyEq_one

/-- The centre $\alpha$ belongs to `smoothOrthoFrameNbhd α`. -/
lemma mem_smoothOrthoFrameNbhd_self (α : M) :
    α ∈ smoothOrthoFrameNbhd (I := I) (M := M) α := by
  classical
  change (chartBumpAt (I := I) (M := M) α : M → ℝ) α = 1
  exact (chartBumpAt (I := I) (M := M) α).eq_one

/-- On the neighbourhood `smoothOrthoFrameNbhd α`, the smooth orthonormal
frame agrees with the un-bumped Gram-Schmidt step. -/
lemma smoothOrthoFrame_eq_on_nbhd
    (g : RiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α) :
    smoothOrthoFrame (I := I) g α i b =
      chartFrameNorm (I := I) g α i b := by
  classical
  unfold smoothOrthoFrame
  have hb1 : (chartBumpAt (I := I) (M := M) α : M → ℝ) b = 1 := hb
  rw [hb1, one_smul]

/-- The neighbourhood `smoothOrthoFrameNbhd α` is contained in the chart
source `(chartAt H α).source`. -/
lemma smoothOrthoFrameNbhd_subset_chartAt_source (α : M) :
    smoothOrthoFrameNbhd (I := I) (M := M) α ⊆ (chartAt H α).source := by
  classical
  intro b hb
  have hb1 : (chartBumpAt (I := I) (M := M) α : M → ℝ) b = 1 := hb
  have hsupp : b ∈ Function.support (chartBumpAt (I := I) (M := M) α : M → ℝ) := by
    change (chartBumpAt (I := I) (M := M) α : M → ℝ) b ≠ 0
    rw [hb1]; exact one_ne_zero
  exact (chartBumpAt (I := I) (M := M) α).support_subset_source hsupp

/-- The neighbourhood `smoothOrthoFrameNbhd α` is contained in the
trivialization base set
`(trivializationAt E (TangentSpace I) α).baseSet`. -/
lemma smoothOrthoFrameNbhd_subset_baseSet (α : M) :
    smoothOrthoFrameNbhd (I := I) (M := M) α ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro b hb
  rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
  exact smoothOrthoFrameNbhd_subset_chartAt_source (I := I) (M := M) α hb

/-! ## Stage 5: orthonormality of `smoothOrthoFrame`

On the neighbourhood `smoothOrthoFrameNbhd α`, the smooth orthonormal
frame agrees with the un-bumped Gram-Schmidt frame, which is
$g$-orthonormal at every base-set point (Stage 3a). Combining the two
yields orthonormality of `smoothOrthoFrame g α` on
`smoothOrthoFrameNbhd α`, and (via $\alpha \in \mathrm{Nbhd}\,\alpha$)
at the centre $\alpha$ itself. -/

/-- **Orthonormality of `smoothOrthoFrame` on the bump-equals-1
neighbourhood.** For $b \in \mathrm{smoothOrthoFrameNbhd}\,\alpha$,
the smooth orthonormal frame at $b$ is $g$-orthonormal. -/
theorem smoothOrthoFrame_orthonormal
    (g : RiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        (smoothOrthoFrame (I := I) g α i b)
        (smoothOrthoFrame (I := I) g α j b) =
      if i = j then 1 else 0 := by
  rw [smoothOrthoFrame_eq_on_nbhd (I := I) g α i hb,
      smoothOrthoFrame_eq_on_nbhd (I := I) g α j hb]
  exact chartFrameNorm_orthonormal (I := I) g α
    (smoothOrthoFrameNbhd_subset_baseSet (I := I) (M := M) α hb) i j

/-- **Orthonormality of `smoothOrthoFrame` at the centre.** The frame
`smoothOrthoFrame g α` is $g_\alpha$-orthonormal. Direct corollary of
`smoothOrthoFrame_orthonormal` at $\alpha$, since
$\alpha \in \mathrm{smoothOrthoFrameNbhd}\,\alpha$. -/
theorem smoothOrthoFrame_orthonormal_at_center
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner α
        (smoothOrthoFrame (I := I) g α i α)
        (smoothOrthoFrame (I := I) g α j α) =
      if i = j then 1 else 0 :=
  smoothOrthoFrame_orthonormal (I := I) g α
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) α) i j

end Tensor
end Riemannian

end
