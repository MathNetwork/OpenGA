import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import OpenGALib.Algebraic.Auxiliary.OrthonormalBasisDiagonal
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

/-- **Span identity** (recursion-structural): for every $m$ with
$m.\mathrm{val} < i.\mathrm{val}$, the normalised Gram-Schmidt vector
$e_m(b) = \mathrm{chartFrameNormFiber}\,g\,\alpha\,b\,m$ lies in the
$\mathbb{R}$-span of the chart-basis vectors $v_0(b), \ldots,
v_{i-1}(b)$. Proved by strong induction on $m.\mathrm{val}$ using the
recursive Gram-Schmidt formula `chartFrameNormFiber_eq`; entirely
self-contained (no orthonormality IH required). -/
private lemma chartFrameNormFiber_mem_span_chartBasis
    (g : RiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∀ kk : ℕ, ∀ m : Fin (Module.finrank ℝ E),
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
    exact ⟨⟨0, hm_lt⟩, Set.mem_univ _, rfl⟩
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

/-- **Non-degeneracy of the unnormalised Gram-Schmidt step**: at any
base-set point, $\mathrm{raw}_i \ne 0$.

Argument: if $\mathrm{raw}_i = 0$, then $v_i$ equals its projection
onto $\mathrm{span}(e_0, \ldots, e_{i-1})$. By
`chartFrameNormFiber_mem_span_chartBasis`, this span is contained in
$\mathrm{span}(v_0, \ldots, v_{i-1})$, so
$v_i \in \mathrm{span}(v_0, \ldots, v_{i-1})$ — contradicting linear
independence of the chart-basis family. -/
private lemma chartFrameRawFiber_ne_zero
    (g : RiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartFrameRawFiber (I := I) g α b i ≠ 0 := by
  classical
  have hLI : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        chartBasisVecFiber (I := I) α i b) :=
    chartBasisFamily_linearIndependent (I := I) α hb
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
    exact chartFrameNormFiber_mem_span_chartBasis (I := I) g α b i
      (Module.finrank ℝ E) ⟨j'.val, lt_trans j'.isLt i.isLt⟩
      (Nat.le_of_lt (lt_trans j'.isLt i.isLt)) j'.isLt
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
      exact ⟨⟨n.val, lt_trans n.isLt i.isLt⟩, n.isLt, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n.val, hn⟩, Set.mem_univ _, rfl⟩
  rw [hset_eq] at hvi_in_span
  have hi_notin : i ∉ {n : Fin (Module.finrank ℝ E) | n.val < i.val} := by
    simp [Set.mem_setOf_eq]
  exact hLI.notMem_span_image hi_notin hvi_in_span

/-- **Orthogonality of `raw_i` to each previous `e_j`**, given that
$\{e_0, \ldots, e_{i-1}\}$ is already $g$-orthonormal at $b$.

Bilinear unfold of $\mathrm{raw}_i = v_i - \sum_{m < i} \langle v_i,
e_m\rangle e_m$ paired with $e_j$ on the left: only the $m = j$ term
of the sum survives (orthonormality), and that term equals
$\langle e_j, v_i\rangle$ via $g.\mathrm{symm}$, cancelling the
leading $\langle e_j, v_i\rangle$ to give $0$. -/
private lemma chartFrameRawFiber_orth_to_orthonormal_prefix
    (g : RiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E))
    (h_orth : ∀ j j' : Fin (Module.finrank ℝ E),
      j.val < i.val → j'.val < i.val →
      g.inner b
          (chartFrameNormFiber (I := I) g α b j)
          (chartFrameNormFiber (I := I) g α b j') =
        if j = j' then 1 else 0) :
    ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
      g.inner b
          (chartFrameNormFiber (I := I) g α b j)
          (chartFrameRawFiber (I := I) g α b i) = 0 := by
  classical
  intro j hj_lt
  -- Local notation for the recurring index-coerced normalised vector.
  set e := fun (j' : Fin i.val) =>
    chartFrameNormFiber (I := I) g α b
      ⟨j'.val, lt_trans j'.isLt i.isLt⟩ with he_def
  set vi := chartBasisVecFiber (I := I) α i b with hvi_def
  set ej := chartFrameNormFiber (I := I) g α b j with hej_def
  set c : Fin i.val → ℝ := fun j' => g.inner b vi (e j') with hc_def
  -- Unfold raw_i to the explicit subtraction form, then bilinearity.
  change g.inner b ej (vi - ∑ j' : Fin i.val, c j' • e j') = 0
  rw [show (g.inner b) ej (vi - ∑ j' : Fin i.val, c j' • e j') =
      (g.inner b) ej vi - (g.inner b) ej (∑ j' : Fin i.val, c j' • e j') from
    map_sub _ _ _]
  rw [g_inner_sum_right (I := I) g b ej Finset.univ e c]
  -- The sum: only j' = ⟨j.val, hj_lt⟩ survives.
  set j_inFin : Fin i.val := ⟨j.val, hj_lt⟩ with hj_inFin_def
  have hj_eq_inFin : (⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩ :
      Fin (Module.finrank ℝ E)) = j := Fin.ext rfl
  have hsingleton :
      ∑ j' ∈ (Finset.univ : Finset (Fin i.val)),
          c j' * g.inner b ej (e j') =
        c j_inFin * g.inner b ej (e j_inFin) := by
    refine Finset.sum_eq_single j_inFin ?_ ?_
    · intro j' _ hj'_ne
      have hj'_ne_val : j'.val ≠ j.val := fun h => hj'_ne (Fin.ext h)
      have hj'_in_total : (⟨j'.val, lt_trans j'.isLt i.isLt⟩ :
          Fin (Module.finrank ℝ E)).val < i.val := j'.isLt
      have hj_in_total : j.val < i.val := hj_lt
      have hj_ne_j' : j ≠ ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := by
        intro h
        exact hj'_ne_val (congrArg Fin.val h).symm
      have hzero := h_orth j ⟨j'.val, lt_trans j'.isLt i.isLt⟩
        hj_in_total hj'_in_total
      rw [if_neg hj_ne_j'] at hzero
      show c j' * g.inner b ej (chartFrameNormFiber (I := I) g α b
          ⟨j'.val, lt_trans j'.isLt i.isLt⟩) = 0
      rw [hzero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j_inFin) h
  rw [hsingleton]
  have hej_eq : e j_inFin = ej := by
    show chartFrameNormFiber (I := I) g α b
        ⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩ = ej
    rw [hj_eq_inFin]
  rw [hej_eq]
  have hjj_unit : g.inner b ej ej = 1 := by
    have h := h_orth j j hj_lt hj_lt
    rw [if_pos rfl] at h
    exact h
  rw [hjj_unit, mul_one]
  -- c j_inFin = ⟨v_i, e j_inFin⟩ = ⟨v_i, ej⟩ = ⟨ej, v_i⟩ by g.symm.
  have hc_eq : c j_inFin = g.inner b vi ej := by
    show g.inner b vi (e j_inFin) = g.inner b vi ej
    rw [hej_eq]
  rw [hc_eq, g.symm]; ring

/-- The strong-induction package for the orthonormality of
`chartFrameNormFiber`. The conclusion bundles three facts at every
$i \le k$:

1. $\mathrm{chartFrameRawFiber}\,g\,\alpha\,b\,i \ne 0$;
2. for all $j < i$, $\langle e_j, e_i\rangle_g = 0$;
3. $\langle e_i, e_i\rangle_g = 1$.

Now a thin wrapper: the bundled IH is unpacked into an "orthonormality
on a prefix" hypothesis, which is fed to the standalone helpers
`chartFrameRawFiber_ne_zero` (Step 2) and
`chartFrameRawFiber_orth_to_orthonormal_prefix` (Step 1). The Step 3
normalisation uses `g_inner_normalised`. No `maxHeartbeats` bump
required — each helper compiles in isolation under defaults. -/
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
  intro k
  induction k with
  | zero =>
    intro i hi_le
    have hi_val : i.val = 0 := Nat.le_zero.mp hi_le
    have hi_eq : i = ⟨0, NeZero.pos _⟩ := Fin.ext hi_val
    subst hi_eq
    refine ⟨?_, ?_, ?_⟩
    · exact chartFrameRawFiber_ne_zero (I := I) g α hb _
    · intro j hj
      simp at hj
    · exact chartFrameNormFiber_at_zero_norm (I := I) g α hb
  | succ k ih =>
    intro i hi_le
    by_cases hi_lt : i.val ≤ k
    · exact ih i hi_lt
    · -- i.val = k + 1: extract orthonormality on the prefix from the IH.
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
      -- Orthonormality on the prefix {0, …, i.val - 1} (trichotomy on j vs j').
      have h_orth_prefix : ∀ j j' : Fin (Module.finrank ℝ E),
          j.val < i.val → j'.val < i.val →
          g.inner b
              (chartFrameNormFiber (I := I) g α b j)
              (chartFrameNormFiber (I := I) g α b j') =
            if j = j' then 1 else 0 := by
        intro j j' hj_lt hj'_lt
        rcases Nat.lt_trichotomy j.val j'.val with hlt | heq | hgt
        · -- j.val < j'.val: use IH at j'.
          have hzero := (ih_below j' hj'_lt).2.1 j hlt
          have hne : j ≠ j' := fun h => by rw [h] at hlt; omega
          rw [if_neg hne, hzero]
        · -- j = j'.
          have hjj : j = j' := Fin.ext heq
          subst hjj
          rw [if_pos rfl]
          exact (ih_below j hj_lt).2.2
        · -- j.val > j'.val: use IH at j, swap with g.symm.
          have hzero := (ih_below j hj_lt).2.1 j' hgt
          have hne : j ≠ j' := fun h => by rw [h] at hgt; omega
          rw [if_neg hne, g.symm]; exact hzero
      -- Step 2: raw_i ≠ 0 (standalone).
      have hraw_ne := chartFrameRawFiber_ne_zero (I := I) g α hb i
      -- Step 1: ⟨e_j, raw_i⟩ = 0 for j.val < i.val (uses h_orth_prefix).
      have horth_raw := chartFrameRawFiber_orth_to_orthonormal_prefix
        (I := I) g α b i h_orth_prefix
      -- Step 3: orthogonality + unit norm of e_i = (1/√N) • raw_i.
      have hgpos : 0 < g.inner b
          (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i) :=
        g.pos b (chartFrameRawFiber (I := I) g α b i) hraw_ne
      refine ⟨hraw_ne, ?_, ?_⟩
      · intro j hj_lt
        conv_lhs => rw [show chartFrameNormFiber (I := I) g α b i =
            (Real.sqrt (g.inner b
                (chartFrameRawFiber (I := I) g α b i)
                (chartFrameRawFiber (I := I) g α b i)))⁻¹ •
              chartFrameRawFiber (I := I) g α b i from
          chartFrameNormFiber_eq (I := I) g α b i]
        rw [g_inner_smul_right_normalised (I := I) g b _ _ _]
        rw [horth_raw j hj_lt, mul_zero]
      · rw [chartFrameNormFiber_eq]
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

/-! ## Stage 6: smoothness of the smooth orthonormal frame

We establish that each `smoothOrthoFrame g α i` is $C^\infty$ as a
tangent-bundle section on $M$. The argument has three layers:

1. **Inner product of smooth sections is smooth.** The fiberwise inner
   product `b ↦ g.inner b (Y b) (Z b)` of two $C^\infty$ tangent
   sections is a $C^\infty$ scalar function, via
   `ContMDiffOn.clm_bundle_apply₂` applied to the bundled bilinear
   form `g.contMDiff`.
2. **Strong induction on the Gram-Schmidt step.** By strong induction
   on `i.val`, both `chartFrameRawFiber g α b i` and
   `chartFrameNormFiber g α b i` are $C^\infty$ as sections on the
   trivialization base set. The Gram-Schmidt formula combines smooth
   scalars (`g.inner` plus `Real.sqrt` and `inv₀`) with smooth sections
   via `ContMDiffOn.smul_section`, `.sum_section`, `.sub_section`.
   Positivity of $g.\mathrm{inner}\,b\,\mathrm{raw}_i\,\mathrm{raw}_i$
   (from `chartFrameNormFiber_orth_strong_aux`) keeps `Real.sqrt`
   nonzero so its inverse is smooth.
3. **Bump multiplication is globally smooth.** Multiplying by
   `chartBumpAt α` and using `ContMDiffOn.smul_section_of_tsupport`
   together with `tsupport_subset_chartAt_source` extends the local
   smoothness to a global $C^\infty$ tangent section. -/

/-- **Step 1 of Stage 6.** The fiberwise inner product of two
$C^\infty$ tangent-bundle sections is a $C^\infty$ scalar function on
the same set `s ⊆ M`. -/
private lemma g_inner_contMDiffOn_of_sections
    (g : RiemannianMetric I M)
    {Y Z : Π b : M, TangentSpace I b} {s : Set M}
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) s)
    (hZ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% Z) s) :
    ContMDiffOn I 𝓘(ℝ) ∞ (fun b : M => g.inner b (Y b) (Z b)) s := by
  classical
  have hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        b (g.inner b)) s :=
    g.contMDiff.contMDiffOn
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m, g.inner m (Y m) (Z m)⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ))) s :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hg hY hZ
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

/-- **Step 1' of Stage 6.** `T%`-form repackaging of
`chartBasisVec_contMDiffOn`: the chart-basis tangent section is
$C^\infty$ on the trivialization base set, stated in the `T%` form
expected by Mathlib's section-level API
(`ContMDiffOn.smul_section`, etc.). -/
private lemma chartBasisVec_contMDiffOn_section
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => chartBasisVecFiber (I := I) α i b))
        (trivializationAt E (TangentSpace I) α).baseSet :=
  chartBasisVec_contMDiffOn (I := I) α i

/-- **Step 2 helper (generic normalisation).** Given a smooth tangent
section `Y` that is nonvanishing on `s`, the normalised section
$b \mapsto (\sqrt{g_b(Y_b, Y_b)})^{-1} \cdot Y_b$ is $C^\infty$ on `s`.

This is the workhorse for both the zero-case and the succ-case of
`chartFrameNormFiber_contMDiffOn_strong`. Factoring it out keeps each
case under default `maxHeartbeats`, replacing the external $20\times$
bump on the inlined induction. -/
private lemma chartFrame_normalise_section_contMDiffOn
    (g : RiemannianMetric I M)
    {Y : Π b : M, TangentSpace I b} {s : Set M}
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) s)
    (hY_ne : ∀ b ∈ s, Y b ≠ 0) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => (Real.sqrt (g.inner b (Y b) (Y b)))⁻¹ • Y b)) s := by
  classical
  have h_inner : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => g.inner b (Y b) (Y b)) s :=
    g_inner_contMDiffOn_of_sections (I := I) g hY hY
  have h_inner_pos : ∀ b ∈ s, 0 < g.inner b (Y b) (Y b) :=
    fun b hb => g.pos b _ (hY_ne b hb)
  have h_sqrt_ne : ∀ b ∈ s,
      Real.sqrt (g.inner b (Y b) (Y b)) ≠ 0 :=
    fun b hb => ne_of_gt (Real.sqrt_pos.mpr (h_inner_pos b hb))
  have h_sqrt : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => Real.sqrt (g.inner b (Y b) (Y b))) s := by
    intro b hb
    have h_inner_at := h_inner b hb
    have h_sqrt_real : ContDiffAt ℝ ∞ Real.sqrt (g.inner b (Y b) (Y b)) :=
      Real.contDiffAt_sqrt (ne_of_gt (h_inner_pos b hb))
    exact h_sqrt_real.contMDiffAt.comp_contMDiffWithinAt
      (I := I) (I' := 𝓘(ℝ)) (I'' := 𝓘(ℝ)) b h_inner_at
  have h_inv : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (Real.sqrt (g.inner b (Y b) (Y b)))⁻¹) s :=
    fun b hb => (h_sqrt b hb).inv₀ (h_sqrt_ne b hb)
  exact ContMDiffOn.smul_section h_inv hY

/-- **Step 2 helper (succ step).** Given that
`chartFrameNormFiber g α b j` is $C^\infty$ as a section on the
trivialization base set for every `j` with `j.val < i.val`, the
unnormalised Gram-Schmidt vector `chartFrameRawFiber g α b i` is
$C^\infty$ as a section on the base set. -/
private lemma chartFrameRawFiber_succ_section_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E))
    (ih : ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
        ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
          (T% (fun b : M => chartFrameNormFiber (I := I) g α b j))
          (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => chartFrameRawFiber (I := I) g α b i))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hbase_i := chartBasisVec_contMDiffOn_section (I := I) α i
  have h_j' : ∀ j' : Fin i.val,
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => chartFrameNormFiber (I := I) g α b
            ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    fun j' => ih ⟨j'.val, lt_trans j'.isLt i.isLt⟩ j'.isLt
  have h_coef : ∀ j' : Fin i.val,
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => g.inner b (chartBasisVecFiber (I := I) α i b)
            (chartFrameNormFiber (I := I) g α b
              ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    fun j' => g_inner_contMDiffOn_of_sections (I := I) g hbase_i (h_j' j')
  have h_summand : ∀ j' ∈ (Finset.univ : Finset (Fin i.val)),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M =>
          g.inner b (chartBasisVecFiber (I := I) α i b)
              (chartFrameNormFiber (I := I) g α b
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
            chartFrameNormFiber (I := I) g α b
              ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    fun j' _ => ContMDiffOn.smul_section (h_coef j') (h_j' j')
  have h_sum : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M =>
        ∑ j' : Fin i.val,
          g.inner b (chartBasisVecFiber (I := I) α i b)
              (chartFrameNormFiber (I := I) g α b
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
            chartFrameNormFiber (I := I) g α b
              ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.sum_section h_summand
  have h_sub : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M =>
        chartBasisVecFiber (I := I) α i b -
          ∑ j' : Fin i.val,
            g.inner b (chartBasisVecFiber (I := I) α i b)
                (chartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
              chartFrameNormFiber (I := I) g α b
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.sub_section hbase_i h_sum
  have hT_eq : (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
        (chartFrameRawFiber (I := I) g α b i)) =
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
        (chartBasisVecFiber (I := I) α i b -
          ∑ j' : Fin i.val,
            g.inner b (chartBasisVecFiber (I := I) α i b)
                (chartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
              chartFrameNormFiber (I := I) g α b
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) := by
    funext b; unfold chartFrameRawFiber; rfl
  rw [hT_eq]
  exact h_sub

/-- **Step 2 of Stage 6 (joint smoothness).** By strong induction on
`i.val`, both `chartFrameRawFiber g α b i` and
`chartFrameNormFiber g α b i` define $C^\infty$ sections on the
trivialization base set. Thin wrapper around
`chartFrame_normalise_section_contMDiffOn` and
`chartFrameRawFiber_succ_section_contMDiffOn`; each case factored
through these helpers compiles under default `maxHeartbeats`. -/
private theorem chartFrameNormFiber_contMDiffOn_strong
    (g : RiemannianMetric I M) (α : M) :
    ∀ k : ℕ, ∀ i : Fin (Module.finrank ℝ E), i.val ≤ k →
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => chartFrameRawFiber (I := I) g α b i))
        (trivializationAt E (TangentSpace I) α).baseSet ∧
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => chartFrameNormFiber (I := I) g α b i))
        (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  intro k
  induction k with
  | zero =>
    intro i hi
    have hi_val : i.val = 0 := Nat.le_zero.mp hi
    have hi_eq : i = ⟨0, NeZero.pos _⟩ := Fin.ext hi_val
    subst hi_eq
    have h_v := chartBasisVec_contMDiffOn_section (I := I) α ⟨0, NeZero.pos _⟩
    refine ⟨?_, ?_⟩
    · -- raw_0 = chartBasisVecFiber α 0
      have hT_eq : (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
            (chartFrameRawFiber (I := I) g α b ⟨0, NeZero.pos _⟩)) =
          (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
            (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)) := by
        funext b; rw [chartFrameRawFiber_at_zero (I := I) g α b]
      rw [hT_eq]; exact h_v
    · -- norm_0 via Helper A on Y = chartBasisVecFiber α 0
      have h_v_ne : ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
          chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b ≠ 0 :=
        fun b hb =>
          (chartBasisFamily_linearIndependent (I := I) α hb).ne_zero _
      have h_norm := chartFrame_normalise_section_contMDiffOn
        (I := I) g h_v h_v_ne
      have hT_eq : (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
            (chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩)) =
          (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
            ((Real.sqrt (g.inner b
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)))⁻¹ •
              chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)) := by
        funext b; rw [chartFrameNormFiber_at_zero (I := I) g α b]
      rw [hT_eq]; exact h_norm
  | succ k ih =>
    intro i hi
    by_cases hcase : i.val ≤ k
    · exact ih i hcase
    · have ih_below : ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M => chartFrameNormFiber (I := I) g α b j))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro j hj
        have hj_le_k : j.val ≤ k := by omega
        exact (ih j hj_le_k).2
      have h_raw := chartFrameRawFiber_succ_section_contMDiffOn
        (I := I) g α i ih_below
      have h_raw_ne : ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
          chartFrameRawFiber (I := I) g α b i ≠ 0 :=
        fun b hb => chartFrameRawFiber_ne_zero (I := I) g α hb i
      have h_norm := chartFrame_normalise_section_contMDiffOn
        (I := I) g h_raw h_raw_ne
      have hT_eq : (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
            (chartFrameNormFiber (I := I) g α b i)) =
          (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
            ((Real.sqrt (g.inner b
                (chartFrameRawFiber (I := I) g α b i)
                (chartFrameRawFiber (I := I) g α b i)))⁻¹ •
              chartFrameRawFiber (I := I) g α b i)) := by
        funext b; rw [chartFrameNormFiber_eq (I := I) g α b i]
      refine ⟨h_raw, ?_⟩
      rw [hT_eq]; exact h_norm

/-- **Step 2 of Stage 6 (section form).** `chartFrameNorm g α i b` is
$C^\infty$ as a tangent-bundle section in `b`, on the trivialization
base set. -/
lemma chartFrameNorm_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => chartFrameNorm (I := I) g α i b))
        (trivializationAt E (TangentSpace I) α).baseSet := by
  unfold chartFrameNorm
  exact (chartFrameNormFiber_contMDiffOn_strong (I := I) g α i.val i
    (le_refl _)).2

/-- **Step 3 of Stage 6 — global smoothness of the smooth orthonormal
frame.** Each component `smoothOrthoFrame g α i` is $C^\infty$ as a
tangent-bundle section on $M$. The bump function `chartBumpAt α` is
$C^\infty$ globally; its tsupport sits inside the chart source where
`chartFrameNorm g α i` is $C^\infty$. `ContMDiffOn.smul_section_of_tsupport`
combines these into a global $C^\infty$ section.

The `[T2Space M]` assumption is required for the bump function's
`tsupport_subset_chartAt_source` (Mathlib's `SmoothBumpFunction`
tsupport API is gated on Hausdorffness). All Riemannian manifolds in
applications are Hausdorff, so this is a free assumption downstream. -/
theorem smoothOrthoFrame_smooth [T2Space M]
    (g : RiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (smoothOrthoFrame (I := I) g α i)) := by
  classical
  set u : Set M := (chartAt H α).source with hu_def
  set ψ : M → ℝ := (chartBumpAt (I := I) (M := M) α : M → ℝ) with hψ_def
  have hψ_smooth : ContMDiffOn I 𝓘(ℝ) ∞ ψ u :=
    (chartBumpAt (I := I) (M := M) α).contMDiff.contMDiffOn
  have hu_open : IsOpen u := (chartAt H α).open_source
  have hψ_tsupport : tsupport ψ ⊆ u :=
    (chartBumpAt (I := I) (M := M) α).tsupport_subset_chartAt_source
  have hs_smooth : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => chartFrameNorm (I := I) g α i b)) u := by
    rw [show u = (trivializationAt E (TangentSpace I) α).baseSet from rfl]
    exact chartFrameNorm_contMDiffOn (I := I) g α i
  have h := ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (n := ∞)
    (V := TangentSpace I) hψ_smooth hu_open hψ_tsupport hs_smooth
  -- smoothOrthoFrame g α i b = ψ b • chartFrameNorm g α i b by definition.
  have h_eq : (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
        (smoothOrthoFrame (I := I) g α i b)) =
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
        ((ψ • fun b' : M => chartFrameNorm (I := I) g α i b') b)) := by
    funext b
    change TotalSpace.mk' E b (smoothOrthoFrame (I := I) g α i b) =
      TotalSpace.mk' E b ((ψ b) • chartFrameNorm (I := I) g α i b)
    unfold smoothOrthoFrame
    rfl
  rw [h_eq]
  exact h

/-! ## Stage 7: smoothOrthoFrame as an `OrthonormalBasis` at $\alpha$,
and the basis-invariance bridge

For the heart-of-Bochner closure, we need to compare diagonal sums
indexed by the smooth orthonormal frame (smooth-section-friendly) with
diagonal sums indexed by `stdOrthonormalBasis ℝ (TangentSpace I α)`
(the basis used in the existing `connectionLaplacian` /
`scalarLaplacian` API). The values $b_i = \mathrm{smoothOrthoFrame}\,
\mathrm{hm.metric}\,\alpha\,i\,\alpha \in T_\alpha M$ form an
orthonormal family at $\alpha$ (in the IPS sense, via the
`HasMetric I M` typeclass bridge), and so can be packaged as an
`OrthonormalBasis`. Combined with
`OrthonormalBasis.sum_apply_diagonal_invariant`, this gives
basis-invariance of $\sum_i B(b_i)(b_i)$ for any bilinear
$B : T_\alpha M \to_\ell T_\alpha M \to_\ell W$.

This stage uses `[HasMetric I M]` and instantiates the construction at
the canonical metric `hm.metric`; the IPS inner product
`⟪·, ·⟫_ℝ` on `TangentSpace I α` is then definitionally
`hm.metric.inner α`. -/

variable [hm : HasMetric I M]

open scoped InnerProductSpace

/-- Orthonormality of `smoothOrthoFrame hm.metric α · α` in the
`InnerProductSpace ℝ` sense (via `⟪·, ·⟫_ℝ` rather than
`hm.metric.inner α`). Direct from
`smoothOrthoFrame_orthonormal_at_center` and the def-eq
`⟪v, w⟫_ℝ = hm.metric.inner α v w` via the `RiemannianBundle` routing
from `instRiemannianBundleOfHasMetric`. -/
theorem smoothOrthoFrame_inner_at_center (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ⟪smoothOrthoFrame (I := I) hm.metric α i α,
        smoothOrthoFrame (I := I) hm.metric α j α⟫_ℝ =
      if i = j then 1 else 0 := by
  -- The IPS inner product on `TangentSpace I α` (via `HasMetric I M` →
  -- `RiemannianBundle (TangentSpace I)`) is definitionally `hm.metric.inner α`.
  show hm.metric.inner α _ _ = _
  exact smoothOrthoFrame_orthonormal_at_center (I := I) hm.metric α i j

/-- `smoothOrthoFrame hm.metric α · α` is an `Orthonormal` family in
`TangentSpace I α`. -/
theorem smoothOrthoFrame_orthonormal_family (α : M) :
    Orthonormal ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        smoothOrthoFrame (I := I) hm.metric α i α) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  exact smoothOrthoFrame_inner_at_center (I := I) α i j

/-- **`smoothOrthoFrame` packaged as an `OrthonormalBasis` at $\alpha$**.
The smooth orthonormal frame evaluated at the centre $\alpha$, indexed
by `Fin (Module.finrank ℝ E)`, with the canonical orthonormality from
`smoothOrthoFrame_orthonormal_family`. Constructed via
`basisOfOrthonormalOfCardEqFinrank` (orthonormal family of correct
cardinality is a basis) and `Basis.toOrthonormalBasis` (upgrade to
`OrthonormalBasis` given the orthonormality witness, which transfers
through `coe_basisOfOrthonormalOfCardEqFinrank`). -/
noncomputable def smoothOrthoFrameOrthonormalBasis (α : M) :
    OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I α) := by
  classical
  have hOrth := smoothOrthoFrame_orthonormal_family (I := I) α
  -- `TangentSpace I α` reduces to `E` via Mathlib's `@[reducible] def TangentSpace`.
  have hcard : Fintype.card (Fin (Module.finrank ℝ E))
      = Module.finrank ℝ (TangentSpace I α) := Fintype.card_fin _
  refine (basisOfOrthonormalOfCardEqFinrank hOrth hcard).toOrthonormalBasis ?_
  rw [coe_basisOfOrthonormalOfCardEqFinrank]
  exact hOrth

@[simp] theorem smoothOrthoFrameOrthonormalBasis_apply (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    smoothOrthoFrameOrthonormalBasis (I := I) α i =
      smoothOrthoFrame (I := I) hm.metric α i α := by
  unfold smoothOrthoFrameOrthonormalBasis
  rw [Module.Basis.coe_toOrthonormalBasis]
  exact congrFun
    (coe_basisOfOrthonormalOfCardEqFinrank
      (smoothOrthoFrame_orthonormal_family (I := I) α) _) i

/-- **Basis-change bridge at $\alpha$**: for any bilinear
$B : T_\alpha M \to_\ell T_\alpha M \to_\ell W$ and any
`OrthonormalBasis b` of `TangentSpace I α`, the diagonal sum over
the smooth orthonormal frame equals the diagonal sum over $b$.

Applied with $b = \mathrm{stdOrthonormalBasis}\,\mathbb{R}\,
(T_\alpha M)$, this bridges the heart-of-Bochner formulation against
`smoothOrthoFrame` (which is smoothness-friendly for the algebraic
chain) to the existing API formulation against `stdOrthonormalBasis`
(used in `connectionLaplacian` / `scalarLaplacian`). -/
theorem sum_diagonal_smoothOrthoFrame_eq_orthonormalBasis
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (α : M)
    (B : TangentSpace I α →ₗ[ℝ] TangentSpace I α →ₗ[ℝ] W)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I α)) :
    ∑ i, B (smoothOrthoFrame (I := I) hm.metric α i α)
            (smoothOrthoFrame (I := I) hm.metric α i α) =
      ∑ i, B (b i) (b i) := by
  have h := OrthonormalBasis.sum_apply_diagonal_invariant
    (smoothOrthoFrameOrthonormalBasis (I := I) α) b B
  -- Rewrite LHS sum via the simp lemma for smoothOrthoFrameOrthonormalBasis.
  simp only [smoothOrthoFrameOrthonormalBasis_apply] at h
  exact h

/-- **Basis-change bridge to `stdOrthonormalBasis`**: specialization of
`sum_diagonal_smoothOrthoFrame_eq_orthonormalBasis` with
$b = \mathrm{stdOrthonormalBasis}\,\mathbb{R}\,(T_\alpha M)$ — the
basis used by `connectionLaplacian` / `scalarLaplacian` / the
heart-of-Bochner statement. -/
theorem sum_diagonal_smoothOrthoFrame_eq_std
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (α : M)
    (B : TangentSpace I α →ₗ[ℝ] TangentSpace I α →ₗ[ℝ] W) :
    ∑ i, B (smoothOrthoFrame (I := I) hm.metric α i α)
            (smoothOrthoFrame (I := I) hm.metric α i α) =
      ∑ i, B ((stdOrthonormalBasis ℝ (TangentSpace I α)) i)
              ((stdOrthonormalBasis ℝ (TangentSpace I α)) i) :=
  sum_diagonal_smoothOrthoFrame_eq_orthonormalBasis (I := I) α B
    (stdOrthonormalBasis ℝ (TangentSpace I α))

/-! ### `smoothOrthoFrame` as `OrthonormalBasis` at any point in the nbhd

At any `b ∈ smoothOrthoFrameNbhd α`, the frame `(smoothOrthoFrame hm.metric α i b)_i`
forms a `g_b`-orthonormal basis of `T_bM`. Same construction as
`smoothOrthoFrameOrthonormalBasis α` but parameterised by the nbhd point. -/

/-- Inner-product (IPS) form of `smoothOrthoFrame_orthonormal` at `b ∈ nbhd α`,
routed through `HasMetric I M` → `InnerProductSpace ℝ (TangentSpace I b)`. -/
theorem smoothOrthoFrame_inner_at_nbhd (α : M) {b : M}
    (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    ⟪smoothOrthoFrame (I := I) hm.metric α i b,
        smoothOrthoFrame (I := I) hm.metric α j b⟫_ℝ =
      if i = j then 1 else 0 := by
  show hm.metric.inner b _ _ = _
  exact smoothOrthoFrame_orthonormal (I := I) hm.metric α hb i j

/-- `smoothOrthoFrame hm.metric α · b` is an `Orthonormal` family in `T_bM`. -/
theorem smoothOrthoFrame_orthonormal_family_at_nbhd (α : M) {b : M}
    (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α) :
    Orthonormal ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        smoothOrthoFrame (I := I) hm.metric α i b) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  exact smoothOrthoFrame_inner_at_nbhd (I := I) α hb i j

/-- **`smoothOrthoFrame` packaged as an `OrthonormalBasis` at `b ∈ nbhd α`**.
Parametric in the nbhd point. -/
noncomputable def smoothOrthoFrameOrthonormalBasis_at_nbhd (α : M) {b : M}
    (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α) :
    OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I b) := by
  classical
  have hOrth := smoothOrthoFrame_orthonormal_family_at_nbhd (I := I) α hb
  have hcard : Fintype.card (Fin (Module.finrank ℝ E))
      = Module.finrank ℝ (TangentSpace I b) := Fintype.card_fin _
  refine (basisOfOrthonormalOfCardEqFinrank hOrth hcard).toOrthonormalBasis ?_
  rw [coe_basisOfOrthonormalOfCardEqFinrank]
  exact hOrth

@[simp] theorem smoothOrthoFrameOrthonormalBasis_at_nbhd_apply
    (α : M) {b : M} (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α)
    (i : Fin (Module.finrank ℝ E)) :
    smoothOrthoFrameOrthonormalBasis_at_nbhd (I := I) α hb i =
      smoothOrthoFrame (I := I) hm.metric α i b := by
  unfold smoothOrthoFrameOrthonormalBasis_at_nbhd
  rw [Module.Basis.coe_toOrthonormalBasis]
  exact congrFun
    (coe_basisOfOrthonormalOfCardEqFinrank
      (smoothOrthoFrame_orthonormal_family_at_nbhd (I := I) α hb) _) i

/-- **Basis-change bridge at `b ∈ nbhd α` (to `stdOrthonormalBasis`)**:
the diagonal sum over the smooth orthonormal frame at any nbhd point `b`
equals the diagonal sum over `stdOrthonormalBasis ℝ (T_bM)`. Parametric
version of `sum_diagonal_smoothOrthoFrame_eq_std`. -/
theorem sum_diagonal_smoothOrthoFrame_at_nbhd_eq_std
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (α : M) {b : M}
    (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α)
    (B : TangentSpace I b →ₗ[ℝ] TangentSpace I b →ₗ[ℝ] W) :
    ∑ i, B (smoothOrthoFrame (I := I) hm.metric α i b)
            (smoothOrthoFrame (I := I) hm.metric α i b) =
      ∑ i, B ((stdOrthonormalBasis ℝ (TangentSpace I b)) i)
              ((stdOrthonormalBasis ℝ (TangentSpace I b)) i) := by
  have h := OrthonormalBasis.sum_apply_diagonal_invariant
    (smoothOrthoFrameOrthonormalBasis_at_nbhd (I := I) α hb)
    (stdOrthonormalBasis ℝ (TangentSpace I b)) B
  simp only [smoothOrthoFrameOrthonormalBasis_at_nbhd_apply] at h
  exact h

end Tensor
end Riemannian

end
