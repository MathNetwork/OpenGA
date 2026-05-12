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

end Tensor
end Riemannian

end
