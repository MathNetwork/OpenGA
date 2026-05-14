import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import OpenGALib.Riemannian.Metric.RiemannianMetric
import OpenGALib.Riemannian.TangentBundle.TangentSmooth
import OpenGALib.Riemannian.TensorBundle.SmoothOrthoFrame

/-!
# Smoothness of the chart-Gram-Schmidt frame and `smoothOrthoFrame`

Engineering scaffolding for `Tensor/SmoothOrthoFrame.lean`'s smoothness
clause. Six helper lemmas drive the chart-base-set smoothness of
`chartFrameNorm`, then `smoothOrthoFrame_smooth` lifts to a global
$C^\infty$ tangent section via bump multiplication.

The argument has three layers:

1. **Inner product of smooth sections is smooth** — `g.inner` paired with
   two $C^\infty$ sections via `ContMDiffOn.clm_bundle_apply₂`.
2. **Strong induction on the Gram-Schmidt step** — both
   `chartFrameRawFiber` and `chartFrameNormFiber` are $C^\infty$ as
   sections on the trivialization base set, by induction on `i.val`,
   factored through `chartFrame_normalise_section_contMDiffOn` and
   `chartFrameRawFiber_succ_section_contMDiffOn` to compile under
   default `maxHeartbeats`.
3. **Bump multiplication is globally smooth** — `chartBumpAt α`'s
   tsupport inside `(chartAt H α).source` lifts the local smoothness of
   `chartFrameNorm` to a global $C^\infty$ section via
   `ContMDiffOn.smul_section_of_tsupport`.
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

/-- **Eng.** Stage 6 Step 1. The fiberwise inner product of two
$C^\infty$ tangent-bundle sections is a $C^\infty$ scalar function on
the same set `s ⊆ M`. -/
private lemma g_inner_contMDiffOn_of_sections
    (g : RiemannianMetric I M)
    {Y Z : VectorFieldSection I M} {s : Set M}
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

/-- **Eng.** Stage 6 Step 1'. `T%`-form repackaging of
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

/-- **Eng.** Stage 6 Step 2 helper (generic normalisation). Given a smooth tangent
section `Y` that is nonvanishing on `s`, the normalised section
$b \mapsto (\sqrt{g_b(Y_b, Y_b)})^{-1} \cdot Y_b$ is $C^\infty$ on `s`.

This is the workhorse for both the zero-case and the succ-case of
`chartFrameNormFiber_contMDiffOn_strong`. Factoring it out keeps each
case under default `maxHeartbeats`, replacing the external $20\times$
bump on the inlined induction. -/
private lemma chartFrame_normalise_section_contMDiffOn
    (g : RiemannianMetric I M)
    {Y : VectorFieldSection I M} {s : Set M}
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

/-- **Eng.** Stage 6 Step 2 helper (succ step). Given that
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

/-- **Eng.** Stage 6 Step 2 (joint smoothness). By strong induction on
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

/-- **Math.** Stage 6 Step 2 (section form). `chartFrameNorm g α i b` is
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

/-- **Math.** Stage 6 Step 3 — global smoothness of the smooth orthonormal
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

end Tensor
end Riemannian
