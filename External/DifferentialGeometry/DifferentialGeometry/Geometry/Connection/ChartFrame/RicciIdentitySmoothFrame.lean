import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentity
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartMetric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.BumpFunction


noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

private noncomputable def chartFrameNormFiber
    (g : SmoothRiemannianMetric I M) (α : M) (b : M)
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

noncomputable def chartFrameNorm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (b : M) : TangentSpace I b :=
  chartFrameNormFiber (I := I) g α b i

private noncomputable def chartFrameRawFiber
    (g : SmoothRiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) : TangentSpace I b :=
  chartBasisVecFiber (I := I) α i b -
    ∑ j : Fin i.val,
      (g.inner b (chartBasisVecFiber (I := I) α i b)
          (chartFrameNormFiber (I := I) g α b
            ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
        chartFrameNormFiber (I := I) g α b
          ⟨j.val, lt_trans j.isLt i.isLt⟩

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartFrameNormFiber_eq
    (g : SmoothRiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    chartFrameNormFiber (I := I) g α b i =
      (Real.sqrt (g.inner b
          (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i)))⁻¹ •
        chartFrameRawFiber (I := I) g α b i := by
  unfold chartFrameNormFiber chartFrameRawFiber
  rfl

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartFrameRawFiber_at_zero
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    chartFrameRawFiber (I := I) g α b ⟨0, NeZero.pos _⟩ =
      chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b := by
  unfold chartFrameRawFiber
  simp

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartFrameNormFiber_at_zero
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩ =
      (Real.sqrt
          (g.inner b
            (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
            (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)))⁻¹ •
        chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b := by
  rw [chartFrameNormFiber_eq, chartFrameRawFiber_at_zero]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartFrameNormFiber_at_zero_norm
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    g.inner b
        (chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩)
        (chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩) = 1 := by
  classical
  rw [chartFrameNormFiber_at_zero]
  set v : TangentSpace I b :=
    chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b with hv_def
  have hv_ne_zero : v ≠ 0 := by
    have hLI := chartBasisFamily_linearIndependent (I := I) α hb
    intro hv0
    have : (1 : ℝ) • v = 0 := by rw [one_smul]; exact hv0
    have h := hLI.ne_zero (i := ⟨0, NeZero.pos _⟩)
    exact h hv0
  have hpos : 0 < g.inner b v v := g.pos b v hv_ne_zero
  set N : ℝ := g.inner b v v with hN_def
  set s : ℝ := Real.sqrt N with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hpos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hexpand :
      g.inner b (s⁻¹ • v) (s⁻¹ • v) = s⁻¹ * (s⁻¹ * N) := by
    have h_outer : g.inner b (s⁻¹ • v) = s⁻¹ • g.inner b v := by
      rw [map_smul]
    rw [h_outer]
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show g.inner b v (s⁻¹ • v) = s⁻¹ * g.inner b v v from by
      rw [map_smul]; rfl]
  rw [hexpand]
  have hs_sq : s * s = N := by
    rw [hs_def]; exact Real.mul_self_sqrt (le_of_lt hpos)
  have h1 : s⁻¹ * (s⁻¹ * N) = (s * s)⁻¹ * N := by
    rw [mul_inv]; ring
  rw [h1, hs_sq]
  exact inv_mul_cancel₀ (ne_of_gt hpos)

private noncomputable def chartBumpAt (α : M) : SmoothBumpFunction I α :=
  Classical.arbitrary (SmoothBumpFunction I α)

noncomputable def smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Π b : M, TangentSpace I b :=
  fun b => (chartBumpAt (I := I) (M := M) α : M → ℝ) b •
    chartFrameNorm (I := I) g α i b

noncomputable def smoothOrthoFrameNbhd (α : M) : Set M :=
  {b : M | (chartBumpAt (I := I) (M := M) α : M → ℝ) b = 1}

noncomputable def smoothOrthoOpen (α : M) : Set M :=
  interior (smoothOrthoFrameNbhd (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma smoothOrthoOpen_open (α : M) :
    IsOpen (smoothOrthoOpen (I := I) (M := M) α) := by
  exact isOpen_interior

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma smoothOrthoFrameNbhd_mem_nhds (α : M) :
    smoothOrthoFrameNbhd (I := I) (M := M) α ∈ 𝓝 α := by
  classical
  exact (chartBumpAt (I := I) (M := M) α).eventuallyEq_one

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma mem_smoothOrthoOpen (α : M) :
    α ∈ smoothOrthoOpen (I := I) (M := M) α := by
  exact mem_interior_iff_mem_nhds.mpr
    (smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma mem_smoothOrthoFrameNbhd_self (α : M) :
    α ∈ smoothOrthoFrameNbhd (I := I) (M := M) α := by
  classical
  change (chartBumpAt (I := I) (M := M) α : M → ℝ) α = 1
  exact (chartBumpAt (I := I) (M := M) α).eq_one

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma smoothOrthoFrame_eq_on_nbhd
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α) :
    smoothOrthoFrame (I := I) g α i b =
      chartFrameNorm (I := I) g α i b := by
  classical
  unfold smoothOrthoFrame
  have hb1 : (chartBumpAt (I := I) (M := M) α : M → ℝ) b = 1 := hb
  rw [hb1, one_smul]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma smoothOrthoFrameNbhd_subset_chartAt_source (α : M) :
    smoothOrthoFrameNbhd (I := I) (M := M) α ⊆ (chartAt H α).source := by
  classical
  intro b hb
  have hb1 : (chartBumpAt (I := I) (M := M) α : M → ℝ) b = 1 := hb
  have hsupp : b ∈ Function.support (chartBumpAt (I := I) (M := M) α : M → ℝ) := by
    change (chartBumpAt (I := I) (M := M) α : M → ℝ) b ≠ 0
    rw [hb1]; exact one_ne_zero
  exact (chartBumpAt (I := I) (M := M) α).support_subset_source hsupp

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma smoothOrthoFrameNbhd_subset_baseSet (α : M) :
    smoothOrthoFrameNbhd (I := I) (M := M) α ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro b hb
  rw [trivializationAt_baseSet_eq_chartAt_source]
  exact smoothOrthoFrameNbhd_subset_chartAt_source (I := I) (M := M) α hb

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem smoothOrthoFrame_orthonormal_of_chartFrameNorm
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E))
    (hOrth : g.inner b
        (chartFrameNorm (I := I) g α i b)
        (chartFrameNorm (I := I) g α j b) = if i = j then 1 else 0) :
    g.inner b
        (smoothOrthoFrame (I := I) g α i b)
        (smoothOrthoFrame (I := I) g α j b) = if i = j then 1 else 0 := by
  rw [smoothOrthoFrame_eq_on_nbhd (I := I) g α i hb,
      smoothOrthoFrame_eq_on_nbhd (I := I) g α j hb]
  exact hOrth

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartFrameNorm_at_zero_norm_one
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    g.inner b
        (chartFrameNorm (I := I) g α ⟨0, NeZero.pos _⟩ b)
        (chartFrameNorm (I := I) g α ⟨0, NeZero.pos _⟩ b) = 1 := by
  unfold chartFrameNorm
  exact chartFrameNormFiber_at_zero_norm (I := I) g α hb

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartBasisVecFiber_eq_of_chartAt_eq
    {α₁ α₂ : M} (h : chartAt H α₁ = chartAt H α₂)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    chartBasisVecFiber (I := I) α₁ i x = chartBasisVecFiber (I := I) α₂ i x := by
  classical
  unfold chartBasisVecFiber
  have h_triv : trivializationAt E (TangentSpace I) α₁ =
      trivializationAt E (TangentSpace I) α₂ := by
    rw [TangentBundle.trivializationAt_eq_localTriv (I := I) α₁,
        TangentBundle.trivializationAt_eq_localTriv (I := I) α₂]
    congr 1
    apply Subtype.ext
    change (chartAt H α₁ : OpenPartialHomeomorph M H) = (chartAt H α₂ : OpenPartialHomeomorph M H)
    exact h
  rw [h_triv]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem chartFrame_eq_of_chartAt_eq_strong
    (g : SmoothRiemannianMetric I M) {α₁ α₂ : M}
    (h : chartAt H α₁ = chartAt H α₂) (b : M) :
    ∀ k : ℕ, ∀ i : Fin (Module.finrank ℝ E), i.val ≤ k →
      chartFrameRawFiber (I := I) g α₁ b i =
        chartFrameRawFiber (I := I) g α₂ b i ∧
      chartFrameNormFiber (I := I) g α₁ b i =
        chartFrameNormFiber (I := I) g α₂ b i := by
  classical
  intro k
  induction k with
  | zero =>
    intro i hi_le
    have hi_val : i.val = 0 := Nat.le_zero.mp hi_le
    have hi_eq : i = ⟨0, NeZero.pos _⟩ := Fin.ext hi_val
    subst hi_eq
    refine ⟨?_, ?_⟩
    · rw [chartFrameRawFiber_at_zero, chartFrameRawFiber_at_zero,
          chartBasisVecFiber_eq_of_chartAt_eq (I := I) (H := H) (M := M) h]
    · rw [chartFrameNormFiber_at_zero, chartFrameNormFiber_at_zero,
          chartBasisVecFiber_eq_of_chartAt_eq (I := I) (H := H) (M := M) h]
  | succ k ih =>
    intro i hi_le
    by_cases hi_lt : i.val ≤ k
    · exact ih i hi_lt
    · have hi_eq : i.val = k + 1 := by omega
      have ih_below : ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
          chartFrameNormFiber (I := I) g α₁ b j =
            chartFrameNormFiber (I := I) g α₂ b j := by
        intro j hj
        have hj_le : j.val ≤ k := by omega
        exact (ih j hj_le).2
      have h_raw : chartFrameRawFiber (I := I) g α₁ b i =
          chartFrameRawFiber (I := I) g α₂ b i := by
        unfold chartFrameRawFiber
        rw [chartBasisVecFiber_eq_of_chartAt_eq (I := I) (H := H) (M := M) h]
        congr 1
        apply Finset.sum_congr rfl
        intro j' _
        have hlift : (⟨j'.val, lt_trans j'.isLt i.isLt⟩ :
            Fin (Module.finrank ℝ E)).val < i.val := j'.isLt
        rw [ih_below ⟨j'.val, lt_trans j'.isLt i.isLt⟩ hlift]
      refine ⟨h_raw, ?_⟩
      rw [chartFrameNormFiber_eq, chartFrameNormFiber_eq, h_raw]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartFrameNorm_eq_of_chartAt_eq
    (g : SmoothRiemannianMetric I M) {α₁ α₂ : M}
    (h : chartAt H α₁ = chartAt H α₂)
    (i : Fin (Module.finrank ℝ E)) (b : M) :
    chartFrameNorm (I := I) g α₁ i b = chartFrameNorm (I := I) g α₂ i b := by
  classical
  unfold chartFrameNorm
  exact (chartFrame_eq_of_chartAt_eq_strong (I := I) g h b i.val i (le_refl _)).2

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma g_inner_sum_right
    (g : SmoothRiemannianMetric I M) (b : M)
    (v : TangentSpace I b)
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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma g_inner_sum_left
    (g : SmoothRiemannianMetric I M) (b : M)
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

set_option maxHeartbeats 4000000 in

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem chartFrameNormFiber_orth_strong_aux
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
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
    have hi_eq : i = ⟨0, NeZero.pos _⟩ := by
      apply Fin.ext
      exact hi_val
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
    · have hi_eq : i.val = k + 1 := by omega
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
      have horth_raw : ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
          g.inner b
              (chartFrameNormFiber (I := I) g α b j)
              (chartFrameRawFiber (I := I) g α b i) = 0 := by
        intro j hj_lt
        rw [show chartFrameRawFiber (I := I) g α b i =
            chartBasisVecFiber (I := I) α i b -
              ∑ j' : Fin i.val,
                (g.inner b (chartBasisVecFiber (I := I) α i b)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                  chartFrameNormFiber (I := I) g α b
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩ from rfl]
        rw [show ((g.inner b) (chartFrameNormFiber (I := I) g α b j))
              (chartBasisVecFiber (I := I) α i b -
                ∑ j' : Fin i.val,
                  (g.inner b (chartBasisVecFiber (I := I) α i b)
                      (chartFrameNormFiber (I := I) g α b
                        ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                    chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩) =
            ((g.inner b) (chartFrameNormFiber (I := I) g α b j))
              (chartBasisVecFiber (I := I) α i b) -
            ((g.inner b) (chartFrameNormFiber (I := I) g α b j))
              (∑ j' : Fin i.val,
                (g.inner b (chartBasisVecFiber (I := I) α i b)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                  chartFrameNormFiber (I := I) g α b
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩) from by
          rw [map_sub]]
        rw [g_inner_sum_right (I := I) g b
            (chartFrameNormFiber (I := I) g α b j)
            (Finset.univ : Finset (Fin i.val))
            (fun j' => chartFrameNormFiber (I := I) g α b
              ⟨j'.val, lt_trans j'.isLt i.isLt⟩)
            (fun j' => g.inner b
              (chartBasisVecFiber (I := I) α i b)
              (chartFrameNormFiber (I := I) g α b
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩))]
        have hsum_eq :
            ∑ j' ∈ (Finset.univ : Finset (Fin i.val)),
                g.inner b
                    (chartBasisVecFiber (I := I) α i b)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩) *
                  g.inner b
                    (chartFrameNormFiber (I := I) g α b j)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩) =
              g.inner b
                (chartFrameNormFiber (I := I) g α b j)
                (chartBasisVecFiber (I := I) α i b) := by
          have hj_in_fin : j.val < i.val := hj_lt
          set j_inFin : Fin i.val := ⟨j.val, hj_in_fin⟩
          have hsingleton :
              ∑ j' ∈ (Finset.univ : Finset (Fin i.val)),
                  g.inner b
                      (chartBasisVecFiber (I := I) α i b)
                      (chartFrameNormFiber (I := I) g α b
                        ⟨j'.val, lt_trans j'.isLt i.isLt⟩) *
                    g.inner b
                      (chartFrameNormFiber (I := I) g α b j)
                      (chartFrameNormFiber (I := I) g α b
                        ⟨j'.val, lt_trans j'.isLt i.isLt⟩) =
                g.inner b
                    (chartBasisVecFiber (I := I) α i b)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩) *
                  g.inner b
                    (chartFrameNormFiber (I := I) g α b j)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩) := by
            rw [Finset.sum_eq_single j_inFin]
            · intro j' _ hj'
              have hj'_neq : j'.val ≠ j.val := fun h => hj' (Fin.ext h)
              by_cases hcompare : j'.val < j.val
              · have hIH_j := ih_below j hj_lt
                have hzero := hIH_j.2.1 ⟨j'.val, lt_trans hcompare j.isLt⟩ hcompare
                rw [show (g.inner b
                    (chartFrameNormFiber (I := I) g α b j)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) =
                  g.inner b
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans hcompare j.isLt⟩)
                    (chartFrameNormFiber (I := I) g α b j) from by
                  rw [g.symm]]
                rw [hzero, mul_zero]
              · have hcompare_le : j.val ≤ j'.val := Nat.le_of_not_lt hcompare
                have hcompare' : j.val < j'.val := lt_of_le_of_ne hcompare_le hj'_neq.symm
                have hj'_in : (⟨j'.val, lt_trans j'.isLt i.isLt⟩ :
                  Fin (Module.finrank ℝ E)).val < i.val := j'.isLt
                have hIH_j' := ih_below ⟨j'.val, lt_trans j'.isLt i.isLt⟩ hj'_in
                have hzero := hIH_j'.2.1 j hcompare'
                rw [hzero, mul_zero]
            · intro h
              exact absurd (Finset.mem_univ j_inFin) h
          rw [hsingleton]
          have hIH_j := ih_below j hj_lt
          have hjj_unit : g.inner b
              (chartFrameNormFiber (I := I) g α b j)
              (chartFrameNormFiber (I := I) g α b j) = 1 := hIH_j.2.2
          have hj_eq : (⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩ :
              Fin (Module.finrank ℝ E)) = j := by
            apply Fin.ext
            rfl
          rw [hj_eq, hjj_unit, mul_one, g.symm]
        rw [hsum_eq]
        ring
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
        have h_e_in_span_v : ∀ k : ℕ, ∀ m : Fin (Module.finrank ℝ E),
            m.val ≤ k → m.val < i.val →
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
            have hm_eq : m = ⟨0, NeZero.pos _⟩ := by
              apply Fin.ext
              exact hm_val
            subst hm_eq
            rw [chartFrameNormFiber_at_zero]
            have h0_in_fin : (0 : ℕ) < i.val := hm_lt
            apply Submodule.smul_mem
            apply Submodule.subset_span
            refine ⟨⟨0, h0_in_fin⟩, ?_, rfl⟩
            exact Set.mem_univ _
          | succ kk ih_kk =>
            intro m hm_le hm_lt
            by_cases hcase : m.val ≤ kk
            · exact ih_kk m hcase hm_lt
            · have hm_eq : m.val = kk + 1 := by omega
              rw [chartFrameNormFiber_eq]
              apply Submodule.smul_mem
              unfold chartFrameRawFiber
              apply Submodule.sub_mem
              · apply Submodule.subset_span
                refine ⟨⟨m.val, hm_lt⟩, ?_, ?_⟩
                · exact Set.mem_univ _
                · rfl
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
        have hcontra : chartBasisVecFiber (I := I) α i b ∉
            Submodule.span ℝ
              ((fun n : Fin i.val =>
                chartBasisVecFiber (I := I) α
                  ⟨n.val, lt_trans n.isLt i.isLt⟩ b) ''
                Set.univ) := by
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
              refine ⟨⟨n.val, hn⟩, ?_, rfl⟩
              exact Set.mem_univ _
          rw [hset_eq]
          have hi_notin : i ∉ {n : Fin (Module.finrank ℝ E) | n.val < i.val} := by
            simp [Set.mem_setOf_eq]
          exact hLI.notMem_span_image hi_notin
        exact hcontra hvi_in_span
      have hgpos : 0 < g.inner b
          (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i) :=
        g.pos b (chartFrameRawFiber (I := I) g α b i) hraw_ne
      set N : ℝ := g.inner b
          (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i) with hN_def
      set s : ℝ := Real.sqrt N with hs_def
      have hs_pos : 0 < s := Real.sqrt_pos.mpr hgpos
      have hs_ne : s ≠ 0 := ne_of_gt hs_pos
      have hs_sq : s * s = N := Real.mul_self_sqrt (le_of_lt hgpos)
      refine ⟨hraw_ne, ?_, ?_⟩
      · intro j hj_lt
        have hei_eq : chartFrameNormFiber (I := I) g α b i =
            s⁻¹ • chartFrameRawFiber (I := I) g α b i :=
          chartFrameNormFiber_eq (I := I) g α b i
        rw [hei_eq]
        rw [show g.inner b (chartFrameNormFiber (I := I) g α b j)
              (s⁻¹ • chartFrameRawFiber (I := I) g α b i) =
            s⁻¹ * g.inner b (chartFrameNormFiber (I := I) g α b j)
              (chartFrameRawFiber (I := I) g α b i) from by
          rw [map_smul]; rfl]
        rw [horth_raw j hj_lt, mul_zero]
      · have hei_eq : chartFrameNormFiber (I := I) g α b i =
            s⁻¹ • chartFrameRawFiber (I := I) g α b i :=
          chartFrameNormFiber_eq (I := I) g α b i
        rw [hei_eq]
        have hinner_smul :
            g.inner b (s⁻¹ • chartFrameRawFiber (I := I) g α b i)
                (s⁻¹ • chartFrameRawFiber (I := I) g α b i) =
            s⁻¹ * (s⁻¹ * g.inner b
              (chartFrameRawFiber (I := I) g α b i)
              (chartFrameRawFiber (I := I) g α b i)) := by
          have h1 : g.inner b (s⁻¹ • chartFrameRawFiber (I := I) g α b i) =
              s⁻¹ • g.inner b (chartFrameRawFiber (I := I) g α b i) := by
            rw [map_smul]
          rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul]
          rw [show g.inner b (chartFrameRawFiber (I := I) g α b i)
                (s⁻¹ • chartFrameRawFiber (I := I) g α b i) =
              s⁻¹ * g.inner b (chartFrameRawFiber (I := I) g α b i)
                (chartFrameRawFiber (I := I) g α b i) from by
            rw [map_smul]; rfl]
        rw [hinner_smul]
        change s⁻¹ * (s⁻¹ * N) = 1
        have h1 : s⁻¹ * (s⁻¹ * N) = (s * s)⁻¹ * N := by rw [mul_inv]; ring
        rw [h1, hs_sq]
        exact inv_mul_cancel₀ (ne_of_gt hgpos)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartFrameNormFiber_orthonormal
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
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
    have hne : i ≠ j := by
      intro h_eq; rw [h_eq] at hlt; omega
    rw [if_neg hne, horth]
  · have hi_eq_j : i = j := Fin.ext heq
    rw [if_pos hi_eq_j, ← hi_eq_j]
    have h := chartFrameNormFiber_orth_strong_aux (I := I) g α hb i.val i (le_refl _)
    exact h.2.2
  · have h := chartFrameNormFiber_orth_strong_aux (I := I) g α hb i.val i (le_refl _)
    have horth_ji := h.2.1 j hgt
    have hne : i ≠ j := by
      intro h_eq; rw [h_eq] at hgt; omega
    rw [if_neg hne]
    rw [g.symm]
    exact horth_ji

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartFrameNorm_orthonormal
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        (chartFrameNorm (I := I) g α i b)
        (chartFrameNorm (I := I) g α j b) =
      if i = j then 1 else 0 := by
  unfold chartFrameNorm
  exact chartFrameNormFiber_orthonormal (I := I) g α hb i j

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem smoothOrthoFrame_orthonormal
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        (smoothOrthoFrame (I := I) g α i b)
        (smoothOrthoFrame (I := I) g α j b) =
      if i = j then 1 else 0 := by
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    smoothOrthoFrameNbhd_subset_baseSet (I := I) (M := M) α hb
  exact smoothOrthoFrame_orthonormal_of_chartFrameNorm (I := I) g α hb i j
    (chartFrameNorm_orthonormal (I := I) g α hb_base i j)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma smoothOrtho_li
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α) :
    LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ E) =>
      smoothOrthoFrame (I := I) g α i b) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hpair :
      g.inner b (∑ j, c j • smoothOrthoFrame (I := I) g α j b)
        (smoothOrthoFrame (I := I) g α i b) = 0 := by
    rw [hc]
    simp
  rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
  rw [Finset.sum_eq_single i] at hpair
  · rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
      smoothOrthoFrame_orthonormal (I := I) g α hb i i,
      if_pos rfl, smul_eq_mul, mul_one] at hpair
    exact hpair
  · intro j _ hji
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
      smoothOrthoFrame_orthonormal (I := I) g α hb j i,
      if_neg (by simpa using hji), smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem bochner_identity_smoothOrthoFrame_of_inner_form [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (x : M)
    (hSmooth : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (smoothOrthoFrame (I := I) g x i)))
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (localConnLap_vector (LeviCivita (I := I) g)
                  (smoothOrthoFrame (I := I) g x)
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    localConnLap_vector (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x)
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) :=
  localConnLap_vector_eq_bochnerFormula_of_inner_form (I := I) g hf
    (smoothOrthoFrame (I := I) g x) hSmooth x hInner

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem smoothOrthoFrame_orthonormal_at_center
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner x
        (smoothOrthoFrame (I := I) g x i x)
        (smoothOrthoFrame (I := I) g x j x) =
      if i = j then 1 else 0 :=
  smoothOrthoFrame_orthonormal (I := I) g x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) i j

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma g_inner_contMDiffOn_of_sections
    (g : SmoothRiemannianMetric I M)
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
        (fun m : M => (⟨m,
            g.inner m (Y m) (Z m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ))) s :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hg hY hZ
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartBasisVec_contMDiffOn_section
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => chartBasisVecFiber (I := I) α i b))
        (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x hx
  have h := chartBasisVec_contMDiffOn (I := I) α i x hx
  exact h

set_option maxHeartbeats 4000000 in

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem chartFrameNormFiber_contMDiffOn_strong
    (g : SmoothRiemannianMetric I M) (α : M) :
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
    refine ⟨?_, ?_⟩
    · have hsec_eq : ∀ b : M,
          chartFrameRawFiber (I := I) g α b ⟨0, NeZero.pos _⟩ =
            chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b :=
        fun b => chartFrameRawFiber_at_zero (I := I) g α b
      have hbase :=
        chartBasisVec_contMDiffOn_section (I := I) α ⟨0, NeZero.pos _⟩
      have hT_eq : (fun b : M => TotalSpace.mk' E
              (E := TangentSpace I) b
              (chartFrameRawFiber (I := I) g α b ⟨0, NeZero.pos _⟩)) =
          (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)) := by
        funext b; rw [hsec_eq b]
      rw [hT_eq]
      exact hbase
    · have hsec_eq : ∀ b : M,
          chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩ =
            (Real.sqrt (g.inner b
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)))⁻¹ •
              chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b :=
        fun b => chartFrameNormFiber_at_zero (I := I) g α b
      have hbase :=
        chartBasisVec_contMDiffOn_section (I := I) α ⟨0, NeZero.pos _⟩
      have h_inner :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => g.inner b
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b))
            (trivializationAt E (TangentSpace I) α).baseSet :=
        g_inner_contMDiffOn_of_sections (I := I) g hbase hbase
      have h_inner_pos : ∀ b : M,
          b ∈ (trivializationAt E (TangentSpace I) α).baseSet →
          0 < g.inner b
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b) := by
        intro b hb
        have hLI := chartBasisFamily_linearIndependent (I := I) α hb
        have hv_ne_zero :
            chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b ≠ 0 :=
          hLI.ne_zero ⟨0, NeZero.pos _⟩
        exact g.pos b _ hv_ne_zero
      have h_sqrt_ne :
          ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
          Real.sqrt (g.inner b
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)) ≠ 0 := by
        intro b hb
        have := h_inner_pos b hb
        exact ne_of_gt (Real.sqrt_pos.mpr this)
      have h_sqrt :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => Real.sqrt
                (g.inner b
                  (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
                  (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro b hb
        have h_inner_at := h_inner b hb
        have hpos := h_inner_pos b hb
        have h_sqrt_real : ContDiffAt ℝ ∞ Real.sqrt
            (g.inner b
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)) :=
          Real.contDiffAt_sqrt (ne_of_gt hpos)
        have h_sqrt_md :
            ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ Real.sqrt
              (g.inner b
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)) :=
          h_sqrt_real.contMDiffAt
        exact h_sqrt_md.comp_contMDiffWithinAt (I := I) (I' := 𝓘(ℝ))
          (I'' := 𝓘(ℝ)) b h_inner_at
      have h_inv :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M =>
              (Real.sqrt (g.inner b
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)))⁻¹)
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro b hb
        exact (h_sqrt b hb).inv₀ (h_sqrt_ne b hb)
      have h_smul :
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M =>
              (Real.sqrt (g.inner b
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)))⁻¹ •
              chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b))
            (trivializationAt E (TangentSpace I) α).baseSet :=
        ContMDiffOn.smul_section h_inv hbase
      have hT_eq : (fun b : M => TotalSpace.mk' E
              (E := TangentSpace I) b
              (chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩)) =
          (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
              ((Real.sqrt (g.inner b
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)))⁻¹ •
              chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)) := by
        funext b; rw [hsec_eq b]
      rw [hT_eq]
      exact h_smul
  | succ k ih =>
    intro i hi
    by_cases hcase : i.val ≤ k
    · exact ih i hcase
    · have hi_val : i.val = k + 1 := by omega
      have ih_below : ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M => chartFrameNormFiber (I := I) g α b j))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro j hj
        have hj_le_k : j.val ≤ k := by omega
        exact (ih j hj_le_k).2
      have hbase_i :=
        chartBasisVec_contMDiffOn_section (I := I) α i
      have h_j'_small_section : ∀ j' : Fin i.val,
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M => chartFrameNormFiber (I := I) g α b
              ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro j'
        exact ih_below ⟨j'.val, lt_trans j'.isLt i.isLt⟩ j'.isLt
      have h_innerCoef : ∀ j' : Fin i.val,
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => g.inner b
              (chartBasisVecFiber (I := I) α i b)
              (chartFrameNormFiber (I := I) g α b
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro j'
        exact g_inner_contMDiffOn_of_sections (I := I) g hbase_i
          (h_j'_small_section j')
      have h_summand : ∀ j' ∈ (Finset.univ : Finset (Fin i.val)),
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M =>
              g.inner b
                (chartBasisVecFiber (I := I) α i b)
                (chartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
              chartFrameNormFiber (I := I) g α b
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro j' _
        exact ContMDiffOn.smul_section
          (h_innerCoef j') (h_j'_small_section j')
      have h_sum :
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M =>
              ∑ j' : Fin i.val,
                g.inner b
                  (chartBasisVecFiber (I := I) α i b)
                  (chartFrameNormFiber (I := I) g α b
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
                chartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
            (trivializationAt E (TangentSpace I) α).baseSet :=
        ContMDiffOn.sum_section h_summand
      have h_raw : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
          (T% (fun b : M =>
            chartBasisVecFiber (I := I) α i b -
              ∑ j' : Fin i.val,
                g.inner b
                  (chartBasisVecFiber (I := I) α i b)
                  (chartFrameNormFiber (I := I) g α b
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
                chartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
          (trivializationAt E (TangentSpace I) α).baseSet :=
        ContMDiffOn.sub_section hbase_i h_sum
      have h_raw_eq : ∀ b : M,
          chartFrameRawFiber (I := I) g α b i =
            chartBasisVecFiber (I := I) α i b -
              ∑ j' : Fin i.val,
                g.inner b
                  (chartBasisVecFiber (I := I) α i b)
                  (chartFrameNormFiber (I := I) g α b
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
                chartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := fun b => by
        unfold chartFrameRawFiber; rfl
      have h_raw_section :
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M => chartFrameRawFiber (I := I) g α b i))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        have hT_eq : (fun b : M => TotalSpace.mk' E
                (E := TangentSpace I) b
                (chartFrameRawFiber (I := I) g α b i)) =
            (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
                (chartBasisVecFiber (I := I) α i b -
                  ∑ j' : Fin i.val,
                    g.inner b
                      (chartBasisVecFiber (I := I) α i b)
                      (chartFrameNormFiber (I := I) g α b
                        ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
                    chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) := by
          funext b; rw [h_raw_eq b]
        rw [hT_eq]
        exact h_raw
      have h_inner_raw :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => g.inner b
                (chartFrameRawFiber (I := I) g α b i)
                (chartFrameRawFiber (I := I) g α b i))
            (trivializationAt E (TangentSpace I) α).baseSet :=
        g_inner_contMDiffOn_of_sections (I := I) g h_raw_section h_raw_section
      have h_inner_raw_pos : ∀ b : M,
          b ∈ (trivializationAt E (TangentSpace I) α).baseSet →
          0 < g.inner b
              (chartFrameRawFiber (I := I) g α b i)
              (chartFrameRawFiber (I := I) g α b i) := by
        intro b hb
        have h_aux := chartFrameNormFiber_orth_strong_aux
          (I := I) g α hb i.val i (le_refl _)
        have hraw_ne : chartFrameRawFiber (I := I) g α b i ≠ 0 := h_aux.1
        exact g.pos b _ hraw_ne
      have h_sqrt_ne :
          ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
          Real.sqrt (g.inner b
              (chartFrameRawFiber (I := I) g α b i)
              (chartFrameRawFiber (I := I) g α b i)) ≠ 0 := by
        intro b hb
        have := h_inner_raw_pos b hb
        exact ne_of_gt (Real.sqrt_pos.mpr this)
      have h_sqrt :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => Real.sqrt
                (g.inner b
                  (chartFrameRawFiber (I := I) g α b i)
                  (chartFrameRawFiber (I := I) g α b i)))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro b hb
        have h_inner_at := h_inner_raw b hb
        have hpos := h_inner_raw_pos b hb
        have h_sqrt_real : ContDiffAt ℝ ∞ Real.sqrt
            (g.inner b
              (chartFrameRawFiber (I := I) g α b i)
              (chartFrameRawFiber (I := I) g α b i)) :=
          Real.contDiffAt_sqrt (ne_of_gt hpos)
        have h_sqrt_md :
            ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ Real.sqrt
              (g.inner b
                (chartFrameRawFiber (I := I) g α b i)
                (chartFrameRawFiber (I := I) g α b i)) :=
          h_sqrt_real.contMDiffAt
        exact h_sqrt_md.comp_contMDiffWithinAt (I := I) (I' := 𝓘(ℝ))
          (I'' := 𝓘(ℝ)) b h_inner_at
      have h_inv :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M =>
              (Real.sqrt (g.inner b
                (chartFrameRawFiber (I := I) g α b i)
                (chartFrameRawFiber (I := I) g α b i)))⁻¹)
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro b hb
        exact (h_sqrt b hb).inv₀ (h_sqrt_ne b hb)
      have h_smul :
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M =>
              (Real.sqrt (g.inner b
                (chartFrameRawFiber (I := I) g α b i)
                (chartFrameRawFiber (I := I) g α b i)))⁻¹ •
              chartFrameRawFiber (I := I) g α b i))
            (trivializationAt E (TangentSpace I) α).baseSet :=
        ContMDiffOn.smul_section h_inv h_raw_section
      have h_norm_eq : ∀ b : M,
          chartFrameNormFiber (I := I) g α b i =
            (Real.sqrt (g.inner b
                (chartFrameRawFiber (I := I) g α b i)
                (chartFrameRawFiber (I := I) g α b i)))⁻¹ •
              chartFrameRawFiber (I := I) g α b i := fun b =>
        chartFrameNormFiber_eq (I := I) g α b i
      have h_norm_section :
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M => chartFrameNormFiber (I := I) g α b i))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        have hT_eq : (fun b : M => TotalSpace.mk' E
                (E := TangentSpace I) b
                (chartFrameNormFiber (I := I) g α b i)) =
            (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
                ((Real.sqrt (g.inner b
                  (chartFrameRawFiber (I := I) g α b i)
                  (chartFrameRawFiber (I := I) g α b i)))⁻¹ •
                chartFrameRawFiber (I := I) g α b i)) := by
          funext b; rw [h_norm_eq b]
        rw [hT_eq]
        exact h_smul
      exact ⟨h_raw_section, h_norm_section⟩

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartFrameNorm_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => chartFrameNorm (I := I) g α i b))
        (trivializationAt E (TangentSpace I) α).baseSet := by
  unfold chartFrameNorm
  exact (chartFrameNormFiber_contMDiffOn_strong (I := I) g α i.val i (le_refl _)).2

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem smoothOrthoFrame_smooth
    (g : SmoothRiemannianMetric I M) (α : M)
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

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem smoothOrtho_isLocal
    (g : SmoothRiemannianMetric I M) (α : M) :
    IsLocalFrameOn I E (∞ : WithTop ℕ∞)
      (smoothOrthoFrame (I := I) g α)
      (smoothOrthoFrameNbhd (I := I) (M := M) α) where
  linearIndependent hb := smoothOrtho_li (I := I) g α hb
  generating := by
    intro b hb
    have hcard :
        Fintype.card (Fin (Module.finrank ℝ E)) =
          Module.finrank ℝ (TangentSpace I b) := by
      rw [Fintype.card_fin]
      rfl
    exact ge_of_eq
      ((smoothOrtho_li (I := I) g α hb).span_eq_top_of_card_eq_finrank hcard)
  contMDiffOn i := (smoothOrthoFrame_smooth (I := I) g α i).contMDiffOn

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem smoothOrtho_local
    (g : SmoothRiemannianMetric I M) (α : M) :
    IsLocalFrameOn I E (∞ : WithTop ℕ∞)
      (smoothOrthoFrame (I := I) g α)
      (smoothOrthoOpen (I := I) (M := M) α) :=
  (smoothOrtho_isLocal (I := I) g α).mono interior_subset

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem smoothOrtho_localOne
    (g : SmoothRiemannianMetric I M) (α : M) :
    IsLocalFrameOn I E (1 : WithTop ℕ∞)
      (smoothOrthoFrame (I := I) g α)
      (smoothOrthoOpen (I := I) (M := M) α) where
  linearIndependent hb := (smoothOrtho_local (I := I) g α).linearIndependent hb
  generating hb := (smoothOrtho_local (I := I) g α).generating hb
  contMDiffOn i := (smoothOrtho_local (I := I) g α).contMDiffOn i |>.of_le (by simp)

omit [SigmaCompactSpace M] in
theorem heart_of_bochner_smoothOrthoFrame [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (x : M)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (localConnLap_vector (LeviCivita (I := I) g)
                  (smoothOrthoFrame (I := I) g x)
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    localConnLap_vector (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x)
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) :=
  bochner_identity_smoothOrthoFrame_of_inner_form (I := I) g hf x
    (fun i => smoothOrthoFrame_smooth (I := I) g x i) hInner

end Connection
end Integral
end DifferentialGeometry
