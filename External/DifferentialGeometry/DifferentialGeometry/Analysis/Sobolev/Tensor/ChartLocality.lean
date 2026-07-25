import DifferentialGeometry.Analysis.Sobolev.Tensor.NormBasics


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComp_eq_zero_of_notMem_finset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) {α : M}
    (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s T α Idx Jdx = (fun _ => (0 : ℝ)) := by
  have hρ_zero : ∀ x : M, (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x = 0 :=
    fun x => chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
  funext y
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [tensorChartComp_apply_of_mem (I := I) (M := M) g r s T α Idx Jdx hy]
    unfold tensorChartComponentPou
    rw [hρ_zero]
    ring
  · exact tensorChartComp_apply_of_notMem (I := I) (M := M) g r s T α Idx Jdx hy

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNorm_chartTerm_eq_zero_of_notMem_finset
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) {α : M}
    (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M)) :
    (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro Idx _
  refine Finset.sum_eq_zero ?_
  intro Jdx _
  rw [tensorChartComp_eq_zero_of_notMem_finset (I := I) (M := M) g r s T hα Idx Jdx]
  exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkp_tensorChartComp_of_notMem_finset
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) {α : M}
    (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) (2 * k) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  rw [tensorChartComp_eq_zero_of_notMem_finset (I := I) (M := M) g r s T hα Idx Jdx]
  exact MemWkp_zero_fun (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] in
theorem MemWtwokTwo_iff_forall_finset
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    MemWtwokTwo (I := I) (M := M) g k T ↔
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          MemWkp (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α) := by
  constructor
  · intro hT α _ Idx Jdx
    exact hT α Idx Jdx
  · intro hT α Idx Jdx
    by_cases hα : α ∈ chartAtlasPOU_finset (I := I) (M := M)
    · exact hT α hα Idx Jdx
    · exact memWkp_tensorChartComp_of_notMem_finset
        (I := I) (M := M) g k T hα Idx Jdx

omit [NeZero (Module.finrank ℝ E)] in
theorem MemWtwokTwo_of_forall_finset_memWkp
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s)
    (hT : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    MemWtwokTwo (I := I) (M := M) g k T :=
  (MemWtwokTwo_iff_forall_finset (I := I) (M := M) g k T).mpr hT

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem MemWtwokTwo.memWkp_chartComp_finset
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T)
    {α : M} (_hα : α ∈ chartAtlasPOU_finset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) (2 * k) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  hT α Idx Jdx

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem MemWtwokTwo.memWkp_chartComp
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) (2 * k) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  hT α Idx Jdx

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNorm_eq_finset_sum
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    wtwokTwoNorm (I := I) (M := M) g k T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α) := by
  unfold wtwokTwoNorm
  rw [tsum_eq_sum]
  intro α hα
  exact wtwokTwoNorm_chartTerm_eq_zero_of_notMem_finset
    (I := I) (M := M) g k T hα

def wtwokTwoChartTerm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) (α : M) : ℝ≥0∞ :=
  ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
    ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma wtwokTwoChartTerm_def
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) (α : M) :
    wtwokTwoChartTerm (I := I) (M := M) g k T α =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem wtwokTwoChartTerm_lt_top
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) (α : M) :
    wtwokTwoChartTerm (I := I) (M := M) g k T α < ⊤ := by
  rw [wtwokTwoChartTerm_def]
  refine ENNReal.sum_lt_top.mpr ?_
  intro Idx _
  refine ENNReal.sum_lt_top.mpr ?_
  intro Jdx _
  exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E) (hT α Idx Jdx)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem wtwokTwoChartTerm_ne_top
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) (α : M) :
    wtwokTwoChartTerm (I := I) (M := M) g k T α ≠ ⊤ :=
  (wtwokTwoChartTerm_lt_top (I := I) (M := M) g hT α).ne

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNorm_eq_finset_sum_chartTerm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    wtwokTwoNorm (I := I) (M := M) g k T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        wtwokTwoChartTerm (I := I) (M := M) g k T α := by
  rw [wtwokTwoNorm_eq_finset_sum (I := I) (M := M) g k T]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoChartTerm_le_wtwokTwoNorm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) {α : M}
    (hα : α ∈ chartAtlasPOU_finset (I := I) (M := M)) :
    wtwokTwoChartTerm (I := I) (M := M) g k T α ≤
      wtwokTwoNorm (I := I) (M := M) g k T := by
  rw [wtwokTwoNorm_eq_finset_sum_chartTerm (I := I) (M := M) g k T]
  exact Finset.single_le_sum
    (f := fun α => wtwokTwoChartTerm (I := I) (M := M) g k T α)
    (fun α _ => zero_le _) hα

omit [NeZero (Module.finrank ℝ E)] in
theorem wkpNorm_tensorChartComp_le_wtwokTwoNorm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) {α : M}
    (hα : α ∈ chartAtlasPOU_finset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      wtwokTwoNorm (I := I) (M := M) g k T := by
  refine le_trans ?_ (wtwokTwoChartTerm_le_wtwokTwoNorm (I := I) (M := M) g k T hα)
  rw [wtwokTwoChartTerm_def]
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun Idx => ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α))
    (fun Idx _ => zero_le _) (Finset.mem_univ Idx))
  exact Finset.single_le_sum
    (f := fun Jdx => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α))
    (fun Jdx _ => zero_le _) (Finset.mem_univ Jdx)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComp_reconstruct
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    tensorChartPushed (I := I) (M := M) g r s T α y =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y •
            tensorChartBasisElement (E := E) r s Idx Jdx :=
  tensorChartPushed_eq_sum_tensorChartComp (I := I) (M := M) g r s T α y

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartPushed_eqOn_zero_of_tensorChartComp_eqOn_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (h : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      Set.EqOn (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (fun _ => (0 : ℝ)) (chartTargetEuclid (I := I) (M := M) α)) :
    Set.EqOn (tensorChartPushed (I := I) (M := M) g r s T α)
      (fun _ => (0 : TensorRSModel r s ℝ E))
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [tensorChartComp_reconstruct (I := I) (M := M) g r s T α y]
  refine Finset.sum_eq_zero ?_
  intro Idx _
  refine Finset.sum_eq_zero ?_
  intro Jdx _
  rw [h Idx Jdx hy, zero_smul]

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNormReal_eq_finset_sum_toReal
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    wtwokTwoNormReal (I := I) (M := M) g k T =
      (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal := by
  unfold wtwokTwoNormReal
  rw [wtwokTwoNorm_eq_finset_sum_chartTerm (I := I) (M := M) g k T]

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNormReal_le_finset_sum
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) :
    wtwokTwoNormReal (I := I) (M := M) g k T ≤
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal := by
  rw [wtwokTwoNormReal_eq_finset_sum_toReal (I := I) (M := M) g k T]
  rw [ENNReal.toReal_sum]
  intro α _
  exact wtwokTwoChartTerm_ne_top (I := I) (M := M) g hT α

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNormReal_ge_finset_sum
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal ≤
      wtwokTwoNormReal (I := I) (M := M) g k T := by
  rw [wtwokTwoNormReal_eq_finset_sum_toReal (I := I) (M := M) g k T]
  rw [ENNReal.toReal_sum]
  intro α _
  exact wtwokTwoChartTerm_ne_top (I := I) (M := M) g hT α

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNormReal_eq_finset_sum
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) :
    wtwokTwoNormReal (I := I) (M := M) g k T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal :=
  le_antisymm
    (wtwokTwoNormReal_le_finset_sum (I := I) (M := M) g hT)
    (wtwokTwoNormReal_ge_finset_sum (I := I) (M := M) g hT)

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoChartTerm_toReal_le_wtwokTwoNormReal
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) {α : M}
    (hα : α ∈ chartAtlasPOU_finset (I := I) (M := M)) :
    (wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal ≤
      wtwokTwoNormReal (I := I) (M := M) g k T := by
  unfold wtwokTwoNormReal
  refine ENNReal.toReal_le_toReal
    (wtwokTwoChartTerm_ne_top (I := I) (M := M) g hT α)
    (wtwokTwoNorm_ne_top (I := I) (M := M) g hT) |>.mpr ?_
  exact wtwokTwoChartTerm_le_wtwokTwoNorm (I := I) (M := M) g k T hα

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNormReal_le_card_mul
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T)
    {C : ℝ}
    (hbound : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      (wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal ≤ C) :
    wtwokTwoNormReal (I := I) (M := M) g k T ≤
      (chartAtlasPOU_finset (I := I) (M := M)).card * C := by
  rw [wtwokTwoNormReal_eq_finset_sum (I := I) (M := M) g hT]
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [Finset.sum_const, nsmul_eq_mul]

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
