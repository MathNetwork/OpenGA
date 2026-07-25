import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAveraging

set_option autoImplicit false











noncomputable section

universe uX uι

namespace DifferentialGeometry
namespace HCGCompactness

open scoped BigOperators



noncomputable def cutRaw {X : Type uX} {ι : Type uι} [DecidableEq ι]
    (cut : X → ℝ) (a : ι → X → ℝ) (i0 i : ι) (x : X) : ℝ :=
  if i = i0 then a i0 x else (1 - cut x) * a i x


@[simp] theorem cutRaw_same {X : Type uX} {ι : Type uι} [DecidableEq ι]
    (cut : X → ℝ) (a : ι → X → ℝ) (i0 : ι) (x : X) :
    cutRaw cut a i0 i0 x = a i0 x := by
  rw [cutRaw, if_pos rfl]


theorem cutRaw_of_ne {X : Type uX} {ι : Type uι} [DecidableEq ι]
    (cut : X → ℝ) (a : ι → X → ℝ) (i0 i : ι) (x : X) (hi : i ≠ i0) :
    cutRaw cut a i0 i x = (1 - cut x) * a i x := by
  rw [cutRaw, if_neg hi]



theorem cutRaw_nonneg {X : Type uX} {ι : Type uι} [DecidableEq ι]
    {cut : X → ℝ} {a : ι → X → ℝ} {i0 : ι} {x : X}
    (hcut : cut x ∈ Set.Icc (0 : ℝ) 1) (hnn : ∀ i, 0 ≤ a i x) (i : ι) :
    0 ≤ cutRaw cut a i0 i x := by
  by_cases hi : i = i0
  · subst i
    rw [cutRaw_same]
    exact hnn i0
  · rw [cutRaw_of_ne cut a i0 i x hi]
    exact mul_nonneg (sub_nonneg.mpr hcut.2) (hnn i)


theorem num_ne_of_cut_ne {X : Type uX} {ι : Type uι} [DecidableEq ι]
    {cut : X → ℝ} {a : ι → X → ℝ} {i0 i : ι} {x : X}
    (hraw : cutRaw cut a i0 i x ≠ 0) : a i x ≠ 0 := by
  intro ha
  by_cases hi : i = i0
  · subst i
    exact hraw (by rw [cutRaw_same, ha])
  · exact hraw (by rw [cutRaw_of_ne cut a i0 i x hi, ha, mul_zero])



theorem cutRaw_pos {X : Type uX} {ι : Type uι} [DecidableEq ι]
    {cut : X → ℝ} {a : ι → X → ℝ} {i0 : ι} {x : X}
    (hnn : ∀ i, 0 ≤ a i x)
    (hcover : ∃ i, 0 < a i x) (hbase : cut x ≠ 0 → 0 < a i0 x) :
    ∃ i, 0 < cutRaw cut a i0 i x := by
  by_cases hi0 : 0 < a i0 x
  · exact ⟨i0, by simpa only [cutRaw_same] using hi0⟩
  have hai0 : a i0 x = 0 := le_antisymm (not_lt.mp hi0) (hnn i0)
  have hcut0 : cut x = 0 := by
    by_contra hc
    exact hi0 (hbase hc)
  obtain ⟨i, hi⟩ := hcover
  have hine : i ≠ i0 := by
    intro h
    subst i
    rw [hai0] at hi
    exact (lt_irrefl 0) hi
  refine ⟨i, ?_⟩
  rw [cutRaw_of_ne cut a i0 i x hine, hcut0, sub_zero, one_mul]
  exact hi



theorem cutRaw_sum_pos {X : Type uX} {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {cut : X → ℝ} {a : ι → X → ℝ} {i0 : ι} {x : X}
    (hcut : cut x ∈ Set.Icc (0 : ℝ) 1) (hnn : ∀ i, 0 ≤ a i x)
    (hcover : ∃ i, 0 < a i x) (hbase : cut x ≠ 0 → 0 < a i0 x) :
    0 < ∑ i, cutRaw cut a i0 i x := by
  obtain ⟨i, hi⟩ := cutRaw_pos hnn hcover hbase
  exact (Finset.sum_pos_iff_of_nonneg
    (fun j (_hj : j ∈ Finset.univ) => cutRaw_nonneg hcut hnn j)).2
      ⟨i, Finset.mem_univ i, hi⟩


theorem cutRaw_delta {X : Type uX} {ι : Type uι} [DecidableEq ι]
    {cut : X → ℝ} {a : ι → X → ℝ} {i0 : ι} {x : X}
    (hcut : cut x = 1) :
    cutRaw cut a i0 i0 x = a i0 x ∧
      ∀ i, i ≠ i0 → cutRaw cut a i0 i x = 0 := by
  refine ⟨cutRaw_same cut a i0 x, fun i hi => ?_⟩
  rw [cutRaw_of_ne cut a i0 i x hi, hcut, sub_self, zero_mul]


noncomputable def rawWeights {X : Type uX} {ι : Type uι} [Fintype ι]
    (a : ι → X → ℝ) (x : X) (i : ι) : ℝ :=
  a i x / ∑ j, a j x



theorem rawWeights_sum {X : Type uX} {ι : Type uι} [Fintype ι]
    {a : ι → X → ℝ} {x : X} (hne : (∑ j, a j x) ≠ 0) :
    ∑ i, rawWeights a x i = 1 := by
  simp only [rawWeights, ← Finset.sum_div]
  exact div_self hne


theorem rawWeights_nonneg {X : Type uX} {ι : Type uι} [Fintype ι]
    {a : ι → X → ℝ} {x : X} (hnn : ∀ j, 0 ≤ a j x) (i : ι) :
    0 ≤ rawWeights a x i :=
  div_nonneg (hnn i) (Finset.sum_nonneg fun j _ => hnn j)



theorem rawWeights_pos {X : Type uX} {ι : Type uι} [Fintype ι]
    {a : ι → X → ℝ} {x : X} (hnn : ∀ j, 0 ≤ a j x)
    (hne : (∑ j, a j x) ≠ 0) : ∃ i, 0 < rawWeights a x i := by
  have hsum : ∑ i, rawWeights a x i = 1 := rawWeights_sum hne
  have hpos : 0 < ∑ i, rawWeights a x i := by rw [hsum]; exact zero_lt_one
  simpa only [Finset.mem_univ, true_and] using
    (Finset.sum_pos_iff_of_nonneg
      (fun i (_hi : i ∈ Finset.univ) => rawWeights_nonneg hnn i)).mp hpos



theorem num_ne_of_raw_ne {X : Type uX} {ι : Type uι} [Fintype ι]
    {a : ι → X → ℝ} {x : X} {i : ι} (hweight : rawWeights a x i ≠ 0) :
    a i x ≠ 0 := by
  intro hnum
  apply hweight
  simp [rawWeights, hnum]



theorem rawWeights_delta {X : Type uX} {ι : Type uι} [Fintype ι]
    {a : ι → X → ℝ} {x : X} (i0 : ι)
    (hzero : ∀ j, j ≠ i0 → a j x = 0) (hne : a i0 x ≠ 0) :
    rawWeights a x i0 = 1 ∧ ∀ j, j ≠ i0 → rawWeights a x j = 0 := by
  have hsum : ∑ j, a j x = a i0 x :=
    Finset.sum_eq_single i0 (fun j _ hj => hzero j hj)
      (fun h => absurd (Finset.mem_univ i0) h)
  refine ⟨?_, fun j hj => ?_⟩
  · simp [rawWeights, hsum, div_self hne]
  · simp [rawWeights, hzero j hj]



theorem rawWeights_data {X : Type uX} {ι : Type} [Fintype ι]
    {s : Set X} {U : ι → Set X} {a : ι → X → ℝ}
    (hnn : ∀ x ∈ s, ∀ i, 0 ≤ a i x)
    (hne : ∀ x ∈ s, (∑ j, a j x) ≠ 0)
    (hactive : ∀ x ∈ s, ∀ i, a i x ≠ 0 → x ∈ U i) :
    centerAverage.WeightDataOn s U (rawWeights a) where
  nonneg x hx i := rawWeights_nonneg (hnn x hx) i
  pos x hx := rawWeights_pos (hnn x hx) (hne x hx)
  sum_one x hx := rawWeights_sum (hne x hx)
  active_mem x hx i hi := hactive x hx i (num_ne_of_raw_ne hi)



theorem cutWeights_data {X : Type uX} {ι : Type} [Fintype ι] [DecidableEq ι]
    {s : Set X} {U : ι → Set X} {cut : X → ℝ} {a : ι → X → ℝ} {i0 : ι}
    (hcut : ∀ x ∈ s, cut x ∈ Set.Icc (0 : ℝ) 1)
    (hnn : ∀ x ∈ s, ∀ i, 0 ≤ a i x)
    (hcover : ∀ x ∈ s, ∃ i, 0 < a i x)
    (hbase : ∀ x ∈ s, cut x ≠ 0 → 0 < a i0 x)
    (hactive : ∀ x ∈ s, ∀ i, a i x ≠ 0 → x ∈ U i) :
    centerAverage.WeightDataOn s U (rawWeights (cutRaw cut a i0)) := by
  apply rawWeights_data
  · intro x hx i
    exact cutRaw_nonneg (hcut x hx) (hnn x hx) i
  · intro x hx
    exact ne_of_gt (cutRaw_sum_pos (hcut x hx) (hnn x hx) (hcover x hx) (hbase x hx))
  · intro x hx i hi
    exact hactive x hx i (num_ne_of_cut_ne hi)

end HCGCompactness
end DifferentialGeometry
