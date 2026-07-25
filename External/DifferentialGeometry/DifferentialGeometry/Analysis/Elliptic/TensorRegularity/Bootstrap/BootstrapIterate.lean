import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Bootstrap.IteratedRegularityBootstrap


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter MeasureTheory Topology Function
open scoped Manifold Topology ContDiff BigOperators Matrix InnerProductSpace
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section Headline

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

local notation "dimE" => Module.finrank ℝ E

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
  [NeZero (Module.finrank ℝ E)] in

private lemma chain_step_le
    {S S' BFp BFp' L : ℝ≥0∞} {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hBF_mono : BFp ≤ BFp')
    (hlow : S ≤ ENNReal.ofReal c * (BFp + L))
    (hstep : S' ≤ ENNReal.ofReal a * (BFp' + S)) :
    S' ≤ ENNReal.ofReal (a * (1 + c)) * (BFp' + L) := by
  have hlow' : S ≤ ENNReal.ofReal c * (BFp' + L) :=
    hlow.trans (mul_le_mul_of_nonneg_left
      (add_le_add hBF_mono le_rfl) (zero_le _))
  have hsum : BFp' + S ≤ (1 + ENNReal.ofReal c) * (BFp' + L) := by
    rw [add_mul, one_mul]
    exact add_le_add (le_add_right le_rfl) hlow'
  refine hstep.trans ?_
  refine (mul_le_mul_of_nonneg_left hsum (zero_le _)).trans (le_of_eq ?_)
  rw [← mul_assoc,
    show (1 : ℝ≥0∞) + ENNReal.ofReal c = ENNReal.ofReal (1 + c) from by
      rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hc, ENNReal.ofReal_one],
    ← ENNReal.ofReal_mul ha]

omit [NeZero dimE] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma sum_componentNorm_mono_order
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (F : SmoothCcTensor g r s)
    (α : M) {Ω'' : Set EuclN} {n n' : ℕ} (hn : n ≤ n') :
    (∑ Q : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) n 2
        (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') ≤
      ∑ Q : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) n' 2
        (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'' :=
  Finset.sum_le_sum (fun _Q _ => wkpNorm_mono_order (d := dimE) hn _ _)

set_option maxHeartbeats 3200000 in

theorem tensorComponent_aPriori_estimate
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (k : ℕ) (P₀ : CompIdx E r s)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (hΩ''_target : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hK_Ω'' : K ⊆ Ω'') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T F : SmoothCcTensor g r s),
      tsupport T.toFun ⊆ (chartAt H α).source →
      tsupport F.toFun ⊆ (chartAt H α).source →
      (∀ P : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) ⊆ K) →
      (∀ Q : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s F α Q) ⊆ K) →
      (∀ v : SmoothCcTensor g r s,
        ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) →
      iteratedWeakSobolevNorm (d := dimE) (2 * k + 2) 2
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) Ω'' ≤
        ENNReal.ofReal C *
          ((∑ Q : CompIdx E r s,
              iteratedWeakSobolevNorm (d := dimE) (2 * k) 2
                (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') +
            ∑ P : CompIdx E r s,
              iteratedWeakSobolevNorm (d := dimE) 1 2
                (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') := by
  classical
  suffices h_tuple : ∃ C : ℝ, 0 ≤ C ∧ ∀ (T F : SmoothCcTensor g r s),
      tsupport T.toFun ⊆ (chartAt H α).source →
      tsupport F.toFun ⊆ (chartAt H α).source →
      (∀ P : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) ⊆ K) →
      (∀ Q : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s F α Q) ⊆ K) →
      (∀ v : SmoothCcTensor g r s,
        ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) →
      (∑ P : CompIdx E r s,
        iteratedWeakSobolevNorm (d := dimE) (2 * k + 2) 2
          (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') ≤
        ENNReal.ofReal C *
          ((∑ Q : CompIdx E r s,
              iteratedWeakSobolevNorm (d := dimE) (2 * k) 2
                (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') +
            ∑ P : CompIdx E r s,
              iteratedWeakSobolevNorm (d := dimE) 1 2
                (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') by
    obtain ⟨C, hC_nn, hC⟩ := h_tuple
    refine ⟨C, hC_nn, fun T F hT_supp hF_supp hT_K hF_K hweak => ?_⟩
    exact (Finset.single_le_sum
      (f := fun P : CompIdx E r s => iteratedWeakSobolevNorm (d := dimE) (2 * k + 2) 2
        (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'')
      (fun P _ => zero_le _) (Finset.mem_univ P₀)).trans
        (hC T F hT_supp hF_supp hT_K hF_K hweak)
  induction k with
  | zero =>
      obtain ⟨C, hC_nn, hC⟩ :=
        tensorComponent_aPriori_succ_sum (I := I) (M := M) g r s α hK hK_target
          0 hΩ''_open hΩ''_compact_closure hΩ''_target hK_Ω''
      refine ⟨C, hC_nn, fun T F hT_supp hF_supp hT_K hF_K hweak => ?_⟩
      have h := hC T F hT_supp hF_supp hT_K hF_K hweak
      simpa using h
  | succ k ih =>
      obtain ⟨Ck, hCk_nn, hCk⟩ := ih
      obtain ⟨A, hA_nn, hA⟩ :=
        tensorComponent_aPriori_succ_sum (I := I) (M := M) g r s α hK hK_target
          (2 * k + 1) hΩ''_open hΩ''_compact_closure hΩ''_target hK_Ω''
      obtain ⟨B, hB_nn, hB⟩ :=
        tensorComponent_aPriori_succ_sum (I := I) (M := M) g r s α hK hK_target
          (2 * k + 2) hΩ''_open hΩ''_compact_closure hΩ''_target hK_Ω''
      refine ⟨B * (1 + A * (1 + Ck)), by positivity,
        fun T F hT_supp hF_supp hT_K hF_K hweak => ?_⟩
      set L : ℝ≥0∞ := ∑ P : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) 1 2
        (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'' with hL_def
      have h_ih := hCk T F hT_supp hF_supp hT_K hF_K hweak
      have h_step1 := hA T F hT_supp hF_supp hT_K hF_K hweak
      have h_step2 := hB T F hT_supp hF_supp hT_K hF_K hweak
      have h_23 :
          (∑ P : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) (2 * k + 1 + 2) 2
            (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') ≤
          ENNReal.ofReal (A * (1 + Ck)) *
            ((∑ Q : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) (2 * k + 1) 2
                (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') +
              L) :=
        chain_step_le hA_nn hCk_nn
          (sum_componentNorm_mono_order (I := I) (M := M) g r s F α
            (Ω'' := Ω'') (by omega : 2 * k ≤ 2 * k + 1))
          h_ih h_step1
      have h_24 :
          (∑ P : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) (2 * k + 2 + 2) 2
            (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') ≤
          ENNReal.ofReal (B * (1 + A * (1 + Ck))) *
            ((∑ Q : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) (2 * k + 2) 2
                (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') +
              L) :=
        chain_step_le hB_nn (by positivity)
          (sum_componentNorm_mono_order (I := I) (M := M) g r s F α
            (Ω'' := Ω'') (by omega : 2 * k + 1 ≤ 2 * k + 2))
          h_23 h_step2
      have h_lhs : 2 * k + 2 + 2 = 2 * (k + 1) + 2 := by ring
      have h_rhs : 2 * k + 2 = 2 * (k + 1) := by ring
      rw [h_lhs, h_rhs] at h_24
      exact h_24

theorem tensorComponent_aPriori_estimate_all
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (k : ℕ)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (hΩ''_target : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hK_Ω'' : K ⊆ Ω'') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P₀ : CompIdx E r s) (T F : SmoothCcTensor g r s),
      tsupport T.toFun ⊆ (chartAt H α).source →
      tsupport F.toFun ⊆ (chartAt H α).source →
      (∀ P : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) ⊆ K) →
      (∀ Q : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s F α Q) ⊆ K) →
      (∀ v : SmoothCcTensor g r s,
        ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) →
      iteratedWeakSobolevNorm (d := dimE) (2 * k + 2) 2
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) Ω'' ≤
        ENNReal.ofReal C *
          ((∑ Q : CompIdx E r s,
              iteratedWeakSobolevNorm (d := dimE) (2 * k) 2
                (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') +
            ∑ P : CompIdx E r s,
              iteratedWeakSobolevNorm (d := dimE) 1 2
                (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') := by
  classical
  have h_per : ∀ P₀ : CompIdx E r s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T F : SmoothCcTensor g r s),
        tsupport T.toFun ⊆ (chartAt H α).source →
        tsupport F.toFun ⊆ (chartAt H α).source →
        (∀ P : CompIdx E r s,
          tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) ⊆ K) →
        (∀ Q : CompIdx E r s,
          tsupport (tensorComponentEuclid (I := I) (M := M) g r s F α Q) ⊆ K) →
        (∀ v : SmoothCcTensor g r s,
          ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
            tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) →
        iteratedWeakSobolevNorm (d := dimE) (2 * k + 2) 2
            (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) Ω'' ≤
          ENNReal.ofReal C *
            ((∑ Q : CompIdx E r s,
                iteratedWeakSobolevNorm (d := dimE) (2 * k) 2
                  (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') +
              ∑ P : CompIdx E r s,
                iteratedWeakSobolevNorm (d := dimE) 1 2
                  (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') :=
    fun P₀ => tensorComponent_aPriori_estimate (I := I) (M := M) g r s α hK
      hK_target k P₀ hΩ''_open hΩ''_compact_closure hΩ''_target hK_Ω''
  choose Cf hCf_nn hCf using h_per
  have hCI_ne : (Finset.univ : Finset (CompIdx E r s)).Nonempty :=
    ⟨Classical.arbitrary (CompIdx E r s), Finset.mem_univ _⟩
  refine ⟨(Finset.univ : Finset (CompIdx E r s)).sup' hCI_ne Cf, ?_, ?_⟩
  · exact le_trans (hCf_nn (Classical.arbitrary (CompIdx E r s)))
      (Finset.le_sup' Cf (Finset.mem_univ _))
  · intro P₀ T F hT_supp hF_supp hT_K hF_K hweak
    refine (hCf P₀ T F hT_supp hF_supp hT_K hF_K hweak).trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (Finset.le_sup' Cf (Finset.mem_univ P₀)))
      (zero_le _)

end Headline

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
