import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Bootstrap.BootstrapSource

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
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section Headline

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

local notation "dimE" => Module.finrank ℝ E

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero dimE] in
private lemma exists_densityMul_sourcePairingCoeff_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {K : Set EuclN}
    (hK : IsCompact K) (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (m : ℕ) (P₀ : CompIdx E r s) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ {F : SmoothCcTensor g r s},
      tsupport F.toFun ⊆ (chartAt H α).source →
      (∀ P : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s F α P) ⊆ K) →
      ∀ {Ω'' : Set EuclN}, IsOpen Ω'' →
      Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemWkp (d := dimE) m 2
          (fun y => densityOnEuclid (I := I) g α y *
            sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y) Ω'' ∧
        iteratedWeakSobolevNorm (d := dimE) m 2
            (fun y => densityOnEuclid (I := I) g α y *
              sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y) Ω'' ≤
          ENNReal.ofReal Kc *
            ∑ P : CompIdx E r s,
              iteratedWeakSobolevNorm (d := dimE) m 2
                (tensorComponentEuclid (I := I) (M := M) g r s F α P) Ω'' := by
  classical
  set cF : CompIdx E r s × CompIdx E r s → EuclN → ℝ :=
    fun a y => densityOnEuclid (I := I) g α y *
      gramInvEntry (I := I) (M := M) g r s α a.1 P₀ y *
      covChartMetricGram (I := I) (M := M) g r s α a.2 a.1 y with hcF_def
  have hcF_cd : ∀ a ∈ (Finset.univ : Finset (CompIdx E r s × CompIdx E r s)),
      ContDiffOn ℝ ∞ (cF a) (chartTargetEuclid (I := I) (M := M) α) := by
    intro a _
    exact ((densityOnEuclid_contDiffOn (I := I) g α).mul
      (gramInvEntry_contDiffOn (I := I) (M := M) g r s α a.1 P₀)).mul
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α a.2 a.1)
  obtain ⟨Kc, hKc_nn, hKc⟩ :=
    exists_wkpNorm_chartCoeffSum_bddBy (I := I) (M := M) α hK hK_target m
      Finset.univ cF hcF_cd
  refine ⟨Kc, hKc_nn, ?_⟩
  intro F hF_supp hF_K Ω'' hΩ''_open hΩ''_target
  set vF : CompIdx E r s × CompIdx E r s → EuclN → ℝ :=
    fun a => tensorComponentEuclid (I := I) (M := M) g r s F α a.2 with hvF_def
  have hvF_cd : ∀ a ∈ (Finset.univ : Finset (CompIdx E r s × CompIdx E r s)),
      ContDiff ℝ ∞ (vF a) := fun a _ =>
    tensorComponentEuclid_contDiff (I := I) (M := M) g r s F α a.2 hF_supp
  have hvF_cpt : ∀ a ∈ (Finset.univ : Finset (CompIdx E r s × CompIdx E r s)),
      HasCompactSupport (vF a) := fun a _ =>
    tensorComponentEuclid_hasCompactSupport (I := I) (M := M) g r s F α a.2 hF_supp
  have hvF_K : ∀ a ∈ (Finset.univ : Finset (CompIdx E r s × CompIdx E r s)),
      tsupport (vF a) ⊆ K := fun a _ => hF_K a.2
  have hvF_bd : ∀ a ∈ (Finset.univ : Finset (CompIdx E r s × CompIdx E r s)),
      iteratedWeakSobolevNorm (d := dimE) m 2 (vF a) Ω'' ≤
        ∑ P : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) m 2
          (tensorComponentEuclid (I := I) (M := M) g r s F α P) Ω'' := by
    intro a _
    exact Finset.single_le_sum
      (f := fun P => iteratedWeakSobolevNorm (d := dimE) m 2
        (tensorComponentEuclid (I := I) (M := M) g r s F α P) Ω'')
      (fun P _ => zero_le _) (Finset.mem_univ a.2)
  obtain ⟨h_sum_mem, h_sum_le⟩ :=
    hKc hvF_cd hvF_cpt hvF_K hΩ''_open hΩ''_target hvF_bd
  have h_eqOn : Set.EqOn
      (fun y => densityOnEuclid (I := I) g α y *
        sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y)
      (fun y => ∑ a ∈ Finset.univ, cF a y * vF a y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro y _
    change densityOnEuclid (I := I) g α y *
        sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y =
      ∑ a : CompIdx E r s × CompIdx E r s, cF a y * vF a y
    have h_rhs : (∑ a : CompIdx E r s × CompIdx E r s, cF a y * vF a y) =
        ∑ Q : CompIdx E r s, ∑ P : CompIdx E r s,
          cF (Q, P) y * vF (Q, P) y :=
      Fintype.sum_prod_type _
    rw [h_rhs]
    simp only [hcF_def, hvF_def, sourcePairingCoeff_def, gramInvEntry,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun Q _ => Finset.sum_congr rfl fun P _ => ?_
    ring
  have h_ae : (fun y => densityOnEuclid (I := I) g α y *
      sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y)
      =ᵐ[volume.restrict Ω''] (fun y => ∑ a ∈ Finset.univ, cF a y * vF a y) :=
    eqOn_open_imp_ae_restrict (E := E) hΩ''_open
      (h_eqOn.mono hΩ''_target)
  refine ⟨(MemWkp_congr_ae (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hΩ''_open h_ae).mpr h_sum_mem, ?_⟩
  rw [wkpNorm_congr_ae (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hΩ''_open h_ae]
  exact h_sum_le

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero dimE] in
private lemma exists_densityMul_covPrincipalRotationCoeff_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {K : Set EuclN}
    (hK : IsCompact K) (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (m : ℕ) (P₀ : CompIdx E r s) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ {T : SmoothCcTensor g r s},
      tsupport T.toFun ⊆ (chartAt H α).source →
      (∀ P : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) ⊆ K) →
      ∀ {Ω'' : Set EuclN}, IsOpen Ω'' →
      Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemWkp (d := dimE) m 2
          (fun y => densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y) Ω'' ∧
        iteratedWeakSobolevNorm (d := dimE) m 2
            (fun y => densityOnEuclid (I := I) g α y *
              covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y) Ω'' ≤
          ENNReal.ofReal Kc *
            ∑ P : CompIdx E r s,
              iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
                (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'' := by
  classical
  set Idx := CompIdx E r s × CompIdx E r s × Fin dimE × Fin dimE
  set cT : Idx → EuclN → ℝ :=
    fun a y => densityOnEuclid (I := I) g α y *
      covChartMetricGram (I := I) (M := M) g r s α a.1 a.2.1 y *
      chartInvGramEuclid (I := I) g α a.2.2.1 a.2.2.2 y *
      euclidPartial (E := E) a.2.2.2
        (gramInvEntry (I := I) (M := M) g r s α a.2.1 P₀) y with hcT_def
  have hcT_cd : ∀ a ∈ (Finset.univ : Finset Idx),
      ContDiffOn ℝ ∞ (cT a) (chartTargetEuclid (I := I) (M := M) α) := by
    intro a _
    refine (((densityOnEuclid_contDiffOn (I := I) g α).mul
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α a.1 a.2.1)).mul
      (chartInvGramEuclid_contDiffOn (I := I) g α a.2.2.1 a.2.2.2)).mul ?_
    exact euclidPartial_contDiffOn_target (I := I) (M := M) α a.2.2.2
      (gramInvEntry_contDiffOn (I := I) (M := M) g r s α a.2.1 P₀)
  obtain ⟨Kc, hKc_nn, hKc⟩ :=
    exists_wkpNorm_chartCoeffSum_bddBy (I := I) (M := M) α hK hK_target m
      Finset.univ cT hcT_cd
  refine ⟨Kc, hKc_nn, ?_⟩
  intro T hT_supp hT_K Ω'' hΩ''_open hΩ''_target
  set vT : Idx → EuclN → ℝ :=
    fun a => euclidPartial (E := E) a.2.2.1
      (tensorComponentEuclid (I := I) (M := M) g r s T α a.1) with hvT_def
  have hT_comp_cd : ∀ P : CompIdx E r s,
      ContDiff ℝ ∞ (tensorComponentEuclid (I := I) (M := M) g r s T α P) :=
    fun P => tensorComponentEuclid_contDiff (I := I) (M := M) g r s T α P hT_supp
  have hvT_cd : ∀ a ∈ (Finset.univ : Finset Idx), ContDiff ℝ ∞ (vT a) :=
    fun a _ => euclidPartial_contDiff (E := E) (hT_comp_cd a.1) a.2.2.1
  have hvT_cpt : ∀ a ∈ (Finset.univ : Finset Idx), HasCompactSupport (vT a) :=
    fun a _ => euclidPartial_hasCompactSupport (E := E) hK (hT_K a.1) a.2.2.1
  have hvT_K : ∀ a ∈ (Finset.univ : Finset Idx), tsupport (vT a) ⊆ K :=
    fun a _ => (euclidPartial_tsupport_subset (E := E) a.2.2.1).trans (hT_K a.1)
  have hvT_bd : ∀ a ∈ (Finset.univ : Finset Idx),
      iteratedWeakSobolevNorm (d := dimE) m 2 (vT a) Ω'' ≤
        ∑ P : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
          (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'' := by
    intro a _
    have h_mem_succ : MemWkp (d := dimE) (m + 1) 2
        (tensorComponentEuclid (I := I) (M := M) g r s T α a.1) Ω'' :=
      memWkp_of_smooth_compactSupport_anyOpen (d := dimE) hΩ''_open
        (by simpa using hT_comp_cd a.1)
        (tensorComponentEuclid_hasCompactSupport (I := I) (M := M)
          g r s T α a.1 hT_supp) (by norm_num : (1 : ℝ≥0∞) ≤ 2) (m + 1)
    refine (wkpNorm_euclidPartial_le (E := E) hΩ''_open
      (hT_comp_cd a.1) h_mem_succ a.2.2.1).trans ?_
    exact Finset.single_le_sum
      (f := fun P => iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
        (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'')
      (fun P _ => zero_le _) (Finset.mem_univ a.1)
  obtain ⟨h_sum_mem, h_sum_le⟩ :=
    hKc hvT_cd hvT_cpt hvT_K hΩ''_open hΩ''_target hvT_bd
  have h_eqOn : Set.EqOn
      (fun y => densityOnEuclid (I := I) g α y *
        covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y)
      (fun y => ∑ a ∈ Finset.univ, cT a y * vT a y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro y _
    change densityOnEuclid (I := I) g α y *
        covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y =
      ∑ a : Idx, cT a y * vT a y
    have h_rhs : (∑ a : Idx, cT a y * vT a y) =
        ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          ∑ k : Fin dimE, ∑ l : Fin dimE,
            cT (P, Q, k, l) y * vT (P, Q, k, l) y :=
      (Fintype.sum_prod_type _).trans
        (Fintype.sum_congr _ _ fun _ => (Fintype.sum_prod_type _).trans
          (Fintype.sum_congr _ _ fun _ => Fintype.sum_prod_type _))
    rw [h_rhs]
    simp only [covPrincipalRotationCoeff_def, hcT_def, hvT_def,
      tensorComponentEuclid_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have h_ae : (fun y => densityOnEuclid (I := I) g α y *
      covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y)
      =ᵐ[volume.restrict Ω''] (fun y => ∑ a ∈ Finset.univ, cT a y * vT a y) :=
    eqOn_open_imp_ae_restrict (E := E) hΩ''_open
      (h_eqOn.mono hΩ''_target)
  refine ⟨(MemWkp_congr_ae (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hΩ''_open h_ae).mpr h_sum_mem, ?_⟩
  rw [wkpNorm_congr_ae (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hΩ''_open h_ae]
  exact h_sum_le

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero dimE] in
private lemma exists_densityMul_covLowerOrderRotationValueCoeff_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {K : Set EuclN}
    (hK : IsCompact K) (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (m : ℕ) (P₀ : CompIdx E r s) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ {T : SmoothCcTensor g r s},
      tsupport T.toFun ⊆ (chartAt H α).source →
      (∀ P : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) ⊆ K) →
      ∀ {Ω'' : Set EuclN}, IsOpen Ω'' →
      Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemWkp (d := dimE) m 2
          (fun y => densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y)
          Ω'' ∧
        iteratedWeakSobolevNorm (d := dimE) m 2
            (fun y => densityOnEuclid (I := I) g α y *
              covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y)
            Ω'' ≤
          ENNReal.ofReal Kc *
            ∑ P : CompIdx E r s,
              iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
                (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'' := by
  classical
  set IdxA := CompIdx E r s × CompIdx E r s × Fin dimE × Fin dimE
  set IdxBC := CompIdx E r s × CompIdx E r s × Fin dimE × Fin dimE × CompIdx E r s
  set cA : IdxA → EuclN → ℝ :=
    fun a y => densityOnEuclid (I := I) g α y *
      covChartMetricGram (I := I) (M := M) g r s α a.1 a.2.1 y *
      chartInvGramEuclid (I := I) g α a.2.2.1 a.2.2.2 y *
      lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ a.2.2.2 a.2.1 y
      with hcA_def
  set cBC : IdxBC → EuclN → ℝ :=
    fun a y => densityOnEuclid (I := I) g α y *
      covChartMetricGram (I := I) (M := M) g r s α a.1 a.2.1 y *
      chartInvGramEuclid (I := I) g α a.2.2.1 a.2.2.2.1 y *
      covDerivLowerOrderCoeff (I := I) (M := M) g r s α a.2.2.1
        a.1.1 a.2.2.2.2.1 a.1.2 a.2.2.2.2.2 y *
      (euclidPartial (E := E) a.2.2.2.1
          (gramInvEntry (I := I) (M := M) g r s α a.2.1 P₀) y +
        lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀
          a.2.2.2.1 a.2.1 y) with hcBC_def
  have hcA_cd : ∀ a ∈ (Finset.univ : Finset IdxA),
      ContDiffOn ℝ ∞ (cA a) (chartTargetEuclid (I := I) (M := M) α) := by
    intro a _
    exact (((densityOnEuclid_contDiffOn (I := I) g α).mul
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α a.1 a.2.1)).mul
      (chartInvGramEuclid_contDiffOn (I := I) g α a.2.2.1 a.2.2.2)).mul
      (lowerOrderRotationLOCoeff_contDiffOn (I := I) (M := M)
        g r s α P₀ a.2.2.2 a.2.1)
  have hcBC_cd : ∀ a ∈ (Finset.univ : Finset IdxBC),
      ContDiffOn ℝ ∞ (cBC a) (chartTargetEuclid (I := I) (M := M) α) := by
    intro a _
    refine ((((densityOnEuclid_contDiffOn (I := I) g α).mul
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α a.1 a.2.1)).mul
      (chartInvGramEuclid_contDiffOn (I := I) g α a.2.2.1 a.2.2.2.1)).mul
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α a.2.2.1
        a.1.1 a.2.2.2.2.1 a.1.2 a.2.2.2.2.2)).mul ?_
    exact (euclidPartial_contDiffOn_target (I := I) (M := M) α a.2.2.2.1
      (gramInvEntry_contDiffOn (I := I) (M := M) g r s α a.2.1 P₀)).add
      (lowerOrderRotationLOCoeff_contDiffOn (I := I) (M := M)
        g r s α P₀ a.2.2.2.1 a.2.1)
  obtain ⟨KcA, hKcA_nn, hKcA⟩ :=
    exists_wkpNorm_chartCoeffSum_bddBy (I := I) (M := M) α hK hK_target m
      Finset.univ cA hcA_cd
  obtain ⟨KcBC, hKcBC_nn, hKcBC⟩ :=
    exists_wkpNorm_chartCoeffSum_bddBy (I := I) (M := M) α hK hK_target m
      Finset.univ cBC hcBC_cd
  refine ⟨KcA + KcBC, by positivity, ?_⟩
  intro T hT_supp hT_K Ω'' hΩ''_open hΩ''_target
  have hT_comp_cd : ∀ P : CompIdx E r s,
      ContDiff ℝ ∞ (tensorComponentEuclid (I := I) (M := M) g r s T α P) :=
    fun P => tensorComponentEuclid_contDiff (I := I) (M := M) g r s T α P hT_supp
  have hT_comp_succ : ∀ P : CompIdx E r s, MemWkp (d := dimE) (m + 1) 2
      (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'' :=
    fun P => memWkp_of_smooth_compactSupport_anyOpen (d := dimE) hΩ''_open
      (by simpa using hT_comp_cd P)
      (tensorComponentEuclid_hasCompactSupport (I := I) (M := M)
        g r s T α P hT_supp) (by norm_num : (1 : ℝ≥0∞) ≤ 2) (m + 1)
  set vA : IdxA → EuclN → ℝ :=
    fun a => euclidPartial (E := E) a.2.2.1
      (tensorComponentEuclid (I := I) (M := M) g r s T α a.1) with hvA_def
  have hvA_cd : ∀ a ∈ (Finset.univ : Finset IdxA), ContDiff ℝ ∞ (vA a) :=
    fun a _ => euclidPartial_contDiff (E := E) (hT_comp_cd a.1) a.2.2.1
  have hvA_cpt : ∀ a ∈ (Finset.univ : Finset IdxA), HasCompactSupport (vA a) :=
    fun a _ => euclidPartial_hasCompactSupport (E := E) hK (hT_K a.1) a.2.2.1
  have hvA_K : ∀ a ∈ (Finset.univ : Finset IdxA), tsupport (vA a) ⊆ K :=
    fun a _ => (euclidPartial_tsupport_subset (E := E) a.2.2.1).trans (hT_K a.1)
  have hvA_bd : ∀ a ∈ (Finset.univ : Finset IdxA),
      iteratedWeakSobolevNorm (d := dimE) m 2 (vA a) Ω'' ≤
        ∑ P : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
          (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'' := by
    intro a _
    refine (wkpNorm_euclidPartial_le (E := E) hΩ''_open
      (hT_comp_cd a.1) (hT_comp_succ a.1) a.2.2.1).trans ?_
    exact Finset.single_le_sum
      (f := fun P => iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
        (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'')
      (fun P _ => zero_le _) (Finset.mem_univ a.1)
  set vBC : IdxBC → EuclN → ℝ :=
    fun a => tensorComponentEuclid (I := I) (M := M) g r s T α a.2.2.2.2
      with hvBC_def
  have hvBC_cd : ∀ a ∈ (Finset.univ : Finset IdxBC), ContDiff ℝ ∞ (vBC a) :=
    fun a _ => hT_comp_cd a.2.2.2.2
  have hvBC_cpt : ∀ a ∈ (Finset.univ : Finset IdxBC),
      HasCompactSupport (vBC a) := fun a _ =>
    tensorComponentEuclid_hasCompactSupport (I := I) (M := M)
      g r s T α a.2.2.2.2 hT_supp
  have hvBC_K : ∀ a ∈ (Finset.univ : Finset IdxBC),
      tsupport (vBC a) ⊆ K := fun a _ => hT_K a.2.2.2.2
  have hvBC_bd : ∀ a ∈ (Finset.univ : Finset IdxBC),
      iteratedWeakSobolevNorm (d := dimE) m 2 (vBC a) Ω'' ≤
        ∑ P : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
          (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'' := by
    intro a _
    refine (wkpNorm_mono_order (d := dimE) (Nat.le_succ m) (vBC a) Ω'').trans ?_
    exact Finset.single_le_sum
      (f := fun P => iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
        (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'')
      (fun P _ => zero_le _) (Finset.mem_univ a.2.2.2.2)
  obtain ⟨hA_mem, hA_le⟩ :=
    hKcA hvA_cd hvA_cpt hvA_K hΩ''_open hΩ''_target hvA_bd
  obtain ⟨hBC_mem, hBC_le⟩ :=
    hKcBC hvBC_cd hvBC_cpt hvBC_K hΩ''_open hΩ''_target hvBC_bd
  have h_eqOn : Set.EqOn
      (fun y => densityOnEuclid (I := I) g α y *
        covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y)
      (fun y => (∑ a : IdxA, cA a y * vA a y) +
        ∑ a : IdxBC, cBC a y * vBC a y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro y hy
    change densityOnEuclid (I := I) g α y *
        covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y =
      (∑ a : IdxA, cA a y * vA a y) + ∑ a : IdxBC, cBC a y * vBC a y
    have hA_rhs : (∑ a : IdxA, cA a y * vA a y) =
        ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          ∑ k : Fin dimE, ∑ l : Fin dimE,
            cA (P, Q, k, l) y * vA (P, Q, k, l) y :=
      (Fintype.sum_prod_type _).trans
        (Fintype.sum_congr _ _ fun _ => (Fintype.sum_prod_type _).trans
          (Fintype.sum_congr _ _ fun _ => Fintype.sum_prod_type _))
    have hBC_rhs : (∑ a : IdxBC, cBC a y * vBC a y) =
        ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          ∑ k : Fin dimE, ∑ l : Fin dimE, ∑ p : CompIdx E r s,
            cBC (P, Q, k, l, p) y * vBC (P, Q, k, l, p) y :=
      (Fintype.sum_prod_type _).trans
        (Fintype.sum_congr _ _ fun _ => (Fintype.sum_prod_type _).trans
          (Fintype.sum_congr _ _ fun _ => (Fintype.sum_prod_type _).trans
            (Fintype.sum_congr _ _ fun _ => Fintype.sum_prod_type _)))
    rw [hA_rhs, hBC_rhs, covLowerOrderRotationValueCoeff_def]
    simp only [hcA_def, hcBC_def, hvA_def, hvBC_def,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [covDerivLowerOrderTerm_eq_sum_componentEuclid (I := I) (M := M)
      g r s T α k P.1 P.2 hy,
      ← tensorComponentEuclid_def (I := I) (M := M) g r s T α P]
    rw [show densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          (chartInvGramEuclid (I := I) g α k l y *
            (euclidPartial (E := E) k
                (tensorComponentEuclid (I := I) (M := M) g r s T α P) y *
              lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y +
            (∑ p : CompIdx E r s,
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α k P.1 p.1
                P.2 p.2 y *
                tensorComponentEuclid (I := I) (M := M) g r s T α p y) *
              euclidPartial (E := E) l
                (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
            (∑ p : CompIdx E r s,
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α k P.1 p.1
                P.2 p.2 y *
                tensorComponentEuclid (I := I) (M := M) g r s T α p y) *
              lowerOrderRotationLOCoeff (I := I) (M := M)
                g r s α P₀ l Q y))) =
        densityOnEuclid (I := I) g α y *
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
            chartInvGramEuclid (I := I) g α k l y *
            lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y *
            euclidPartial (E := E) k
              (tensorComponentEuclid (I := I) (M := M) g r s T α P) y +
          densityOnEuclid (I := I) g α y *
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
            chartInvGramEuclid (I := I) g α k l y *
            ((∑ p : CompIdx E r s,
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α k P.1 p.1
                P.2 p.2 y *
                tensorComponentEuclid (I := I) (M := M) g r s T α p y) *
              (euclidPartial (E := E) l
                  (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
                lowerOrderRotationLOCoeff (I := I) (M := M)
                  g r s α P₀ l Q y)) from by ring]
    rw [Finset.sum_mul, Finset.mul_sum]
    refine congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun p _ => by ring)
  have h_ae : (fun y => densityOnEuclid (I := I) g α y *
      covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y)
      =ᵐ[volume.restrict Ω''] (fun y => (∑ a : IdxA, cA a y * vA a y) +
        ∑ a : IdxBC, cBC a y * vBC a y) :=
    eqOn_open_imp_ae_restrict (E := E) hΩ''_open (h_eqOn.mono hΩ''_target)
  have h_sum_mem : MemWkp (d := dimE) m 2
      (fun y => (∑ a : IdxA, cA a y * vA a y) +
        ∑ a : IdxBC, cBC a y * vBC a y) Ω'' :=
    MemWkp.add (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ''_open
      hA_mem hBC_mem
  refine ⟨(MemWkp_congr_ae (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hΩ''_open h_ae).mpr h_sum_mem, ?_⟩
  rw [wkpNorm_congr_ae (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hΩ''_open h_ae]
  refine (wkpNorm_add_le (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hΩ''_open hA_mem hBC_mem).trans ?_
  rw [ENNReal.ofReal_add hKcA_nn hKcBC_nn, add_mul]
  exact add_le_add hA_le hBC_le

private noncomputable def weightedGradChartCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) (P₀ : CompIdx E r s)
    (l : Fin dimE)
    (a : CompIdx E r s × CompIdx E r s × Fin dimE × CompIdx E r s) :
    EuclN → ℝ :=
  fun y => densityOnEuclid (I := I) g α y *
    covChartMetricGram (I := I) (M := M) g r s α a.1 a.2.1 y *
    chartInvGramEuclid (I := I) g α a.2.2.1 l y *
    covDerivLowerOrderCoeff (I := I) (M := M) g r s α a.2.2.1
      a.1.1 a.2.2.2.1 a.1.2 a.2.2.2.2 y *
    covChartMetricGramInv (I := I) (M := M) g r s α y a.2.1 P₀

omit [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
omit [NeZero dimE] in
private lemma weightedGradChartCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) (P₀ : CompIdx E r s)
    (l : Fin dimE)
    (a : CompIdx E r s × CompIdx E r s × Fin dimE × CompIdx E r s) :
    ContDiffOn ℝ ∞ (weightedGradChartCoeff (I := I) (M := M) g r s α P₀ l a)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold weightedGradChartCoeff
  exact ((((densityOnEuclid_contDiffOn (I := I) g α).mul
    (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α a.1 a.2.1)).mul
    (chartInvGramEuclid_contDiffOn (I := I) g α a.2.2.1 l)).mul
    (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α a.2.2.1
      a.1.1 a.2.2.2.1 a.1.2 a.2.2.2.2)).mul
    (covChartMetricGramInv_entry_contDiffOn (I := I) (M := M)
      g r s α a.2.1 P₀)

omit [NeZero dimE] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma weightedGradCoeff_eq_chartCoeffSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (P₀ : CompIdx E r s)
    (l : Fin dimE) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y =
      ∑ a : CompIdx E r s × CompIdx E r s × Fin dimE × CompIdx E r s,
        weightedGradChartCoeff (I := I) (M := M) g r s α P₀ l a y *
          tensorComponentEuclid (I := I) (M := M) g r s T α a.2.2.2 y := by
  classical
  have h_rhs : (∑ a : CompIdx E r s × CompIdx E r s × Fin dimE × CompIdx E r s,
      weightedGradChartCoeff (I := I) (M := M) g r s α P₀ l a y *
        tensorComponentEuclid (I := I) (M := M) g r s T α a.2.2.2 y) =
      ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s, ∑ k : Fin dimE,
        ∑ p : CompIdx E r s,
          weightedGradChartCoeff (I := I) (M := M) g r s α P₀ l (P, Q, k, p) y *
            tensorComponentEuclid (I := I) (M := M) g r s T α p y :=
    (Fintype.sum_prod_type _).trans
      (Fintype.sum_congr _ _ fun _ => (Fintype.sum_prod_type _).trans
        (Fintype.sum_congr _ _ fun _ => Fintype.sum_prod_type _))
  rw [show weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y =
      densityOnEuclid (I := I) g α y *
        covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y
    from rfl, covLowerOrderRotationGradCoeff_def, h_rhs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [covDerivLowerOrderTerm_eq_sum_componentEuclid (I := I) (M := M)
    g r s T α k P.1 P.2 hy, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold weightedGradChartCoeff
  ring

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero dimE] in
private lemma exists_gradientGroup_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {K : Set EuclN}
    (hK : IsCompact K) (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (m : ℕ) (P₀ : CompIdx E r s) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ {T : SmoothCcTensor g r s},
      tsupport T.toFun ⊆ (chartAt H α).source →
      (∀ P : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) ⊆ K) →
      ∀ {Ω'' : Set EuclN}, IsOpen Ω'' →
      Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemWkp (d := dimE) m 2
          (fun y => ∑ l : Fin dimE, euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y) Ω'' ∧
        iteratedWeakSobolevNorm (d := dimE) m 2
            (fun y => ∑ l : Fin dimE, euclidPartial (E := E) l
              (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y) Ω'' ≤
          ENNReal.ofReal Kc *
            ∑ P : CompIdx E r s,
              iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
                (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'' := by
  classical
  have hper : ∀ l : Fin dimE, ∃ Kl : ℝ, 0 ≤ Kl ∧ ∀ {v : (CompIdx E r s ×
      CompIdx E r s × Fin dimE × CompIdx E r s) → EuclN → ℝ},
      (∀ a ∈ (Finset.univ : Finset _), ContDiff ℝ ∞ (v a)) →
      (∀ a ∈ (Finset.univ : Finset _), HasCompactSupport (v a)) →
      (∀ a ∈ (Finset.univ : Finset _), tsupport (v a) ⊆ K) →
      ∀ {Ω'' : Set EuclN}, IsOpen Ω'' →
      Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α → ∀ {G : ℝ≥0∞},
      (∀ a ∈ (Finset.univ : Finset _),
        iteratedWeakSobolevNorm (d := dimE) (m + 1) 2 (v a) Ω'' ≤ G) →
      MemWkp (d := dimE) (m + 1) 2
        (fun y => ∑ a ∈ Finset.univ,
          weightedGradChartCoeff (I := I) (M := M) g r s α P₀ l a y *
            v a y) Ω'' ∧
        iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
          (fun y => ∑ a ∈ Finset.univ,
            weightedGradChartCoeff (I := I) (M := M) g r s α P₀ l a y *
              v a y) Ω'' ≤ ENNReal.ofReal Kl * G :=
    fun l => exists_wkpNorm_chartCoeffSum_bddBy (I := I) (M := M)
      α hK hK_target (m + 1) Finset.univ
      (weightedGradChartCoeff (I := I) (M := M) g r s α P₀ l)
      (fun a _ => weightedGradChartCoeff_contDiffOn (I := I) (M := M)
        g r s α P₀ l a)
  choose Kl hKl_nn hKl using hper
  refine ⟨∑ l : Fin dimE, Kl l, Finset.sum_nonneg (fun l _ => hKl_nn l), ?_⟩
  intro T hT_supp hT_K Ω'' hΩ''_open hΩ''_target
  have hT_comp_cd : ∀ P : CompIdx E r s,
      ContDiff ℝ ∞ (tensorComponentEuclid (I := I) (M := M) g r s T α P) :=
    fun P => tensorComponentEuclid_contDiff (I := I) (M := M) g r s T α P hT_supp
  have hT_comp_cpt : ∀ P : CompIdx E r s,
      HasCompactSupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) :=
    fun P => tensorComponentEuclid_hasCompactSupport (I := I) (M := M)
      g r s T α P hT_supp
  set Wext : Fin dimE → EuclN → ℝ :=
    fun l y => ∑ a : CompIdx E r s × CompIdx E r s × Fin dimE × CompIdx E r s,
      weightedGradChartCoeff (I := I) (M := M) g r s α P₀ l a y *
        tensorComponentEuclid (I := I) (M := M) g r s T α a.2.2.2 y
    with hWext_def
  have h_comp_cd : ∀ (l : Fin dimE) (a : CompIdx E r s × CompIdx E r s ×
      Fin dimE × CompIdx E r s) (_ : a ∈ (Finset.univ : Finset _)),
      ContDiff ℝ ∞ (fun y => tensorComponentEuclid (I := I) (M := M)
        g r s T α a.2.2.2 y) := fun l a _ => hT_comp_cd a.2.2.2
  have h_comp_cpt : ∀ (l : Fin dimE) (a : CompIdx E r s × CompIdx E r s ×
      Fin dimE × CompIdx E r s) (_ : a ∈ (Finset.univ : Finset _)),
      HasCompactSupport (fun y => tensorComponentEuclid (I := I) (M := M)
        g r s T α a.2.2.2 y) := fun l a _ => hT_comp_cpt a.2.2.2
  have h_comp_K : ∀ (l : Fin dimE) (a : CompIdx E r s × CompIdx E r s ×
      Fin dimE × CompIdx E r s) (_ : a ∈ (Finset.univ : Finset _)),
      tsupport (fun y => tensorComponentEuclid (I := I) (M := M)
        g r s T α a.2.2.2 y) ⊆ K := fun l a _ => hT_K a.2.2.2
  have hWext_cd : ∀ l : Fin dimE, ContDiff ℝ ∞ (Wext l) := by
    intro l
    rw [hWext_def]
    exact chartCoeffSum_contDiff (I := I) (M := M) α hK hK_target Finset.univ
      (weightedGradChartCoeff (I := I) (M := M) g r s α P₀ l) _
      (fun a _ => weightedGradChartCoeff_contDiffOn (I := I) (M := M)
        g r s α P₀ l a)
      (h_comp_cd l) (h_comp_K l)
  have hWext_cpt : ∀ l : Fin dimE, HasCompactSupport (Wext l) := by
    intro l
    rw [hWext_def]
    exact chartCoeffSum_hasCompactSupport hK Finset.univ
      (weightedGradChartCoeff (I := I) (M := M) g r s α P₀ l) _ (h_comp_K l)
  have hWext_mem : ∀ l : Fin dimE,
      MemWkp (d := dimE) (m + 1) 2 (Wext l) Ω'' := fun l =>
    memWkp_of_smooth_compactSupport_anyOpen (d := dimE) hΩ''_open
      (by simpa using hWext_cd l) (hWext_cpt l)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (m + 1)
  have h_comp_bd : ∀ (l : Fin dimE) (a : CompIdx E r s × CompIdx E r s ×
      Fin dimE × CompIdx E r s) (_ : a ∈ (Finset.univ : Finset _)),
      iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
        (fun y => tensorComponentEuclid (I := I) (M := M)
          g r s T α a.2.2.2 y) Ω'' ≤
        ∑ P : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
          (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'' :=
    fun l a _ => Finset.single_le_sum
      (f := fun P => iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
        (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'')
      (fun P _ => zero_le _) (Finset.mem_univ a.2.2.2)
  have hWext_bd : ∀ l : Fin dimE,
      iteratedWeakSobolevNorm (d := dimE) (m + 1) 2 (Wext l) Ω'' ≤
        ENNReal.ofReal (Kl l) *
          ∑ P : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
            (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'' :=
    fun l => (hKl l (h_comp_cd l) (h_comp_cpt l) (h_comp_K l)
      hΩ''_open hΩ''_target (h_comp_bd l)).2
  have h_partial_eqOn : ∀ l : Fin dimE, Set.EqOn
      (euclidPartial (E := E) l
        (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l))
      (euclidPartial (E := E) l (Wext l)) Ω'' := by
    intro l y hy
    refine euclidPartial_congr_of_eqOn_open (E := E) hΩ''_open ?_ l hy
    intro z hz
    exact (weightedGradCoeff_eq_chartCoeffSum (I := I) (M := M)
      g r s T α P₀ l (hΩ''_target hz)).trans (by rw [hWext_def])
  have h_eqOn : Set.EqOn
      (fun y => ∑ l : Fin dimE, euclidPartial (E := E) l
        (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y)
      (fun y => ∑ l : Fin dimE, euclidPartial (E := E) l (Wext l) y) Ω'' := by
    intro y hy
    exact Finset.sum_congr rfl fun l _ => h_partial_eqOn l hy
  have h_ae : (fun y => ∑ l : Fin dimE, euclidPartial (E := E) l
        (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y)
      =ᵐ[volume.restrict Ω'']
      (fun y => ∑ l : Fin dimE, euclidPartial (E := E) l (Wext l) y) :=
    eqOn_open_imp_ae_restrict (E := E) hΩ''_open h_eqOn
  have h_partial_mem : ∀ l : Fin dimE,
      MemWkp (d := dimE) m 2 (euclidPartial (E := E) l (Wext l)) Ω'' :=
    fun l => memWkp_euclidPartial (E := E) hΩ''_open (hWext_cd l)
      (hWext_mem l) l
  have h_partial_le : ∀ l ∈ (Finset.univ : Finset (Fin dimE)),
      iteratedWeakSobolevNorm (d := dimE) m 2 (euclidPartial (E := E) l (Wext l)) Ω'' ≤
        ENNReal.ofReal (Kl l) *
          ∑ P : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
            (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'' :=
    fun l _ => (wkpNorm_euclidPartial_le (E := E) hΩ''_open (hWext_cd l)
      (hWext_mem l) l).trans (hWext_bd l)
  have h_sum_mem : MemWkp (d := dimE) m 2
      (fun y => ∑ l : Fin dimE, euclidPartial (E := E) l (Wext l) y) Ω'' :=
    memWkp_finset_sum (d := dimE) hΩ''_open Finset.univ _
      (fun l _ => h_partial_mem l)
  refine ⟨(MemWkp_congr_ae (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hΩ''_open h_ae).mpr h_sum_mem, ?_⟩
  rw [wkpNorm_congr_ae (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hΩ''_open h_ae]
  refine (wkpNorm_finset_sum_le (d := dimE) hΩ''_open Finset.univ _
    (fun l _ => h_partial_mem l) Kl (fun l _ => hKl_nn l)
    (∑ P : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
      (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'')
    h_partial_le).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => hKl_nn l)]

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero dimE] in
theorem tensorComponentWeakRHS_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {K : Set EuclN}
    (hK : IsCompact K) (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (m : ℕ) (P₀ : CompIdx E r s) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ (T F : SmoothCcTensor g r s),
      tsupport T.toFun ⊆ (chartAt H α).source →
      tsupport F.toFun ⊆ (chartAt H α).source →
      (∀ P : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) ⊆ K) →
      (∀ Q : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s F α Q) ⊆ K) →
      ∀ {Ω'' : Set EuclN}, IsOpen Ω'' →
      Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α →
      iteratedWeakSobolevNorm (d := dimE) m 2
          (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀)
          Ω'' ≤
        ENNReal.ofReal Kc *
          ((∑ Q : CompIdx E r s,
              iteratedWeakSobolevNorm (d := dimE) m 2
                (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') +
            ∑ P : CompIdx E r s,
              iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
                (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') := by
  classical
  obtain ⟨Kc1, hKc1_nn, hKc1⟩ :=
    exists_densityMul_sourcePairingCoeff_wkpNorm_le (I := I) (M := M)
      g r s α hK hK_target m P₀
  obtain ⟨Kc2, hKc2_nn, hKc2⟩ :=
    exists_densityMul_covPrincipalRotationCoeff_wkpNorm_le (I := I) (M := M)
      g r s α hK hK_target m P₀
  obtain ⟨Kc3, hKc3_nn, hKc3⟩ :=
    exists_densityMul_covLowerOrderRotationValueCoeff_wkpNorm_le (I := I)
      (M := M) g r s α hK hK_target m P₀
  obtain ⟨Kc4, hKc4_nn, hKc4⟩ :=
    exists_gradientGroup_wkpNorm_le (I := I) (M := M)
      g r s α hK hK_target m P₀
  refine ⟨Kc1 + Kc2 + Kc3 + Kc4, by positivity, ?_⟩
  intro T F hT_supp hF_supp hT_K hF_K Ω'' hΩ''_open hΩ''_target
  set G1 : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
    sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y with hG1_def
  set G2 : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
    covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y with hG2_def
  set G3 : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
    covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y
    with hG3_def
  set G4 : EuclN → ℝ := fun y => ∑ l : Fin dimE, euclidPartial (E := E) l
    (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y with hG4_def
  obtain ⟨hG1_mem, hG1_le⟩ := hKc1 hF_supp hF_K hΩ''_open hΩ''_target
  obtain ⟨hG2_mem, hG2_le⟩ := hKc2 hT_supp hT_K hΩ''_open hΩ''_target
  obtain ⟨hG3_mem, hG3_le⟩ := hKc3 hT_supp hT_K hΩ''_open hΩ''_target
  obtain ⟨hG4_mem, hG4_le⟩ := hKc4 hT_supp hT_K hΩ''_open hΩ''_target
  have h_eqOn : Set.EqOn
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀)
      (fun y => G1 y + (-G2 y) + (-G3 y) + G4 y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro y hy
    rw [tensorComponentWeakRHS_apply_of_mem (I := I) (M := M)
      g r s T F α hK hK_target P₀ hy]
    simp only [hG1_def, hG2_def, hG3_def, hG4_def]
    ring
  have h_ae : tensorComponentWeakRHS (I := I) (M := M)
        g r s T F α hK hK_target P₀
      =ᵐ[volume.restrict Ω'']
      (fun y => G1 y + (-G2 y) + (-G3 y) + G4 y) :=
    eqOn_open_imp_ae_restrict (E := E) hΩ''_open (h_eqOn.mono hΩ''_target)
  have hnG2_mem : MemWkp (d := dimE) m 2 (fun y => -G2 y) Ω'' :=
    MemWkp.neg (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ''_open hG2_mem
  have hnG3_mem : MemWkp (d := dimE) m 2 (fun y => -G3 y) Ω'' :=
    MemWkp.neg (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ''_open hG3_mem
  have h12_mem : MemWkp (d := dimE) m 2
      (fun y => G1 y + (-G2 y)) Ω'' :=
    MemWkp.add (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ''_open
      hG1_mem hnG2_mem
  have h123_mem : MemWkp (d := dimE) m 2
      (fun y => G1 y + (-G2 y) + (-G3 y)) Ω'' :=
    MemWkp.add (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ''_open
      h12_mem hnG3_mem
  have h_enorm_negOne : ‖(-1 : ℝ)‖ₑ = 1 := by
    rw [show (-1 : ℝ) = -(1 : ℝ) from rfl, enorm_neg, enorm_one]
  have hnG2_norm : iteratedWeakSobolevNorm (d := dimE) m 2 (fun y => -G2 y) Ω'' =
      iteratedWeakSobolevNorm (d := dimE) m 2 G2 Ω'' := by
    rw [show (fun y => -G2 y) = (fun y => (-1 : ℝ) * G2 y) by funext y; ring,
      wkpNorm_const_smul (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        hΩ''_open hG2_mem (-1), h_enorm_negOne, one_mul]
  have hnG3_norm : iteratedWeakSobolevNorm (d := dimE) m 2 (fun y => -G3 y) Ω'' =
      iteratedWeakSobolevNorm (d := dimE) m 2 G3 Ω'' := by
    rw [show (fun y => -G3 y) = (fun y => (-1 : ℝ) * G3 y) by funext y; ring,
      wkpNorm_const_smul (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        hΩ''_open hG3_mem (-1), h_enorm_negOne, one_mul]
  rw [wkpNorm_congr_ae (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hΩ''_open h_ae]
  have h_tri :
      iteratedWeakSobolevNorm (d := dimE) m 2
          (fun y => G1 y + (-G2 y) + (-G3 y) + G4 y) Ω'' ≤
        iteratedWeakSobolevNorm (d := dimE) m 2 G1 Ω'' + iteratedWeakSobolevNorm (d := dimE) m 2 G2 Ω'' +
          iteratedWeakSobolevNorm (d := dimE) m 2 G3 Ω'' + iteratedWeakSobolevNorm (d := dimE) m 2 G4 Ω'' := by
    refine (wkpNorm_add_le (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      hΩ''_open h123_mem hG4_mem).trans ?_
    refine add_le_add ?_ le_rfl
    refine (wkpNorm_add_le (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      hΩ''_open h12_mem hnG3_mem).trans ?_
    rw [hnG3_norm]
    refine add_le_add ?_ le_rfl
    refine (wkpNorm_add_le (d := dimE) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      hΩ''_open hG1_mem hnG2_mem).trans ?_
    rw [hnG2_norm]
  refine h_tri.trans ?_
  set SF : ℝ≥0∞ := ∑ Q : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) m 2
    (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'' with hSF_def
  set ST : ℝ≥0∞ := ∑ P : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
    (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'' with hST_def
  have hsum : Kc1 + Kc2 + Kc3 + Kc4 ≥ 0 := by positivity
  have hG1_final : iteratedWeakSobolevNorm (d := dimE) m 2 G1 Ω'' ≤
      ENNReal.ofReal (Kc1 + Kc2 + Kc3 + Kc4) * SF := by
    refine hG1_le.trans (mul_le_mul_of_nonneg_right ?_ (zero_le _))
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hG234_final :
      iteratedWeakSobolevNorm (d := dimE) m 2 G2 Ω'' + iteratedWeakSobolevNorm (d := dimE) m 2 G3 Ω'' +
        iteratedWeakSobolevNorm (d := dimE) m 2 G4 Ω'' ≤
        ENNReal.ofReal (Kc1 + Kc2 + Kc3 + Kc4) * ST := by
    refine (add_le_add (add_le_add hG2_le hG3_le) hG4_le).trans ?_
    rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add hKc2_nn hKc3_nn,
      ← ENNReal.ofReal_add (by positivity) hKc4_nn]
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (by linarith)) (zero_le _)
  calc iteratedWeakSobolevNorm (d := dimE) m 2 G1 Ω'' + iteratedWeakSobolevNorm (d := dimE) m 2 G2 Ω'' +
        iteratedWeakSobolevNorm (d := dimE) m 2 G3 Ω'' + iteratedWeakSobolevNorm (d := dimE) m 2 G4 Ω''
      = iteratedWeakSobolevNorm (d := dimE) m 2 G1 Ω'' +
          (iteratedWeakSobolevNorm (d := dimE) m 2 G2 Ω'' + iteratedWeakSobolevNorm (d := dimE) m 2 G3 Ω'' +
            iteratedWeakSobolevNorm (d := dimE) m 2 G4 Ω'') := by ring
    _ ≤ ENNReal.ofReal (Kc1 + Kc2 + Kc3 + Kc4) * SF +
          ENNReal.ofReal (Kc1 + Kc2 + Kc3 + Kc4) * ST :=
        add_le_add hG1_final hG234_final
    _ = ENNReal.ofReal (Kc1 + Kc2 + Kc3 + Kc4) * (SF + ST) := by
        rw [mul_add]

end Headline

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
