import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Bootstrap.BootstrapMixed


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

section UniformMultiplier

variable {d : ℕ} [NeZero d]

local notation "EE" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma wkpNorm_chosenWeakPartial_le_succ
    (k : ℕ) {Ω : Set EE} (u : EE → ℝ) (i : Fin d) :
    iteratedWeakSobolevNorm (d := d) k 2 (chosenWeakPartial' 2 i u Ω) Ω ≤
      iteratedWeakSobolevNorm (d := d) (k + 1) 2 u Ω := by
  classical
  rw [wkpNorm_succ_eq_eLpNorm_add_sum_partial (d := d) k 2 Ω u]
  refine le_trans ?_ le_add_self
  exact Finset.single_le_sum
    (f := fun j : Fin d => iteratedWeakSobolevNorm (d := d) k 2 (chosenWeakPartial' 2 j u Ω) Ω)
    (fun j _ => zero_le _) (Finset.mem_univ i)

omit [NeZero d] in
theorem wkpNorm_smul_globalSmooth_uniform
    (k : ℕ) {η : EE → ℝ} (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ j ≤ k, ∀ x : EE, ‖iteratedFDeriv ℝ j η x‖ ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {Ω : Set EE}, IsOpen Ω → ∀ {u : EE → ℝ},
      MemWkp (d := d) k 2 u Ω →
      iteratedWeakSobolevNorm (d := d) k 2 (fun x => η x * u x) Ω ≤
        ENNReal.ofReal K * iteratedWeakSobolevNorm (d := d) k 2 u Ω := by
  classical
  induction k generalizing η with
  | zero =>
      refine ⟨C + 1, by linarith, ?_⟩
      intro Ω hΩ u _hu
      have h0 : ∀ x ∈ Ω, ‖η x‖ ≤ C := by
        intro x _
        have h := hbound 0 (le_refl 0) x
        rwa [norm_iteratedFDeriv_zero] at h
      rw [wkpNorm_zero (d := d), wkpNorm_zero (d := d)]
      refine (eLpNorm_eta_mul_le (d := d) hΩ h0 u).trans ?_
      exact mul_le_mul_of_nonneg_right
        (ENNReal.ofReal_le_ofReal (by linarith)) (zero_le _)
  | succ k ih =>
      have hbound_k : ∀ j ≤ k, ∀ x : EE, ‖iteratedFDeriv ℝ j η x‖ ≤ C :=
        fun j hj x => hbound j (hj.trans (Nat.le_succ _)) x
      obtain ⟨Kη, hKη_nn, hKη⟩ := ih hη_smooth hbound_k
      have h_partial_smooth : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
          (fun x : EE => (fderiv ℝ η x) (EuclideanSpace.single i 1)) := fun i =>
        contDiff_partial_eta (d := d) hη_smooth i
      have h_partial_bound : ∀ i : Fin d, ∀ j ≤ k, ∀ x : EE,
          ‖iteratedFDeriv ℝ j
            (fun x : EE => (fderiv ℝ η x) (EuclideanSpace.single i 1)) x‖ ≤ C := by
        intro i j hj x
        exact (norm_iteratedFDeriv_partial_le (d := d) hη_smooth i j x).trans
          (hbound (j + 1) (Nat.succ_le_succ hj) x)
      have h_partial_ih : ∀ i : Fin d, ∃ K' : ℝ, 0 ≤ K' ∧
          ∀ {Ω : Set EE}, IsOpen Ω → ∀ {u : EE → ℝ}, MemWkp (d := d) k 2 u Ω →
            iteratedWeakSobolevNorm (d := d) k 2
              (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) Ω ≤
              ENNReal.ofReal K' * iteratedWeakSobolevNorm (d := d) k 2 u Ω := fun i =>
        ih (h_partial_smooth i) (h_partial_bound i)
      choose Ki hKi_nn hKi using h_partial_ih
      have hsummand_nn : ∀ i : Fin d, 0 ≤ Kη + Ki i :=
        fun i => add_nonneg hKη_nn (hKi_nn i)
      refine ⟨C + ∑ i : Fin d, (Kη + Ki i),
        add_nonneg hC (Finset.sum_nonneg (fun i _ => hsummand_nn i)), ?_⟩
      intro Ω hΩ u hu
      have hη_bound_succ : ∀ j ≤ k + 1, ∀ x ∈ Ω,
          ‖iteratedFDeriv ℝ j η x‖ ≤ C := fun j hj x _ => hbound j hj x
      rw [wkpNorm_succ_eq_eLpNorm_add_sum_partial (d := d) k 2 Ω
        (fun x => η x * u x)]
      set D : ℝ≥0∞ := iteratedWeakSobolevNorm (d := d) (k + 1) 2 u Ω with hD_def
      have h0 : ∀ x ∈ Ω, ‖η x‖ ≤ C := by
        intro x _
        have h := hbound 0 (Nat.zero_le _) x
        rwa [norm_iteratedFDeriv_zero] at h
      have hLp_le : eLpNorm (fun x => η x * u x) 2 (volume.restrict Ω) ≤
          ENNReal.ofReal C * D := by
        refine (eLpNorm_eta_mul_le (d := d) hΩ h0 u).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
        rw [hD_def, wkpNorm_succ_eq_eLpNorm_add_sum_partial (d := d) k 2 Ω u]
        exact le_self_add
      have hpartial_le : ∀ i : Fin d,
          iteratedWeakSobolevNorm (d := d) k 2
            (chosenWeakPartial' 2 i (fun x => η x * u x) Ω) Ω ≤
            ENNReal.ofReal (Kη + Ki i) * D := by
        intro i
        have hu_W1 : DeGiorgi.MemW1p (d := d) 2 u Ω := hu.memW1p
        have hae := chosenWeakPartial'_smul_smooth_bounded_ae (d := d)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ hη_smooth h0
          (fun x hx => by
            have h := hbound 1 (by omega) x
            rwa [norm_iteratedFDeriv_one] at h) hu_W1 i
        rw [wkpNorm_congr_ae (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ hae]
        have h_du_mem : MemWkp (d := d) k 2 (chosenWeakPartial' 2 i u Ω) Ω :=
          hu.chosenWeakPartial_mem i
        have hu_k : MemWkp (d := d) k 2 u Ω := hu.le_succ
        have h_eta_du_mem : MemWkp (d := d) k 2
            (fun x => η x * chosenWeakPartial' 2 i u Ω x) Ω :=
          MemWkp.smul_smooth_bounded (d := d) k (by norm_num : (1 : ℝ≥0∞) ≤ 2)
            hΩ hη_smooth (fun j hj x _ => hbound_k j hj x) h_du_mem
        have h_dei_u_mem : MemWkp (d := d) k 2
            (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) Ω :=
          MemWkp.smul_smooth_bounded (d := d) k (by norm_num : (1 : ℝ≥0∞) ≤ 2)
            hΩ (h_partial_smooth i) (fun j hj x _ => h_partial_bound i j hj x) hu_k
        refine (wkpNorm_add_le (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ
          h_eta_du_mem h_dei_u_mem).trans ?_
        have hA : iteratedWeakSobolevNorm (d := d) k 2
            (fun x => η x * chosenWeakPartial' 2 i u Ω x) Ω ≤
            ENNReal.ofReal Kη * D := by
          refine (hKη hΩ h_du_mem).trans ?_
          exact mul_le_mul_of_nonneg_left
            (wkpNorm_chosenWeakPartial_le_succ (d := d) k u i) (zero_le _)
        have hB : iteratedWeakSobolevNorm (d := d) k 2
            (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) Ω ≤
            ENNReal.ofReal (Ki i) * D := by
          refine (hKi i hΩ hu_k).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
          rw [hD_def]
          exact wkpNorm_mono_order (d := d) (Nat.le_succ k) u Ω
        refine (add_le_add hA hB).trans ?_
        rw [← add_mul, ← ENNReal.ofReal_add hKη_nn (hKi_nn i)]
      have hsum_le :
          (∑ i : Fin d, iteratedWeakSobolevNorm (d := d) k 2
            (chosenWeakPartial' 2 i (fun x => η x * u x) Ω) Ω) ≤
            ENNReal.ofReal (∑ i : Fin d, (Kη + Ki i)) * D := by
        refine (Finset.sum_le_sum (fun i _ => hpartial_le i)).trans ?_
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg
          (fun i _ => hsummand_nn i)]
      refine (add_le_add hLp_le hsum_le).trans ?_
      rw [← add_mul, ← ENNReal.ofReal_add hC
        (Finset.sum_nonneg (fun i _ => hsummand_nn i))]

end UniformMultiplier

section Headline

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

local notation "dimE" => Module.finrank ℝ E

omit [FiniteDimensional ℝ E] [NeZero dimE] in
private lemma contDiff_of_contDiffOn_zero_off_closed
    {P : EuclN → ℝ} {U C : Set EuclN}
    (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hP : ContDiffOn ℝ ∞ P U) (hzero : ∀ y, y ∉ C → P y = 0) :
    ContDiff ℝ ∞ P := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact hP.contDiffAt (hU.mem_nhds hy)
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hC.isOpen_compl.mem_nhds (fun hyC => hy (hCU hyC))] with z hz
      using hzero z hz

private structure ChartCutoff (α : M) {K : Set EuclN}
    (hK : IsCompact K) (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    where

  toFun : EuclN → ℝ

  smooth : ContDiff ℝ ∞ toFun

  one_on : ∀ y ∈ K, toFun y = 1

  tsupport_subset : tsupport toFun ⊆ chartTargetEuclid (I := I) (M := M) α

  hasCompactSupport : HasCompactSupport toFun

omit [NeZero dimE] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma exists_chartCutoff (α : M) {K : Set EuclN}
    (hK : IsCompact K) (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Nonempty (ChartCutoff (I := I) (M := M) α hK hK_target) := by
  classical
  have hcTE_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨L, hL_compact, hKL, hL_target⟩ :=
    exists_compact_between hK hcTE_open hK_target
  obtain ⟨ζ, hζ_one, hζ_zero, -⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ, EuclN))
      (n := (⊤ : ℕ∞)) hK.isClosed hKL
  have hζ_cd : ContDiff ℝ ∞ (fun y => ζ y) :=
    (contMDiff_iff_contDiff (n := (⊤ : ℕ∞))).mp ζ.contMDiff
  have hζ_supp : tsupport (fun y => ζ y) ⊆ L := by
    refine closure_minimal (fun y hy => ?_) hL_compact.isClosed
    rw [Function.mem_support] at hy
    by_contra hyL
    exact hy (hζ_zero y hyL)
  exact ⟨{ toFun := fun y => ζ y
           smooth := hζ_cd
           one_on := fun y hy =>
             (hζ_one.filter_mono (nhds_le_nhdsSet hy)).self_of_nhds
           tsupport_subset := hζ_supp.trans hL_target
           hasCompactSupport := HasCompactSupport.of_support_subset_isCompact
             hL_compact ((subset_tsupport _).trans hζ_supp) }⟩

omit [NeZero dimE] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma cutoff_mul_coeff_contDiff (α : M) {K : Set EuclN}
    {hK : IsCompact K} {hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α}
    (ζ : ChartCutoff (I := I) (M := M) α hK hK_target)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    ContDiff ℝ ∞ (fun y => ζ.toFun y * c y) := by
  classical
  refine contDiff_of_contDiffOn_zero_off_closed
    (U := chartTargetEuclid (I := I) (M := M) α) (C := tsupport ζ.toFun)
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α) (isClosed_tsupport _)
    ζ.tsupport_subset (ζ.smooth.contDiffOn.mul hc) ?_
  intro y hy
  rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

omit [NeZero dimE] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma exists_wkpNorm_chartCoeff_mul_le (α : M) {K : Set EuclN}
    (hK : IsCompact K) (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (m : ℕ) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ {v : EuclN → ℝ}, ContDiff ℝ ∞ v → HasCompactSupport v →
      tsupport v ⊆ K → ∀ {Ω'' : Set EuclN}, IsOpen Ω'' →
      Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemWkp (d := dimE) m 2 (fun y => c y * v y) Ω'' ∧
        iteratedWeakSobolevNorm (d := dimE) m 2 (fun y => c y * v y) Ω'' ≤
          ENNReal.ofReal Kc * iteratedWeakSobolevNorm (d := dimE) m 2 v Ω'' := by
  classical
  obtain ⟨ζ⟩ := exists_chartCutoff (I := I) (M := M) α hK hK_target
  have hζc_smooth : ContDiff ℝ ∞ (fun y => ζ.toFun y * c y) :=
    cutoff_mul_coeff_contDiff (I := I) (M := M) α ζ hc
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := dimE)
      (η := fun y => ζ.toFun y * c y)
      (by simpa using hζc_smooth)
      (ζ.hasCompactSupport.mul_right) m
  have hC_bound' : ∀ j ≤ m, ∀ x : EuclN, ‖iteratedFDeriv ℝ j
      (fun y => ζ.toFun y * c y) x‖ ≤ C := fun j hj x => hC_bound x j hj
  obtain ⟨K₀, hK₀_nn, hK₀⟩ :=
    wkpNorm_smul_globalSmooth_uniform (d := dimE) m
      (η := fun y => ζ.toFun y * c y) (by simpa using hζc_smooth) hC_nn hC_bound'
  refine ⟨K₀, hK₀_nn, ?_⟩
  intro v hv_smooth hv_cpt hv_K Ω'' hΩ''_open _hΩ''_target
  have hv_mem : MemWkp (d := dimE) m 2 v Ω'' :=
    memWkp_of_smooth_compactSupport_anyOpen (d := dimE) hΩ''_open
      (by simpa using hv_smooth) hv_cpt (by norm_num : (1 : ℝ≥0∞) ≤ 2) m
  have h_eq : (fun y => c y * v y) = (fun y => (ζ.toFun y * c y) * v y) := by
    funext y
    by_cases hyK : y ∈ K
    · rw [ζ.one_on y hyK, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun hy => hyK (hv_K hy)),
        mul_zero, mul_zero]
  refine ⟨?_, ?_⟩
  · rw [h_eq]
    exact MemWkp.smul_smooth_bounded (d := dimE) m
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ''_open (by simpa using hζc_smooth)
      (fun j hj x _ => hC_bound x j hj) hv_mem
  · rw [h_eq]
    exact hK₀ hΩ''_open hv_mem

omit [FiniteDimensional ℝ E] [NeZero dimE] in
lemma euclidPartial_contDiff {v : EuclN → ℝ} (hv : ContDiff ℝ ∞ v)
    (l : Fin dimE) :
    ContDiff ℝ ∞ (euclidPartial (E := E) l v) := by
  have h := contDiff_partial_eta (d := dimE) (by simpa using hv) l
  simpa [euclidPartial] using h

omit [FiniteDimensional ℝ E] [NeZero dimE] in
private lemma euclidPartial_eq_zero_of_notMem_tsupport {v : EuclN → ℝ}
    (l : Fin dimE) {y : EuclN} (hy : y ∉ tsupport v) :
    euclidPartial (E := E) l v y = 0 := by
  classical
  have hy_nhds : (tsupport v)ᶜ ∈ 𝓝 y :=
    (isClosed_tsupport v).isOpen_compl.mem_nhds hy
  have hv_zero_evt : v =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
    Filter.eventually_of_mem hy_nhds
      (fun y' hy' => image_eq_zero_of_notMem_tsupport hy')
  rw [euclidPartial_def, Filter.EventuallyEq.fderiv_eq hv_zero_evt,
    fderiv_const_apply, ContinuousLinearMap.zero_apply]

omit [FiniteDimensional ℝ E] [NeZero dimE] in
lemma euclidPartial_tsupport_subset {v : EuclN → ℝ}
    (l : Fin dimE) :
    tsupport (euclidPartial (E := E) l v) ⊆ tsupport v := by
  refine closure_minimal (fun y hy => ?_) (isClosed_tsupport _)
  rw [Function.mem_support] at hy
  by_contra hyv
  exact hy (euclidPartial_eq_zero_of_notMem_tsupport (E := E) l hyv)

omit [FiniteDimensional ℝ E] [NeZero dimE] in
lemma euclidPartial_hasCompactSupport {K : Set EuclN} (hK : IsCompact K)
    {v : EuclN → ℝ} (hv_K : tsupport v ⊆ K) (l : Fin dimE) :
    HasCompactSupport (euclidPartial (E := E) l v) :=
  HasCompactSupport.of_support_subset_isCompact hK
    ((subset_tsupport _).trans
      ((euclidPartial_tsupport_subset (E := E) l).trans hv_K))

omit [FiniteDimensional ℝ E] [NeZero dimE] in
lemma wkpNorm_euclidPartial_le {m : ℕ} {Ω'' : Set EuclN}
    (hΩ'' : IsOpen Ω'') {v : EuclN → ℝ} (hv_smooth : ContDiff ℝ ∞ v)
    (hv : MemWkp (d := dimE) (m + 1) 2 v Ω'') (l : Fin dimE) :
    iteratedWeakSobolevNorm (d := dimE) m 2 (euclidPartial (E := E) l v) Ω'' ≤
      iteratedWeakSobolevNorm (d := dimE) (m + 1) 2 v Ω'' :=
  wkpNorm_classicalPartial_le (d := dimE) hΩ'' (by simpa using hv_smooth) hv l

omit [FiniteDimensional ℝ E] [NeZero dimE] in
lemma memWkp_euclidPartial {m : ℕ} {Ω'' : Set EuclN}
    (hΩ'' : IsOpen Ω'') {v : EuclN → ℝ} (hv_smooth : ContDiff ℝ ∞ v)
    (hv : MemWkp (d := dimE) (m + 1) 2 v Ω'') (l : Fin dimE) :
    MemWkp (d := dimE) m 2 (euclidPartial (E := E) l v) Ω'' :=
  classicalPartial_memWkp_of_memWkp_succ (d := dimE) hΩ''
    (by simpa using hv_smooth) hv l

omit [NeZero dimE] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
lemma covDerivLowerOrderTerm_eq_sum_componentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (k : Fin dimE)
    (Idx : Fin r → Fin dimE) (Jdx : Fin s → Fin dimE)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s T α k Idx Jdx y =
      ∑ p : CompIdx E r s,
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α k Idx p.1 Jdx p.2 y *
          tensorComponentEuclid (I := I) (M := M) g r s T α p y := by
  classical
  rw [covDerivLowerOrderTerm_def]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r s T α p hy]

omit [NeZero dimE] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma chartCoeff_mul_contDiff (α : M) {K : Set EuclN}
    (hK : IsCompact K) (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {v : EuclN → ℝ} (hv : ContDiff ℝ ∞ v) (hv_K : tsupport v ⊆ K) :
    ContDiff ℝ ∞ (fun y => c y * v y) := by
  classical
  obtain ⟨ζ⟩ := exists_chartCutoff (I := I) (M := M) α hK hK_target
  have hζc_smooth : ContDiff ℝ ∞ (fun y => ζ.toFun y * c y) :=
    cutoff_mul_coeff_contDiff (I := I) (M := M) α ζ hc
  have h_eq : (fun y => c y * v y) = (fun y => (ζ.toFun y * c y) * v y) := by
    funext y
    by_cases hyK : y ∈ K
    · rw [ζ.one_on y hyK, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun hy => hyK (hv_K hy)),
        mul_zero, mul_zero]
  rw [h_eq]
  exact hζc_smooth.mul hv

omit [NeZero dimE] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
lemma chartCoeffSum_contDiff (α : M) {K : Set EuclN}
    (hK : IsCompact K) (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {ι : Type*} (S : Finset ι) (c v : ι → EuclN → ℝ)
    (hc : ∀ a ∈ S, ContDiffOn ℝ ∞ (c a)
      (chartTargetEuclid (I := I) (M := M) α))
    (hv : ∀ a ∈ S, ContDiff ℝ ∞ (v a))
    (hv_K : ∀ a ∈ S, tsupport (v a) ⊆ K) :
    ContDiff ℝ ∞ (fun y => ∑ a ∈ S, c a y * v a y) := by
  classical
  refine ContDiff.sum (fun a ha => ?_)
  exact chartCoeff_mul_contDiff (I := I) (M := M) α hK hK_target
    (hc a ha) (hv a ha) (hv_K a ha)

omit [FiniteDimensional ℝ E] [NeZero dimE] in
lemma chartCoeffSum_hasCompactSupport {K : Set EuclN}
    (hK : IsCompact K)
    {ι : Type*} (S : Finset ι) (c v : ι → EuclN → ℝ)
    (hv_K : ∀ a ∈ S, tsupport (v a) ⊆ K) :
    HasCompactSupport (fun y => ∑ a ∈ S, c a y * v a y) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro y hy
  rw [Function.mem_support] at hy
  by_contra hyK
  exact hy (Finset.sum_eq_zero (fun a ha => by
    rw [image_eq_zero_of_notMem_tsupport (fun hy' => hyK (hv_K a ha hy')),
      mul_zero]))

omit [NeZero dimE] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma exists_wkpNorm_chartCoeffSum_le (α : M) {K : Set EuclN}
    (hK : IsCompact K) (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (m : ℕ) {ι : Type*} (S : Finset ι) (c : ι → EuclN → ℝ)
    (hc : ∀ a ∈ S, ContDiffOn ℝ ∞ (c a)
      (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ {v : ι → EuclN → ℝ},
      (∀ a ∈ S, ContDiff ℝ ∞ (v a)) → (∀ a ∈ S, HasCompactSupport (v a)) →
      (∀ a ∈ S, tsupport (v a) ⊆ K) → ∀ {Ω'' : Set EuclN}, IsOpen Ω'' →
      Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemWkp (d := dimE) m 2 (fun y => ∑ a ∈ S, c a y * v a y) Ω'' ∧
        iteratedWeakSobolevNorm (d := dimE) m 2 (fun y => ∑ a ∈ S, c a y * v a y) Ω'' ≤
          ENNReal.ofReal Kc *
            ∑ a ∈ S, iteratedWeakSobolevNorm (d := dimE) m 2 (v a) Ω'' := by
  classical
  have hper : ∀ a ∈ S, ∃ Ka : ℝ, 0 ≤ Ka ∧
      ∀ {v : EuclN → ℝ}, ContDiff ℝ ∞ v → HasCompactSupport v →
      tsupport v ⊆ K → ∀ {Ω'' : Set EuclN}, IsOpen Ω'' →
      Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemWkp (d := dimE) m 2 (fun y => c a y * v y) Ω'' ∧
        iteratedWeakSobolevNorm (d := dimE) m 2 (fun y => c a y * v y) Ω'' ≤
          ENNReal.ofReal Ka * iteratedWeakSobolevNorm (d := dimE) m 2 v Ω'' :=
    fun a ha => exists_wkpNorm_chartCoeff_mul_le (I := I) (M := M)
      α hK hK_target m (hc a ha)
  choose! Ka hKa_nn hKa using hper
  refine ⟨∑ a ∈ S, Ka a, Finset.sum_nonneg (fun a ha => hKa_nn a ha), ?_⟩
  intro v hv_smooth hv_cpt hv_K Ω'' hΩ''_open hΩ''_target
  have h_term_mem : ∀ a ∈ S,
      MemWkp (d := dimE) m 2 (fun y => c a y * v a y) Ω'' :=
    fun a ha => (hKa a ha (hv_smooth a ha) (hv_cpt a ha) (hv_K a ha)
      hΩ''_open hΩ''_target).1
  refine ⟨memWkp_finset_sum (d := dimE) hΩ''_open S _ h_term_mem, ?_⟩
  set D : ℝ≥0∞ := ∑ a ∈ S, iteratedWeakSobolevNorm (d := dimE) m 2 (v a) Ω'' with hD_def
  have h_term_le : ∀ a ∈ S,
      iteratedWeakSobolevNorm (d := dimE) m 2 (fun y => c a y * v a y) Ω'' ≤
        ENNReal.ofReal (Ka a) * D := by
    intro a ha
    refine ((hKa a ha (hv_smooth a ha) (hv_cpt a ha) (hv_K a ha)
      hΩ''_open hΩ''_target).2).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
    exact Finset.single_le_sum
      (f := fun b => iteratedWeakSobolevNorm (d := dimE) m 2 (v b) Ω'') (fun b _ => zero_le _) ha
  refine (wkpNorm_finset_sum_le (d := dimE) hΩ''_open S _ h_term_mem
    Ka (fun a ha => hKa_nn a ha) D h_term_le).trans ?_
  rw [hD_def]

omit [NeZero dimE] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
lemma exists_wkpNorm_chartCoeffSum_bddBy (α : M) {K : Set EuclN}
    (hK : IsCompact K) (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (m : ℕ) {ι : Type*} (S : Finset ι) (c : ι → EuclN → ℝ)
    (hc : ∀ a ∈ S, ContDiffOn ℝ ∞ (c a)
      (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ {v : ι → EuclN → ℝ},
      (∀ a ∈ S, ContDiff ℝ ∞ (v a)) → (∀ a ∈ S, HasCompactSupport (v a)) →
      (∀ a ∈ S, tsupport (v a) ⊆ K) → ∀ {Ω'' : Set EuclN}, IsOpen Ω'' →
      Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α → ∀ {G : ℝ≥0∞},
      (∀ a ∈ S, iteratedWeakSobolevNorm (d := dimE) m 2 (v a) Ω'' ≤ G) →
      MemWkp (d := dimE) m 2 (fun y => ∑ a ∈ S, c a y * v a y) Ω'' ∧
        iteratedWeakSobolevNorm (d := dimE) m 2 (fun y => ∑ a ∈ S, c a y * v a y) Ω'' ≤
          ENNReal.ofReal Kc * G := by
  classical
  obtain ⟨Kc, hKc_nn, hKc⟩ :=
    exists_wkpNorm_chartCoeffSum_le (I := I) (M := M) α hK hK_target m S c hc
  refine ⟨Kc * (S.card : ℝ), mul_nonneg hKc_nn (by positivity), ?_⟩
  intro v hv_cd hv_cpt hv_K Ω'' hΩ''_open hΩ''_target G hG
  obtain ⟨h_mem, h_le⟩ := hKc hv_cd hv_cpt hv_K hΩ''_open hΩ''_target
  refine ⟨h_mem, h_le.trans ?_⟩
  have hsum : (∑ a ∈ S, iteratedWeakSobolevNorm (d := dimE) m 2 (v a) Ω'') ≤ S.card • G :=
    Finset.sum_le_card_nsmul S _ G hG
  refine (mul_le_mul_of_nonneg_left hsum (zero_le _)).trans ?_
  rw [nsmul_eq_mul, ← mul_assoc, ENNReal.ofReal_mul hKc_nn, ENNReal.ofReal_natCast]

omit [FiniteDimensional ℝ E] [NeZero dimE] in
lemma eqOn_open_imp_ae_restrict {U : Set EuclN} (hU : IsOpen U)
    {f h : EuclN → ℝ} (hfh : Set.EqOn f h U) :
    f =ᵐ[volume.restrict U] h := by
  have hmem : ∀ᵐ y ∂(volume.restrict U), y ∈ U :=
    ae_restrict_mem hU.measurableSet
  filter_upwards [hmem] with y hy using hfh hy

omit [FiniteDimensional ℝ E] [NeZero dimE] in
lemma euclidPartial_congr_of_eqOn_open {U : Set EuclN} (hU : IsOpen U)
    {f h : EuclN → ℝ} (hfh : Set.EqOn f h U)
    (l : Fin dimE) {y : EuclN} (hy : y ∈ U) :
    euclidPartial (E := E) l f y = euclidPartial (E := E) l h y := by
  have hevt : f =ᶠ[𝓝 y] h :=
    Filter.eventually_of_mem (hU.mem_nhds hy) (fun z hz => hfh hz)
  rw [euclidPartial_def, euclidPartial_def, Filter.EventuallyEq.fderiv_eq hevt]

end Headline

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
