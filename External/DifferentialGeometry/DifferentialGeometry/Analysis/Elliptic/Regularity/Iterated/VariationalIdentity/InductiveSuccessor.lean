import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.VariationalIdentity.SuccessorSource


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedVariationalIdentityStep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP
open DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials
open DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData
open DifferentialGeometry.Analysis.Laplacian.IteratedVariationalIdentityStepScaffold
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma contDiff_fderiv_apply_single
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) := by
  have h_fderiv : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => fderiv ℝ ψ y) :=
    (contDiff_infty_iff_fderiv.1 hψ).2
  have h_eval : ContDiff ℝ (⊤ : ℕ∞)
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ))).contDiff
  exact h_eval.comp h_fderiv

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma hasCompactSupport_fderiv_apply_single
    {ψ : EuclN → ℝ} (hψ_cs : HasCompactSupport ψ)
    (l : Fin (Module.finrank ℝ E)) :
    HasCompactSupport (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) :=
  hψ_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma tsupport_fderiv_apply_single_subset
    (ψ : EuclN → ℝ) (l : Fin (Module.finrank ℝ E)) :
    tsupport (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) ⊆
      tsupport ψ :=
  tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single l 1)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma fderiv_apply_single_swap
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : EuclN)
    (j l : Fin (Module.finrank ℝ E)) :
    (fderiv ℝ
      (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
        (EuclideanSpace.single j 1) =
    (fderiv ℝ
      (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single j 1)) y)
        (EuclideanSpace.single l 1) := by
  classical
  have h_diff_fderiv : Differentiable ℝ (fderiv ℝ ψ) :=
    ((contDiff_infty_iff_fderiv.1 hψ).2).differentiable (by simp)
  have h_flip_eq : ∀ k : Fin (Module.finrank ℝ E),
      fderiv ℝ
        (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single k 1)) y =
        (fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single k 1) := by
    intro k
    have h_const_diff :
        DifferentiableAt ℝ
          (fun _ : EuclN => (EuclideanSpace.single k (1 : ℝ))) y :=
      differentiableAt_const _
    have h_step :=
      fderiv_clm_apply (𝕜 := ℝ)
        (c := fderiv ℝ ψ) (u := fun _ : EuclN => EuclideanSpace.single k (1 : ℝ))
        (x := y) (h_diff_fderiv y) h_const_diff
    have h_const_fderiv :
        fderiv ℝ (fun _ : EuclN => EuclideanSpace.single k (1 : ℝ)) y = 0 :=
      fderiv_const_apply (EuclideanSpace.single k (1 : ℝ))
    rw [h_step, h_const_fderiv]; simp
  rw [h_flip_eq l, h_flip_eq j]
  have h_symm : IsSymmSndFDerivAt ℝ ψ y := by
    have h_ge : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]; decide
    exact hψ.contDiffAt.isSymmSndFDerivAt (𝕜 := ℝ) h_ge
  change ((fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single l 1))
        (EuclideanSpace.single j 1) =
      ((fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single j 1))
        (EuclideanSpace.single l 1)
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
  exact h_symm (EuclideanSpace.single j 1) (EuclideanSpace.single l 1)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma chosenWeakPartial'_ae_zero_on_open_subset_of_ae_zero
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω V : Set EuclN}
    (_hΩ : IsOpen Ω) (hV : IsOpen V) (hV_sub : V ⊆ Ω)
    {u : EuclN → ℝ}
    (hu : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p u Ω)
    (hu_ae_zero_V : u =ᵐ[(volume : Measure EuclN).restrict V] (fun _ => (0 : ℝ)))
    (i : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω
      =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have hu_V : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p u V := by
    refine ⟨?_, ?_⟩
    · exact hu.1.mono_measure
        (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
    · intro j
      obtain ⟨g, hg_memLp, hg_weak⟩ := hu.2 j
      refine ⟨g, ?_, ?_⟩
      · exact hg_memLp.mono_measure
          (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
      · exact DeGiorgi.HasWeakPartialDeriv.restrict hV hV_sub hg_weak
  have h_partial_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartial' (d := Module.finrank ℝ E) p i u V) u V :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_V i
  have h_partial_Ω : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω) u Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem hu i
  have h_partial_Ω_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω) u V :=
    DeGiorgi.HasWeakPartialDeriv.restrict hV hV_sub h_partial_Ω
  have h_chosen_V_zero :
      chosenWeakPartial' (d := Module.finrank ℝ E) p i u V
        =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartial'_ae_zero_of_ae_zero (d := Module.finrank ℝ E)
      hp hV hu_ae_zero_V i
  have hg_lp_Ω : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω) p
      ((volume : Measure EuclN).restrict Ω) :=
    chosenWeakPartial'_memLp_of_mem hu i
  have hg_lp_Ω_V : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω) p
      ((volume : Measure EuclN).restrict V) :=
    hg_lp_Ω.mono_measure (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
  have hg_loc_Ω_V : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω)
      ((volume : Measure EuclN).restrict V) :=
    hg_lp_Ω_V.locallyIntegrable hp
  have hgV_lp : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) p i u V) p
      ((volume : Measure EuclN).restrict V) :=
    chosenWeakPartial'_memLp_of_mem hu_V i
  have hgV_loc : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) p i u V)
      ((volume : Measure EuclN).restrict V) :=
    hgV_lp.locallyIntegrable hp
  have h_unique :
      chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω
        =ᵐ[(volume : Measure EuclN).restrict V]
        chosenWeakPartial' (d := Module.finrank ℝ E) p i u V :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hV h_partial_Ω_V h_partial_V
      hg_loc_Ω_V hgV_loc
  exact h_unique.trans h_chosen_V_zero

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushed_u_h_ae_zero_off_chartImagePOUTsupport
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  have h_diff_open : IsOpen
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
      (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
  refine (ae_restrict_iff' h_diff_open.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro y hy
  exact chartPushed_eq_zero_off_chartImagePOUTsupport
    (I := I) (M := M) α _ hy.1 hy.2

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenMthMixedPartialChartPushedU_ae_zero_off_chartImagePOUTsupport
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ) :
    ∀ (_h_parent : MemWkp (d := Module.finrank ℝ E) m 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    (idx : Fin m → Fin (Module.finrank ℝ E)),
      chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
  induction m with
  | zero =>
      intro _h_parent _idx
      simpa [chosenMthMixedPartialChartPushedU_zero] using
        chartPushed_u_h_ae_zero_off_chartImagePOUTsupport
          (I := I) (M := M) g α u_h
  | succ m ih =>
      intro h_parent idx
      have h_parent_m : MemWkp (d := Module.finrank ℝ E) m 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (chartTargetEuclid (I := I) (M := M) α) := h_parent.le_succ
      have h_inner_ae := ih h_parent_m (Fin.init idx)
      have h_inner_memWkp : MemWkp (d := Module.finrank ℝ E) 1 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
            (Fin.init idx))
          (chartTargetEuclid (I := I) (M := M) α) := by
        have h_parent_m_plus_1 : MemWkp (d := Module.finrank ℝ E) (1 + m) 2
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
              ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
            (chartTargetEuclid (I := I) (M := M) α) := by
          rw [Nat.add_comm]
          exact h_parent
        exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
          (I := I) (M := M) g α u_h m 1 h_parent_m_plus_1 (Fin.init idx)
      have h_inner_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
            (Fin.init idx))
          (chartTargetEuclid (I := I) (M := M) α) := by
        rw [MemWkp.one_iff_memW1p] at h_inner_memWkp
        exact h_inner_memWkp
      have h_diff_open : IsOpen
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α) :=
        (chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
          (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
      have h_diff_subset : chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α ⊆
            chartTargetEuclid (I := I) (M := M) α := fun _ hy => hy.1
      have h_step :=
        chosenWeakPartial'_ae_zero_on_open_subset_of_ae_zero
          (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          (chartTargetEuclid_isOpen (I := I) (M := M) α)
          h_diff_open h_diff_subset
          h_inner_memW1p h_inner_ae (idx (Fin.last m))
      rw [chosenMthMixedPartialChartPushedU_succ]
      exact h_step

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem ibp_density_fChartEffPrev
    (g : SmoothRiemannianMetric I M) (α : M)
    {fChartEffPrev : EuclN → ℝ}
    (h_fChartEffPrev_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 fChartEffPrev
        (chartTargetEuclid (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * fChartEffPrev y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ (densityOnEuclid (I := I) g α) y)
              (EuclideanSpace.single l 1) *
            fChartEffPrev y * ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 l fChartEffPrev
              (chartTargetEuclid (I := I) (M := M) α) y *
            ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set v : EuclN → ℝ := fChartEffPrev with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun j =>
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 j v Ω with hw_def
  have h_v_memLp : MemLp v 2 ((volume : Measure EuclN).restrict Ω) :=
    h_fChartEffPrev_memW1p.1
  have hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := by
    intro K' hK'_compact hK'_in
    have hK'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
    have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K' =
        (volume : Measure EuclN).restrict K' := by
      rw [Measure.restrict_restrict hK'_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK'_in
    rw [← h_eq]
    exact h_v_memLp.restrict K'
  have hw_global : ∀ j : Fin (Module.finrank ℝ E),
      MemLp (w j) 2 ((volume : Measure EuclN).restrict Ω) := fun j =>
    chosenWeakPartial'_memLp_of_mem h_fChartEffPrev_memW1p j
  have hw_locMemLp : ∀ (j : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w j) 2 ((volume : Measure EuclN).restrict K') := by
    intro j K' hK'_compact hK'_in
    have hK'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
    have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K' =
        (volume : Measure EuclN).restrict K' := by
      rw [Measure.restrict_restrict hK'_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK'_in
    rw [← h_eq]
    exact (hw_global j).restrict K'
  have hw_isWeakPartial : ∀ j : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) j (w j) v Ω :=
    fun j => chosenWeakPartial'_isWeakPartial_of_mem h_fChartEffPrev_memW1p j
  have h_dens_chart : ContDiffOn ℝ (⊤ : ℕ∞)
      (densityOnEuclid (I := I) g α) Ω :=
    densityOnEuclid_contDiffOn (I := I) g α
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  obtain ⟨δ, dExt, hδ_pos, hδ_subset, hdExt_smooth, hdExt_eq⟩ :=
    exists_smooth_global_extension (I := I) (M := M)
      (φ := densityOnEuclid (I := I) g α) α h_dens_chart hK_compact hK_in
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have h_thick : Metric.cthickening δ K ⊆ Ω := hδ_subset
  have hK_in_thick : K ⊆ Metric.cthickening δ K := Metric.self_subset_cthickening _
  have h_fderiv_ψ_zero : ∀ x ∉ K, fderiv ℝ ψ x = 0 := by
    intro x hx
    have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
    have hx_in_compl : x ∈ Kᶜ := hx
    have hψ_zero_nbhd : ∀ᶠ y in 𝓝 x, ψ y = 0 := by
      filter_upwards [h_compl_open.mem_nhds hx_in_compl] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hψ_const_zero : fderiv ℝ ψ x = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hψ_zero_nbhd] with y hy
      rw [hy]
    rw [hψ_const_zero]; simp
  have h_ibp_ext :=
    integral_smul_weak_partial_eq (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := dExt) hdExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial l
      (ψ := ψ) hψ_smooth hψ_cs hψ_supp
  have hLHS_eq :
      ∫ y in Ω, dExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l 1) ∂(volume : Measure EuclN) =
      ∫ y in Ω, densityOnEuclid (I := I) g α y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l 1) ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [hdExt_eq y (hK_in_thick hy_K)]
    · rw [h_fderiv_ψ_zero y hy_K]
      simp
  have h_fderiv_dExt_eq_dens : ∀ y ∈ K, ∀ j' : Fin (Module.finrank ℝ E),
      (fderiv ℝ dExt y) (EuclideanSpace.single j' 1) =
      (fderiv ℝ (densityOnEuclid (I := I) g α) y) (EuclideanSpace.single j' 1) := by
    intro y hy_K j'
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]
      refine ⟨y, hy_K, ?_⟩
      simp [hδ_pos]
    have h_thick_open : IsOpen (Metric.thickening δ K) := Metric.isOpen_thickening
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y := h_thick_open.mem_nhds hy_thick_open
    have h_thick_sub : Metric.thickening δ K ⊆ Metric.cthickening δ K :=
      Metric.thickening_subset_cthickening _ _
    have h_eq_nbhd : dExt =ᶠ[𝓝 y] densityOnEuclid (I := I) g α := by
      filter_upwards [h_nbhd] with z hz
      exact hdExt_eq z (h_thick_sub hz)
    have h_fderiv_eq : fderiv ℝ dExt y = fderiv ℝ (densityOnEuclid (I := I) g α) y :=
      Filter.EventuallyEq.fderiv_eq h_eq_nbhd
    rw [h_fderiv_eq]
  have hLeib1_eq :
      ∫ y in Ω, (fderiv ℝ dExt y) (EuclideanSpace.single l 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ (densityOnEuclid (I := I) g α) y)
          (EuclideanSpace.single l 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_dExt_eq_dens y hy_K l]
    · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_K
      rw [hψy]; ring
  have hLeib2_eq :
      ∫ y in Ω, dExt y * w l y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, densityOnEuclid (I := I) g α y * w l y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [hdExt_eq y (hK_in_thick hy_K)]
    · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_K
      rw [hψy]; ring
  rw [← hLHS_eq, ← hLeib1_eq, ← hLeib2_eq]
  exact h_ibp_ext

private lemma snoc_cons_eq_cons_snoc {β : Type*} {m : ℕ}
    (i : β) (dirs : Fin m → β) (l : β) :
    @Fin.snoc m.succ (fun _ => β) (Fin.cons i dirs) l =
      Fin.cons i (Fin.snoc dirs l) :=
  (Fin.cons_snoc_eq_snoc_cons (β := β) i dirs l).symm

omit [NeZero (Module.finrank ℝ E)] in
private theorem ibp_principal_pair
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_2 :
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E))
    (i j : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        weightedInvGramOnEuclid (I := I) g α i j y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            (m + 1) (Fin.cons i dirs) y *
          (fderiv ℝ (fun z : EuclN =>
            (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
              (EuclideanSpace.single j 1)
        ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
              (EuclideanSpace.single l 1) *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 1) (Fin.cons i dirs) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 2) (Fin.cons i (Fin.snoc dirs l)) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN))) := by
  classical
  set ψ_j : EuclN → ℝ := fun y => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
    with hψ_j_def
  have hψ_j_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ_j :=
    contDiff_fderiv_apply_single (ψ := ψ) hψ_smooth j
  have hψ_j_cs : HasCompactSupport ψ_j :=
    hasCompactSupport_fderiv_apply_single (ψ := ψ) hψ_cs j
  have hψ_j_supp : tsupport ψ_j ⊆ chartTargetEuclid (I := I) (M := M) α :=
    (tsupport_fderiv_apply_single_subset ψ j).trans hψ_supp
  have h_schwarz : ∀ y : EuclN,
      (fderiv ℝ (fun z : EuclN =>
        (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
          (EuclideanSpace.single j 1) =
      (fderiv ℝ ψ_j y) (EuclideanSpace.single l 1) := by
    intro y
    change (fderiv ℝ
        (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
          (EuclideanSpace.single j 1) =
      (fderiv ℝ
        (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single j 1)) y)
          (EuclideanSpace.single l 1)
    exact fderiv_apply_single_swap (ψ := ψ) hψ_smooth y j l
  have h_lhs_schwarz :
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 1) (Fin.cons i dirs) y *
            (fderiv ℝ (fun z : EuclN =>
              (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
                (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN)) =
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 1) (Fin.cons i dirs) y *
            (fderiv ℝ ψ_j y) (EuclideanSpace.single l 1)
          ∂(volume : Measure EuclN)) := by
    refine setIntegral_congr_fun
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
      (fun y _ => ?_)
    rw [h_schwarz y]
  rw [h_lhs_schwarz]
  have h_ibp := per_pair_ibp_chosenMthMixed
    (I := I) (M := M) g α (m + 1) (Fin.cons i dirs)
    h_chart_H_m_plus_2
    (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j)
    hψ_j_smooth hψ_j_cs hψ_j_supp l
  have h_snoc_cons :
      Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E)) (Fin.cons i dirs) l =
        Fin.cons i (Fin.snoc dirs l) :=
    snoc_cons_eq_cons_snoc (β := Fin (Module.finrank ℝ E)) i dirs l
  rw [h_snoc_cons] at h_ibp
  exact h_ibp

omit [NeZero (Module.finrank ℝ E)] in
private theorem ibp_mass
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_1 :
      MemWkp (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l 1)
        ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ (densityOnEuclid (I := I) g α) y)
              (EuclideanSpace.single l 1) *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs y *
            ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 1) (Fin.snoc dirs l) y *
            ψ y
          ∂(volume : Measure EuclN))) :=
  per_pair_ibp_chosenMthMixed (I := I) (M := M) g α m dirs
    h_chart_H_m_plus_1
    (densityOnEuclid_contDiffOn (I := I) g α)
    hψ_smooth hψ_cs hψ_supp l

omit [NeZero (Module.finrank ℝ E)] in
private theorem ibp_inner_j
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_2 :
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E))
    (i j : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            (m + 1) (Fin.cons i dirs) y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
        ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 1) (Fin.cons i dirs) y *
            ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 2) (Fin.cons i (Fin.snoc dirs j)) y *
            ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  have h_ibp := per_pair_ibp_chosenMthMixed
    (I := I) (M := M) g α (m + 1) (Fin.cons i dirs)
    h_chart_H_m_plus_2
    (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l)
    hψ_smooth hψ_cs hψ_supp j
  have h_snoc_cons :
      Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E)) (Fin.cons i dirs) j =
        Fin.cons i (Fin.snoc dirs j) :=
    snoc_cons_eq_cons_snoc (β := Fin (Module.finrank ℝ E)) i dirs j
  rw [h_snoc_cons] at h_ibp
  exact h_ibp

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma integrable_triple_helper
    {α : M} {K : Set EuclN}
    (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {a : EuclN → ℝ}
    (ha : ContinuousOn a (chartTargetEuclid (I := I) (M := M) α))
    {u : EuclN → ℝ} (hu : IntegrableOn u K (volume : Measure EuclN))
    {h : EuclN → ℝ} (hh_cont : Continuous h) (hh_supp : tsupport h ⊆ K) :
    Integrable (fun y => a y * u y * h y)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hK_closed : IsClosed K := hK_compact.isClosed
  set h_prod : EuclN → ℝ := fun y => a y * h y
  have hh_prod_supp : tsupport h_prod ⊆ K := by
    refine closure_minimal (fun y hy => ?_) hK_closed
    by_contra hy_notin
    have hh_y : h y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h_in => hy_notin (hh_supp h_in))
    have h_eq_zero : a y * h y = 0 := by rw [hh_y, mul_zero]
    exact hy h_eq_zero
  have hh_prod_cont : Continuous h_prod := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y ∈ K
    · exact (ha.continuousAt (hΩ_open.mem_nhds (hK_in hy))).mul hh_cont.continuousAt
    · have h_compl_open : IsOpen (Kᶜ) := hK_closed.isOpen_compl
      have h_eq_zero : ∀ᶠ z in 𝓝 y, h_prod z = 0 := by
        filter_upwards [h_compl_open.mem_nhds hy] with z hz
        have hh_z : h z = 0 := image_eq_zero_of_notMem_tsupport
          (fun h_in => hz (hh_supp h_in))
        change a z * h z = 0; rw [hh_z, mul_zero]
      rw [continuousAt_congr h_eq_zero]; exact continuousAt_const
  have hh_prod_contOn_K : ContinuousOn h_prod K := hh_prod_cont.continuousOn
  have hu_h_int_K : IntegrableOn (fun y => u y * h_prod y) K
      (volume : Measure EuclN) :=
    hu.mul_continuousOn hh_prod_contOn_K hK_compact
  have h_vanish : ∀ y, y ∉ K → u y * h_prod y = 0 := by
    intro y hy
    have hp : h_prod y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hy_supp => hy (hh_prod_supp hy_supp))
    simp [hp]
  have h_eq_ind :
      (fun y => u y * h_prod y) = K.indicator (fun y => u y * h_prod y) := by
    funext y
    by_cases hy : y ∈ K
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy, h_vanish y hy]
  have ind_int : Integrable (K.indicator (fun y => u y * h_prod y))
      (volume : Measure EuclN) :=
    (integrable_indicator_iff hK_meas).mpr hu_h_int_K
  have full_int : Integrable (fun y => u y * h_prod y) (volume : Measure EuclN) := by
    rw [h_eq_ind]; exact ind_int
  have h_reassoc : (fun y => u y * h_prod y) = (fun y => a y * u y * h y) := by
    funext y; change u y * (a y * h y) = _; ring
  rw [h_reassoc] at full_int
  exact full_int.restrict

set_option maxHeartbeats 4000000 in

noncomputable def iteratedDiffChartBilinearData_step
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} (m : ℕ)
    (D_m : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m)
    (l : Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_1 :
      MemWkp (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_m_plus_2 :
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_fChartEff_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 D_m.diffChartForcing
        (chartTargetEuclid (I := I) (M := M) α))
    (h_fChartEff_ae_zero_off_K :
      D_m.diffChartForcing =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ))) :
    IteratedDiffChartBilinearData (I := I) (M := M) g α u_h (m + 1) :=
  IteratedDiffChartBilinearData.mk_from_hypotheses
    (Fin.snoc D_m.directions l)
    (fChartEffStep (I := I) (M := M) g α u_h m D_m.directions D_m.diffChartForcing l)
    (fChartEffStep_memLp_two_weighted (I := I) (M := M)
      (g := g) (α := α) (u_h := u_h) (m := m) (dirs := D_m.directions)
      h_chart_H_m_plus_1 h_chart_H_m_plus_2
      (fChartEffPrev := D_m.diffChartForcing)
      D_m.fChartEff_memLp_weighted (l := l))
    (by
      classical
      intro ψ hψ_smooth hψ_cs hψ_supp
      set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
      have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
      have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
      set Kα : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hKα_def
      have hKα_compact : IsCompact Kα :=
        chartImagePOUTsupport_isCompact (I := I) (M := M) α
      have hKα_meas : MeasurableSet Kα := hKα_compact.isClosed.measurableSet
      have hKα_in : Kα ⊆ Ω := chartImagePOUTsupport_subset_target (I := I) (M := M) α
      have hΩ_diff_Kα_open : IsOpen (Ω \ Kα) := hΩ_open.sdiff hKα_compact.isClosed
      have hΩ_diff_Kα_meas : MeasurableSet (Ω \ Kα) := hΩ_diff_Kα_open.measurableSet
      set ψ_l : EuclN → ℝ := fun y =>
        (fderiv ℝ ψ y) (EuclideanSpace.single l 1) with hψ_l_def
      have hψ_l_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ_l :=
        contDiff_fderiv_apply_single (ψ := ψ) hψ_smooth l
      have hψ_l_cs : HasCompactSupport ψ_l :=
        hasCompactSupport_fderiv_apply_single (ψ := ψ) hψ_cs l
      have hψ_l_supp : tsupport ψ_l ⊆ Ω :=
        (tsupport_fderiv_apply_single_subset ψ l).trans hψ_supp
      have h_level_m :=
        D_m.m_diff_variational_identity ψ_l hψ_l_smooth hψ_l_cs hψ_l_supp
      set A_pair : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
        fun i j =>
          ∫ y in Ω,
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
                (EuclideanSpace.single j 1) *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 1) (Fin.cons i D_m.directions) y *
              ψ y
            ∂(volume : Measure EuclN) with hA_pair_def
      set B_pair : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
        fun i j =>
          ∫ y in Ω,
            weightedInvGramDerivOnEuclid (I := I) g α i j l y *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 2) (Fin.cons i (Fin.snoc D_m.directions j)) y *
              ψ y
            ∂(volume : Measure EuclN) with hB_pair_def
      set PR_pair : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
        fun i j =>
          ∫ y in Ω,
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 2) (Fin.cons i (Fin.snoc D_m.directions l)) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
            ∂(volume : Measure EuclN) with hPR_pair_def
      set INT_LHS_m_pair : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
        fun i j =>
          ∫ y in Ω,
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 1) (Fin.cons i D_m.directions) y *
              (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1)
            ∂(volume : Measure EuclN) with hINT_LHS_m_pair_def
      have h_principal_pair : ∀ i j : Fin (Module.finrank ℝ E),
          INT_LHS_m_pair i j = A_pair i j + B_pair i j - PR_pair i j := by
        intro i j
        have h_pp := ibp_principal_pair (I := I) (M := M) g α m D_m.directions
          h_chart_H_m_plus_2 l i j hψ_smooth hψ_cs hψ_supp
        have h_inner := ibp_inner_j (I := I) (M := M) g α m D_m.directions
          h_chart_H_m_plus_2 l i j hψ_smooth hψ_cs hψ_supp
        have h_pp' : INT_LHS_m_pair i j =
            -((∫ y in Ω,
                weightedInvGramDerivOnEuclid (I := I) g α i j l y *
                  chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                    (m + 1) (Fin.cons i D_m.directions) y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
                ∂(volume : Measure EuclN))
              + PR_pair i j) := h_pp
        rw [h_pp', h_inner]
        ring
      set K : Set EuclN := tsupport ψ with hK_def
      have hK_compact : IsCompact K := hψ_cs
      have hK_meas : MeasurableSet K := (isClosed_tsupport ψ).measurableSet
      have hK_in : K ⊆ Ω := hψ_supp
      have h_aij_cont : ∀ i j : Fin (Module.finrank ℝ E),
          ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j) Ω :=
        fun i j => (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
      have h_daij_cont : ∀ i j : Fin (Module.finrank ℝ E),
          ContinuousOn (weightedInvGramDerivOnEuclid (I := I) g α i j l) Ω :=
        fun i j =>
          (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l).continuousOn
      have h_dens_cont : ContinuousOn (densityOnEuclid (I := I) g α) Ω :=
        densityOnEuclid_continuousOn (I := I) g α
      have h_dens_deriv_cont : ContinuousOn
          (densityDerivOnEuclid (I := I) g α l) Ω :=
        (densityDerivOnEuclid_contDiffOn (I := I) g α l).continuousOn
      have h_aij_fderiv_cont : ∀ i j : Fin (Module.finrank ℝ E),
          ContinuousOn (fun y : EuclN =>
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1)) Ω := by
        intro i j
        have h_diffOn :
            ContDiffOn ℝ (⊤ : ℕ∞) (weightedInvGramDerivOnEuclid (I := I) g α i j l) Ω :=
          weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l
        have h_fderiv_diff :
            ContDiffOn ℝ (⊤ : ℕ∞)
              (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y) Ω :=
          ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ_open).1 h_diffOn).2
        have h_eval : ContDiff ℝ (⊤ : ℕ∞)
            (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single j 1)) :=
          (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).contDiff
        exact (h_eval.contDiffOn.comp h_fderiv_diff (mapsTo_univ _ _)).continuousOn
      have h_dens_fderiv_cont : ContinuousOn (fun y : EuclN =>
            (fderiv ℝ (densityOnEuclid (I := I) g α) y)
              (EuclideanSpace.single l 1)) Ω := by
        change ContinuousOn (densityDerivOnEuclid (I := I) g α l) Ω
        exact h_dens_deriv_cont
      have hψ_cont : Continuous ψ := hψ_smooth.continuous
      have hψ_supp_K : tsupport ψ ⊆ K := le_refl _
      have hψ_partial_cont : ∀ j : Fin (Module.finrank ℝ E),
          Continuous (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
        fun j => (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
      have hψ_partial_supp : ∀ j : Fin (Module.finrank ℝ E),
          tsupport (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) ⊆ K :=
        fun j => tsupport_fderiv_apply_single_subset ψ j
      have hψ_l_partial_cont : ∀ j : Fin (Module.finrank ℝ E),
          Continuous (fun y : EuclN => (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1)) :=
        fun j => (hψ_l_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
      have hψ_l_partial_supp : ∀ j : Fin (Module.finrank ℝ E),
          tsupport (fun y : EuclN => (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1)) ⊆ K :=
        fun j =>
          (tsupport_fderiv_apply_single_subset ψ_l j).trans
            (tsupport_fderiv_apply_single_subset ψ l)
      have hvolK_finite : (volume : Measure EuclN) K < (⊤ : ℝ≥0∞) :=
        hK_compact.measure_lt_top
      have hvolK_finite' : (volume.restrict K : Measure EuclN) Set.univ < (⊤ : ℝ≥0∞) := by
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact hvolK_finite
      haveI : IsFiniteMeasure ((volume : Measure EuclN).restrict K) := ⟨hvolK_finite'⟩
      have h_M_m_int : IntegrableOn
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
            D_m.directions) K (volume : Measure EuclN) := by
        have h_parent_m : MemWkp (d := Module.finrank ℝ E) m 2
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
              ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
            (chartTargetEuclid (I := I) (M := M) α) :=
          h_chart_H_m_plus_1.le_succ
        exact (chosenMthMixedPartialChartPushedU_locally_memLp
          (I := I) (M := M) g α u_h m h_parent_m D_m.directions
          hK_compact hK_in).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h_M_m1_int : ∀ idx : Fin (m + 1) → Fin (Module.finrank ℝ E),
          IntegrableOn
            (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1) idx)
            K (volume : Measure EuclN) :=
        fun idx =>
          (chosenMthMixedPartialChartPushedU_locally_memLp (I := I) (M := M) g α u_h
            (m + 1) h_chart_H_m_plus_1 idx
            hK_compact hK_in).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h_M_m2_int : ∀ idx : Fin (m + 2) → Fin (Module.finrank ℝ E),
          IntegrableOn
            (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 2) idx)
            K (volume : Measure EuclN) :=
        fun idx =>
          (chosenMthMixedPartialChartPushedU_locally_memLp (I := I) (M := M) g α u_h
            (m + 2) h_chart_H_m_plus_2 idx
            hK_compact hK_in).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h_fChartEff_int : IntegrableOn D_m.diffChartForcing K (volume : Measure EuclN) := by
        have h_global : MemLp D_m.diffChartForcing 2
            ((volume : Measure EuclN).restrict Ω) := h_fChartEff_memW1p.1
        have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K =
            (volume : Measure EuclN).restrict K := by
          rw [Measure.restrict_restrict hK_meas]; congr 1
          exact Set.inter_eq_self_of_subset_left hK_in
        have h_K : MemLp D_m.diffChartForcing 2 ((volume : Measure EuclN).restrict K) := by
          rw [← h_eq]; exact h_global.restrict K
        exact h_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h_fChartEff_wp_int : IntegrableOn
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 l D_m.diffChartForcing Ω)
          K (volume : Measure EuclN) := by
        have h_global := chosenWeakPartial'_memLp_of_mem h_fChartEff_memW1p l
        have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K =
            (volume : Measure EuclN).restrict K := by
          rw [Measure.restrict_restrict hK_meas]; congr 1
          exact Set.inter_eq_self_of_subset_left hK_in
        have h_K : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 l
            D_m.diffChartForcing Ω) 2
            ((volume : Measure EuclN).restrict K) := by
          rw [← h_eq]; exact h_global.restrict K
        exact h_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h_int_LHS_m_pair : ∀ i j : Fin (Module.finrank ℝ E),
          Integrable (fun y => weightedInvGramOnEuclid (I := I) g α i j y *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 1) (Fin.cons i D_m.directions) y *
              (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1))
            ((volume : Measure EuclN).restrict Ω) := fun i j =>
        integrable_triple_helper (α := α) hK_compact hK_meas hK_in
          (h_aij_cont i j) (h_M_m1_int (Fin.cons i D_m.directions))
          (hψ_l_partial_cont j) (hψ_l_partial_supp j)
      have h_int_A_pair : ∀ i j,
          Integrable (fun y =>
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 1) (Fin.cons i D_m.directions) y * ψ y)
            ((volume : Measure EuclN).restrict Ω) := fun i j =>
        integrable_triple_helper (α := α) hK_compact hK_meas hK_in
          (h_aij_fderiv_cont i j)
          (h_M_m1_int (Fin.cons i D_m.directions)) hψ_cont hψ_supp_K
      have h_int_B_pair : ∀ i j,
          Integrable (fun y =>
            weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 2) (Fin.cons i (Fin.snoc D_m.directions j)) y * ψ y)
            ((volume : Measure EuclN).restrict Ω) := fun i j =>
        integrable_triple_helper (α := α) hK_compact hK_meas hK_in
          (h_daij_cont i j)
          (h_M_m2_int (Fin.cons i (Fin.snoc D_m.directions j))) hψ_cont hψ_supp_K
      have h_int_PR_pair : ∀ i j,
          Integrable (fun y =>
            weightedInvGramOnEuclid (I := I) g α i j y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 2) (Fin.cons i (Fin.snoc D_m.directions l)) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
            ((volume : Measure EuclN).restrict Ω) := fun i j =>
        integrable_triple_helper (α := α) hK_compact hK_meas hK_in
          (h_aij_cont i j)
          (h_M_m2_int (Fin.cons i (Fin.snoc D_m.directions l)))
          (hψ_partial_cont j) (hψ_partial_supp j)
      set INT_LHS_principal_m_l : ℝ :=
        ∫ y in Ω,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                  (m + 1) (Fin.cons i D_m.directions) y *
                (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) with hINT_LHS_principal_m_l_def
      set INT_LHS_mass_m_l : ℝ :=
        ∫ y in Ω,
          densityOnEuclid (I := I) g α y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
              D_m.directions y * ψ_l y
          ∂(volume : Measure EuclN) with hINT_LHS_mass_m_l_def
      set INT_RHS_m_l : ℝ :=
        ∫ y in Ω,
          densityOnEuclid (I := I) g α y * D_m.diffChartForcing y * ψ_l y
          ∂(volume : Measure EuclN) with hINT_RHS_m_l_def
      have h_level_m' :
          INT_LHS_principal_m_l + INT_LHS_mass_m_l = INT_RHS_m_l := h_level_m
      have h_swap_LHS_principal :
          INT_LHS_principal_m_l = ∑ i, ∑ j, INT_LHS_m_pair i j := by
        change (∫ y in Ω,
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α i j y *
                  chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                    (m + 1) (Fin.cons i D_m.directions) y *
                  (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1))
            ∂(volume : Measure EuclN)) = _
        rw [integral_finset_sum _ (fun i _ =>
          (integrable_finset_sum _ (fun j _ => h_int_LHS_m_pair i j)))]
        refine Finset.sum_congr rfl ?_; intro i _
        rw [integral_finset_sum _ (fun j _ => h_int_LHS_m_pair i j)]
      have h_sum_principal :
          ∑ i, ∑ j, INT_LHS_m_pair i j =
          (∑ i, ∑ j, A_pair i j) + (∑ i, ∑ j, B_pair i j) - (∑ i, ∑ j, PR_pair i j) := by
        calc ∑ i, ∑ j, INT_LHS_m_pair i j
            = ∑ i, ∑ j, (A_pair i j + B_pair i j - PR_pair i j) := by
              refine Finset.sum_congr rfl ?_; intro i _
              refine Finset.sum_congr rfl ?_; intro j _
              exact h_principal_pair i j
          _ = ∑ i, ∑ j, (A_pair i j + (B_pair i j + (-(PR_pair i j)))) := by
              refine Finset.sum_congr rfl ?_; intro i _
              refine Finset.sum_congr rfl ?_; intro j _
              ring
          _ = ∑ i, (∑ j, A_pair i j) + ∑ i, (∑ j, (B_pair i j + (-(PR_pair i j)))) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_; intro i _
              exact Finset.sum_add_distrib
          _ = (∑ i, ∑ j, A_pair i j) +
              ((∑ i, ∑ j, B_pair i j) + ∑ i, ∑ j, -(PR_pair i j)) := by
              congr 1
              rw [show (fun i => ∑ j, (B_pair i j + (-(PR_pair i j)))) =
                  (fun i => (∑ j, B_pair i j) + (∑ j, -(PR_pair i j))) by
                funext i; exact Finset.sum_add_distrib]
              exact Finset.sum_add_distrib
          _ = (∑ i, ∑ j, A_pair i j) + (∑ i, ∑ j, B_pair i j) -
              (∑ i, ∑ j, PR_pair i j) := by
              simp_rw [Finset.sum_neg_distrib (s :=
                (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
              ring
      have h_dens_fderiv_eq : ∀ y : EuclN,
          (fderiv ℝ (densityOnEuclid (I := I) g α) y) (EuclideanSpace.single l 1) =
            densityDerivOnEuclid (I := I) g α l y := fun _ => rfl
      set N_C : ℝ :=
        ∫ y in Ω, densityDerivOnEuclid (I := I) g α l y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
            D_m.directions y * ψ y
          ∂(volume : Measure EuclN) with hN_C_def
      set N_mass_new : ℝ :=
        ∫ y in Ω,
          densityOnEuclid (I := I) g α y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            (m + 1) (Fin.snoc D_m.directions l) y * ψ y
          ∂(volume : Measure EuclN) with hN_mass_new_def
      have h_mass_ibp : INT_LHS_mass_m_l = -(N_C + N_mass_new) := by
        have hb := ibp_mass (I := I) (M := M) g α m D_m.directions
          h_chart_H_m_plus_1 l hψ_smooth hψ_cs hψ_supp
        change (∫ y in Ω,
            densityOnEuclid (I := I) g α y *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
                D_m.directions y * ψ_l y
            ∂(volume : Measure EuclN)) = _
        rw [hb]
        rfl
      set N_D : ℝ :=
        ∫ y in Ω, densityDerivOnEuclid (I := I) g α l y *
          D_m.diffChartForcing y * ψ y
          ∂(volume : Measure EuclN) with hN_D_def
      set N_E : ℝ :=
        ∫ y in Ω, densityOnEuclid (I := I) g α y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 l D_m.diffChartForcing Ω y * ψ y
          ∂(volume : Measure EuclN) with hN_E_def
      have h_rhs_ibp : INT_RHS_m_l = -(N_D + N_E) := by
        have hb := ibp_density_fChartEffPrev (I := I) (M := M) g α
          h_fChartEff_memW1p l hψ_smooth hψ_cs hψ_supp
        change (∫ y in Ω,
            densityOnEuclid (I := I) g α y * D_m.diffChartForcing y * ψ_l y
            ∂(volume : Measure EuclN)) = _
        rw [hb]
        rfl
      have h_combine : (∑ i, ∑ j, PR_pair i j) + N_mass_new =
          (∑ i, ∑ j, A_pair i j) + (∑ i, ∑ j, B_pair i j) +
            (-N_C) + N_D + N_E := by
        have h := h_level_m'
        rw [h_swap_LHS_principal, h_sum_principal, h_mass_ibp, h_rhs_ibp] at h
        linarith
      set I_step_RHS : ℝ :=
        ∫ y in Ω,
          densityOnEuclid (I := I) g α y *
            fChartEffStep (I := I) (M := M) g α u_h m D_m.directions
              D_m.diffChartForcing l y * ψ y
          ∂(volume : Measure EuclN) with hI_step_RHS_def
      set LHS_principal_new : ℝ :=
        ∫ y in Ω,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                  (m + 2) (Fin.cons i (Fin.snoc D_m.directions l)) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) with hLHS_principal_new_def
      have h_LHS_principal_new_eq : LHS_principal_new = ∑ i, ∑ j, PR_pair i j := by
        change (∫ y in Ω,
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α i j y *
                  chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                    (m + 2) (Fin.cons i (Fin.snoc D_m.directions l)) y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
            ∂(volume : Measure EuclN)) = _
        rw [integral_finset_sum _ (fun i _ =>
          (integrable_finset_sum _ (fun j _ => h_int_PR_pair i j)))]
        refine Finset.sum_congr rfl ?_; intro i _
        rw [integral_finset_sum _ (fun j _ => h_int_PR_pair i j)]
      have h_M_m_ae :
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m D_m.directions
            =ᵐ[(volume : Measure EuclN).restrict (Ω \ Kα)]
            (fun _ : EuclN => (0 : ℝ)) :=
        chosenMthMixedPartialChartPushedU_ae_zero_off_chartImagePOUTsupport
          (I := I) (M := M) g α u_h m h_chart_H_m_plus_1.le_succ D_m.directions
      have h_M_m1_ae : ∀ idx : Fin (m + 1) → Fin (Module.finrank ℝ E),
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1) idx
            =ᵐ[(volume : Measure EuclN).restrict (Ω \ Kα)]
            (fun _ : EuclN => (0 : ℝ)) := fun idx =>
        chosenMthMixedPartialChartPushedU_ae_zero_off_chartImagePOUTsupport
          (I := I) (M := M) g α u_h (m + 1) h_chart_H_m_plus_1 idx
      have h_M_m2_ae : ∀ idx : Fin (m + 2) → Fin (Module.finrank ℝ E),
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 2) idx
            =ᵐ[(volume : Measure EuclN).restrict (Ω \ Kα)]
            (fun _ : EuclN => (0 : ℝ)) := fun idx =>
        chosenMthMixedPartialChartPushedU_ae_zero_off_chartImagePOUTsupport
          (I := I) (M := M) g α u_h (m + 2) h_chart_H_m_plus_2 idx
      have h_fChartEff_wp_ae :
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 l D_m.diffChartForcing Ω
            =ᵐ[(volume : Measure EuclN).restrict (Ω \ Kα)]
            (fun _ : EuclN => (0 : ℝ)) := by
        exact
          chosenWeakPartial'_ae_zero_on_open_subset_of_ae_zero
            (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
            hΩ_open hΩ_diff_Kα_open (fun _ hy => hy.1)
            h_fChartEff_memW1p h_fChartEff_ae_zero_off_K l
      have h_numer_ae_zero :
          ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Kα)),
            fChartEffStepNumerator (I := I) (M := M) g α u_h m D_m.directions
              D_m.diffChartForcing l y = 0 := by
        have h_M_m1_each : ∀ i : Fin (Module.finrank ℝ E),
            ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Kα)),
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1)
                (Fin.cons i D_m.directions) y = 0 :=
          fun i => h_M_m1_ae (Fin.cons i D_m.directions)
        have h_M_m2_j_each : ∀ i j : Fin (Module.finrank ℝ E),
            ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Kα)),
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 2)
                (Fin.cons i (Fin.snoc D_m.directions j)) y = 0 :=
          fun i j => h_M_m2_ae (Fin.cons i (Fin.snoc D_m.directions j))
        have h_M_m1_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Kα)),
            ∀ i : Fin (Module.finrank ℝ E),
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1)
                (Fin.cons i D_m.directions) y = 0 := by
          rw [ae_all_iff]; exact h_M_m1_each
        have h_M_m2_j_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Kα)),
            ∀ i j : Fin (Module.finrank ℝ E),
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 2)
                (Fin.cons i (Fin.snoc D_m.directions j)) y = 0 := by
          rw [ae_all_iff]; intro i; rw [ae_all_iff]; exact h_M_m2_j_each i
        filter_upwards [h_M_m_ae, h_M_m1_all, h_M_m2_j_all,
          h_fChartEff_ae_zero_off_K, h_fChartEff_wp_ae] with y h_M_m_y h_M_m1_y
          h_M_m2_j_y h_fE_y h_fE_wp_y
        unfold fChartEffStepNumerator
        have h_A_zero :
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
                    (EuclideanSpace.single j 1) *
                  chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1)
                    (Fin.cons i D_m.directions) y) = 0 := by
          refine Finset.sum_eq_zero ?_; intro i _
          refine Finset.sum_eq_zero ?_; intro _ _
          rw [h_M_m1_y i]; ring
        have h_B_zero :
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                weightedInvGramDerivOnEuclid (I := I) g α i j l y *
                  chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 2)
                    (Fin.cons i (Fin.snoc D_m.directions j)) y) = 0 := by
          refine Finset.sum_eq_zero ?_; intro i _
          refine Finset.sum_eq_zero ?_; intro j _
          rw [h_M_m2_j_y i j]; ring
        rw [h_A_zero, h_B_zero, h_M_m_y, h_fE_y, h_fE_wp_y]
        ring
      have h_step_RHS_eq_indicator :
          I_step_RHS =
          ∫ y in Ω,
            Set.indicator Kα
              (fun z => fChartEffStepNumerator (I := I) (M := M) g α u_h m
                D_m.directions D_m.diffChartForcing l z) y * ψ y
            ∂(volume : Measure EuclN) := by
        change (∫ y in Ω,
            densityOnEuclid (I := I) g α y *
              fChartEffStep (I := I) (M := M) g α u_h m D_m.directions
                D_m.diffChartForcing l y * ψ y
            ∂(volume : Measure EuclN)) = _
        refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
        have h_pt := density_mul_fChartEffStep_eq_indicator_numerator
          (I := I) (M := M) g α u_h m D_m.directions D_m.diffChartForcing l y hy
        rw [show densityOnEuclid (I := I) g α y *
            fChartEffStep (I := I) (M := M) g α u_h m D_m.directions
              D_m.diffChartForcing l y * ψ y =
            (densityOnEuclid (I := I) g α y *
              fChartEffStep (I := I) (M := M) g α u_h m D_m.directions
                D_m.diffChartForcing l y) * ψ y from rfl]
        rw [h_pt]
      have h_indicator_eq_numerator :
          ∫ y in Ω,
            Set.indicator Kα
              (fun z => fChartEffStepNumerator (I := I) (M := M) g α u_h m
                D_m.directions D_m.diffChartForcing l z) y * ψ y
            ∂(volume : Measure EuclN) =
          ∫ y in Ω,
            fChartEffStepNumerator (I := I) (M := M) g α u_h m D_m.directions
              D_m.diffChartForcing l y * ψ y
            ∂(volume : Measure EuclN) := by
        refine MeasureTheory.integral_congr_ae ?_
        refine (ae_restrict_iff' hΩ_meas).mpr ?_
        have h_off : ∀ᵐ y ∂(volume : Measure EuclN),
            y ∈ Ω \ Kα →
            fChartEffStepNumerator (I := I) (M := M) g α u_h m D_m.directions
              D_m.diffChartForcing l y = 0 := by
          rw [← ae_restrict_iff' hΩ_diff_Kα_meas]
          exact h_numer_ae_zero
        filter_upwards [h_off] with y hy hy_Ω
        by_cases hy_Kα : y ∈ Kα
        · rw [Set.indicator_of_mem hy_Kα]
        · rw [Set.indicator_of_notMem hy_Kα]
          have hy_diff : y ∈ Ω \ Kα := ⟨hy_Ω, hy_Kα⟩
          rw [hy hy_diff]
      have h_step_RHS_eq_num : I_step_RHS =
          ∫ y in Ω,
            fChartEffStepNumerator (I := I) (M := M) g α u_h m D_m.directions
              D_m.diffChartForcing l y * ψ y
            ∂(volume : Measure EuclN) := by
        rw [h_step_RHS_eq_indicator]; exact h_indicator_eq_numerator
      have h_int_C : Integrable (fun y =>
          densityDerivOnEuclid (I := I) g α l y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
              D_m.directions y * ψ y)
          ((volume : Measure EuclN).restrict Ω) :=
        integrable_triple_helper (α := α) hK_compact hK_meas hK_in
          h_dens_deriv_cont h_M_m_int hψ_cont hψ_supp_K
      have h_int_D : Integrable (fun y =>
          densityDerivOnEuclid (I := I) g α l y * D_m.diffChartForcing y * ψ y)
          ((volume : Measure EuclN).restrict Ω) :=
        integrable_triple_helper (α := α) hK_compact hK_meas hK_in
          h_dens_deriv_cont h_fChartEff_int hψ_cont hψ_supp_K
      have h_int_E : Integrable (fun y =>
          densityOnEuclid (I := I) g α y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 l D_m.diffChartForcing Ω y * ψ y)
          ((volume : Measure EuclN).restrict Ω) :=
        integrable_triple_helper (α := α) hK_compact hK_meas hK_in
          h_dens_cont h_fChartEff_wp_int hψ_cont hψ_supp_K
      have h_numer_decomp :
          (∫ y in Ω,
            fChartEffStepNumerator (I := I) (M := M) g α u_h m D_m.directions
              D_m.diffChartForcing l y * ψ y
            ∂(volume : Measure EuclN)) =
          (∑ i, ∑ j, A_pair i j) + (∑ i, ∑ j, B_pair i j) - N_C + N_D + N_E := by
        set f_A : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 1) (Fin.cons i D_m.directions) y * ψ y with hf_A_def
        set f_B : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 2) (Fin.cons i (Fin.snoc D_m.directions j)) y * ψ y with hf_B_def
        set f_C : EuclN → ℝ := fun y =>
          - (densityDerivOnEuclid (I := I) g α l y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
              D_m.directions y * ψ y) with hf_C_def
        set f_D : EuclN → ℝ := fun y =>
          densityDerivOnEuclid (I := I) g α l y *
            D_m.diffChartForcing y * ψ y with hf_D_def
        set f_E : EuclN → ℝ := fun y =>
          densityOnEuclid (I := I) g α y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 l D_m.diffChartForcing Ω y *
            ψ y with hf_E_def
        have h_integrand_eq : ∀ y : EuclN,
            fChartEffStepNumerator (I := I) (M := M) g α u_h m D_m.directions
              D_m.diffChartForcing l y * ψ y =
            f_A y + f_B y + f_C y + f_D y + f_E y := by
          intro y
          unfold fChartEffStepNumerator
          simp only [add_mul, sub_mul, Finset.sum_mul]
          ring
        rw [setIntegral_congr_fun hΩ_meas (fun y _ => h_integrand_eq y)]
        have hint_A : Integrable f_A ((volume : Measure EuclN).restrict Ω) :=
          integrable_finset_sum _ (fun i _ =>
            integrable_finset_sum _ (fun j _ => h_int_A_pair i j))
        have hint_B : Integrable f_B ((volume : Measure EuclN).restrict Ω) :=
          integrable_finset_sum _ (fun i _ =>
            integrable_finset_sum _ (fun j _ => h_int_B_pair i j))
        have hint_C : Integrable f_C ((volume : Measure EuclN).restrict Ω) :=
          h_int_C.neg
        have hint_D : Integrable f_D ((volume : Measure EuclN).restrict Ω) :=
          h_int_D
        have hint_E : Integrable f_E ((volume : Measure EuclN).restrict Ω) :=
          h_int_E
        have h_sum_AB : Integrable (fun y => f_A y + f_B y)
            ((volume : Measure EuclN).restrict Ω) := hint_A.add hint_B
        have h_sum_ABC : Integrable (fun y => f_A y + f_B y + f_C y)
            ((volume : Measure EuclN).restrict Ω) := h_sum_AB.add hint_C
        have h_sum_ABCD : Integrable (fun y => f_A y + f_B y + f_C y + f_D y)
            ((volume : Measure EuclN).restrict Ω) := h_sum_ABC.add hint_D
        rw [MeasureTheory.integral_add h_sum_ABCD hint_E]
        rw [MeasureTheory.integral_add h_sum_ABC hint_D]
        rw [MeasureTheory.integral_add h_sum_AB hint_C]
        rw [MeasureTheory.integral_add hint_A hint_B]
        have h_int_f_A : (∫ y in Ω, f_A y ∂(volume : Measure EuclN)) =
            ∑ i, ∑ j, A_pair i j := by
          change (∫ y in Ω,
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
                    (EuclideanSpace.single j 1) *
                  chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                    (m + 1) (Fin.cons i D_m.directions) y * ψ y
              ∂(volume : Measure EuclN)) = _
          rw [integral_finset_sum _ (fun i _ =>
            (integrable_finset_sum _ (fun j _ => h_int_A_pair i j)))]
          refine Finset.sum_congr rfl ?_; intro i _
          rw [integral_finset_sum _ (fun j _ => h_int_A_pair i j)]
        have h_int_f_B : (∫ y in Ω, f_B y ∂(volume : Measure EuclN)) =
            ∑ i, ∑ j, B_pair i j := by
          change (∫ y in Ω,
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  weightedInvGramDerivOnEuclid (I := I) g α i j l y *
                  chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                    (m + 2) (Fin.cons i (Fin.snoc D_m.directions j)) y * ψ y
              ∂(volume : Measure EuclN)) = _
          rw [integral_finset_sum _ (fun i _ =>
            (integrable_finset_sum _ (fun j _ => h_int_B_pair i j)))]
          refine Finset.sum_congr rfl ?_; intro i _
          rw [integral_finset_sum _ (fun j _ => h_int_B_pair i j)]
        have h_int_f_C : (∫ y in Ω, f_C y ∂(volume : Measure EuclN)) = -N_C := by
          change (∫ y in Ω,
              - (densityDerivOnEuclid (I := I) g α l y *
                chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
                  D_m.directions y * ψ y)
              ∂(volume : Measure EuclN)) = _
          rw [MeasureTheory.integral_neg]
        have h_int_f_D : (∫ y in Ω, f_D y ∂(volume : Measure EuclN)) = N_D := rfl
        have h_int_f_E : (∫ y in Ω, f_E y ∂(volume : Measure EuclN)) = N_E := rfl
        rw [h_int_f_A, h_int_f_B, h_int_f_C, h_int_f_D, h_int_f_E]
        ring
      change LHS_principal_new + N_mass_new = I_step_RHS
      rw [h_LHS_principal_new_eq, h_step_RHS_eq_num, h_numer_decomp]
      linarith)

end IteratedVariationalIdentityStep
end Laplacian
end Analysis
end DifferentialGeometry

end
