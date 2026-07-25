import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifold
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuant
import DifferentialGeometry.Analysis.Sobolev.Tools.StrictStrongSupport
import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.Approximation.ContMDiffDenseLemmas
import DifferentialGeometry.Analysis.Sobolev.Manifold.SobolevAlgebraSmoothExtension


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private def chartLifted (α : M) (v : M → ℝ) : EuclN → ℝ :=
  fun y => v ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

omit [IsManifold I ∞ M] in
private lemma chartPushed_mul_eq_chartPushed_mul_chartLifted
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (α : M) (u v : M → ℝ) (y : EuclN) :
    chartPushed (I := I) (M := M) ρ α (fun x => u x * v x) y =
      chartPushed (I := I) (M := M) ρ α u y *
        chartLifted (I := I) (M := M) α v y := by
  unfold chartPushed chartLifted
  ring

omit [IsManifold I ∞ M] in
private lemma chartLifted_apply_norm_le
    (α : M) (v : M → ℝ) {Cv : ℝ} (hCv : ∀ x : M, ‖v x‖ ≤ Cv) (y : EuclN) :
    ‖chartLifted (I := I) (M := M) α v y‖ ≤ Cv := by
  unfold chartLifted
  exact hCv _

private lemma chartPushed_norm_le_sup
    [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) {Cu : ℝ} (hCu : ∀ x : M, ‖u x‖ ≤ Cu) (y : EuclN) :
    ‖chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y‖ ≤ Cu := by
  unfold chartPushed
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
  have hρ_range :
      Set.range ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro r ⟨z, hz⟩
    refine ⟨?_, ?_⟩
    · have := (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg α z
      rw [← hz]; exact this
    · have := (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).le_one α z
      rw [← hz]; exact this
  have hρ_x_nonneg : 0 ≤ (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x :=
    (hρ_range ⟨x, rfl⟩).1
  have hρ_x_le_one : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x ≤ 1 :=
    (hρ_range ⟨x, rfl⟩).2
  calc
    ‖((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x‖
        = |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x| * ‖u x‖ := by
          rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    _ = ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * ‖u x‖ := by
          rw [abs_of_nonneg hρ_x_nonneg]
    _ ≤ 1 * ‖u x‖ := by
          gcongr
    _ = ‖u x‖ := one_mul _
    _ ≤ Cu := hCu x

noncomputable def leftSmoothFactor (α : M) (b u : M → ℝ) : EuclN → ℝ :=
  smoothExtension (I := I) (M := M) α (fun x => b x * u x)

omit [IsManifold I ∞ M] in
private lemma leftSmoothFactor_norm_le
    (α : M) (b u : M → ℝ) {Cu Cb : ℝ}
    (hCu : ∀ x : M, ‖u x‖ ≤ Cu) (hCb : ∀ x : M, ‖b x‖ ≤ Cb) (hCu_nn : 0 ≤ Cu)
    (hCb_nn : 0 ≤ Cb) (y : EuclN) :
    ‖leftSmoothFactor (I := I) (M := M) α b u y‖ ≤ Cb * Cu := by
  classical
  unfold leftSmoothFactor smoothExtension
  by_cases hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
  · change ‖(if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              (fun x : M => b x * u x)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0)‖ ≤ Cb * Cu
    rw [if_pos hy]
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
    calc
      ‖b x * u x‖ = ‖b x‖ * ‖u x‖ := norm_mul _ _
      _ ≤ Cb * Cu := mul_le_mul (hCb x) (hCu x) (norm_nonneg _) hCb_nn
  · change ‖(if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              (fun x : M => b x * u x)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0)‖ ≤ Cb * Cu
    rw [if_neg hy]
    rw [norm_zero]
    exact mul_nonneg hCb_nn hCu_nn

lemma exists_chart_cutoff_with_data
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (α : M) :
    ∃ b : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ b ∧
      (∀ x : M, 0 ≤ b x ∧ b x ≤ 1) ∧
      (∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), b x = 1) ∧
      tsupport b ⊆ (chartAt H α).source := by
  obtain ⟨b, hb_smooth, hb_range, hb_one_on_tsupp, hb_supp⟩ :=
    exists_chart_cutoff (I := I) (M := M) α
  refine ⟨b, hb_smooth, ?_, hb_one_on_tsupp, hb_supp⟩
  intro x
  exact hb_range ⟨x, rfl⟩

private lemma smoothExtension_eq_chartPushed_uv
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) (u v : M → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    smoothExtension (I := I) (M := M) α
        (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x * v x) y =
      chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (fun x => u x * v x) y := by
  classical
  rw [smoothExtension_apply_of_mem_chartTargetEuclid (I := I) (M := M) α
    (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x * v x) hy]
  unfold chartPushed
  ring

private lemma chartSmoothExt_pou_mul_eq_chartPushed
    [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) (y : EuclN)
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    smoothExtension (I := I) (M := M) α
        (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) y =
      chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y := by
  classical
  rw [smoothExtension_apply_of_mem_chartTargetEuclid (I := I) (M := M) α
    (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) hy]
  rfl

omit [FiniteDimensional ℝ E] in
lemma chosenWeakPartial_eq_classical_ae
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {f : EuclN → ℝ}
    (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f) (hf_compact : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ Ω) (i : Fin (Module.finrank ℝ E)) :
    (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i (1 : ℝ)))
      =ᵐ[volume.restrict Ω]
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i f Ω := by
  classical
  have hf_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
      (d := Module.finrank ℝ E) hΩ_open hf_smooth hf_compact hf_supp hp_one 1
  have hf_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp hf_mem
  have h_classical_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i (1 : ℝ))) f Ω :=
    DeGiorgi.HasWeakPartialDeriv.of_contDiff (Ω := Ω) (i := i) (f := f)
      hΩ_open (hf_smooth.of_le (by norm_cast))
  have h_chosen_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p i f Ω) f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      hf_W1p i
  have h_classical_loc : LocallyIntegrable
      (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i (1 : ℝ)))
      (volume.restrict Ω) := by
    have h_cont : Continuous
        (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i (1 : ℝ))) :=
      ((hf_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
  have h_chosen_loc : LocallyIntegrable
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i f Ω) (volume.restrict Ω) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      hf_W1p i).locallyIntegrable hp_one
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq (Ω := Ω) hΩ_open
    h_classical_isWeak h_chosen_isWeak h_classical_loc h_chosen_loc

noncomputable def liftedPou
    [T2Space M] [SigmaCompactSpace M] (α : M) : EuclN → ℝ :=
  smoothExtension (I := I) (M := M) α
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ)

noncomputable def smoothPushed
    [T2Space M] [SigmaCompactSpace M] (α : M) (u : M → ℝ) : EuclN → ℝ :=
  smoothExtension (I := I) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x)

noncomputable def chartCarrierLocal
    [T2Space M] [SigmaCompactSpace M] (α : M) : Set EuclN :=
  (toEuclidean (E := E)) ''
    ((extChartAt I α) ''
      (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)))

lemma chartCarrierLocal_isCompact
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (α : M) :
    IsCompact (chartCarrierLocal (I := I) (M := M) α) := by
  classical
  unfold chartCarrierLocal
  exact image_extChartAt_tsupport_isCompact (I := I) (M := M)
    (f := ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ)) (α := α)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)

private lemma chartCarrierLocal_subset_chartTarget
    [T2Space M] [SigmaCompactSpace M] (α : M) :
    chartCarrierLocal (I := I) (M := M) α ⊆ chartTargetEuclid (I := I) (M := M) α := by
  classical
  unfold chartCarrierLocal
  exact image_tsupport_subset_chartTarget (I := I) (M := M)
    (f := ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ)) (α := α)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)

lemma tsupport_liftedPou_subset_chartCarrierLocal
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (α : M) :
    tsupport (liftedPou (I := I) (M := M) α) ⊆
      chartCarrierLocal (I := I) (M := M) α := by
  classical
  unfold liftedPou chartCarrierLocal
  exact tsupport_smoothExtension_subset_image (I := I) (M := M) α
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)

lemma liftedPou_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) : ContDiff ℝ ∞ (liftedPou (I := I) (M := M) α) := by
  classical
  unfold liftedPou
  refine contDiff_smoothExtension (I := I) (M := M) α
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯).contMDiff ?_
  exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α

private lemma liftedPou_hasCompactSupport
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) : HasCompactSupport (liftedPou (I := I) (M := M) α) := by
  classical
  unfold liftedPou
  refine hasCompactSupport_smoothExtension (I := I) (M := M) α ?_
  exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α

lemma smoothPushed_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContDiff ℝ ∞ (smoothPushed (I := I) (M := M) α u) := by
  classical
  unfold smoothPushed
  have hpou_u_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯).contMDiff.mul hu
  have hpou_u_supp : tsupport (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) ⊆ (chartAt H α).source :=
    DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartAtlasPOU_mul_subset_chartAt_source
      (I := I) (M := M) α u
  exact contDiff_smoothExtension (I := I) (M := M) α hpou_u_smooth hpou_u_supp

lemma smoothPushed_hasCompactSupport
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) :
    HasCompactSupport (smoothPushed (I := I) (M := M) α u) := by
  classical
  unfold smoothPushed
  have hpou_u_supp : tsupport (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) ⊆ (chartAt H α).source :=
    DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartAtlasPOU_mul_subset_chartAt_source
      (I := I) (M := M) α u
  exact hasCompactSupport_smoothExtension (I := I) (M := M) α hpou_u_supp

lemma leftSmoothFactor_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {b u : M → ℝ}
    (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hb_supp : tsupport b ⊆ (chartAt H α).source) :
    ContDiff ℝ ∞ (leftSmoothFactor (I := I) (M := M) α b u) := by
  classical
  unfold leftSmoothFactor
  have hbu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => b x * u x) := hb.mul hu
  have hbu_supp : tsupport (fun x : M => b x * u x) ⊆ (chartAt H α).source := by
    have h_eq : (fun x : M => b x * u x) = (fun x : M => b x • u x) := by funext x; rfl
    rw [h_eq]
    refine (tsupport_smul_subset_left (f := b) (g := u)).trans hb_supp
  exact contDiff_smoothExtension (I := I) (M := M) α hbu_smooth hbu_supp

omit [IsManifold I ∞ M] in
private lemma leftSmoothFactor_hasCompactSupport
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) {b u : M → ℝ}
    (hb_supp : tsupport b ⊆ (chartAt H α).source) :
    HasCompactSupport (leftSmoothFactor (I := I) (M := M) α b u) := by
  classical
  unfold leftSmoothFactor
  have hbu_supp : tsupport (fun x : M => b x * u x) ⊆ (chartAt H α).source := by
    have h_eq : (fun x : M => b x * u x) = (fun x : M => b x • u x) := by funext x; rfl
    rw [h_eq]
    refine (tsupport_smul_subset_left (f := b) (g := u)).trans hb_supp
  exact hasCompactSupport_smoothExtension (I := I) (M := M) α hbu_supp

omit [IsManifold I ∞ M] in
private lemma tsupport_leftSmoothFactor_subset_chartTarget
    [CompactSpace M] (α : M) {b u : M → ℝ}
    (hb_supp : tsupport b ⊆ (chartAt H α).source) :
    tsupport (leftSmoothFactor (I := I) (M := M) α b u) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  unfold leftSmoothFactor
  have hbu_supp : tsupport (fun x : M => b x * u x) ⊆ (chartAt H α).source := by
    have h_eq : (fun x : M => b x * u x) = (fun x : M => b x • u x) := by funext x; rfl
    rw [h_eq]
    refine (tsupport_smul_subset_left (f := b) (g := u)).trans hb_supp
  exact tsupport_smoothExtension_subset_chartTarget (I := I) (M := M) α hbu_supp

lemma tsupport_smoothPushed_subset_chartTarget
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) :
    tsupport (smoothPushed (I := I) (M := M) α u) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  unfold smoothPushed
  have hpou_u_supp : tsupport (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) ⊆ (chartAt H α).source :=
    DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartAtlasPOU_mul_subset_chartAt_source
      (I := I) (M := M) α u
  exact tsupport_smoothExtension_subset_chartTarget (I := I) (M := M) α hpou_u_supp

lemma leftSmoothFactor_memW1p
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (α : M) {b u : M → ℝ}
    (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hb_supp : tsupport b ⊆ (chartAt H α).source)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) p
      (leftSmoothFactor (I := I) (M := M) α b u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hSmooth : ContDiff ℝ ∞ (leftSmoothFactor (I := I) (M := M) α b u) :=
    leftSmoothFactor_smooth (I := I) (M := M) α hb hu hb_supp
  have hCompact : HasCompactSupport (leftSmoothFactor (I := I) (M := M) α b u) :=
    leftSmoothFactor_hasCompactSupport (I := I) (M := M) α hb_supp
  have h_tsupp : tsupport (leftSmoothFactor (I := I) (M := M) α b u) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    tsupport_leftSmoothFactor_subset_chartTarget (I := I) (M := M) α hb_supp
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
    (d := Module.finrank ℝ E) hΩ_open hSmooth hCompact h_tsupp hp_one 1).memW1p

lemma smoothPushed_memW1p
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) p
      (smoothPushed (I := I) (M := M) α u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hSmooth : ContDiff ℝ ∞ (smoothPushed (I := I) (M := M) α u) :=
    smoothPushed_smooth (I := I) (M := M) α hu
  have hCompact : HasCompactSupport (smoothPushed (I := I) (M := M) α u) :=
    smoothPushed_hasCompactSupport (I := I) (M := M) α u
  have h_tsupp : tsupport (smoothPushed (I := I) (M := M) α u) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    tsupport_smoothPushed_subset_chartTarget (I := I) (M := M) α u
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
    (d := Module.finrank ℝ E) hΩ_open hSmooth hCompact h_tsupp hp_one 1).memW1p

private lemma liftedPou_apply_in_unit_interval
    [T2Space M] [SigmaCompactSpace M] (α : M) (y : EuclN) :
    0 ≤ liftedPou (I := I) (M := M) α y ∧ liftedPou (I := I) (M := M) α y ≤ 1 := by
  classical
  unfold liftedPou smoothExtension
  by_cases hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
  · change 0 ≤ (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0) ∧ _ ≤ 1
    rw [if_pos hy]
    exact ⟨(DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg α _,
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).le_one α _⟩
  · change 0 ≤ (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0) ∧ _ ≤ 1
    rw [if_neg hy]
    exact ⟨le_refl 0, zero_le_one⟩

lemma liftedPou_norm_le_one
    [T2Space M] [SigmaCompactSpace M] (α : M) (y : EuclN) :
    ‖liftedPou (I := I) (M := M) α y‖ ≤ 1 := by
  obtain ⟨h_nn, h_le⟩ := liftedPou_apply_in_unit_interval (I := I) (M := M) α y
  rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
  exact h_le

lemma exists_liftedPou_grad_bound
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) : ∃ Cα : ℝ, 0 ≤ Cα ∧
      ∀ y : EuclN, ‖fderiv ℝ (liftedPou (I := I) (M := M) α) y‖ ≤ Cα := by
  classical
  unfold liftedPou
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯).contMDiff
  have hf_supp : tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  obtain ⟨C, hC_nn, hC⟩ :=
    smoothExtension_first_order_bound (I := I) (M := M) α hf_smooth hf_supp
  refine ⟨C, hC_nn, fun y => ?_⟩
  have h := hC 1 (le_refl _) y
  rwa [norm_iteratedFDeriv_one] at h

lemma smoothPushed_norm_le_of_bound
    [T2Space M] [SigmaCompactSpace M] (α : M) {u : M → ℝ} {uMax : ℝ}
    (hu_bound : ∀ x : M, ‖u x‖ ≤ uMax) (huMax_nn : 0 ≤ uMax) (y : EuclN) :
    ‖smoothPushed (I := I) (M := M) α u y‖ ≤ uMax := by
  classical
  unfold smoothPushed smoothExtension
  by_cases hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
  · change ‖(if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              (fun x : M =>
                ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0)‖ ≤ uMax
    rw [if_pos hy]
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
    have hρ_x_nonneg : 0 ≤ ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg α x
    have hρ_x_le_one : ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≤ 1 :=
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).le_one α x
    calc
      ‖((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x‖
          = ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * ‖u x‖ := by
            rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs,
              abs_of_nonneg hρ_x_nonneg]
      _ ≤ 1 * ‖u x‖ := by gcongr
      _ = ‖u x‖ := one_mul _
      _ ≤ uMax := hu_bound x
  · change ‖(if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              (fun x : M =>
                ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0)‖ ≤ uMax
    rw [if_neg hy, norm_zero]
    exact huMax_nn

omit [IsManifold I ∞ M] in
lemma leftSmoothFactor_norm_le_of_bound
    (α : M) {b u : M → ℝ}
    (hb_le_one : ∀ x : M, 0 ≤ b x ∧ b x ≤ 1) {uMax : ℝ}
    (hu_bound : ∀ x : M, ‖u x‖ ≤ uMax) (huMax_nn : 0 ≤ uMax) (y : EuclN) :
    ‖leftSmoothFactor (I := I) (M := M) α b u y‖ ≤ uMax := by
  classical
  unfold leftSmoothFactor smoothExtension
  by_cases hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
  · change ‖(if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              (fun x : M => b x * u x)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0)‖ ≤ uMax
    rw [if_pos hy]
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
    have hb_x_nn : 0 ≤ b x := (hb_le_one x).1
    have hb_x_le_one : b x ≤ 1 := (hb_le_one x).2
    calc
      ‖b x * u x‖ = b x * ‖u x‖ := by
        rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, abs_of_nonneg hb_x_nn]
      _ ≤ 1 * ‖u x‖ := by gcongr
      _ = ‖u x‖ := one_mul _
      _ ≤ uMax := hu_bound x
  · change ‖(if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              (fun x : M => b x * u x)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0)‖ ≤ uMax
    rw [if_neg hy, norm_zero]
    exact huMax_nn

lemma liftedPou_mul_leftSmoothFactor_eq_smoothPushed
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {b v : M → ℝ}
    (hb_one : ∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
      I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), b x = 1) :
    (fun y : EuclN => liftedPou (I := I) (M := M) α y *
      leftSmoothFactor (I := I) (M := M) α b v y) =
    smoothPushed (I := I) (M := M) α v := by
  classical
  unfold liftedPou leftSmoothFactor smoothPushed
  rw [smoothExtension_mul_eq (I := I) (M := M) α
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    (fun x : M => b x * v x)]
  congr 1
  funext x
  by_cases hρ : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯) x = 0
  · rw [hρ]; ring
  · have hx_supp : x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ (Function.mem_support.mpr hρ)
    have hb_x : b x = 1 := hb_one x hx_supp
    rw [hb_x]; ring

lemma smoothPushed_mul_leftSmoothFactor_eq_smoothExtension_uv
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {b u v : M → ℝ}
    (hb_one : ∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
      I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), b x = 1) :
    (fun y : EuclN => smoothPushed (I := I) (M := M) α u y *
      leftSmoothFactor (I := I) (M := M) α b v y) =
    smoothExtension (I := I) (M := M) α
      (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x * v x) := by
  classical
  unfold smoothPushed leftSmoothFactor
  exact (smoothExtension_three_factor (I := I) (M := M) α hb_one).symm

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
