import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedDatum


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in

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

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma hasCompactSupport_fderiv_apply_single
    {ψ : EuclN → ℝ} (hψ_cs : HasCompactSupport ψ)
    (l : Fin (Module.finrank ℝ E)) :
    HasCompactSupport (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) :=
  hψ_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma tsupport_fderiv_apply_single_subset
    (ψ : EuclN → ℝ) (l : Fin (Module.finrank ℝ E)) :
    tsupport (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) ⊆
      tsupport ψ :=
  tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single l 1)

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in

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

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in

private lemma snoc_cons_eq_cons_snoc {β : Type*} {m : ℕ}
    (i : β) (dirs : Fin m → β) (l : β) :
    @Fin.snoc m.succ (fun _ => β) (Fin.cons i dirs) l =
      Fin.cons i (Fin.snoc dirs l) :=
  (Fin.cons_snoc_eq_snoc_cons (β := β) i dirs l).symm

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

private lemma chosenWeakPartial'_memLp_volume_uncond
    {Ω : Set EuclN} (k : Fin (Module.finrank ℝ E)) (w : EuclN → ℝ) :
    MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k w Ω) 2
      ((volume : Measure EuclN).restrict Ω) := by
  classical
  by_cases hw : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 w Ω
  · exact chosenWeakPartial'_memLp_of_mem hw k
  · rw [chosenWeakPartial'_of_not_mem hw k]
    exact MemLp.zero

omit [CompleteSpace E] in
private lemma density_mul_eigenvectorChartIteratedStep_eq_indicator_numerator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (y : EuclN) (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    densityOnEuclid (I := I) g α y *
        eigenvectorChartIteratedStep (I := I) (M := M)
          g r s i α P₀ m dirs fChartEffPrev l y =
      Set.indicator (chartPouKernel (I := I) (M := M) α)
        (fun z => eigenvectorChartIteratedStepNumerator (I := I) (M := M)
          g r s i α P₀ m dirs fChartEffPrev l z) y := by
  classical
  rw [eigenvectorChartIteratedStep]
  by_cases hy_K : y ∈ chartPouKernel (I := I) (M := M) α
  · rw [Set.indicator_of_mem hy_K, Set.indicator_of_mem hy_K]
    have h_pos : 0 < densityOnEuclid (I := I) g α y :=
      densityOnEuclid_pos (I := I) g α hy
    field_simp
  · rw [Set.indicator_of_notMem hy_K, Set.indicator_of_notMem hy_K, mul_zero]

omit [CompleteSpace E] in
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
          ∂(volume : Measure EuclN))) :=
  generic_per_pair_ibp (I := I) (M := M) (α := α)
    h_fChartEffPrev_memW1p (densityOnEuclid_contDiffOn (I := I) g α)
    hψ_smooth hψ_cs hψ_supp l

omit [CompleteSpace E] in
private theorem ibp_principal_pair_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_2 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 2) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E))
    (a j : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        weightedInvGramOnEuclid (I := I) g α a j y *
          eigenvectorChartIteratedPartial (I := I) (M := M) g r s i α P₀
            (m + 1) (Fin.cons a dirs) y *
          (fderiv ℝ (fun z : EuclN =>
            (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
              (EuclideanSpace.single j 1)
        ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α a j) y)
              (EuclideanSpace.single l 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M) g r s i α P₀
              (m + 1) (Fin.cons a dirs) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          weightedInvGramOnEuclid (I := I) g α a j y *
            eigenvectorChartIteratedPartial (I := I) (M := M) g r s i α P₀
              (m + 2) (Fin.cons a (Fin.snoc dirs l)) y *
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
          weightedInvGramOnEuclid (I := I) g α a j y *
            eigenvectorChartIteratedPartial (I := I) (M := M) g r s i α P₀
              (m + 1) (Fin.cons a dirs) y *
            (fderiv ℝ (fun z : EuclN =>
              (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
                (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN)) =
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
          weightedInvGramOnEuclid (I := I) g α a j y *
            eigenvectorChartIteratedPartial (I := I) (M := M) g r s i α P₀
              (m + 1) (Fin.cons a dirs) y *
            (fderiv ℝ ψ_j y) (EuclideanSpace.single l 1)
          ∂(volume : Measure EuclN)) := by
    refine setIntegral_congr_fun
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
      (fun y _ => ?_)
    rw [h_schwarz y]
  rw [h_lhs_schwarz]
  have h_ibp := eigenvector_per_pair_ibp
    (I := I) (M := M) g r s i α P₀ (m + 1) (Fin.cons a dirs)
    h_chart_H_m_plus_2
    (weightedInvGramOnEuclid_contDiffOn (I := I) g α a j)
    hψ_j_smooth hψ_j_cs hψ_j_supp l
  have h_snoc_cons :
      Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E)) (Fin.cons a dirs) l =
        Fin.cons a (Fin.snoc dirs l) :=
    snoc_cons_eq_cons_snoc (β := Fin (Module.finrank ℝ E)) a dirs l
  rw [h_snoc_cons] at h_ibp
  exact h_ibp

omit [CompleteSpace E] in
private theorem ibp_mass_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          eigenvectorChartIteratedPartial (I := I) (M := M) g r s i α P₀
            m dirs y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l 1)
        ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ (densityOnEuclid (I := I) g α) y)
              (EuclideanSpace.single l 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M) g r s i α P₀
              m dirs y *
            ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            eigenvectorChartIteratedPartial (I := I) (M := M) g r s i α P₀
              (m + 1) (Fin.snoc dirs l) y *
            ψ y
          ∂(volume : Measure EuclN))) :=
  eigenvector_per_pair_ibp (I := I) (M := M) g r s i α P₀ m dirs
    h_chart_H_m_plus_1 (densityOnEuclid_contDiffOn (I := I) g α)
    hψ_smooth hψ_cs hψ_supp l

omit [CompleteSpace E] in
private theorem ibp_inner_j_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_2 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 2) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E))
    (a j : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        weightedInvGramDerivOnEuclid (I := I) g α a j l y *
          eigenvectorChartIteratedPartial (I := I) (M := M) g r s i α P₀
            (m + 1) (Fin.cons a dirs) y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
        ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a j l) y)
              (EuclideanSpace.single j 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M) g r s i α P₀
              (m + 1) (Fin.cons a dirs) y *
            ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          weightedInvGramDerivOnEuclid (I := I) g α a j l y *
            eigenvectorChartIteratedPartial (I := I) (M := M) g r s i α P₀
              (m + 2) (Fin.cons a (Fin.snoc dirs j)) y *
            ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  have h_ibp := eigenvector_per_pair_ibp
    (I := I) (M := M) g r s i α P₀ (m + 1) (Fin.cons a dirs)
    h_chart_H_m_plus_2
    (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a j l)
    hψ_smooth hψ_cs hψ_supp j
  have h_snoc_cons :
      Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E)) (Fin.cons a dirs) j =
        Fin.cons a (Fin.snoc dirs j) :=
    snoc_cons_eq_cons_snoc (β := Fin (Module.finrank ℝ E)) a dirs j
  rw [h_snoc_cons] at h_ibp
  exact h_ibp

omit [CompleteSpace E] in

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

noncomputable def eigenvectorIteratedTensorChartBilinearData_step
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (D_m : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s i α P₀ m)
    (l : Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_m_plus_2 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 2) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_fChartEff_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 D_m.diffChartForcing
        (chartTargetEuclid (I := I) (M := M) α))
    (h_fChartEff_ae_zero_off_K :
      D_m.diffChartForcing =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ))) :
    eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s i α P₀ (m + 1) :=
  eigenvectorIteratedTensorChartBilinearData.mk_from_hypotheses
    (Fin.snoc D_m.directions l)
    (eigenvectorChartIteratedStep (I := I) (M := M)
      g r s i α P₀ m D_m.directions D_m.diffChartForcing l)
    (eigenvectorChartIteratedStep_memLp_two_weighted (I := I) (M := M)
      g r s i α P₀ m D_m.directions
      D_m.fChartEff_memLp_weighted l)
    (by
      classical
      intro ψ hψ_smooth hψ_cs hψ_supp
      set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
      have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
      have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
      set Kα : Set EuclN := chartPouKernel (I := I) (M := M) α with hKα_def
      have hKα_compact : IsCompact Kα :=
        chartPouKernel_isCompact (I := I) (M := M) α
      have hKα_meas : MeasurableSet Kα :=
        chartPouKernel_measurableSet (I := I) (M := M) α
      have hKα_in : Kα ⊆ Ω :=
        chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
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
        fun a j =>
          ∫ y in Ω,
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a j l) y)
                (EuclideanSpace.single j 1) *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a D_m.directions) y *
              ψ y
            ∂(volume : Measure EuclN) with hA_pair_def
      set B_pair : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
        fun a j =>
          ∫ y in Ω,
            weightedInvGramDerivOnEuclid (I := I) g α a j l y *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 2) (Fin.cons a (Fin.snoc D_m.directions j)) y *
              ψ y
            ∂(volume : Measure EuclN) with hB_pair_def
      set PR_pair : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
        fun a j =>
          ∫ y in Ω,
            weightedInvGramOnEuclid (I := I) g α a j y *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 2) (Fin.cons a (Fin.snoc D_m.directions l)) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
            ∂(volume : Measure EuclN) with hPR_pair_def
      set INT_LHS_m_pair : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
        fun a j =>
          ∫ y in Ω,
            weightedInvGramOnEuclid (I := I) g α a j y *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a D_m.directions) y *
              (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1)
            ∂(volume : Measure EuclN) with hINT_LHS_m_pair_def
      have h_principal_pair : ∀ a j : Fin (Module.finrank ℝ E),
          INT_LHS_m_pair a j = A_pair a j + B_pair a j - PR_pair a j := by
        intro a j
        have h_pp := ibp_principal_pair_unconditional (I := I) (M := M)
          g r s i α P₀ m D_m.directions
          h_chart_H_m_plus_2 l a j hψ_smooth hψ_cs hψ_supp
        have h_inner := ibp_inner_j_unconditional (I := I) (M := M)
          g r s i α P₀ m D_m.directions
          h_chart_H_m_plus_2 l a j hψ_smooth hψ_cs hψ_supp
        have h_pp' : INT_LHS_m_pair a j =
            -((∫ y in Ω,
                weightedInvGramDerivOnEuclid (I := I) g α a j l y *
                  eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a D_m.directions) y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
                ∂(volume : Measure EuclN))
              + PR_pair a j) := h_pp
        rw [h_pp', h_inner]
        ring
      set K : Set EuclN := tsupport ψ with hK_def
      have hK_compact : IsCompact K := hψ_cs
      have hK_meas : MeasurableSet K := (isClosed_tsupport ψ).measurableSet
      have hK_in : K ⊆ Ω := hψ_supp
      have h_aij_cont : ∀ a j : Fin (Module.finrank ℝ E),
          ContinuousOn (weightedInvGramOnEuclid (I := I) g α a j) Ω :=
        fun a j => (weightedInvGramOnEuclid_contDiffOn (I := I) g α a j).continuousOn
      have h_daij_cont : ∀ a j : Fin (Module.finrank ℝ E),
          ContinuousOn (weightedInvGramDerivOnEuclid (I := I) g α a j l) Ω :=
        fun a j =>
          (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a j l).continuousOn
      have h_dens_cont : ContinuousOn (densityOnEuclid (I := I) g α) Ω :=
        densityOnEuclid_continuousOn (I := I) g α
      have h_dens_deriv_cont : ContinuousOn
          (densityDerivOnEuclid (I := I) g α l) Ω :=
        (densityDerivOnEuclid_contDiffOn (I := I) g α l).continuousOn
      have h_aij_fderiv_cont : ∀ a j : Fin (Module.finrank ℝ E),
          ContinuousOn (fun y : EuclN =>
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a j l) y)
              (EuclideanSpace.single j 1)) Ω := by
        intro a j
        have h_diffOn :
            ContDiffOn ℝ (⊤ : ℕ∞) (weightedInvGramDerivOnEuclid (I := I) g α a j l) Ω :=
          weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a j l
        have h_fderiv_diff :
            ContDiffOn ℝ (⊤ : ℕ∞)
              (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a j l) y) Ω :=
          ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ_open).1 h_diffOn).2
        have h_eval : ContDiff ℝ (⊤ : ℕ∞)
            (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single j 1)) :=
          (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).contDiff
        exact (h_eval.contDiffOn.comp h_fderiv_diff (mapsTo_univ _ _)).continuousOn
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
      have hvolK_finite' :
          (volume.restrict K : Measure EuclN) Set.univ < (⊤ : ℝ≥0∞) := by
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact hvolK_finite
      haveI : IsFiniteMeasure ((volume : Measure EuclN).restrict K) :=
        ⟨hvolK_finite'⟩
      have h_restrict_K_eq : ((volume : Measure EuclN).restrict Ω).restrict K =
          (volume : Measure EuclN).restrict K := by
        rw [Measure.restrict_restrict hK_meas]; congr 1
        exact Set.inter_eq_self_of_subset_left hK_in
      have h_M_m_int : IntegrableOn
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m D_m.directions) K (volume : Measure EuclN) := by
        have h := (eigenvectorChartIteratedPartial_memLp_volume (I := I) (M := M)
          g r s i α P₀ m D_m.directions).restrict K
        rw [h_restrict_K_eq] at h
        exact h.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h_M_m1_int : ∀ idx : Fin (m + 1) → Fin (Module.finrank ℝ E),
          IntegrableOn
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) idx)
            K (volume : Measure EuclN) := by
        intro idx
        have h := (eigenvectorChartIteratedPartial_memLp_volume (I := I) (M := M)
          g r s i α P₀ (m + 1) idx).restrict K
        rw [h_restrict_K_eq] at h
        exact h.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h_M_m2_int : ∀ idx : Fin (m + 2) → Fin (Module.finrank ℝ E),
          IntegrableOn
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 2) idx)
            K (volume : Measure EuclN) := by
        intro idx
        have h := (eigenvectorChartIteratedPartial_memLp_volume (I := I) (M := M)
          g r s i α P₀ (m + 2) idx).restrict K
        rw [h_restrict_K_eq] at h
        exact h.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
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
      have h_int_LHS_m_pair : ∀ a j : Fin (Module.finrank ℝ E),
          Integrable (fun y => weightedInvGramOnEuclid (I := I) g α a j y *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a D_m.directions) y *
              (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1))
            ((volume : Measure EuclN).restrict Ω) := fun a j =>
        integrable_triple_helper (α := α) hK_compact hK_meas hK_in
          (h_aij_cont a j) (h_M_m1_int (Fin.cons a D_m.directions))
          (hψ_l_partial_cont j) (hψ_l_partial_supp j)
      have h_int_A_pair : ∀ a j,
          Integrable (fun y =>
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a j l) y)
              (EuclideanSpace.single j 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a D_m.directions) y * ψ y)
            ((volume : Measure EuclN).restrict Ω) := fun a j =>
        integrable_triple_helper (α := α) hK_compact hK_meas hK_in
          (h_aij_fderiv_cont a j)
          (h_M_m1_int (Fin.cons a D_m.directions)) hψ_cont hψ_supp_K
      have h_int_B_pair : ∀ a j,
          Integrable (fun y =>
            weightedInvGramDerivOnEuclid (I := I) g α a j l y *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 2) (Fin.cons a (Fin.snoc D_m.directions j)) y * ψ y)
            ((volume : Measure EuclN).restrict Ω) := fun a j =>
        integrable_triple_helper (α := α) hK_compact hK_meas hK_in
          (h_daij_cont a j)
          (h_M_m2_int (Fin.cons a (Fin.snoc D_m.directions j))) hψ_cont hψ_supp_K
      have h_int_PR_pair : ∀ a j,
          Integrable (fun y =>
            weightedInvGramOnEuclid (I := I) g α a j y *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 2) (Fin.cons a (Fin.snoc D_m.directions l)) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
            ((volume : Measure EuclN).restrict Ω) := fun a j =>
        integrable_triple_helper (α := α) hK_compact hK_meas hK_in
          (h_aij_cont a j)
          (h_M_m2_int (Fin.cons a (Fin.snoc D_m.directions l)))
          (hψ_partial_cont j) (hψ_partial_supp j)
      set INT_LHS_principal_m_l : ℝ :=
        ∫ y in Ω,
          (∑ a : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α a j y *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a D_m.directions) y *
                (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) with hINT_LHS_principal_m_l_def
      set INT_LHS_mass_m_l : ℝ :=
        ∫ y in Ω,
          densityOnEuclid (I := I) g α y *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ m D_m.directions y * ψ_l y
          ∂(volume : Measure EuclN) with hINT_LHS_mass_m_l_def
      set INT_RHS_m_l : ℝ :=
        ∫ y in Ω,
          densityOnEuclid (I := I) g α y * D_m.diffChartForcing y * ψ_l y
          ∂(volume : Measure EuclN) with hINT_RHS_m_l_def
      have h_level_m' :
          INT_LHS_principal_m_l + INT_LHS_mass_m_l = INT_RHS_m_l := h_level_m
      have h_swap_LHS_principal :
          INT_LHS_principal_m_l = ∑ a, ∑ j, INT_LHS_m_pair a j := by
        change (∫ y in Ω,
            (∑ a : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α a j y *
                  eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a D_m.directions) y *
                  (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1))
            ∂(volume : Measure EuclN)) = _
        rw [integral_finset_sum _ (fun a _ =>
          (integrable_finset_sum _ (fun j _ => h_int_LHS_m_pair a j)))]
        refine Finset.sum_congr rfl ?_; intro a _
        rw [integral_finset_sum _ (fun j _ => h_int_LHS_m_pair a j)]
      have h_sum_principal :
          ∑ a, ∑ j, INT_LHS_m_pair a j =
          (∑ a, ∑ j, A_pair a j) + (∑ a, ∑ j, B_pair a j) - (∑ a, ∑ j, PR_pair a j) := by
        calc ∑ a, ∑ j, INT_LHS_m_pair a j
            = ∑ a, ∑ j, (A_pair a j + B_pair a j - PR_pair a j) := by
              refine Finset.sum_congr rfl ?_; intro a _
              refine Finset.sum_congr rfl ?_; intro j _
              exact h_principal_pair a j
          _ = ∑ a, ∑ j, (A_pair a j + (B_pair a j + (-(PR_pair a j)))) := by
              refine Finset.sum_congr rfl ?_; intro a _
              refine Finset.sum_congr rfl ?_; intro j _
              ring
          _ = ∑ a, (∑ j, A_pair a j) + ∑ a, (∑ j, (B_pair a j + (-(PR_pair a j)))) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_; intro a _
              exact Finset.sum_add_distrib
          _ = (∑ a, ∑ j, A_pair a j) +
              ((∑ a, ∑ j, B_pair a j) + ∑ a, ∑ j, -(PR_pair a j)) := by
              congr 1
              rw [show (fun a => ∑ j, (B_pair a j + (-(PR_pair a j)))) =
                  (fun a => (∑ j, B_pair a j) + (∑ j, -(PR_pair a j))) by
                funext a; exact Finset.sum_add_distrib]
              exact Finset.sum_add_distrib
          _ = (∑ a, ∑ j, A_pair a j) + (∑ a, ∑ j, B_pair a j) -
              (∑ a, ∑ j, PR_pair a j) := by
              simp_rw [Finset.sum_neg_distrib (s :=
                (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
              ring
      set N_C : ℝ :=
        ∫ y in Ω, densityDerivOnEuclid (I := I) g α l y *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m D_m.directions y * ψ y
          ∂(volume : Measure EuclN) with hN_C_def
      set N_mass_new : ℝ :=
        ∫ y in Ω,
          densityOnEuclid (I := I) g α y *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.snoc D_m.directions l) y * ψ y
          ∂(volume : Measure EuclN) with hN_mass_new_def
      have h_mass_ibp : INT_LHS_mass_m_l = -(N_C + N_mass_new) := by
        have hb := ibp_mass_unconditional (I := I) (M := M) g r s i α P₀ m D_m.directions
          h_chart_H_m_plus_1 l hψ_smooth hψ_cs hψ_supp
        change (∫ y in Ω,
            densityOnEuclid (I := I) g α y *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ m D_m.directions y * ψ_l y
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
      have h_combine : (∑ a, ∑ j, PR_pair a j) + N_mass_new =
          (∑ a, ∑ j, A_pair a j) + (∑ a, ∑ j, B_pair a j) +
            (-N_C) + N_D + N_E := by
        have h := h_level_m'
        rw [h_swap_LHS_principal, h_sum_principal, h_mass_ibp, h_rhs_ibp] at h
        linarith
      set I_step_RHS : ℝ :=
        ∫ y in Ω,
          densityOnEuclid (I := I) g α y *
            eigenvectorChartIteratedStep (I := I) (M := M)
              g r s i α P₀ m D_m.directions D_m.diffChartForcing l y * ψ y
          ∂(volume : Measure EuclN) with hI_step_RHS_def
      set LHS_principal_new : ℝ :=
        ∫ y in Ω,
          (∑ a : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α a j y *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 2) (Fin.cons a (Fin.snoc D_m.directions l)) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) with hLHS_principal_new_def
      have h_LHS_principal_new_eq : LHS_principal_new = ∑ a, ∑ j, PR_pair a j := by
        change (∫ y in Ω,
            (∑ a : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α a j y *
                  eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 2) (Fin.cons a (Fin.snoc D_m.directions l)) y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
            ∂(volume : Measure EuclN)) = _
        rw [integral_finset_sum _ (fun a _ =>
          (integrable_finset_sum _ (fun j _ => h_int_PR_pair a j)))]
        refine Finset.sum_congr rfl ?_; intro a _
        rw [integral_finset_sum _ (fun j _ => h_int_PR_pair a j)]
      have h_M_m_ae :
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m D_m.directions
            =ᵐ[(volume : Measure EuclN).restrict (Ω \ Kα)]
            (fun _ : EuclN => (0 : ℝ)) := by
        have h := eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ m D_m.directions
        exact h
      have h_M_m1_ae : ∀ idx : Fin (m + 1) → Fin (Module.finrank ℝ E),
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) idx
            =ᵐ[(volume : Measure EuclN).restrict (Ω \ Kα)]
            (fun _ : EuclN => (0 : ℝ)) := fun idx =>
        eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ (m + 1) idx
      have h_M_m2_ae : ∀ idx : Fin (m + 2) → Fin (Module.finrank ℝ E),
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 2) idx
            =ᵐ[(volume : Measure EuclN).restrict (Ω \ Kα)]
            (fun _ : EuclN => (0 : ℝ)) := fun idx =>
        eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ (m + 2) idx
      have h_fChartEff_wp_ae :
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 l D_m.diffChartForcing Ω
            =ᵐ[(volume : Measure EuclN).restrict (Ω \ Kα)]
            (fun _ : EuclN => (0 : ℝ)) :=
        chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
          (I := I) (M := M) α h_fChartEff_ae_zero_off_K l
      have h_numer_ae_zero :
          ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Kα)),
            eigenvectorChartIteratedStepNumerator (I := I) (M := M)
              g r s i α P₀ m D_m.directions D_m.diffChartForcing l y = 0 := by
        have h_M_m1_each : ∀ a : Fin (Module.finrank ℝ E),
            ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Kα)),
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a D_m.directions) y = 0 :=
          fun a => h_M_m1_ae (Fin.cons a D_m.directions)
        have h_M_m1_wp_each : ∀ a b : Fin (Module.finrank ℝ E),
            ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Kα)),
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a D_m.directions)) Ω y = 0 :=
          fun a b =>
            chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
              (I := I) (M := M) α (h_M_m1_ae (Fin.cons a D_m.directions)) b
        have h_M_m1_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Kα)),
            ∀ a : Fin (Module.finrank ℝ E),
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a D_m.directions) y = 0 := by
          rw [ae_all_iff]; exact h_M_m1_each
        have h_M_m1_wp_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Kα)),
            ∀ a b : Fin (Module.finrank ℝ E),
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a D_m.directions)) Ω y = 0 := by
          rw [ae_all_iff]; intro a; rw [ae_all_iff]; exact h_M_m1_wp_each a
        filter_upwards [h_M_m_ae, h_M_m1_all, h_M_m1_wp_all,
          h_fChartEff_ae_zero_off_K, h_fChartEff_wp_ae] with y h_M_m_y h_M_m1_y
          h_M_m1_wp_y h_fE_y h_fE_wp_y
        unfold eigenvectorChartIteratedStepNumerator
        have h_A_zero :
            (∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b l) y)
                    (EuclideanSpace.single b 1) *
                  eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a D_m.directions) y) = 0 := by
          refine Finset.sum_eq_zero ?_; intro a _
          refine Finset.sum_eq_zero ?_; intro _ _
          rw [h_M_m1_y a]; ring
        have h_B_zero :
            (∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                weightedInvGramDerivOnEuclid (I := I) g α a b l y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                    (eigenvectorChartIteratedPartial (I := I) (M := M)
                      g r s i α P₀ (m + 1) (Fin.cons a D_m.directions))
                    (chartTargetEuclid (I := I) (M := M) α) y) = 0 := by
          refine Finset.sum_eq_zero ?_; intro a _
          refine Finset.sum_eq_zero ?_; intro b _
          rw [h_M_m1_wp_y a b]; ring
        rw [h_A_zero, h_B_zero, h_M_m_y, h_fE_y, h_fE_wp_y]
        ring
      have h_step_RHS_eq_indicator :
          I_step_RHS =
          ∫ y in Ω,
            Set.indicator Kα
              (fun z => eigenvectorChartIteratedStepNumerator (I := I) (M := M)
                g r s i α P₀ m D_m.directions D_m.diffChartForcing l z) y * ψ y
            ∂(volume : Measure EuclN) := by
        change (∫ y in Ω,
            densityOnEuclid (I := I) g α y *
              eigenvectorChartIteratedStep (I := I) (M := M)
                g r s i α P₀ m D_m.directions D_m.diffChartForcing l y * ψ y
            ∂(volume : Measure EuclN)) = _
        refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
        have h_pt := density_mul_eigenvectorChartIteratedStep_eq_indicator_numerator
          (I := I) (M := M) g r s i α P₀ m D_m.directions D_m.diffChartForcing l y hy
        rw [show densityOnEuclid (I := I) g α y *
            eigenvectorChartIteratedStep (I := I) (M := M)
              g r s i α P₀ m D_m.directions D_m.diffChartForcing l y * ψ y =
            (densityOnEuclid (I := I) g α y *
              eigenvectorChartIteratedStep (I := I) (M := M)
                g r s i α P₀ m D_m.directions D_m.diffChartForcing l y) * ψ y from rfl]
        rw [h_pt]
      have h_indicator_eq_numerator :
          ∫ y in Ω,
            Set.indicator Kα
              (fun z => eigenvectorChartIteratedStepNumerator (I := I) (M := M)
                g r s i α P₀ m D_m.directions D_m.diffChartForcing l z) y * ψ y
            ∂(volume : Measure EuclN) =
          ∫ y in Ω,
            eigenvectorChartIteratedStepNumerator (I := I) (M := M)
              g r s i α P₀ m D_m.directions D_m.diffChartForcing l y * ψ y
            ∂(volume : Measure EuclN) := by
        refine MeasureTheory.integral_congr_ae ?_
        refine (ae_restrict_iff' hΩ_meas).mpr ?_
        have h_off : ∀ᵐ y ∂(volume : Measure EuclN),
            y ∈ Ω \ Kα →
            eigenvectorChartIteratedStepNumerator (I := I) (M := M)
              g r s i α P₀ m D_m.directions D_m.diffChartForcing l y = 0 := by
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
            eigenvectorChartIteratedStepNumerator (I := I) (M := M)
              g r s i α P₀ m D_m.directions D_m.diffChartForcing l y * ψ y
            ∂(volume : Measure EuclN) := by
        rw [h_step_RHS_eq_indicator]; exact h_indicator_eq_numerator
      have h_int_C : Integrable (fun y =>
          densityDerivOnEuclid (I := I) g α l y *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ m D_m.directions y * ψ y)
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
            eigenvectorChartIteratedStepNumerator (I := I) (M := M)
              g r s i α P₀ m D_m.directions D_m.diffChartForcing l y * ψ y
            ∂(volume : Measure EuclN)) =
          (∑ a, ∑ j, A_pair a j) + (∑ a, ∑ j, B_pair a j) - N_C + N_D + N_E := by
        set f_A : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b l) y)
              (EuclideanSpace.single b 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a D_m.directions) y * ψ y
            with hf_A_def
        set f_B : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α a b l y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a D_m.directions))
              (chartTargetEuclid (I := I) (M := M) α) y * ψ y with hf_B_def
        set f_C : EuclN → ℝ := fun y =>
          - (densityDerivOnEuclid (I := I) g α l y *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ m D_m.directions y * ψ y) with hf_C_def
        set f_D : EuclN → ℝ := fun y =>
          densityDerivOnEuclid (I := I) g α l y *
            D_m.diffChartForcing y * ψ y with hf_D_def
        set f_E : EuclN → ℝ := fun y =>
          densityOnEuclid (I := I) g α y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 l D_m.diffChartForcing Ω y *
            ψ y with hf_E_def
        have h_integrand_eq : ∀ y : EuclN,
            eigenvectorChartIteratedStepNumerator (I := I) (M := M)
              g r s i α P₀ m D_m.directions D_m.diffChartForcing l y * ψ y =
            f_A y + f_B y + f_C y + f_D y + f_E y := by
          intro y
          unfold eigenvectorChartIteratedStepNumerator
          simp only [add_mul, sub_mul, Finset.sum_mul]
          ring
        rw [setIntegral_congr_fun hΩ_meas (fun y _ => h_integrand_eq y)]
        have h_int_B_pair_wp : ∀ a b,
            Integrable (fun y =>
              weightedInvGramDerivOnEuclid (I := I) g α a b l y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a D_m.directions))
                (chartTargetEuclid (I := I) (M := M) α) y * ψ y)
              ((volume : Measure EuclN).restrict Ω) := fun a b =>
          integrable_triple_helper (α := α) hK_compact hK_meas hK_in
            (h_daij_cont a b)
            (by
              have h_g := chosenWeakPartial'_memLp_volume_uncond
                (Ω := Ω) b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a D_m.directions))
              have h_g_K := h_g.restrict K
              rw [h_restrict_K_eq] at h_g_K
              exact h_g_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
            hψ_cont hψ_supp_K
        have hint_A : Integrable f_A ((volume : Measure EuclN).restrict Ω) :=
          integrable_finset_sum _ (fun a _ =>
            integrable_finset_sum _ (fun b _ => h_int_A_pair a b))
        have hint_B : Integrable f_B ((volume : Measure EuclN).restrict Ω) :=
          integrable_finset_sum _ (fun a _ =>
            integrable_finset_sum _ (fun b _ => h_int_B_pair_wp a b))
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
            ∑ a, ∑ j, A_pair a j := by
          change (∫ y in Ω,
              ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E),
                  (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b l) y)
                    (EuclideanSpace.single b 1) *
                  eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a D_m.directions) y * ψ y
              ∂(volume : Measure EuclN)) = _
          rw [integral_finset_sum _ (fun a _ =>
            (integrable_finset_sum _ (fun b _ => h_int_A_pair a b)))]
          refine Finset.sum_congr rfl ?_; intro a _
          rw [integral_finset_sum _ (fun b _ => h_int_A_pair a b)]
        have h_int_f_B : (∫ y in Ω, f_B y ∂(volume : Measure EuclN)) =
            ∑ a, ∑ j, B_pair a j := by
          change (∫ y in Ω,
              ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E),
                  weightedInvGramDerivOnEuclid (I := I) g α a b l y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                    (eigenvectorChartIteratedPartial (I := I) (M := M)
                      g r s i α P₀ (m + 1) (Fin.cons a D_m.directions))
                    (chartTargetEuclid (I := I) (M := M) α) y * ψ y
              ∂(volume : Measure EuclN)) = _
          rw [integral_finset_sum _ (fun a _ =>
            (integrable_finset_sum _ (fun b _ => h_int_B_pair_wp a b)))]
          refine Finset.sum_congr rfl ?_; intro a _
          rw [integral_finset_sum _ (fun b _ => h_int_B_pair_wp a b)]
          refine Finset.sum_congr rfl ?_; intro b _
          have h_eq :
              eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 2) (Fin.cons a (Fin.snoc D_m.directions b)) =
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                  (eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a D_m.directions))
                  (chartTargetEuclid (I := I) (M := M) α) := by
            rw [eigenvectorChartIteratedPartial_succ]
            have h_last : (Fin.cons a (Fin.snoc D_m.directions b) :
                Fin (m + 2) → Fin (Module.finrank ℝ E)) (Fin.last (m + 1)) = b := by
              have h_cs :
                  (Fin.cons a (Fin.snoc D_m.directions b) :
                    Fin (m + 2) → Fin (Module.finrank ℝ E)) =
                  Fin.snoc (Fin.cons a D_m.directions) b :=
                (snoc_cons_eq_cons_snoc (β := Fin (Module.finrank ℝ E))
                  a D_m.directions b).symm
              rw [h_cs]; simp
            have h_init : Fin.init (Fin.cons a (Fin.snoc D_m.directions b) :
                Fin (m + 2) → Fin (Module.finrank ℝ E)) =
                Fin.cons a D_m.directions := by
              have h_cs :
                  (Fin.cons a (Fin.snoc D_m.directions b) :
                    Fin (m + 2) → Fin (Module.finrank ℝ E)) =
                  Fin.snoc (Fin.cons a D_m.directions) b :=
                (snoc_cons_eq_cons_snoc (β := Fin (Module.finrank ℝ E))
                  a D_m.directions b).symm
              rw [h_cs]; simp
            rw [h_last, h_init]
          rw [hB_pair_def]
          refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
          rw [h_eq]
        have h_int_f_C : (∫ y in Ω, f_C y ∂(volume : Measure EuclN)) = -N_C := by
          change (∫ y in Ω,
              - (densityDerivOnEuclid (I := I) g α l y *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ m D_m.directions y * ψ y)
              ∂(volume : Measure EuclN)) = _
          rw [MeasureTheory.integral_neg]
        have h_int_f_D : (∫ y in Ω, f_D y ∂(volume : Measure EuclN)) = N_D := rfl
        have h_int_f_E : (∫ y in Ω, f_E y ∂(volume : Measure EuclN)) = N_E := rfl
        rw [h_int_f_A, h_int_f_B, h_int_f_C, h_int_f_D, h_int_f_E]
        ring
      change LHS_principal_new + N_mass_new = I_step_RHS
      rw [h_LHS_principal_new_eq, h_step_RHS_eq_num, h_numer_decomp]
      linarith)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
