import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRemainderPolynomial
import DifferentialGeometry.Geometry.Flow.RicciFlow.PrincipalSymbol
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSecondOrderPart
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.DeTurckCorrectionPrincipalSymbolRemainder
import Mathlib.Analysis.Calculus.FDeriv.Symmetric


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Set Function
open scoped Topology ContDiff Matrix Manifold BigOperators

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace DeTurckLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma hasDerivAt_fderiv_comm
    (Φ : ℝ × E → ℝ) (y₀ : E) (v : E)
    (hΦ : ContDiffAt ℝ ∞ Φ (0, y₀)) :
    HasDerivAt
      (fun s => fderiv ℝ (fun y => Φ (s, y)) y₀ v)
      (fderiv ℝ (fun y => deriv (fun s => Φ (s, y)) 0) y₀ v)
      0 := by
  have hΦ_dfderiv : ContDiffAt ℝ ∞ (fderiv ℝ Φ) (0, y₀) := hΦ.fderiv_right (by simp)
  have get_diff_nhd : ∀ (p₀ : ℝ × E), ContDiffAt ℝ ∞ Φ p₀ →
      ∀ᶠ p : ℝ × E in nhds p₀, DifferentiableAt ℝ Φ p := fun p₀ hp => by
    obtain ⟨f', u, hu, _, hfu⟩ :=
      contDiffAt_one_iff.mp (hp.of_le (by exact_mod_cast le_top : (1 : WithTop ℕ∞) ≤ ∞))
    exact Filter.eventually_of_mem hu fun p hp => (hfu p hp).differentiableAt
  have hΦ_s : ∀ᶠ s in nhds (0 : ℝ), DifferentiableAt ℝ Φ (s, y₀) :=
    (continuous_id.prodMk (continuous_const (y := y₀))).continuousAt (get_diff_nhd _ hΦ)
  have hΦ_y : ∀ᶠ y : E in nhds y₀, DifferentiableAt ℝ Φ (0, y) :=
    (continuous_const (y := (0 : ℝ)) |>.prodMk continuous_id).continuousAt (get_diff_nhd _ hΦ)
  have lhs_eq : (fun s => fderiv ℝ (fun y => Φ (s, y)) y₀ v) =ᶠ[nhds 0]
      (fun s => fderiv ℝ Φ (s, y₀) (0, v)) := by
    filter_upwards [hΦ_s] with s hs
    have h : HasFDerivAt (fun y => Φ (s, y))
        ((fderiv ℝ Φ (s, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ E)) y₀ :=
      hs.hasFDerivAt.comp y₀ (hasFDerivAt_prodMk_right s y₀)
    rw [h.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  have h_fderiv_s : HasFDerivAt (fun s : ℝ => fderiv ℝ Φ (s, y₀))
      ((fderiv ℝ (fderiv ℝ Φ) (0, y₀)).comp (ContinuousLinearMap.inl ℝ ℝ E)) 0 :=
    (hΦ_dfderiv.differentiableAt (by norm_num)).hasFDerivAt.comp 0 (hasFDerivAt_prodMk_left 0 y₀)
  have h_sv : HasDerivAt (fun s => fderiv ℝ Φ (s, y₀) (0, v))
      (fderiv ℝ (fderiv ℝ Φ) (0, y₀) (1, 0) (0, v)) 0 := by
    have h_d : HasDerivAt (fun s : ℝ => fderiv ℝ Φ (s, y₀))
        (fderiv ℝ (fderiv ℝ Φ) (0, y₀) (1, 0)) 0 := by
      simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
        using h_fderiv_s.hasDerivAt
    simpa [map_zero] using h_d.clm_apply (hasDerivAt_const 0 ((0 : ℝ), v))
  have hsymm : IsSymmSndFDerivAt ℝ Φ (0, y₀) :=
    hΦ.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)
  have h_sv' : HasDerivAt (fun s => fderiv ℝ Φ (s, y₀) (0, v))
      (fderiv ℝ (fderiv ℝ Φ) (0, y₀) (0, v) (1, 0)) 0 := by
    rwa [hsymm ((1 : ℝ), (0 : E)) ((0 : ℝ), v)] at h_sv
  have rhs_eq : fderiv ℝ (fun y => deriv (fun s => Φ (s, y)) 0) y₀ v =
      fderiv ℝ (fderiv ℝ Φ) (0, y₀) (0, v) (1, 0) := by
    have h_eq : (fun y => deriv (fun s => Φ (s, y)) 0) =ᶠ[nhds y₀]
        (fun y => fderiv ℝ Φ (0, y) (1, 0)) := by
      filter_upwards [hΦ_y] with y hy
      have := hy.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        (hasFDerivAt_prodMk_left (0 : ℝ) y).hasDerivAt
      exact this.deriv
    rw [Filter.EventuallyEq.fderiv_eq h_eq]
    have h_chain : HasFDerivAt (fun y => fderiv ℝ Φ ((0 : ℝ), y) ((1 : ℝ), (0 : E)))
        ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : E))).comp
          ((fderiv ℝ (fderiv ℝ Φ) ((0 : ℝ), y₀)).comp (ContinuousLinearMap.inr ℝ ℝ E))) y₀ :=
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : E))).hasFDerivAt.comp y₀
        ((hΦ_dfderiv.differentiableAt (by norm_num)).hasFDerivAt.comp y₀
          (hasFDerivAt_prodMk_right 0 y₀))
    simp [h_chain.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
          ContinuousLinearMap.inr_apply]
  rw [rhs_eq]
  exact h_sv'.congr_of_eventuallyEq lhs_eq

omit [NeZero (Module.finrank ℝ E)] in
private lemma hasDerivAt_partialDeriv_comm
    (Φ : ℝ × E → ℝ) (p : Fin (Module.finrank ℝ E)) (y₀ : E)
    (hΦ : ContDiffAt ℝ ∞ Φ (0, y₀)) :
    HasDerivAt
      (fun s => partialDeriv (E := E) p (fun y => Φ (s, y)) y₀)
      (partialDeriv (E := E) p (fun y => deriv (fun s => Φ (s, y)) 0) y₀) 0 := by
  unfold partialDeriv
  exact hasDerivAt_fderiv_comm Φ y₀ (chartModelBasis E p) hΦ

omit [NeZero (Module.finrank ℝ E)] in
private lemma joint_contDiffAt_partialDeriv
    (Ψ : ℝ → E → ℝ) (q : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hΨ : ContDiffAt ℝ ∞ (fun r : ℝ × E => Ψ r.1 r.2) (0, y₀)) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × E => partialDeriv (E := E) q (fun y => Ψ p.1 y) p.2) (0, y₀) := by
  have hf : ContDiffAt ℝ ∞
      (Function.uncurry (fun (p : ℝ × E) (y : E) => Ψ p.1 y))
      ((0, y₀), (fun p : ℝ × E => p.2) (0, y₀)) := by
    have huncurry : (Function.uncurry (fun (p : ℝ × E) (y : E) => Ψ p.1 y)) =
        (fun r : ℝ × E => Ψ r.1 r.2) ∘ (fun z : (ℝ × E) × E => (z.1.1, z.2)) := by
      funext z; rfl
    rw [huncurry]
    refine hΨ.comp ((0, y₀), y₀) ?_
    exact (contDiffAt_fst.comp ((0, y₀), y₀) contDiffAt_fst).prodMk contDiffAt_snd
  have hg : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (0, y₀) := contDiffAt_snd
  have hfd := ContDiffAt.fderiv hf hg (le_refl _)
  exact (ContinuousLinearMap.apply ℝ ℝ (chartModelBasis E q)).contDiff.contDiffAt.comp (0, y₀) hfd

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma joint_contDiffAt_chartGramOnE
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (i j : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartGramOnE (I := I) (gfam r.1) α i j r.2) (0, y₀) :=
  hfam.2.2.1 i j hy

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma symm_mem_baseSet_of_interior {α : M} {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
  have hy_t : y ∈ (extChartAt I α).target := interior_subset hy
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy_t
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  exact hsource

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma s_contDiffAt_chartGramOnE
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞ (fun s : ℝ => chartGramOnE (I := I) (gfam s) α i j y) 0 := by
  have hjoint := hfam.2.2.1 i j hy
  have hcomp : (fun s : ℝ => chartGramOnE (I := I) (gfam s) α i j y) =
      (fun p : ℝ × E => chartGramOnE (I := I) (gfam p.1) α i j p.2) ∘
        (fun s : ℝ => (s, y)) := by
    funext s; rfl
  rw [hcomp]
  refine hjoint.comp 0 ?_
  exact (contDiffAt_id).prodMk contDiffAt_const

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma s_contDiffAt_det_and_ne
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
        (fun s : ℝ => (chartGramMatrix (I := I) (gfam s) α ((extChartAt I α).symm y)).det) 0 ∧
      (chartGramMatrix (I := I) (gfam 0) α ((extChartAt I α).symm y)).det ≠ 0 := by
  classical
  set x : M := (extChartAt I α).symm y with hx_def
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    symm_mem_baseSet_of_interior (I := I) hy
  refine ⟨?_, ?_⟩
  · have hdet_eq : (fun s : ℝ =>
        (chartGramMatrix (I := I) (gfam s) α x).det) =
        (fun s : ℝ => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ k, chartGramMatrix (I := I) (gfam s) α x (σ k) k) := by
      funext s
      rw [Matrix.det_apply]
      simp [Units.smul_def]
    rw [hdet_eq]
    refine ContDiffAt.sum (fun σ _ => ?_)
    refine contDiffAt_const.mul ?_
    refine contDiffAt_prod (fun k _ => ?_)
    have hentry : (fun s : ℝ => chartGramMatrix (I := I) (gfam s) α x (σ k) k) =
        (fun s : ℝ => chartGramOnE (I := I) (gfam s) α (σ k) k y) := by
      funext s; rw [chartGramOnE_def]
    rw [hentry]
    exact s_contDiffAt_chartGramOnE (I := I) hfam (σ k) k hy
  · exact ne_of_gt (chartGramMatrix_det_pos (I := I) (gfam 0) α hx_base)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma s_contDiffAt_adjugate
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun s : ℝ =>
        (chartGramMatrix (I := I) (gfam s) α ((extChartAt I α).symm y)).adjugate i j) 0 := by
  classical
  set x : M := (extChartAt I α).symm y with hx_def
  have hexp : (fun s : ℝ => (chartGramMatrix (I := I) (gfam s) α x).adjugate i j) =
      (fun s : ℝ => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        (Equiv.Perm.sign σ : ℝ) *
          ∏ k, (chartGramMatrix (I := I) (gfam s) α x).updateRow j
              (Pi.single i (1 : ℝ)) (σ k) k) := by
    funext s
    rw [Matrix.adjugate_apply, Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine ContDiffAt.sum (fun σ _ => ?_)
  refine contDiffAt_const.mul ?_
  refine contDiffAt_prod (fun k _ => ?_)
  by_cases hσk : σ k = j
  · have heq : (fun s : ℝ => (chartGramMatrix (I := I) (gfam s) α x).updateRow j
        (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun _ : ℝ => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) i
          (1 : ℝ)) k) := by
      funext s; rw [hσk, Matrix.updateRow_self]
    rw [heq]; exact contDiffAt_const
  · have heq : (fun s : ℝ => (chartGramMatrix (I := I) (gfam s) α x).updateRow j
        (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun s : ℝ => chartGramOnE (I := I) (gfam s) α (σ k) k y) := by
      funext s; rw [Matrix.updateRow_ne hσk, chartGramOnE_def]
    rw [heq]
    exact s_contDiffAt_chartGramOnE (I := I) hfam (σ k) k hy

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma s_contDiffAt_chartInvGramOnE
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (k l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞ (fun s : ℝ => chartInvGramOnE (I := I) (gfam s) α k l y) 0 := by
  classical
  set x : M := (extChartAt I α).symm y with hx_def
  obtain ⟨hdet_smooth, hdet_ne⟩ := s_contDiffAt_det_and_ne (I := I) hfam hy
  have hcongr : (fun s : ℝ => chartInvGramOnE (I := I) (gfam s) α k l y) =
      (fun s : ℝ => ((chartGramMatrix (I := I) (gfam s) α x).det)⁻¹ *
        (chartGramMatrix (I := I) (gfam s) α x).adjugate k l) := by
    funext s
    rw [chartInvGramOnE_def]
    change (chartGramMatrix (I := I) (gfam s) α x)⁻¹ k l = _
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) (gfam s) α x).det •
            (chartGramMatrix (I := I) (gfam s) α x).adjugate) k l = _
    rw [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [hcongr]
  refine ContDiffAt.mul ?_ (s_contDiffAt_adjugate (I := I) hfam k l hy)
  exact (contDiffAt_inv _ hdet_ne).comp 0 hdet_smooth

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma s_differentiableAt_chartInvGramOnE
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (k l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (fun s : ℝ => chartInvGramOnE (I := I) (gfam s) α k l y) 0 :=
  (s_contDiffAt_chartInvGramOnE (I := I) hfam k l hy).differentiableAt (by simp)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma joint_contDiffAt_chartInvGramOnE
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (k l : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × E => chartInvGramOnE (I := I) (gfam p.1) α k l p.2) (0, y₀) := by
  classical

  have hGentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2) a b) (0, y₀) := by
    intro a b
    have := joint_contDiffAt_chartGramOnE (I := I) hfam a b hy
    simpa only [chartGramOnE_def] using this

  have hdet : ContDiffAt ℝ ∞
      (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
        ((extChartAt I α).symm p.2)).det) (0, y₀) := by
    have hdet_eq : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).det) =
        (fun p : ℝ × E => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ kk, chartGramMatrix (I := I) (gfam p.1) α
              ((extChartAt I α).symm p.2) (σ kk) kk) := by
      funext p; rw [Matrix.det_apply]; simp [Units.smul_def]
    rw [hdet_eq]
    refine ContDiffAt.sum (fun σ _ => ?_)
    refine contDiffAt_const.mul ?_
    exact contDiffAt_prod (fun kk _ => hGentry (σ kk) kk)
  have hdet_ne : (chartGramMatrix (I := I) (gfam (0, y₀).1) α
      ((extChartAt I α).symm (0, y₀).2)).det ≠ 0 :=
    ne_of_gt (chartGramMatrix_det_pos (I := I) (gfam 0) α
      (symm_mem_baseSet_of_interior (I := I) hy))
  have hadj : ∀ kk ll : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).adjugate kk ll) (0, y₀) := by
    intro kk ll
    have hexp : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).adjugate kk ll) =
        (fun p : ℝ × E => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ m, (chartGramMatrix (I := I) (gfam p.1) α
                ((extChartAt I α).symm p.2)).updateRow ll
                (Pi.single kk (1 : ℝ)) (σ m) m) := by
      funext p; rw [Matrix.adjugate_apply, Matrix.det_apply]; simp [Units.smul_def]
    rw [hexp]
    refine ContDiffAt.sum (fun σ _ => ?_)
    refine contDiffAt_const.mul ?_
    refine contDiffAt_prod (fun m _ => ?_)
    by_cases hσm : σ m = ll
    · have heq : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).updateRow ll (Pi.single kk (1 : ℝ)) (σ m) m) =
          (fun _ : ℝ × E => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) kk
            (1 : ℝ)) m) := by
        funext p; rw [hσm, Matrix.updateRow_self]
      rw [heq]; exact contDiffAt_const
    · have heq : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).updateRow ll (Pi.single kk (1 : ℝ)) (σ m) m) =
          (fun p : ℝ × E => chartGramMatrix (I := I) (gfam p.1) α
            ((extChartAt I α).symm p.2) (σ m) m) := by
        funext p; rw [Matrix.updateRow_ne hσm]
      rw [heq]; exact hGentry (σ m) m
  have hcongr : (fun p : ℝ × E => chartInvGramOnE (I := I) (gfam p.1) α k l p.2) =
      (fun p : ℝ × E => ((chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).det)⁻¹ *
        (chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2)).adjugate k l) := by
    funext p
    rw [chartInvGramOnE_def]
    change (chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2))⁻¹ k l = _
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) (gfam p.1) α
            ((extChartAt I α).symm p.2)).det •
            (chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2)).adjugate) k l = _
    rw [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [hcongr]
  exact ((contDiffAt_inv _ hdet_ne).comp (0, y₀) hdet).mul (hadj k l)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma joint_contDiffAt_partial_chartGramOnE
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (i j p : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => partialDeriv (E := E) p
        (fun y => chartGramOnE (I := I) (gfam r.1) α i j y) r.2) (0, y₀) :=
  joint_contDiffAt_partialDeriv
    (fun s y => chartGramOnE (I := I) (gfam s) α i j y) p
    (joint_contDiffAt_chartGramOnE (I := I) hfam i j hy)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma joint_contDiffAt_gramBracket
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (i j l : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => gramBracket (I := I) (gfam r.1) α i j l r.2) (0, y₀) := by
  have heq : (fun r : ℝ × E => gramBracket (I := I) (gfam r.1) α i j l r.2) =
      (fun r : ℝ × E =>
        partialDeriv (E := E) i (fun y => chartGramOnE (I := I) (gfam r.1) α l j y) r.2 +
          partialDeriv (E := E) j (fun y => chartGramOnE (I := I) (gfam r.1) α l i y) r.2 -
          partialDeriv (E := E) l (fun y => chartGramOnE (I := I) (gfam r.1) α i j y) r.2) := by
    funext r; rw [gramBracket]
  rw [heq]
  exact ((joint_contDiffAt_partial_chartGramOnE (I := I) hfam l j i hy).add
    (joint_contDiffAt_partial_chartGramOnE (I := I) hfam l i j hy)).sub
    (joint_contDiffAt_partial_chartGramOnE (I := I) hfam i j l hy)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma joint_contDiffAt_chartChristoffel
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (i j k : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartChristoffel (I := I) (gfam r.1) α i j k r.2) (0, y₀) := by
  have heq : (fun r : ℝ × E => chartChristoffel (I := I) (gfam r.1) α i j k r.2) =
      (fun r : ℝ × E => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (gfam r.1) α k l r.2 *
          gramBracket (I := I) (gfam r.1) α i j l r.2) := by
    funext r; rw [chartChristoffel_eq_sum_invGramOnE_bracket]
  rw [heq]
  refine contDiffAt_const.mul (ContDiffAt.sum (fun l _ => ?_))
  exact (joint_contDiffAt_chartInvGramOnE (I := I) hfam k l hy).mul
    (joint_contDiffAt_gramBracket (I := I) hfam i j l hy)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma gfam_zero {g₀ : SmoothRiemannianMetric I M} {α : M}
    {h : ChartMetricPerturbation E} {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam) : gfam 0 = g₀ := hfam.1

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma hasDerivAt_chartGramOnE
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    HasDerivAt (fun s : ℝ => chartGramOnE (I := I) (gfam s) α i j y) (h i j y) 0 :=
  hfam.2.1 i j hy

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma s_differentiableAt_chartGramOnE
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (fun s : ℝ => chartGramOnE (I := I) (gfam s) α i j y) 0 :=
  (hasDerivAt_chartGramOnE (I := I) hfam i j hy).differentiableAt

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma hasDerivAt_partial_chartGramOnE
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (i j p : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    HasDerivAt
      (fun s : ℝ => partialDeriv (E := E) p (chartGramOnE (I := I) (gfam s) α i j) y)
      (partialDeriv (E := E) p (h i j) y) 0 :=
  hfam.2.2.2.1 i j p hy

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma hasDerivAt_partial2_chartGramOnE
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (i j p q : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    HasDerivAt
      (fun s : ℝ =>
        partialDeriv (E := E) p
          (partialDeriv (E := E) q (chartGramOnE (I := I) (gfam s) α i j)) y)
      (partialDeriv (E := E) p (partialDeriv (E := E) q (h i j)) y) 0 :=
  hfam.2.2.2.2 i j p q hy

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma hasDerivAt_chartInvGramOnE
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (k l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    HasDerivAt (fun s : ℝ => chartInvGramOnE (I := I) (gfam s) α k l y)
      (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g₀ α k p y * h p q y *
            chartInvGramOnE (I := I) g₀ α q l y)) 0 := by
  classical
  have hg0 : gfam 0 = g₀ := hfam.1
  have hsub : (fun s : ℝ => chartInvGramOnE (I := I) (gfam s) α k l y) =
      (fun s : ℝ => chartInvGramOnE (I := I) g₀ α k l y +
        (∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (gfam s) α k p y *
            (chartGramOnE (I := I) g₀ α p q y - chartGramOnE (I := I) (gfam s) α p q y) *
            chartInvGramOnE (I := I) g₀ α q l y)) := by
    funext s
    have := invGramOnE_sub_eq (I := I) (gfam s) g₀ α k l hy
    linarith [this]
  rw [hsub]
  have hconst : HasDerivAt (fun _ : ℝ => chartInvGramOnE (I := I) g₀ α k l y) 0 0 :=
    hasDerivAt_const 0 _
  have hsum : HasDerivAt
      (fun s : ℝ => ∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (gfam s) α k p y *
            (chartGramOnE (I := I) g₀ α p q y - chartGramOnE (I := I) (gfam s) α p q y) *
            chartInvGramOnE (I := I) g₀ α q l y)
      (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g₀ α k p y * h p q y *
            chartInvGramOnE (I := I) g₀ α q l y)) 0 := by
    rw [show (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₀ α k p y * h p q y *
              chartInvGramOnE (I := I) g₀ α q l y)) =
          (∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₀ α k p y * (-(h p q y)) *
              chartInvGramOnE (I := I) g₀ α q l y) from by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      ring]
    refine HasDerivAt.fun_sum (fun q _ => ?_)
    refine HasDerivAt.fun_sum (fun p _ => ?_)

    set A : ℝ → ℝ := fun s => chartInvGramOnE (I := I) (gfam s) α k p y with hA
    set B : ℝ → ℝ := fun s =>
      chartGramOnE (I := I) g₀ α p q y - chartGramOnE (I := I) (gfam s) α p q y with hB
    have hA_diff : DifferentiableAt ℝ A 0 :=
      s_differentiableAt_chartInvGramOnE (I := I) hfam k p hy
    have hA0 : A 0 = chartInvGramOnE (I := I) g₀ α k p y := by simp only [hA, hg0]
    have hB_deriv : HasDerivAt B (-(h p q y)) 0 := by
      have hconstB : HasDerivAt (fun _ : ℝ => chartGramOnE (I := I) g₀ α p q y) 0 0 :=
        hasDerivAt_const 0 _
      have hg := hasDerivAt_chartGramOnE (I := I) hfam p q hy
      have := hconstB.sub hg
      simpa [hB] using this
    have hB0 : B 0 = 0 := by simp [hB, hg0]

    have hAB : HasDerivAt (fun s => A s * B s)
        (chartInvGramOnE (I := I) g₀ α k p y * (-(h p q y))) 0 := by
      have := hA_diff.hasDerivAt.mul hB_deriv
      rw [hA0, hB0] at this
      simpa using this
    have hABC := hAB.mul_const (chartInvGramOnE (I := I) g₀ α q l y)
    have hgoal_eq : (fun s : ℝ =>
          chartInvGramOnE (I := I) (gfam s) α k p y *
            (chartGramOnE (I := I) g₀ α p q y - chartGramOnE (I := I) (gfam s) α p q y) *
            chartInvGramOnE (I := I) g₀ α q l y) =
        (fun s : ℝ => A s * B s * chartInvGramOnE (I := I) g₀ α q l y) := by
      funext s; rw [hA, hB]
    rw [hgoal_eq]
    refine hABC.congr_deriv ?_
    ring
  have hfinal := hconst.add hsum
  rw [zero_add] at hfinal
  exact hfinal

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma hasDerivAt_gramBracket
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    HasDerivAt (fun s : ℝ => gramBracket (I := I) (gfam s) α i j l y)
      (partialDeriv (E := E) i (h l j) y + partialDeriv (E := E) j (h l i) y -
        partialDeriv (E := E) l (h i j) y) 0 := by
  have h1 := hasDerivAt_partial_chartGramOnE (I := I) hfam l j i hy
  have h2 := hasDerivAt_partial_chartGramOnE (I := I) hfam l i j hy
  have h3 := hasDerivAt_partial_chartGramOnE (I := I) hfam i j l hy
  have hsum := (h1.add h2).sub h3
  have heq : (fun s : ℝ => gramBracket (I := I) (gfam s) α i j l y) =
      (fun s : ℝ =>
        partialDeriv (E := E) i (chartGramOnE (I := I) (gfam s) α l j) y +
          partialDeriv (E := E) j (chartGramOnE (I := I) (gfam s) α l i) y -
          partialDeriv (E := E) l (chartGramOnE (I := I) (gfam s) α i j) y) := by
    funext s; rw [gramBracket]
  rw [heq]; exact hsum

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma chartGramOnE_gfam_zero
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) (gfam 0) α i j y = chartGramOnE (I := I) g₀ α i j y := by
  rw [hfam.1]

def christoffelFirstOrderCorr (g₀ : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₀ α k p y * h p q y *
          chartInvGramOnE (I := I) g₀ α q l y)) *
      gramBracket (I := I) g₀ α i j l y

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma hasDerivAt_chartChristoffel
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    HasDerivAt (fun s : ℝ => chartChristoffel (I := I) (gfam s) α i j k y)
      (chartLinearizedChristoffelPrincipal (I := I) g₀ α h i j k y +
        christoffelFirstOrderCorr (I := I) g₀ α h i j k y) 0 := by
  classical
  have hg0 : gfam 0 = g₀ := hfam.1
  have heq : (fun s : ℝ => chartChristoffel (I := I) (gfam s) α i j k y) =
      (fun s : ℝ => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (gfam s) α k l y * gramBracket (I := I) (gfam s) α i j l y) := by
    funext s; rw [chartChristoffel_eq_sum_invGramOnE_bracket]
  rw [heq]

  set D : ℝ := ∑ l : Fin (Module.finrank ℝ E),
    ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g₀ α k p y * h p q y *
            chartInvGramOnE (I := I) g₀ α q l y)) *
        gramBracket (I := I) g₀ α i j l y +
      chartInvGramOnE (I := I) g₀ α k l y *
        (partialDeriv (E := E) i (h l j) y + partialDeriv (E := E) j (h l i) y -
          partialDeriv (E := E) l (h i j) y)) with hD
  have hsum_deriv : HasDerivAt
      (fun s : ℝ => ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (gfam s) α k l y * gramBracket (I := I) (gfam s) α i j l y)
      D 0 := by
    rw [hD]
    refine HasDerivAt.fun_sum (fun l _ => ?_)
    have hG := hasDerivAt_chartInvGramOnE (I := I) hfam k l hy
    have hbr := hasDerivAt_gramBracket (I := I) hfam i j l hy
    have hprod := hG.mul hbr

    have hGval : chartInvGramOnE (I := I) (gfam 0) α k l y =
        chartInvGramOnE (I := I) g₀ α k l y := by rw [hg0]
    have hbrval : gramBracket (I := I) (gfam 0) α i j l y =
        partialDeriv (E := E) i (chartGramOnE (I := I) g₀ α l j) y +
          partialDeriv (E := E) j (chartGramOnE (I := I) g₀ α l i) y -
          partialDeriv (E := E) l (chartGramOnE (I := I) g₀ α i j) y := by
      rw [hg0, gramBracket]
    rw [hGval, hbrval] at hprod
    refine hprod.congr_deriv ?_
    simp only [gramBracket]
  have hfinal := hsum_deriv.const_mul (1 / 2 : ℝ)
  refine hfinal.congr_deriv ?_
  rw [chartLinearizedChristoffelPrincipal_def, christoffelFirstOrderCorr, hD]
  rw [show (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₀ α k l y *
          (partialDeriv (E := E) i (h l j) y + partialDeriv (E := E) j (h l i) y -
            partialDeriv (E := E) l (h i j) y) +
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g₀ α k p y * h p q y *
                chartInvGramOnE (I := I) g₀ α q l y)) *
            gramBracket (I := I) g₀ α i j l y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g₀ α k p y * h p q y *
                chartInvGramOnE (I := I) g₀ α q l y)) *
            gramBracket (I := I) g₀ α i j l y +
          chartInvGramOnE (I := I) g₀ α k l y *
            (partialDeriv (E := E) i (h l j) y + partialDeriv (E := E) j (h l i) y -
              partialDeriv (E := E) l (h i j) y)) from by
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma hasDerivAt_gramBracketDeriv
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (m i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    HasDerivAt (fun s : ℝ => gramBracketDeriv (I := I) (gfam s) α m i j l y)
      (partialDeriv (E := E) m (partialDeriv (E := E) i (h l j)) y +
        partialDeriv (E := E) m (partialDeriv (E := E) j (h l i)) y -
        partialDeriv (E := E) m (partialDeriv (E := E) l (h i j)) y) 0 := by
  have h1 := hasDerivAt_partial2_chartGramOnE (I := I) hfam l j m i hy
  have h2 := hasDerivAt_partial2_chartGramOnE (I := I) hfam l i m j hy
  have h3 := hasDerivAt_partial2_chartGramOnE (I := I) hfam i j m l hy
  have hsum := (h1.add h2).sub h3
  have heq : (fun s : ℝ => gramBracketDeriv (I := I) (gfam s) α m i j l y) =
      (fun s : ℝ =>
        partialDeriv (E := E) m (partialDeriv (E := E) i (chartGramOnE (I := I) (gfam s) α l j)) y +
          partialDeriv (E := E) m
            (partialDeriv (E := E) j (chartGramOnE (I := I) (gfam s) α l i)) y -
          partialDeriv (E := E) m
            (partialDeriv (E := E) l (chartGramOnE (I := I) (gfam s) α i j)) y) := by
    funext s; rw [gramBracketDeriv]
  rw [heq]; exact hsum

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma hasDerivAt_partial_chartInvGramOnE
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (m j p : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    HasDerivAt
      (fun s : ℝ => partialDeriv (E := E) m (chartInvGramOnE (I := I) (gfam s) α j p) y)
      (-(∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          ((-(∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g₀ α j r y * h r q y *
                  chartInvGramOnE (I := I) g₀ α q a y)) *
              chartInvGramOnE (I := I) g₀ α b p y *
              partialDeriv (E := E) m (chartGramOnE (I := I) g₀ α a b) y +
            chartInvGramOnE (I := I) g₀ α j a y *
              (-(∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g₀ α b r y * h r q y *
                    chartInvGramOnE (I := I) g₀ α q p y)) *
              partialDeriv (E := E) m (chartGramOnE (I := I) g₀ α a b) y +
            chartInvGramOnE (I := I) g₀ α j a y *
              chartInvGramOnE (I := I) g₀ α b p y *
              partialDeriv (E := E) m (h a b) y))) 0 := by
  classical
  have hg0 : gfam 0 = g₀ := hfam.1
  have heq : (fun s : ℝ => partialDeriv (E := E) m (chartInvGramOnE (I := I) (gfam s) α j p) y) =
      (fun s : ℝ => -∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (gfam s) α j a y *
          chartInvGramOnE (I := I) (gfam s) α b p y *
          partialDeriv (E := E) m (chartGramOnE (I := I) (gfam s) α a b) y) := by
    funext s
    rw [partialDeriv_chartInvGramOnE_eq (I := I) (gfam s) α y m j p hy]
  rw [heq]
  refine HasDerivAt.neg ?_
  refine HasDerivAt.fun_sum (fun a _ => ?_)
  refine HasDerivAt.fun_sum (fun b _ => ?_)

  have hG1 := hasDerivAt_chartInvGramOnE (I := I) hfam j a hy
  have hG2 := hasDerivAt_chartInvGramOnE (I := I) hfam b p hy
  have hGd := hasDerivAt_partial_chartGramOnE (I := I) hfam a b m hy
  have hprod := (hG1.mul hG2).mul hGd

  have hG1v : chartInvGramOnE (I := I) (gfam 0) α j a y = chartInvGramOnE (I := I) g₀ α j a y := by
    rw [hg0]
  have hG2v : chartInvGramOnE (I := I) (gfam 0) α b p y = chartInvGramOnE (I := I) g₀ α b p y := by
    rw [hg0]
  have hGdv : partialDeriv (E := E) m (chartGramOnE (I := I) (gfam 0) α a b) y =
      partialDeriv (E := E) m (chartGramOnE (I := I) g₀ α a b) y := by rw [hg0]
  rw [hG1v, hG2v, hGdv] at hprod
  refine hprod.congr_deriv ?_
  simp only [Pi.mul_apply, hg0]
  ring

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma partial_chartGramOnE_differentiableAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (p l b : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (partialDeriv (E := E) p (chartGramOnE (I := I) g α l b)) y₀ := by
  have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l b) (extChartAt I α).target :=
    chartGramOnE_contDiffOn (I := I) g α l b
  have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l b)
      (interior (extChartAt I α).target) := hcd.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (chartGramOnE (I := I) g α l b))
      (interior (extChartAt I α).target) :=
    hcd_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hpd : ContDiffOn ℝ ∞ (partialDeriv (E := E) p (chartGramOnE (I := I) g α l b))
      (interior (extChartAt I α).target) := by
    unfold partialDeriv
    exact hfderiv.clm_apply contDiffOn_const
  exact (hpd.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma christoffelFirstOrderCorr_differentiableAt
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {i j k : Fin (Module.finrank ℝ E)} {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (fun y => christoffelFirstOrderCorr (I := I) g₀ α h i j k y) y₀ := by
  classical
  unfold christoffelFirstOrderCorr
  refine DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.fun_sum (fun l _ => ?_)
  refine DifferentiableAt.mul ?_ ?_
  · refine DifferentiableAt.neg ?_
    refine DifferentiableAt.fun_sum (fun q _ => ?_)
    refine DifferentiableAt.fun_sum (fun p _ => ?_)
    refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_
    · exact chartInvGramOnE_differentiableAt_interior (I := I) g₀ α k p hy
    · exact (h.differentiableAt p q y₀)
    · exact chartInvGramOnE_differentiableAt_interior (I := I) g₀ α q l hy
  · unfold gramBracket
    refine DifferentiableAt.sub (DifferentiableAt.add ?_ ?_) ?_
    · exact partial_chartGramOnE_differentiableAt (I := I) g₀ α i l j hy
    · exact partial_chartGramOnE_differentiableAt (I := I) g₀ α j l i hy
    · exact partial_chartGramOnE_differentiableAt (I := I) g₀ α l i j hy

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma hasDerivAt_partial_chartChristoffel
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (m i j k : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    HasDerivAt
      (fun s : ℝ =>
        partialDeriv (E := E) m (fun y => chartChristoffel (I := I) (gfam s) α i j k y) y₀)
      (partialDeriv (E := E) m
          (fun y => chartLinearizedChristoffelPrincipal (I := I) g₀ α h i j k y) y₀ +
        partialDeriv (E := E) m
          (fun y => christoffelFirstOrderCorr (I := I) g₀ α h i j k y) y₀) 0 := by
  classical

  have hderiv_eq : (fun y => deriv (fun s : ℝ =>
        chartChristoffel (I := I) (gfam s) α i j k y) 0) =ᶠ[nhds y₀]
      (fun y => chartLinearizedChristoffelPrincipal (I := I) g₀ α h i j k y +
        christoffelFirstOrderCorr (I := I) g₀ α h i j k y) := by
    filter_upwards [isOpen_interior.mem_nhds hy] with y hy'
    exact (hasDerivAt_chartChristoffel (I := I) hfam i j k hy').deriv

  have hcomm := hasDerivAt_partialDeriv_comm
    (fun p : ℝ × E => chartChristoffel (I := I) (gfam p.1) α i j k p.2) m y₀
    (joint_contDiffAt_chartChristoffel (I := I) hfam i j k hy)

  have hrhs : partialDeriv (E := E) m
        (fun y => deriv (fun s : ℝ => chartChristoffel (I := I) (gfam s) α i j k y) 0) y₀ =
      partialDeriv (E := E) m
          (fun y => chartLinearizedChristoffelPrincipal (I := I) g₀ α h i j k y) y₀ +
        partialDeriv (E := E) m
          (fun y => christoffelFirstOrderCorr (I := I) g₀ α h i j k y) y₀ := by
    unfold partialDeriv
    rw [Filter.EventuallyEq.fderiv_eq hderiv_eq]
    rw [show (fun y => chartLinearizedChristoffelPrincipal (I := I) g₀ α h i j k y +
          christoffelFirstOrderCorr (I := I) g₀ α h i j k y) =
        (fun y => chartLinearizedChristoffelPrincipal (I := I) g₀ α h i j k y) +
          (fun y => christoffelFirstOrderCorr (I := I) g₀ α h i j k y) from rfl]
    rw [fderiv_add]
    · rfl
    · exact (chartLinearizedChristoffelPrincipal_differentiableAt (I := I) g₀ α h i j k hy)
    · exact christoffelFirstOrderCorr_differentiableAt (I := I) (g₀ := g₀) hy
  rw [hrhs] at hcomm
  exact hcomm

def ricciDerivFirstOrderRemainder (g₀ : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (∑ j : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) j
          (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h i k j y') y -
        partialDeriv (E := E) k
          (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h i j j y') y)) +
    (∑ j : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
      (((chartLinearizedChristoffelPrincipal (I := I) g₀ α h j m j y +
            christoffelFirstOrderCorr (I := I) g₀ α h j m j y) *
          chartChristoffel (I := I) g₀ α i k m y +
        chartChristoffel (I := I) g₀ α j m j y *
          (chartLinearizedChristoffelPrincipal (I := I) g₀ α h i k m y +
            christoffelFirstOrderCorr (I := I) g₀ α h i k m y)) -
        ((chartLinearizedChristoffelPrincipal (I := I) g₀ α h k m j y +
            christoffelFirstOrderCorr (I := I) g₀ α h k m j y) *
          chartChristoffel (I := I) g₀ α i j m y +
        chartChristoffel (I := I) g₀ α k m j y *
          (chartLinearizedChristoffelPrincipal (I := I) g₀ α h i j m y +
            christoffelFirstOrderCorr (I := I) g₀ α h i j m y))))

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartChristoffel_differentiableAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (fun y => chartChristoffel (I := I) g α i j k y) y₀ := by
  classical
  have heq : (fun y => chartChristoffel (I := I) g α i j k y) =
      (fun y => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y * gramBracket (I := I) g α i j l y) := by
    funext y; rw [chartChristoffel_eq_sum_invGramOnE_bracket]
  rw [heq]
  refine DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.fun_sum (fun l _ => ?_)
  refine DifferentiableAt.mul (chartInvGramOnE_differentiableAt_interior (I := I) g α k l hy) ?_
  unfold gramBracket
  exact ((partial_chartGramOnE_differentiableAt (I := I) g α i l j hy).add
    (partial_chartGramOnE_differentiableAt (I := I) g α j l i hy)).sub
    (partial_chartGramOnE_differentiableAt (I := I) g α l i j hy)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma hasDerivAt_chartRicciTensor
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    HasDerivAt (fun s : ℝ => chartRicciTensor (I := I) (gfam s) α i k y)
      (chartRicciSecondOrderPart (I := I) g₀ α h i k y +
        ricciDerivFirstOrderRemainder (I := I) g₀ α h i k y) 0 := by
  classical
  have hg0 : gfam 0 = g₀ := hfam.1

  have hSO : HasDerivAt
      (fun s : ℝ => chartRicciSecondOrderTerm (I := I) (gfam s) α i k y)
      (chartRicciSecondOrderPart (I := I) g₀ α h i k y +
        (∑ j : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) j
              (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h i k j y') y -
            partialDeriv (E := E) k
              (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h i j j y') y))) 0 := by
    have heq : (fun s : ℝ => chartRicciSecondOrderTerm (I := I) (gfam s) α i k y) =
        (fun s : ℝ => ∑ j : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) j
              (fun y' => chartChristoffel (I := I) (gfam s) α i k j y') y -
            partialDeriv (E := E) k
              (fun y' => chartChristoffel (I := I) (gfam s) α i j j y') y)) := by
      funext s; rw [chartRicciSecondOrderTerm]
    rw [heq]
    have hdsum : HasDerivAt
        (fun s : ℝ => ∑ j : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) j
              (fun y' => chartChristoffel (I := I) (gfam s) α i k j y') y -
            partialDeriv (E := E) k
              (fun y' => chartChristoffel (I := I) (gfam s) α i j j y') y))
        (∑ j : Fin (Module.finrank ℝ E),
          ((partialDeriv (E := E) j
                (fun y' => chartLinearizedChristoffelPrincipal (I := I) g₀ α h i k j y') y +
              partialDeriv (E := E) j
                (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h i k j y') y) -
            (partialDeriv (E := E) k
                (fun y' => chartLinearizedChristoffelPrincipal (I := I) g₀ α h i j j y') y +
              partialDeriv (E := E) k
                (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h i j j y') y))) 0 := by
      refine HasDerivAt.fun_sum (fun j _ => ?_)
      exact (hasDerivAt_partial_chartChristoffel (I := I) hfam j i k j hy).sub
        (hasDerivAt_partial_chartChristoffel (I := I) hfam k i j j hy)
    refine hdsum.congr_deriv ?_
    rw [chartRicciSecondOrderPart_def, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring

  have hFO : HasDerivAt
      (fun s : ℝ => chartRicciFirstOrderTerm (I := I) (gfam s) α i k y)
      (∑ j : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        (((chartLinearizedChristoffelPrincipal (I := I) g₀ α h j m j y +
              christoffelFirstOrderCorr (I := I) g₀ α h j m j y) *
            chartChristoffel (I := I) g₀ α i k m y +
          chartChristoffel (I := I) g₀ α j m j y *
            (chartLinearizedChristoffelPrincipal (I := I) g₀ α h i k m y +
              christoffelFirstOrderCorr (I := I) g₀ α h i k m y)) -
          ((chartLinearizedChristoffelPrincipal (I := I) g₀ α h k m j y +
              christoffelFirstOrderCorr (I := I) g₀ α h k m j y) *
            chartChristoffel (I := I) g₀ α i j m y +
          chartChristoffel (I := I) g₀ α k m j y *
            (chartLinearizedChristoffelPrincipal (I := I) g₀ α h i j m y +
              christoffelFirstOrderCorr (I := I) g₀ α h i j m y)))) 0 := by
    have heq : (fun s : ℝ => chartRicciFirstOrderTerm (I := I) (gfam s) α i k y) =
        (fun s : ℝ => ∑ j : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) (gfam s) α j m j y *
              chartChristoffel (I := I) (gfam s) α i k m y -
            chartChristoffel (I := I) (gfam s) α k m j y *
              chartChristoffel (I := I) (gfam s) α i j m y)) := by
      funext s; rw [chartRicciFirstOrderTerm]
    rw [heq]
    refine HasDerivAt.fun_sum (fun j _ => ?_)
    refine HasDerivAt.fun_sum (fun m _ => ?_)
    have hΓ1 := hasDerivAt_chartChristoffel (I := I) hfam j m j hy
    have hΓ2 := hasDerivAt_chartChristoffel (I := I) hfam i k m hy
    have hΓ3 := hasDerivAt_chartChristoffel (I := I) hfam k m j hy
    have hΓ4 := hasDerivAt_chartChristoffel (I := I) hfam i j m hy
    have hp1 := (hΓ1.mul hΓ2)
    have hp2 := (hΓ3.mul hΓ4)
    have hsub := hp1.sub hp2

    rw [show chartChristoffel (I := I) (gfam 0) α j m j y =
          chartChristoffel (I := I) g₀ α j m j y from by rw [hg0],
      show chartChristoffel (I := I) (gfam 0) α i k m y =
          chartChristoffel (I := I) g₀ α i k m y from by rw [hg0],
      show chartChristoffel (I := I) (gfam 0) α k m j y =
          chartChristoffel (I := I) g₀ α k m j y from by rw [hg0],
      show chartChristoffel (I := I) (gfam 0) α i j m y =
          chartChristoffel (I := I) g₀ α i j m y from by rw [hg0]] at hsub
    refine hsub.congr_deriv ?_
    ring

  have htotal := hSO.add hFO
  have heq : (fun s : ℝ => chartRicciTensor (I := I) (gfam s) α i k y) =
      (fun s : ℝ => chartRicciSecondOrderTerm (I := I) (gfam s) α i k y +
        chartRicciFirstOrderTerm (I := I) (gfam s) α i k y) := by
    funext s; rw [chartRicciTensor_eq_secondOrder_add_firstOrder]
  rw [heq]
  refine htotal.congr_deriv ?_
  rw [ricciDerivFirstOrderRemainder]
  ring

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma joint_contDiffAt_const_s_chartChristoffel
    (g_bg : SmoothRiemannianMetric I M) (α : M)
    (a b k : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartChristoffel (I := I) g_bg α a b k r.2) (0, y₀) := by
  classical
  have hcd : ContDiffOn ℝ ∞ (fun y => chartChristoffel (I := I) g_bg α a b k y)
      (interior (extChartAt I α).target) := by
    have heq : (fun y => chartChristoffel (I := I) g_bg α a b k y) =
        (fun y => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g_bg α k l y * gramBracket (I := I) g_bg α a b l y) := by
      funext y; rw [chartChristoffel_eq_sum_invGramOnE_bracket]
    rw [heq]
    refine contDiffOn_const.mul (ContDiffOn.sum (fun l _ => ?_))
    refine ContDiffOn.mul ((chartInvGramOnE_contDiffOn (I := I) g_bg α k l).mono interior_subset) ?_
    unfold gramBracket
    have hp : ∀ p₁ p₂ p₃ : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞ (partialDeriv (E := E) p₁ (chartGramOnE (I := I) g_bg α p₂ p₃))
          (interior (extChartAt I α).target) := by
      intro p₁ p₂ p₃
      have hcdg : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g_bg α p₂ p₃)
          (interior (extChartAt I α).target) :=
        (chartGramOnE_contDiffOn (I := I) g_bg α p₂ p₃).mono interior_subset
      have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (chartGramOnE (I := I) g_bg α p₂ p₃))
          (interior (extChartAt I α).target) :=
        hcdg.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
      unfold partialDeriv
      exact hfderiv.clm_apply contDiffOn_const
    exact ((hp a l b).add (hp b l a)).sub (hp l a b)
  have hcdat : ContDiffAt ℝ ∞ (fun y => chartChristoffel (I := I) g_bg α a b k y) y₀ :=
    hcd.contDiffAt (isOpen_interior.mem_nhds hy)
  have hcomp : (fun r : ℝ × E => chartChristoffel (I := I) g_bg α a b k r.2) =
      (fun y => chartChristoffel (I := I) g_bg α a b k y) ∘ (fun r : ℝ × E => r.2) := rfl
  rw [hcomp]
  exact hcdat.comp (0, y₀) contDiffAt_snd

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma joint_contDiffAt_chartDeTurckVFComp
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (g_bg : SmoothRiemannianMetric I M) (k : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k r.2) (0, y₀) := by
  have heq : (fun r : ℝ × E => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k r.2) =
      (fun r : ℝ × E => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (gfam r.1) α a b r.2 *
          (chartChristoffel (I := I) (gfam r.1) α a b k r.2 -
            chartChristoffel (I := I) g_bg α a b k r.2)) := by
    funext r; rw [chartDeTurckVFComp_def]
  rw [heq]
  refine ContDiffAt.sum (fun a _ => ?_)
  refine ContDiffAt.sum (fun b _ => ?_)
  refine (joint_contDiffAt_chartInvGramOnE (I := I) hfam a b hy).mul ?_
  exact (joint_contDiffAt_chartChristoffel (I := I) hfam a b k hy).sub
    (joint_contDiffAt_const_s_chartChristoffel (I := I) g_bg α a b k hy)

def deTurckVFFirstOrderCorr (g₀ g_bg : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g₀ α a p y * h p q y *
            chartInvGramOnE (I := I) g₀ α q b y)) *
        (chartChristoffel (I := I) g₀ α a b k y -
          chartChristoffel (I := I) g_bg α a b k y) +
      chartInvGramOnE (I := I) g₀ α a b y *
        christoffelFirstOrderCorr (I := I) g₀ α h a b k y)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma hasDerivAt_chartDeTurckVFComp
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (g_bg : SmoothRiemannianMetric I M) (k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    HasDerivAt (fun s : ℝ => chartDeTurckVFComp (I := I) (gfam s) g_bg α k y)
      (chartLinearizedDeTurckVFPrincipal (I := I) g₀ g_bg α h k y +
        deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y) 0 := by
  classical
  have hg0 : gfam 0 = g₀ := hfam.1
  have heq : (fun s : ℝ => chartDeTurckVFComp (I := I) (gfam s) g_bg α k y) =
      (fun s : ℝ => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (gfam s) α a b y *
          (chartChristoffel (I := I) (gfam s) α a b k y -
            chartChristoffel (I := I) g_bg α a b k y)) := by
    funext s; rw [chartDeTurckVFComp_def]
  rw [heq]
  have hd : HasDerivAt
      (fun s : ℝ => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (gfam s) α a b y *
          (chartChristoffel (I := I) (gfam s) α a b k y -
            chartChristoffel (I := I) g_bg α a b k y))
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g₀ α a p y * h p q y *
                chartInvGramOnE (I := I) g₀ α q b y)) *
            (chartChristoffel (I := I) g₀ α a b k y -
              chartChristoffel (I := I) g_bg α a b k y) +
          chartInvGramOnE (I := I) g₀ α a b y *
            (chartLinearizedChristoffelPrincipal (I := I) g₀ α h a b k y +
              christoffelFirstOrderCorr (I := I) g₀ α h a b k y))) 0 := by
    refine HasDerivAt.fun_sum (fun a _ => ?_)
    refine HasDerivAt.fun_sum (fun b _ => ?_)
    have hG := hasDerivAt_chartInvGramOnE (I := I) hfam a b hy
    have hΓ := hasDerivAt_chartChristoffel (I := I) hfam a b k hy
    have hΓbg : HasDerivAt (fun _ : ℝ => chartChristoffel (I := I) g_bg α a b k y) 0 0 :=
      hasDerivAt_const 0 _
    have hdiff := hΓ.sub hΓbg
    have hprod := hG.mul hdiff
    refine hprod.congr_deriv ?_
    simp only [Pi.sub_apply, hg0]
    ring
  refine hd.congr_deriv ?_
  rw [chartLinearizedDeTurckVFPrincipal_def, deTurckVFFirstOrderCorr, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma deTurckVFFirstOrderCorr_differentiableAt
    {g₀ g_bg : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {k : Fin (Module.finrank ℝ E)} {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (fun y => deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y) y₀ := by
  classical
  unfold deTurckVFFirstOrderCorr
  refine DifferentiableAt.fun_sum (fun a _ => ?_)
  refine DifferentiableAt.fun_sum (fun b _ => ?_)
  refine DifferentiableAt.add (DifferentiableAt.mul ?_ ?_) ?_
  · refine DifferentiableAt.neg ?_
    refine DifferentiableAt.fun_sum (fun q _ => ?_)
    refine DifferentiableAt.fun_sum (fun p _ => ?_)
    exact ((chartInvGramOnE_differentiableAt_interior (I := I) g₀ α a p hy).mul
      (h.differentiableAt p q y₀)).mul
      (chartInvGramOnE_differentiableAt_interior (I := I) g₀ α q b hy)
  · exact (chartChristoffel_differentiableAt (I := I) g₀ α a b k hy).sub
      (chartChristoffel_differentiableAt (I := I) g_bg α a b k hy)
  · exact (chartInvGramOnE_differentiableAt_interior (I := I) g₀ α a b hy).mul
      (christoffelFirstOrderCorr_differentiableAt (I := I) (g₀ := g₀) hy)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma hasDerivAt_partial_chartDeTurckVFComp
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (g_bg : SmoothRiemannianMetric I M) (m k : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    HasDerivAt
      (fun s : ℝ =>
        partialDeriv (E := E) m (fun y => chartDeTurckVFComp (I := I) (gfam s) g_bg α k y) y₀)
      (partialDeriv (E := E) m
          (fun y => chartLinearizedDeTurckVFPrincipal (I := I) g₀ g_bg α h k y) y₀ +
        partialDeriv (E := E) m
          (fun y => deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y) y₀) 0 := by
  classical
  have hderiv_eq : (fun y => deriv (fun s : ℝ =>
        chartDeTurckVFComp (I := I) (gfam s) g_bg α k y) 0) =ᶠ[nhds y₀]
      (fun y => chartLinearizedDeTurckVFPrincipal (I := I) g₀ g_bg α h k y +
        deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y) := by
    filter_upwards [isOpen_interior.mem_nhds hy] with y hy'
    exact (hasDerivAt_chartDeTurckVFComp (I := I) hfam g_bg k hy').deriv
  have hcomm := hasDerivAt_partialDeriv_comm
    (fun p : ℝ × E => chartDeTurckVFComp (I := I) (gfam p.1) g_bg α k p.2) m y₀
    (joint_contDiffAt_chartDeTurckVFComp (I := I) hfam g_bg k hy)
  have hrhs : partialDeriv (E := E) m
        (fun y => deriv (fun s : ℝ => chartDeTurckVFComp (I := I) (gfam s) g_bg α k y) 0) y₀ =
      partialDeriv (E := E) m
          (fun y => chartLinearizedDeTurckVFPrincipal (I := I) g₀ g_bg α h k y) y₀ +
        partialDeriv (E := E) m
          (fun y => deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y) y₀ := by
    unfold partialDeriv
    rw [Filter.EventuallyEq.fderiv_eq hderiv_eq]
    rw [show (fun y => chartLinearizedDeTurckVFPrincipal (I := I) g₀ g_bg α h k y +
          deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y) =
        (fun y => chartLinearizedDeTurckVFPrincipal (I := I) g₀ g_bg α h k y) +
          (fun y => deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y) from rfl]
    rw [fderiv_add]
    · rfl
    · exact chartLinearizedDeTurckVFPrincipal_differentiableAt (I := I) g₀ g_bg α h k hy
    · exact deTurckVFFirstOrderCorr_differentiableAt (I := I) (g₀ := g₀) (g_bg := g_bg) hy
  rw [hrhs] at hcomm
  exact hcomm

def lieDerivFirstOrderRemainder (g₀ g_bg : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (∑ k : Fin (Module.finrank ℝ E),
      ((chartLinearizedDeTurckVFPrincipal (I := I) g₀ g_bg α h k y +
            deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y) *
          partialDeriv (E := E) k (chartGramOnE (I := I) g₀ α i j) y +
        chartDeTurckVFComp (I := I) g₀ g_bg α k y * partialDeriv (E := E) k (h i j) y)) +
  (∑ k : Fin (Module.finrank ℝ E),
      (h k j y *
          partialDeriv (E := E) i (fun y' => chartDeTurckVFComp (I := I) g₀ g_bg α k y') y +
        chartGramOnE (I := I) g₀ α k j y *
          partialDeriv (E := E) i
            (fun y' => deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y') y)) +
  (∑ k : Fin (Module.finrank ℝ E),
      (h i k y *
          partialDeriv (E := E) j (fun y' => chartDeTurckVFComp (I := I) g₀ g_bg α k y') y +
        chartGramOnE (I := I) g₀ α i k y *
          partialDeriv (E := E) j
            (fun y' => deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y') y))

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma hasDerivAt_chartLieDeTurckComp
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (g_bg : SmoothRiemannianMetric I M) (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    HasDerivAt (fun s : ℝ => chartLieDeTurckComp (I := I) (gfam s) g_bg α i j y)
      (chartDeTurckCorrSecondOrderPart (I := I) g₀ g_bg α h i j y +
        lieDerivFirstOrderRemainder (I := I) g₀ g_bg α h i j y) 0 := by
  classical
  have hg0 : gfam 0 = g₀ := hfam.1
  have heq : (fun s : ℝ => chartLieDeTurckComp (I := I) (gfam s) g_bg α i j y) =
      (fun s : ℝ =>
        (∑ k : Fin (Module.finrank ℝ E),
            chartDeTurckVFComp (I := I) (gfam s) g_bg α k y *
              partialDeriv (E := E) k (chartGramOnE (I := I) (gfam s) α i j) y)
        + (∑ k : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) (gfam s) α k j y *
              partialDeriv (E := E) i
                (fun y' => chartDeTurckVFComp (I := I) (gfam s) g_bg α k y') y)
        + (∑ k : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) (gfam s) α i k y *
              partialDeriv (E := E) j
                (fun y' => chartDeTurckVFComp (I := I) (gfam s) g_bg α k y') y)) := by
    funext s; rw [chartLieDeTurckComp_def]
  rw [heq]

  have hT1 : HasDerivAt
      (fun s : ℝ => ∑ k : Fin (Module.finrank ℝ E),
        chartDeTurckVFComp (I := I) (gfam s) g_bg α k y *
          partialDeriv (E := E) k (chartGramOnE (I := I) (gfam s) α i j) y)
      (∑ k : Fin (Module.finrank ℝ E),
        ((chartLinearizedDeTurckVFPrincipal (I := I) g₀ g_bg α h k y +
              deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y) *
            partialDeriv (E := E) k (chartGramOnE (I := I) g₀ α i j) y +
          chartDeTurckVFComp (I := I) g₀ g_bg α k y * partialDeriv (E := E) k (h i j) y)) 0 := by
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    have hW := hasDerivAt_chartDeTurckVFComp (I := I) hfam g_bg k hy
    have hG := hasDerivAt_partial_chartGramOnE (I := I) hfam i j k hy
    have hprod := hW.mul hG
    simp only [hg0] at hprod
    exact hprod

  have hT2 : HasDerivAt
      (fun s : ℝ => ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) (gfam s) α k j y *
          partialDeriv (E := E) i (fun y' => chartDeTurckVFComp (I := I) (gfam s) g_bg α k y') y)
      ((∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g₀ α k j y *
            partialDeriv (E := E) i
              (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g₀ g_bg α h k y') y) +
        ∑ k : Fin (Module.finrank ℝ E),
          (h k j y *
              partialDeriv (E := E) i (fun y' => chartDeTurckVFComp (I := I) g₀ g_bg α k y') y +
            chartGramOnE (I := I) g₀ α k j y *
              partialDeriv (E := E) i
                (fun y' => deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y') y)) 0 := by
    rw [← Finset.sum_add_distrib]
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    have hG := hasDerivAt_chartGramOnE (I := I) hfam k j hy
    have hW := hasDerivAt_partial_chartDeTurckVFComp (I := I) hfam g_bg i k hy
    have hprod := hG.mul hW
    simp only [hg0] at hprod
    refine hprod.congr_deriv ?_
    ring

  have hT3 : HasDerivAt
      (fun s : ℝ => ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) (gfam s) α i k y *
          partialDeriv (E := E) j (fun y' => chartDeTurckVFComp (I := I) (gfam s) g_bg α k y') y)
      ((∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g₀ α i k y *
            partialDeriv (E := E) j
              (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g₀ g_bg α h k y') y) +
        ∑ k : Fin (Module.finrank ℝ E),
          (h i k y *
              partialDeriv (E := E) j (fun y' => chartDeTurckVFComp (I := I) g₀ g_bg α k y') y +
            chartGramOnE (I := I) g₀ α i k y *
              partialDeriv (E := E) j
                (fun y' => deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y') y)) 0 := by
    rw [← Finset.sum_add_distrib]
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    have hG := hasDerivAt_chartGramOnE (I := I) hfam i k hy
    have hW := hasDerivAt_partial_chartDeTurckVFComp (I := I) hfam g_bg j k hy
    have hprod := hG.mul hW
    simp only [hg0] at hprod
    refine hprod.congr_deriv ?_
    ring
  have htotal := (hT1.add hT2).add hT3
  refine htotal.congr_deriv ?_
  rw [chartDeTurckCorrSecondOrderPart_def, lieDerivFirstOrderRemainder]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma chartPushforwardFrameVec_eq_chartBasisVecFiber
    (α : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    DifferentialGeometry.PDE.RicciFlow.chartPushforwardFrameVec (I := I) α i x =
      chartBasisVecFiber (I := I) α i x := rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma chartFComponentOnE_deTurckRicciRHS_eq
    (g_bg g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
        (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg) g α i j y =
      chartDeTurckRicciRHS (I := I) g g_bg α i j y := by
  have hy_t : y ∈ (extChartAt I α).target := interior_subset hy
  set z : M := (extChartAt I α).symm y with hz_def
  have hz_src : z ∈ (extChartAt I α).source := (extChartAt I α).map_target hy_t
  have hz_base : z ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    symm_mem_baseSet_of_interior (I := I) hy
  have hyz : extChartAt I α z = y := (extChartAt I α).right_inv hy_t
  have hz_pre : z ∈ (extChartAt I α) ⁻¹' interior ((extChartAt I α).target : Set E) := by
    simp only [Set.mem_preimage, hyz]; exact hy
  have hz_good : z ∈ DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet (I := I) α :=
    ⟨⟨hz_src, hz_base⟩, hz_pre⟩
  rw [DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE]
  simp only [chartPushforwardFrameVec_eq_chartBasisVecFiber]
  rw [deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS (I := I) g g_bg α i j hz_good,
    hyz]

def metricFamilyDeTurckRicciFirstOrderRemainder
    (g₀ g_bg : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (-2 : ℝ) * ricciDerivFirstOrderRemainder (I := I) g₀ α h i j y +
    lieDerivFirstOrderRemainder (I := I) g₀ g_bg α h i j y

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hasDerivAt_chartFComponentOnE_deTurckRicciRHS
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {gfam : ℝ → SmoothRiemannianMetric I M}
    (hfam : IsMetricPerturbationFamily (I := I) g₀ α h gfam)
    (g_bg : SmoothRiemannianMetric I M) (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    HasDerivAt
      (fun s : ℝ => DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
        (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg) (gfam s) α i j y)
      (((-2 : ℝ) * chartRicciSecondOrderPart (I := I) g₀ α h i j y +
          chartDeTurckCorrSecondOrderPart (I := I) g₀ g_bg α h i j y) +
        metricFamilyDeTurckRicciFirstOrderRemainder (I := I) g₀ g_bg α h i j y) 0 := by
  have hcongr : (fun s : ℝ => DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
        (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg) (gfam s) α i j y) =
      (fun s : ℝ => chartDeTurckRicciRHS (I := I) (gfam s) g_bg α i j y) := by
    funext s
    exact chartFComponentOnE_deTurckRicciRHS_eq (I := I) g_bg (gfam s) α i j hy
  rw [hcongr]
  have hcomp : (fun s : ℝ => chartDeTurckRicciRHS (I := I) (gfam s) g_bg α i j y) =
      (fun s : ℝ => -2 * chartRicciTensor (I := I) (gfam s) α i j y +
        chartLieDeTurckComp (I := I) (gfam s) g_bg α i j y) := by
    funext s; rw [chartDeTurckRicciRHS_def]
  rw [hcomp]
  have hR := hasDerivAt_chartRicciTensor (I := I) hfam i j hy
  have hL := hasDerivAt_chartLieDeTurckComp (I := I) hfam g_bg i j hy
  have htotal := (hR.const_mul (-2 : ℝ)).add hL
  refine htotal.congr_deriv ?_
  rw [metricFamilyDeTurckRicciFirstOrderRemainder]
  ring

section FirstOrderVanish

variable {g₀ g_bg : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E} {y : E}
  (hval : ∀ a b, h a b y = 0)
  (hjet : ∀ p a b, partialDeriv (E := E) p (h a b) y = 0)

include hval hjet

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] hval in
private lemma chartLinearizedChristoffelPrincipal_vanish
    (a b k : Fin (Module.finrank ℝ E)) :
    chartLinearizedChristoffelPrincipal (I := I) g₀ α h a b k y = 0 := by
  classical
  rw [chartLinearizedChristoffelPrincipal_def]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun l _ => ?_))
  rw [hjet a l b, hjet b l a, hjet l a b]; ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] hjet in
private lemma christoffelFirstOrderCorr_vanish
    (a b k : Fin (Module.finrank ℝ E)) :
    christoffelFirstOrderCorr (I := I) g₀ α h a b k y = 0 := by
  classical
  rw [christoffelFirstOrderCorr]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun l _ => ?_))
  refine mul_eq_zero_of_left ?_ _
  rw [neg_eq_zero]
  refine Finset.sum_eq_zero (fun q _ => Finset.sum_eq_zero (fun p _ => ?_))
  rw [hval p q]; ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] hval in
private lemma chartLinearizedDeTurckVFPrincipal_vanish
    (k : Fin (Module.finrank ℝ E)) :
    chartLinearizedDeTurckVFPrincipal (I := I) g₀ g_bg α h k y = 0 := by
  classical
  rw [chartLinearizedDeTurckVFPrincipal_def]
  refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
  rw [chartLinearizedChristoffelPrincipal_vanish hjet a b k]; ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] hjet in
private lemma deTurckVFFirstOrderCorr_vanish
    (k : Fin (Module.finrank ℝ E)) :
    deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y = 0 := by
  classical
  rw [deTurckVFFirstOrderCorr]
  refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
  rw [christoffelFirstOrderCorr_vanish hval a b k]
  have hc : (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g₀ α a p y * h p q y *
        chartInvGramOnE (I := I) g₀ α q b y)) = 0 := by
    rw [neg_eq_zero]
    refine Finset.sum_eq_zero (fun q _ => Finset.sum_eq_zero (fun p _ => ?_))
    rw [hval p q]; ring
  rw [hc]; ring

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_invGram_h_invGram_vanish
    (hy : y ∈ interior (extChartAt I α).target)
    (p a b c d : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) p
      (fun y' => chartInvGramOnE (I := I) g₀ α a b y' * h b c y' *
        chartInvGramOnE (I := I) g₀ α c d y') y = 0 := by
  have hG1 := chartInvGramOnE_differentiableAt_interior (I := I) g₀ α a b hy
  have hG2 := chartInvGramOnE_differentiableAt_interior (I := I) g₀ α c d hy
  have hh := h.differentiableAt b c y
  rw [partialDeriv_mul (E := E)
        (fun y' => chartInvGramOnE (I := I) g₀ α a b y' * h b c y')
        (chartInvGramOnE (I := I) g₀ α c d) (hG1.mul hh) hG2,
    partialDeriv_mul (E := E) (chartInvGramOnE (I := I) g₀ α a b) (h b c) hG1 hh]
  rw [hval b c, hjet p b c]
  ring

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma christoffelCorrCoeff_partial_vanish
    (hy : y ∈ interior (extChartAt I α).target)
    (p a l : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) p
      (fun y' => -(∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₀ α a r y' * h r q y' *
          chartInvGramOnE (I := I) g₀ α q l y')) y = 0 := by
  classical
  rw [show (fun y' => -(∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₀ α a r y' * h r q y' *
          chartInvGramOnE (I := I) g₀ α q l y')) =
      (fun y' => (-1 : ℝ) * ∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₀ α a r y' * h r q y' *
          chartInvGramOnE (I := I) g₀ α q l y') from by funext y'; ring]
  have hdiff_summand : ∀ q r : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun y' => chartInvGramOnE (I := I) g₀ α a r y' * h r q y' *
        chartInvGramOnE (I := I) g₀ α q l y') y :=
    fun q r => ((chartInvGramOnE_differentiableAt_interior (I := I) g₀ α a r hy).mul
      (h.differentiableAt r q y)).mul
      (chartInvGramOnE_differentiableAt_interior (I := I) g₀ α q l hy)
  rw [partialDeriv_const_mul (E := E) (-1 : ℝ) _
        (DifferentiableAt.fun_sum (fun q _ => DifferentiableAt.fun_sum (fun r _ =>
          hdiff_summand q r)))]
  rw [partialDeriv_sum Finset.univ _ (fun q _ => DifferentiableAt.fun_sum (fun r _ =>
    hdiff_summand q r))]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun q _ => ?_))
  rw [partialDeriv_sum Finset.univ _ (fun r _ => hdiff_summand q r)]
  refine Finset.sum_eq_zero (fun r _ => ?_)
  exact partialDeriv_invGram_h_invGram_vanish hval hjet hy p a r q l

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_christoffelFirstOrderCorr_vanish
    (hy : y ∈ interior (extChartAt I α).target)
    (p a b k : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) p
      (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h a b k y') y = 0 := by
  classical
  have hcorr_eq : (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h a b k y') =
      (fun y' => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (-(∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₀ α k r y' * h r q y' *
              chartInvGramOnE (I := I) g₀ α q l y')) *
          gramBracket (I := I) g₀ α a b l y') := by
    funext y'; rw [christoffelFirstOrderCorr]
  rw [hcorr_eq]
  set C : Fin (Module.finrank ℝ E) → E → ℝ := fun l y' =>
    -(∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g₀ α k r y' * h r q y' *
        chartInvGramOnE (I := I) g₀ α q l y') with hC
  have hC_diff : ∀ l : Fin (Module.finrank ℝ E), DifferentiableAt ℝ (C l) y := by
    intro l
    rw [hC]
    refine DifferentiableAt.neg ?_
    refine DifferentiableAt.fun_sum (fun q _ => DifferentiableAt.fun_sum (fun r _ => ?_))
    exact ((chartInvGramOnE_differentiableAt_interior (I := I) g₀ α k r hy).mul
      (h.differentiableAt r q y)).mul
      (chartInvGramOnE_differentiableAt_interior (I := I) g₀ α q l hy)
  have hB_diff : ∀ l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (gramBracket (I := I) g₀ α a b l) y := by
    intro l
    unfold gramBracket
    exact ((partial_chartGramOnE_differentiableAt (I := I) g₀ α a l b hy).add
      (partial_chartGramOnE_differentiableAt (I := I) g₀ α b l a hy)).sub
      (partial_chartGramOnE_differentiableAt (I := I) g₀ α l a b hy)
  rw [partialDeriv_const_mul (E := E) (1 / 2 : ℝ)
        (fun y' => ∑ l : Fin (Module.finrank ℝ E), C l y' * gramBracket (I := I) g₀ α a b l y')
        (DifferentiableAt.fun_sum (fun l _ => (hC_diff l).mul (hB_diff l)))]
  refine mul_eq_zero_of_right _ ?_
  rw [partialDeriv_sum Finset.univ (fun l y' => C l y' * gramBracket (I := I) g₀ α a b l y')
    (fun l _ => (hC_diff l).mul (hB_diff l))]
  refine Finset.sum_eq_zero (fun l _ => ?_)
  rw [partialDeriv_mul (E := E) (C l) (gramBracket (I := I) g₀ α a b l) (hC_diff l) (hB_diff l)]
  have hCval : C l y = 0 := by
    rw [hC]; rw [neg_eq_zero]
    refine Finset.sum_eq_zero (fun q _ => Finset.sum_eq_zero (fun r _ => ?_))
    rw [hval r q]; ring
  have hCpartial : partialDeriv (E := E) p (C l) y = 0 := by
    rw [hC]; exact christoffelCorrCoeff_partial_vanish hval hjet hy p k l
  rw [hCval, hCpartial]; ring

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_deTurckVFFirstOrderCorr_vanish
    (hy : y ∈ interior (extChartAt I α).target)
    (p k : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) p
      (fun y' => deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y') y = 0 := by
  classical
  have hcorr_eq : (fun y' => deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y') =
      (fun y' => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((-(∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g₀ α a r y' * h r q y' *
                chartInvGramOnE (I := I) g₀ α q b y')) *
            (chartChristoffel (I := I) g₀ α a b k y' -
              chartChristoffel (I := I) g_bg α a b k y') +
          chartInvGramOnE (I := I) g₀ α a b y' *
            christoffelFirstOrderCorr (I := I) g₀ α h a b k y')) := by
    funext y'; rw [deTurckVFFirstOrderCorr]
  rw [hcorr_eq]

  set C : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ := fun a b y' =>
    -(∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g₀ α a r y' * h r q y' *
        chartInvGramOnE (I := I) g₀ α q b y') with hC
  have hC_diff : ∀ a b : Fin (Module.finrank ℝ E), DifferentiableAt ℝ (C a b) y := by
    intro a b; rw [hC]
    refine DifferentiableAt.neg ?_
    refine DifferentiableAt.fun_sum (fun q _ => DifferentiableAt.fun_sum (fun r _ => ?_))
    exact ((chartInvGramOnE_differentiableAt_interior (I := I) g₀ α a r hy).mul
      (h.differentiableAt r q y)).mul
      (chartInvGramOnE_differentiableAt_interior (I := I) g₀ α q b hy)
  have hΓdiff : ∀ a b : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun y' => chartChristoffel (I := I) g₀ α a b k y' -
        chartChristoffel (I := I) g_bg α a b k y') y :=
    fun a b => (chartChristoffel_differentiableAt (I := I) g₀ α a b k hy).sub
      (chartChristoffel_differentiableAt (I := I) g_bg α a b k hy)
  have hcorr_diff : ∀ a b : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h a b k y') y :=
    fun a b => christoffelFirstOrderCorr_differentiableAt (I := I) (g₀ := g₀) hy
  have hsummand_diff : ∀ a b : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun y' =>
        C a b y' * (chartChristoffel (I := I) g₀ α a b k y' -
            chartChristoffel (I := I) g_bg α a b k y') +
          chartInvGramOnE (I := I) g₀ α a b y' *
            christoffelFirstOrderCorr (I := I) g₀ α h a b k y') y :=
    fun a b => ((hC_diff a b).mul (hΓdiff a b)).add
      ((chartInvGramOnE_differentiableAt_interior (I := I) g₀ α a b hy).mul (hcorr_diff a b))
  rw [partialDeriv_sum Finset.univ _ (fun a _ => DifferentiableAt.fun_sum (fun b _ =>
    hsummand_diff a b))]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  rw [partialDeriv_sum Finset.univ _ (fun b _ => hsummand_diff a b)]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  rw [partialDeriv_add (E := E)
        (fun y' => C a b y' * (chartChristoffel (I := I) g₀ α a b k y' -
          chartChristoffel (I := I) g_bg α a b k y'))
        (fun y' => chartInvGramOnE (I := I) g₀ α a b y' *
          christoffelFirstOrderCorr (I := I) g₀ α h a b k y')
        ((hC_diff a b).mul (hΓdiff a b))
        ((chartInvGramOnE_differentiableAt_interior (I := I) g₀ α a b hy).mul (hcorr_diff a b))]
  rw [partialDeriv_mul (E := E) (C a b)
    (fun y' => chartChristoffel (I := I) g₀ α a b k y' -
      chartChristoffel (I := I) g_bg α a b k y') (hC_diff a b) (hΓdiff a b)]
  rw [partialDeriv_mul (E := E) (chartInvGramOnE (I := I) g₀ α a b)
    (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h a b k y')
    (chartInvGramOnE_differentiableAt_interior (I := I) g₀ α a b hy) (hcorr_diff a b)]

  have hCval : C a b y = 0 := by
    rw [hC, neg_eq_zero]
    refine Finset.sum_eq_zero (fun q _ => Finset.sum_eq_zero (fun r _ => ?_))
    rw [hval r q]; ring
  have hCpartial : partialDeriv (E := E) p (C a b) y = 0 := by
    rw [hC]; exact christoffelCorrCoeff_partial_vanish hval hjet hy p a b
  have hcorrval : christoffelFirstOrderCorr (I := I) g₀ α h a b k y = 0 :=
    christoffelFirstOrderCorr_vanish hval a b k
  have hcorrpartial : partialDeriv (E := E) p
      (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h a b k y') y = 0 :=
    partialDeriv_christoffelFirstOrderCorr_vanish hval hjet hy p a b k
  rw [hCval, hCpartial, hcorrval, hcorrpartial]; ring

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma ricciDerivFirstOrderRemainder_vanish
    (hy : y ∈ interior (extChartAt I α).target)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciDerivFirstOrderRemainder (I := I) g₀ α h i k y = 0 := by
  classical
  rw [ricciDerivFirstOrderRemainder]
  have h1 : (∑ j : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) j
          (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h i k j y') y -
        partialDeriv (E := E) k
          (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h i j j y') y)) = 0 := by
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [partialDeriv_christoffelFirstOrderCorr_vanish hval hjet hy j i k j,
      partialDeriv_christoffelFirstOrderCorr_vanish hval hjet hy k i j j]
    ring
  have h2 : (∑ j : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
      (((chartLinearizedChristoffelPrincipal (I := I) g₀ α h j m j y +
            christoffelFirstOrderCorr (I := I) g₀ α h j m j y) *
          chartChristoffel (I := I) g₀ α i k m y +
        chartChristoffel (I := I) g₀ α j m j y *
          (chartLinearizedChristoffelPrincipal (I := I) g₀ α h i k m y +
            christoffelFirstOrderCorr (I := I) g₀ α h i k m y)) -
        ((chartLinearizedChristoffelPrincipal (I := I) g₀ α h k m j y +
            christoffelFirstOrderCorr (I := I) g₀ α h k m j y) *
          chartChristoffel (I := I) g₀ α i j m y +
        chartChristoffel (I := I) g₀ α k m j y *
          (chartLinearizedChristoffelPrincipal (I := I) g₀ α h i j m y +
            christoffelFirstOrderCorr (I := I) g₀ α h i j m y)))) = 0 := by
    refine Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun m _ => ?_))
    rw [chartLinearizedChristoffelPrincipal_vanish hjet j m j,
      christoffelFirstOrderCorr_vanish hval j m j,
      chartLinearizedChristoffelPrincipal_vanish hjet i k m,
      christoffelFirstOrderCorr_vanish hval i k m,
      chartLinearizedChristoffelPrincipal_vanish hjet k m j,
      christoffelFirstOrderCorr_vanish hval k m j,
      chartLinearizedChristoffelPrincipal_vanish hjet i j m,
      christoffelFirstOrderCorr_vanish hval i j m]
    ring
  rw [h1, h2]; ring

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieDerivFirstOrderRemainder_vanish
    (hy : y ∈ interior (extChartAt I α).target)
    (i j : Fin (Module.finrank ℝ E)) :
    lieDerivFirstOrderRemainder (I := I) g₀ g_bg α h i j y = 0 := by
  classical
  rw [lieDerivFirstOrderRemainder]
  have h1 : (∑ k : Fin (Module.finrank ℝ E),
      ((chartLinearizedDeTurckVFPrincipal (I := I) g₀ g_bg α h k y +
            deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y) *
          partialDeriv (E := E) k (chartGramOnE (I := I) g₀ α i j) y +
        chartDeTurckVFComp (I := I) g₀ g_bg α k y * partialDeriv (E := E) k (h i j) y)) = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [chartLinearizedDeTurckVFPrincipal_vanish hjet k,
      deTurckVFFirstOrderCorr_vanish hval k, hjet k i j]
    ring
  have h2 : (∑ k : Fin (Module.finrank ℝ E),
      (h k j y *
          partialDeriv (E := E) i (fun y' => chartDeTurckVFComp (I := I) g₀ g_bg α k y') y +
        chartGramOnE (I := I) g₀ α k j y *
          partialDeriv (E := E) i
            (fun y' => deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y') y)) = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [hval k j, partialDeriv_deTurckVFFirstOrderCorr_vanish hval hjet hy i k]
    ring
  have h3 : (∑ k : Fin (Module.finrank ℝ E),
      (h i k y *
          partialDeriv (E := E) j (fun y' => chartDeTurckVFComp (I := I) g₀ g_bg α k y') y +
        chartGramOnE (I := I) g₀ α i k y *
          partialDeriv (E := E) j
            (fun y' => deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y') y)) = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [hval i k, partialDeriv_deTurckVFFirstOrderCorr_vanish hval hjet hy j k]
    ring
  rw [h1, h2, h3]; ring

end FirstOrderVanish

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricFamilyDeTurckRicciFirstOrderRemainder_vanish
    {g₀ g_bg : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E} {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (hval : ∀ a b, h a b y = 0)
    (hjet : ∀ p a b, partialDeriv (E := E) p (h a b) y = 0)
    (i j : Fin (Module.finrank ℝ E)) :
    metricFamilyDeTurckRicciFirstOrderRemainder (I := I) g₀ g_bg α h i j y = 0 := by
  rw [metricFamilyDeTurckRicciFirstOrderRemainder,
    ricciDerivFirstOrderRemainder_vanish hval hjet hy i j,
    lieDerivFirstOrderRemainder_vanish hval hjet hy i j]
  ring

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry

end
