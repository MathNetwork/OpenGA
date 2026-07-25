import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamChartRicciDeriv
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.LieDeTurckRemainderOrderSplit


noncomputable section

set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1600000

open Set Function MeasureTheory Bundle
open scoped Topology Manifold BigOperators ContDiff

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] in
theorem hasDerivAt_realizedFam_chartLieDeTurckComp (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    HasDerivAt
      (fun s : ℝ =>
        chartLieDeTurckComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j y)
      (deriv (fun s : ℝ =>
        chartLieDeTurckComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j y) s₀) s₀ := by
  have hG := realizedFam_genJointGram (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hjoint : ContDiffAt ℝ ∞
      (fun r : ℝ × E =>
        chartLieDeTurckComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' r.1) g_bg x i j r.2)
      (s₀, y) :=
    gen_joint_chartLieDeTurckComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ') x hG g_bg i j hs₀ hy
  have hcomp : (fun s : ℝ =>
        chartLieDeTurckComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j y) =
      (fun r : ℝ × E =>
        chartLieDeTurckComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' r.1) g_bg x i j r.2)
        ∘ (fun s : ℝ => (s, y)) := by funext s; rfl
  rw [hcomp]
  exact ((hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)).differentiableAt
    (by simp)).hasDerivAt

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma hasDerivAt_fderiv_comm_at' (Φ : ℝ × E → ℝ) (s₀ : ℝ) (y₀ : E) (v : E)
    (hΦ : ContDiffAt ℝ ∞ Φ (s₀, y₀)) :
    HasDerivAt
      (fun s => fderiv ℝ (fun y => Φ (s, y)) y₀ v)
      (fderiv ℝ (fun y => deriv (fun s => Φ (s, y)) s₀) y₀ v)
      s₀ := by
  have hΦ_dfderiv : ContDiffAt ℝ ∞ (fderiv ℝ Φ) (s₀, y₀) := hΦ.fderiv_right (by simp)
  have get_diff_nhd : ∀ (p₀ : ℝ × E), ContDiffAt ℝ ∞ Φ p₀ →
      ∀ᶠ p : ℝ × E in nhds p₀, DifferentiableAt ℝ Φ p := fun p₀ hp => by
    obtain ⟨f', u, hu, _, hfu⟩ :=
      contDiffAt_one_iff.mp (hp.of_le (by exact_mod_cast le_top : (1 : WithTop ℕ∞) ≤ ∞))
    exact Filter.eventually_of_mem hu fun p hp => (hfu p hp).differentiableAt
  have hΦ_s : ∀ᶠ s in nhds s₀, DifferentiableAt ℝ Φ (s, y₀) :=
    (continuous_id.prodMk (continuous_const (y := y₀))).continuousAt (get_diff_nhd _ hΦ)
  have hΦ_y : ∀ᶠ y : E in nhds y₀, DifferentiableAt ℝ Φ (s₀, y) :=
    (continuous_const (y := s₀) |>.prodMk continuous_id).continuousAt (get_diff_nhd _ hΦ)
  have lhs_eq : (fun s => fderiv ℝ (fun y => Φ (s, y)) y₀ v) =ᶠ[nhds s₀]
      (fun s => fderiv ℝ Φ (s, y₀) (0, v)) := by
    filter_upwards [hΦ_s] with s hs
    have h : HasFDerivAt (fun y => Φ (s, y))
        ((fderiv ℝ Φ (s, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ E)) y₀ :=
      hs.hasFDerivAt.comp y₀ (hasFDerivAt_prodMk_right s y₀)
    rw [h.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  have h_fderiv_s : HasFDerivAt (fun s : ℝ => fderiv ℝ Φ (s, y₀))
      ((fderiv ℝ (fderiv ℝ Φ) (s₀, y₀)).comp (ContinuousLinearMap.inl ℝ ℝ E)) s₀ :=
    (hΦ_dfderiv.differentiableAt (by norm_num)).hasFDerivAt.comp s₀
      (hasFDerivAt_prodMk_left s₀ y₀)
  have h_sv : HasDerivAt (fun s => fderiv ℝ Φ (s, y₀) (0, v))
      (fderiv ℝ (fderiv ℝ Φ) (s₀, y₀) (1, 0) (0, v)) s₀ := by
    have h_d : HasDerivAt (fun s : ℝ => fderiv ℝ Φ (s, y₀))
        (fderiv ℝ (fderiv ℝ Φ) (s₀, y₀) (1, 0)) s₀ := by
      simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
        using h_fderiv_s.hasDerivAt
    simpa [map_zero] using h_d.clm_apply (hasDerivAt_const s₀ ((0 : ℝ), v))
  have hsymm : IsSymmSndFDerivAt ℝ Φ (s₀, y₀) :=
    hΦ.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)
  have h_sv' : HasDerivAt (fun s => fderiv ℝ Φ (s, y₀) (0, v))
      (fderiv ℝ (fderiv ℝ Φ) (s₀, y₀) (0, v) (1, 0)) s₀ := by
    rwa [hsymm ((1 : ℝ), (0 : E)) ((0 : ℝ), v)] at h_sv
  have rhs_eq : fderiv ℝ (fun y => deriv (fun s => Φ (s, y)) s₀) y₀ v =
      fderiv ℝ (fderiv ℝ Φ) (s₀, y₀) (0, v) (1, 0) := by
    have h_eq : (fun y => deriv (fun s => Φ (s, y)) s₀) =ᶠ[nhds y₀]
        (fun y => fderiv ℝ Φ (s₀, y) (1, 0)) := by
      filter_upwards [hΦ_y] with y hy
      have := hy.hasFDerivAt.comp_hasDerivAt (s₀ : ℝ)
        (hasFDerivAt_prodMk_left s₀ y).hasDerivAt
      exact this.deriv
    rw [Filter.EventuallyEq.fderiv_eq h_eq]
    have h_chain : HasFDerivAt (fun y => fderiv ℝ Φ (s₀, y) ((1 : ℝ), (0 : E)))
        ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : E))).comp
          ((fderiv ℝ (fderiv ℝ Φ) (s₀, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ E))) y₀ :=
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : E))).hasFDerivAt.comp y₀
        ((hΦ_dfderiv.differentiableAt (by norm_num)).hasFDerivAt.comp y₀
          (hasFDerivAt_prodMk_right s₀ y₀))
    simp [h_chain.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
          ContinuousLinearMap.inr_apply]
  rw [rhs_eq]
  exact h_sv'.congr_of_eventuallyEq lhs_eq

omit [NeZero (Module.finrank ℝ E)] in
private lemma hasDerivAt_partialDeriv_comm_at'
    (Φ : ℝ × E → ℝ) (p : Fin (Module.finrank ℝ E)) (s₀ : ℝ) (y₀ : E)
    (hΦ : ContDiffAt ℝ ∞ Φ (s₀, y₀)) :
    HasDerivAt
      (fun s => partialDeriv (E := E) p (fun y => Φ (s, y)) y₀)
      (partialDeriv (E := E) p (fun y => deriv (fun s => Φ (s, y)) s₀) y₀) s₀ := by
  unfold partialDeriv
  exact hasDerivAt_fderiv_comm_at' Φ s₀ y₀ (chartModelBasis E p) hΦ

omit [CompactSpace M] in
theorem hasDerivAt_realizedFam_chartDeTurckVFComp (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (x : M) (k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    HasDerivAt
      (fun s : ℝ =>
        chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x k y)
      (deTurckVFDerivRaw (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) g_bg x
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) k y) s₀ := by
  classical
  have heq : (fun s : ℝ =>
        chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x k y) =
      (fun s : ℝ => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b y *
          (chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b k y -
            chartChristoffel (I := I) g_bg x a b k y)) := by
    funext s; rw [chartDeTurckVFComp_def]
  rw [heq]
  have hd : HasDerivAt
      (fun s : ℝ => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b y *
          (chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b k y -
            chartChristoffel (I := I) g_bg x a b k y))
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x a p y *
                realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q y *
                chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x q b y)) *
            (chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x a b k y -
              chartChristoffel (I := I) g_bg x a b k y) +
          chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x a b y *
            ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
              ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
                    chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k p y *
                      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q y *
                      chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x q l y)) *
                  gramBracket (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x a b l y +
                chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k l y *
                  (partialDeriv (E := E) a
                      (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l b) y +
                    partialDeriv (E := E) b
                      (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l a) y -
                    partialDeriv (E := E) l
                      (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) y)))))
      s₀ := by
    refine HasDerivAt.fun_sum (fun a _ => ?_)
    refine HasDerivAt.fun_sum (fun b _ => ?_)
    have hG := hasDerivAt_realizedFam_chartInvGramOnE (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x a b hy hs₀
    have hΓ := hasDerivAt_realizedFam_chartChristoffel (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x a b k hy hs₀
    have hΓbg : HasDerivAt (fun _ : ℝ => chartChristoffel (I := I) g_bg x a b k y) 0 s₀ :=
      hasDerivAt_const s₀ _
    have hprod := hG.mul (hΓ.sub hΓbg)
    refine hprod.congr_deriv ?_
    simp only [Pi.sub_apply]
    ring
  refine hd.congr_deriv ?_
  rw [deTurckVFDerivRaw, chartLinearizedDeTurckVFPrincipalRaw, deTurckVFFirstOrderCorrRaw,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [chartLinearizedChristoffelPrincipalRaw, christoffelFirstOrderCorrRaw,
    Finset.sum_add_distrib]
  ring

omit [CompactSpace M] in
theorem hasDerivAt_realizedFam_partial_chartDeTurckVFComp (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (x : M) (m k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    HasDerivAt
      (fun s : ℝ => partialDeriv (E := E) m
        (fun y' => chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x k y') y)
      (partialDeriv (E := E) m
        (deTurckVFDerivRaw (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) g_bg x
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) k) y) s₀ := by
  have hG := realizedFam_genJointGram (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hjoint := gen_joint_chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ')
    x hG g_bg k hs₀ hy
  have hcomm := hasDerivAt_partialDeriv_comm_at'
    (fun r : ℝ × E =>
      chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' r.1) g_bg x k r.2)
    m s₀ y hjoint
  have hderiv_eq : (fun y' => deriv (fun s : ℝ =>
        chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x k y') s₀)
      =ᶠ[nhds y]
      (deTurckVFDerivRaw (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) g_bg x
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) k) := by
    filter_upwards [isOpen_interior.mem_nhds hy] with y' hy'
    exact (hasDerivAt_realizedFam_chartDeTurckVFComp (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      g_bg x k hy' hs₀).deriv
  have hval : partialDeriv (E := E) m
      (fun y' => deriv (fun s : ℝ =>
        chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x k y') s₀) y =
      partialDeriv (E := E) m
        (deTurckVFDerivRaw (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) g_bg x
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) k) y := by
    unfold partialDeriv
    rw [Filter.EventuallyEq.fderiv_eq hderiv_eq]
  exact hcomm.congr_deriv hval

def lieDeTurckChartSlope (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E))
    (s₀ : ℝ) (y : E) : ℝ :=
  lieDeTurckSlopeExprRaw (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) g_bg x
    (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j y

omit [CompactSpace M] in
theorem hasDerivAt_realizedFam_chartLieDeTurckComp_chartSlope (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    HasDerivAt
      (fun s : ℝ =>
        chartLieDeTurckComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j y)
      (lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg x i j s₀ y) s₀ := by
  classical
  have heq : (fun s : ℝ =>
        chartLieDeTurckComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j y) =
      (fun s : ℝ =>
        (∑ k : Fin (Module.finrank ℝ E),
            chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x k y *
              partialDeriv (E := E) k
                (chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j) y)
        + (∑ k : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k j y *
              partialDeriv (E := E) i
                (fun y' =>
                  chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x k y') y)
        + (∑ k : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k y *
              partialDeriv (E := E) j
                (fun y' =>
                  chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x k y') y)) := by
    funext s; rw [chartLieDeTurckComp_def]
  rw [heq]
  have hT1 : HasDerivAt
      (fun s : ℝ => ∑ k : Fin (Module.finrank ℝ E),
        chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x k y *
          partialDeriv (E := E) k
            (chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j) y)
      (∑ k : Fin (Module.finrank ℝ E),
        (deTurckVFDerivRaw (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) g_bg x
            (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) k y *
            partialDeriv (E := E) k
              (chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i j) y +
          chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) g_bg x k y *
            partialDeriv (E := E) k
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j) y)) s₀ := by
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    have hW := hasDerivAt_realizedFam_chartDeTurckVFComp (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      g_bg x k hy hs₀
    have hGr := hasDerivAt_realizedFam_partial_chartGramOnE (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x i j k hy hs₀
    exact hW.mul hGr
  have hT2 : HasDerivAt
      (fun s : ℝ => ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k j y *
          partialDeriv (E := E) i
            (fun y' =>
              chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x k y') y)
      (∑ k : Fin (Module.finrank ℝ E),
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x k j y *
            partialDeriv (E := E) i
              (fun y' =>
                chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) g_bg x k y') y +
          chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k j y *
            partialDeriv (E := E) i
              (deTurckVFDerivRaw (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) k) y)) s₀ := by
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    have hGr := hasDerivAt_realizedFam_chartGramOnE (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x k j y hs₀
    have hW := hasDerivAt_realizedFam_partial_chartDeTurckVFComp (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' g_bg x i k hy hs₀
    exact hGr.mul hW
  have hT3 : HasDerivAt
      (fun s : ℝ => ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k y *
          partialDeriv (E := E) j
            (fun y' =>
              chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x k y') y)
      (∑ k : Fin (Module.finrank ℝ E),
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k y *
            partialDeriv (E := E) j
              (fun y' =>
                chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) g_bg x k y') y +
          chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i k y *
            partialDeriv (E := E) j
              (deTurckVFDerivRaw (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) k) y)) s₀ := by
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    have hGr := hasDerivAt_realizedFam_chartGramOnE (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x i k y hs₀
    have hW := hasDerivAt_realizedFam_partial_chartDeTurckVFComp (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' g_bg x j k hy hs₀
    exact hGr.mul hW
  have htotal := (hT1.add hT2).add hT3
  refine htotal.congr_deriv ?_
  rw [lieDeTurckChartSlope, lieDeTurckSlopeExprRaw]

omit [CompactSpace M] in
theorem deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun s : ℝ =>
        chartLieDeTurckComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j
          (extChartAt I x x)) s₀ =
      lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg x i j s₀
        (extChartAt I x x) := by
  have hmem : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt ⟨hs₀.1.le, hs₀.2.le⟩
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  exact (hasDerivAt_realizedFam_chartLieDeTurckComp_chartSlope (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' g_bg x i j hy hmem).deriv

omit [CompactSpace M] in
private lemma realizedGramDeriv_differentiableAt' (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (p q : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) :
    DifferentiableAt ℝ (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q) y := by
  have h1 : DifferentiableAt ℝ
      (chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x p q) y :=
    (((chartGramOnE_contDiffOn (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x p q).mono
      interior_subset).contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)
  have h2 : DifferentiableAt ℝ
      (chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x p q) y :=
    (((chartGramOnE_contDiffOn (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x p q).mono
      interior_subset).contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)
  unfold realizedGramDeriv
  exact h1.sub h2

omit [CompactSpace M] in
private lemma partial_realizedGramDeriv_differentiableAt' (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m p q : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E)
        m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q)) y := by
  have hcd : ContDiffOn ℝ ∞ (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q)
      (extChartAt I x).target := by
    unfold realizedGramDeriv
    exact (chartGramOnE_contDiffOn (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x p q).sub
      (chartGramOnE_contDiffOn (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x p q)
  have hcd_int : ContDiffOn ℝ ∞ (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q)
      (interior (extChartAt I x).target) := hcd.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞
      (fderiv ℝ (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q))
      (interior (extChartAt I x).target) :=
    hcd_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hpd : ContDiffOn ℝ ∞
      (partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q))
      (interior (extChartAt I x).target) := by
    unfold partialDeriv
    exact hfderiv.clm_apply contDiffOn_const
  exact (hpd.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

omit [CompactSpace M] in
theorem lieDeTurckChartSlope_eq_orderSplit (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E))
    (s₀ : ℝ) {y : E} (hy : y ∈ interior (extChartAt I x).target) :
    lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg x i j s₀ y =
      chartDeTurckCorrPrincipalSymbolExprRaw (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s₀) g_bg x
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j y +
        lieDeTurckOrder1Raw (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) g_bg x
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j y +
        order0PartRaw (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) g_bg x
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j y := by
  rw [lieDeTurckChartSlope]
  exact lieDeTurckSlopeExprRaw_eq_orderSplit (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ' s₀) g_bg x
    (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j hy
    (fun p q => realizedGramDeriv_differentiableAt' (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x p q hy)
    (fun m p q => partial_realizedGramDeriv_differentiableAt' (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x m p q hy)

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry

end
