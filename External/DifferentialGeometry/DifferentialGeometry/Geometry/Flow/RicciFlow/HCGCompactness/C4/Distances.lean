import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.ApproxIsometryDefs
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false









namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold
open scoped Manifold ContDiff ENNReal

section RiemannianNorm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace











theorem edist_le_of_path_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [TopologicalSpace N] [ChartedSpace H N] [PseudoEMetricSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N]
    (F : M -> N) {K : ENNReal} (hK0 : K ≠ 0) (hKtop : K ≠ ⊤)
    (hpath :
      forall {x y : M}, forall γ : Path x y, CMDiff 1 γ ->
        exists η : Path (F x) (F y), CMDiff 1 η /\
          (∫⁻ t, ‖mfderiv% η t 1‖ₑ) <=
            K * (∫⁻ t, ‖mfderiv% γ t 1‖ₑ))
    (x y : M) :
    edist (F x) (F y) <= K * edist x y := by
  rw [IsRiemannianManifold.out (I := I) (F x) (F y)]
  rw [IsRiemannianManifold.out (I := I) x y]
  conv_rhs => rw [riemannianEDist]
  rw [ENNReal.mul_iInf_of_ne hK0 hKtop]
  refine le_iInf ?_
  intro γ
  rw [ENNReal.mul_iInf_of_ne hK0 hKtop]
  refine le_iInf ?_
  intro hγ
  rcases hpath γ hγ with ⟨η, hη, hlen⟩
  have htarget :
      riemannianEDist I (F x) (F y) <=
        ∫⁻ t, ‖mfderiv% η t 1‖ₑ := by
      rw [riemannianEDist]
      exact (iInf_le _ η).trans (iInf_le _ hη)
  exact htarget.trans hlen



theorem pathComp_tangent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [TopologicalSpace N] [ChartedSpace H N] [PseudoEMetricSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N]
    (F : M -> N) {A : ENNReal} (hA_ne_top : A ≠ ⊤)
    (hspeed :
      forall {x y : M}, forall γ : Path x y, CMDiff 1 γ ->
        exists η : Path (F x) (F y), CMDiff 1 η /\
          forall t : Set.Icc (0 : Real) 1,
            ‖mfderiv% η t 1‖ₑ <= A * ‖mfderiv% γ t 1‖ₑ) :
    forall {x y : M}, forall γ : Path x y, CMDiff 1 γ ->
        exists η : Path (F x) (F y), CMDiff 1 η /\
          (∫⁻ t, ‖mfderiv% η t 1‖ₑ) <=
            A * (∫⁻ t, ‖mfderiv% γ t 1‖ₑ) := by
  intro x y γ hγ
  rcases hspeed γ hγ with ⟨η, hη, hη_speed⟩
  refine ⟨η, hη, ?_⟩
  calc
    (∫⁻ t, ‖mfderiv% η t 1‖ₑ)
        <= ∫⁻ t, A * ‖mfderiv% γ t 1‖ₑ :=
          MeasureTheory.lintegral_mono hη_speed
    _ = A * (∫⁻ t, ‖mfderiv% γ t 1‖ₑ) := by
          rw [MeasureTheory.lintegral_const_mul' A _ hA_ne_top]



theorem dist_le_of_path_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [PseudoMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [TopologicalSpace N] [ChartedSpace H N] [PseudoMetricSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N]
    (F : M -> N) {eps : Real} (heps : 0 < 1 + eps)
    (hpath :
      forall {x y : M}, forall γ : Path x y, CMDiff 1 γ ->
        exists η : Path (F x) (F y), CMDiff 1 η /\
          (∫⁻ t, ‖mfderiv% η t 1‖ₑ) <=
            ENNReal.ofReal (Real.sqrt (1 + eps)) *
              (∫⁻ t, ‖mfderiv% γ t 1‖ₑ))
    (x y : M) :
    dist (F x) (F y) <= Real.sqrt (1 + eps) * dist x y := by
  have hF : LipschitzWith
      ⟨Real.sqrt (1 + eps), Real.sqrt_nonneg (1 + eps)⟩ F :=
    fun x y => by
      have hraw :=
        edist_le_of_path_comp (I := I) F
          (K := ENNReal.ofReal (Real.sqrt (1 + eps)))
          (by simp [Real.sqrt_pos.2 heps]) ENNReal.ofReal_ne_top hpath x y
      simpa [ENNReal.ofReal, Real.toNNReal_of_nonneg (Real.sqrt_nonneg (1 + eps))] using hraw
  simpa using hF.dist_le_mul x y



theorem dist_le_tangent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [PseudoMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [TopologicalSpace N] [ChartedSpace H N] [PseudoMetricSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N]
    (F : M -> N) {eps : Real} (heps : 0 < 1 + eps)
    (hspeed :
      forall {x y : M}, forall γ : Path x y, CMDiff 1 γ ->
        exists η : Path (F x) (F y), CMDiff 1 η /\
          forall t : Set.Icc (0 : Real) 1,
            ‖mfderiv% η t 1‖ₑ <=
              ENNReal.ofReal (Real.sqrt (1 + eps)) *
                ‖mfderiv% γ t 1‖ₑ)
    (x y : M) :
    dist (F x) (F y) <= Real.sqrt (1 + eps) * dist x y := by
  exact dist_le_of_path_comp (I := I) F heps
    (pathComp_tangent (I := I) F ENNReal.ofReal_ne_top hspeed) x y






theorem lipschitz_sqrt_of_dist_le
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : X -> Y) {eps : Real}
    (hdist : forall x y : X,
      dist (F x) (F y) <= Real.sqrt (1 + eps) * dist x y) :
    LipschitzWith ⟨Real.sqrt (1 + eps), Real.sqrt_nonneg (1 + eps)⟩ F := by
  exact LipschitzWith.of_dist_le_mul hdist







theorem image_ball_subset_of_lipschitz_sqrt
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : X -> Y) {eps : Real} (heps : 0 < 1 + eps)
    (hF : LipschitzWith ⟨Real.sqrt (1 + eps), Real.sqrt_nonneg (1 + eps)⟩ F)
    (x0 : X) (r : Real) :
    F '' Metric.ball x0 r ⊆
      Metric.ball (F x0) (Real.sqrt (1 + eps) * r) := by
  have hKpos :
      0 < (⟨Real.sqrt (1 + eps), Real.sqrt_nonneg (1 + eps)⟩ : NNReal) := by
    exact_mod_cast (Real.sqrt_pos.2 heps)
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact hF.mapsTo_ball (ne_of_gt hKpos) x0 r hx







theorem image_ball_subset_of_path_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [PseudoMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [TopologicalSpace N] [ChartedSpace H N] [PseudoMetricSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N]
    (F : M -> N) {eps : Real} (heps : 0 < 1 + eps)
    (hpath :
      forall {x y : M}, forall γ : Path x y, CMDiff 1 γ ->
        exists η : Path (F x) (F y), CMDiff 1 η /\
          (∫⁻ t, ‖mfderiv% η t 1‖ₑ) <=
            ENNReal.ofReal (Real.sqrt (1 + eps)) *
              (∫⁻ t, ‖mfderiv% γ t 1‖ₑ))
    (x0 : M) (r : Real) :
    F '' Metric.ball x0 r ⊆
      Metric.ball (F x0) (Real.sqrt (1 + eps) * r) := by
  have hF : LipschitzWith
      ⟨Real.sqrt (1 + eps), Real.sqrt_nonneg (1 + eps)⟩ F :=
    fun x y => by
      have hraw :=
        edist_le_of_path_comp (I := I) F
          (K := ENNReal.ofReal (Real.sqrt (1 + eps)))
          (by simp [Real.sqrt_pos.2 heps]) ENNReal.ofReal_ne_top hpath x y
      simpa [ENNReal.ofReal, Real.toNNReal_of_nonneg (Real.sqrt_nonneg (1 + eps))] using hraw
  exact image_ball_subset_of_lipschitz_sqrt F heps hF x0 r



theorem image_ball_tangent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [PseudoMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [TopologicalSpace N] [ChartedSpace H N] [PseudoMetricSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N]
    (F : M -> N) {eps : Real} (heps : 0 < 1 + eps)
    (hspeed :
      forall {x y : M}, forall γ : Path x y, CMDiff 1 γ ->
        exists η : Path (F x) (F y), CMDiff 1 η /\
          forall t : Set.Icc (0 : Real) 1,
            ‖mfderiv% η t 1‖ₑ <=
              ENNReal.ofReal (Real.sqrt (1 + eps)) *
                ‖mfderiv% γ t 1‖ₑ)
    (x0 : M) (r : Real) :
    F '' Metric.ball x0 r ⊆
      Metric.ball (F x0) (Real.sqrt (1 + eps) * r) := by
  exact image_ball_subset_of_path_comp (I := I) F heps
    (pathComp_tangent (I := I) F ENNReal.ofReal_ne_top hspeed) x0 r








theorem image_ball_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [TopologicalSpace N] [ChartedSpace H N] [PseudoEMetricSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N]
    (F : M -> N) {eps r : Real} (_heps : 0 < 1 + eps) (_hr : 0 < r) (x0 : M)
    (hspeed : forall {y : M} (γ : ℝ → M), (CMDiff[Set.Icc (0:ℝ) 1] 1 γ) →
      γ 0 = x0 → γ 1 = y →
      Manifold.pathELength (I := I) γ 0 1 < ENNReal.ofReal r →
      exists η : ℝ → N, (CMDiff[Set.Icc (0:ℝ) 1] 1 η) ∧ η 0 = F x0 ∧ η 1 = F y ∧
        Manifold.pathELength (I := I) η 0 1 ≤
          ENNReal.ofReal (Real.sqrt (1 + eps)) * Manifold.pathELength (I := I) γ 0 1) :
    F '' Metric.eball x0 (ENNReal.ofReal r) ⊆
      Metric.closedEBall (F x0) (ENNReal.ofReal (Real.sqrt (1 + eps) * r)) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Metric.mem_eball, edist_comm, IsRiemannianManifold.out (I := I) x0 x] at hx
  obtain ⟨γ, hγ0, hγ1, hγC, hγlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt (I := I) hx
  obtain ⟨η, hηC, hη0, hη1, hηlen⟩ := hspeed γ hγC hγ0 hγ1 hγlen
  rw [Metric.mem_closedEBall, edist_comm, IsRiemannianManifold.out (I := I) (F x0) (F x)]
  calc Manifold.riemannianEDist I (F x0) (F x)
      ≤ Manifold.pathELength (I := I) η 0 1 := by
        refine Manifold.riemannianEDist_le_pathELength hηC ?_ ?_ zero_le_one
        · exact hη0
        · exact hη1
    _ ≤ ENNReal.ofReal (Real.sqrt (1 + eps)) * Manifold.pathELength (I := I) γ 0 1 := hηlen
    _ ≤ ENNReal.ofReal (Real.sqrt (1 + eps)) * ENNReal.ofReal r := by
        gcongr
    _ = ENNReal.ofReal (Real.sqrt (1 + eps) * r) := by
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

universe u uE uH

open DifferentialGeometry.Integral.Connection Tensor0SBundle

section Speed

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem speed_le_of_c0
    (P : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (g : SmoothRiemannianMetric I M) {ε : ℝ} {x : M}
    (hc0 : metricTensorErrorNorm (I := I) P g x ≤ ε)
    (v : TangentSpace I x) :
    P x (fun _ => v) ≤ (1 + ε) * g.inner x v v := by
  classical
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) g x
  have hCS := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I)
    g x 2 basis (fun i j => hON i j)
    (P x - Tensor0SBundle.metricTensorField (I := I) g x)
    (fun _ => v)
  have hval : (P x - Tensor0SBundle.metricTensorField (I := I) g x) (fun _ => v)
      = P x (fun _ => v) - g.inner x v v := by
    calc
      (P x - Tensor0SBundle.metricTensorField (I := I) g x) (fun _ => v) =
          P x (fun _ => v) -
            Tensor0SBundle.metricTensorField (I := I) g x (fun _ => v) :=
        Tensor0SSpace.sub_apply 2 x _ _ _
      _ = P x (fun _ => v) - g.inner x v v := by
        rw [Tensor0SBundle.metricTensorField_apply]
  have hnn : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hprod : (∏ _a : Fin 2, Real.sqrt (g.inner x v v)) = g.inner x v v := by
    rw [Fin.prod_univ_two, Real.mul_self_sqrt hnn]
  have habs : |P x (fun _ => v) - g.inner x v v| ≤ ε * g.inner x v v := by
    unfold metricTensorErrorNorm at hc0
    calc |P x (fun _ => v) - g.inner x v v|
        = |(P x - Tensor0SBundle.metricTensorField (I := I) g x) (fun _ => v)| := by
          rw [hval]
      _ ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2
            (P x - Tensor0SBundle.metricTensorField (I := I) g x))
          * ∏ _a : Fin 2, Real.sqrt (g.inner x v v) := hCS
      _ ≤ ε * g.inner x v v := by
          rw [hprod]
          exact mul_le_mul_of_nonneg_right hc0 hnn
  nlinarith [abs_le.mp habs]

end Speed

section BookData

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]





omit [SigmaCompactSpace M] in
theorem data_image_ball
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [PseudoEMetricSpace N] [RiemannianBundle (fun y : N => TangentSpace I y)]
    [IsRiemannianManifold I N]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)) {O : M} {r r₂ ε : ℝ} {p : ℕ}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hgnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hhnorm : ∀ (y : N) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (h.inner y w w)))
    (hr : 0 < r) (hrr₂ : r ≤ r₂) (hε0 : 0 ≤ ε)
    (hdata : PreApproxIsoDataOn (I := I)
      (Metric.closedEBall O (ENNReal.ofReal r₂)) ε p (Φ : M → N) g h)
    (hsub : Metric.closedEBall O (ENNReal.ofReal r₂) ⊆ Φ.source) :
    (Φ : M → N) '' Metric.eball O (ENNReal.ofReal r) ⊆
      Metric.closedEBall ((Φ : M → N) O)
        (ENNReal.ofReal (Real.sqrt (1 + ε) * r)) := by
  refine image_ball_local (I := I) (Φ : M → N) (by linarith) hr O ?_
  intro y γ hγC hγ0 hγ1 hγlen
  have hrange : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ t ∈ Metric.closedEBall O (ENNReal.ofReal r₂) := by
    intro t ht
    rw [Metric.mem_closedEBall, edist_comm, IsRiemannianManifold.out (I := I) O (γ t)]
    calc Manifold.riemannianEDist I O (γ t)
        ≤ Manifold.pathELength (I := I) γ 0 t := by
          refine Manifold.riemannianEDist_le_pathELength
            (hγC.mono (Set.Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1
      _ ≤ Manifold.pathELength (I := I) γ 0 1 :=
          Manifold.pathELength_mono (I := I) (γ := γ) (a' := 0) (b' := 1) le_rfl ht.2
      _ ≤ ENNReal.ofReal r := le_of_lt hγlen
      _ ≤ ENNReal.ofReal r₂ := ENNReal.ofReal_le_ofReal hrr₂
  refine ⟨(Φ : M → N) ∘ γ, ?_, by simp [Function.comp, hγ0],
    by simp [Function.comp, hγ1], ?_⟩
  · exact (Φ.contMDiffOn_toFun.of_le (by exact_mod_cast le_top)).comp hγC
      (fun t ht => hsub (hrange t ht))
  · rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
      Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
      ← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_mono_ae
      (Filter.eventually_of_mem
        (MeasureTheory.self_mem_ae_restrict measurableSet_Ioo) ?_)
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc_of_Ioo ht
    have hγt : γ t ∈ Metric.closedEBall O (ENNReal.ofReal r₂) := hrange t htIcc
    have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := by
      refine ((hγC.contMDiffAt ?_).mdifferentiableAt (by norm_num))
      exact Icc_mem_nhds ht.1 ht.2
    have hΦd : MDifferentiableAt I I (Φ : M → N) (γ t) :=
      (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (hsub hγt))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hchain := mfderiv_comp t hΦd hγd
    have happ : mfderiv 𝓘(ℝ, ℝ) I ((Φ : M → N) ∘ γ) t 1
        = mfderiv I I (Φ : M → N) (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
      rw [hchain]
      rfl
    rw [happ]
    set w := mfderiv 𝓘(ℝ, ℝ) I γ t 1 with hw
    have hPval : h.inner ((Φ : M → N) (γ t))
        (mfderiv I I (Φ : M → N) (γ t) w) (mfderiv I I (Φ : M → N) (γ t) w)
        = hdata.pullback (γ t) (fun _ => w) := by
      rw [hdata.pullback_apply (γ t) hγt (fun _ => w)]
    have hquad : hdata.pullback (γ t) (fun _ => w)
        ≤ (1 + ε) * g.inner (γ t) w w :=
      speed_le_of_c0 (I := I) hdata.pullback g (hdata.c0_small (γ t) hγt) w
    calc ‖mfderiv I I (Φ : M → N) (γ t) w‖ₑ
        = ENNReal.ofReal (Real.sqrt (h.inner ((Φ : M → N) (γ t))
            (mfderiv I I (Φ : M → N) (γ t) w)
            (mfderiv I I (Φ : M → N) (γ t) w))) := hhnorm _ _
      _ ≤ ENNReal.ofReal (Real.sqrt ((1 + ε) * g.inner (γ t) w w)) := by
          refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
          rw [hPval]
          exact hquad
      _ = ENNReal.ofReal (Real.sqrt (1 + ε))
          * ENNReal.ofReal (Real.sqrt (g.inner (γ t) w w)) := by
          rw [Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 1 + ε),
            ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      _ = ENNReal.ofReal (Real.sqrt (1 + ε)) * ‖w‖ₑ := by
          rw [hgnorm (γ t) w]

end BookData

end RiemannianNorm

end HCGCompactness
end DifferentialGeometry
