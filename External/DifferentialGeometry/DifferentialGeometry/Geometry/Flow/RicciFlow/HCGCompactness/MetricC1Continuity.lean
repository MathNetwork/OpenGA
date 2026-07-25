import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyPair
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivTimeDeriv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvBridge

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]




omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricCov_cont
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (q : SmoothRiemannianMetric I M) {t : Real} (ht : t ∈ D.regular)
    {Idx : Type*}
    {u : Set M} (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (a : ℕ) (slots : Fin (a + 2) → Idx) :
    ContinuousAt
      (fun p : Real × M =>
        metricCovDeriv (I := I) (G.metric p.1) q a p.2
          (fun j => frame (slots j) p.2))
      (t, x) := by
  classical
  obtain ⟨sec, hsec⟩ :=
    hframe.exists_contMDiffSection_eqOn_nhd hu hx
  let V : Fin (a + 2) →
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
    fun j => sec (slots j)
  have htower :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
        (∞ : WithTop ℕ∞)
        (fun p : Real × M =>
          metricCovDeriv (I := I) (G.metric p.1) q a p.2
            (fun j => V j p.2))
        (t, x) := by
    have hbase :
        ∀ W : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
            (TangentSpace I : M → Type _),
          ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
            (∞ : WithTop ℕ∞)
            (fun p : Real × M =>
              (Tensor0SBundle.metricTensorField (I := I) (G.metric p.1)) p.2
                (fun j => W j p.2))
            (t, x) := by
      intro W
      simpa only [Tensor0SBundle.metricTensorField_apply] using
        hG.pairSmoothAt (D.regular_isOpen.mem_nhds ht) W
    simpa only [metricCovDeriv_eq_covDerivOfField] using
      covDerivOfField_eval_contMDiffAt (I := I) q
        (fun t => Tensor0SBundle.metricTensorField (I := I) (G.metric t))
        hbase a V
  have hev : ∀ᶠ y in 𝓝 x, ∀ j : Fin (a + 2),
      V j y = frame (slots j) y :=
    hsec.mono fun y hy j => hy (slots j)
  refine htower.continuousAt.congr_of_eventuallyEq ?_
  have hev' : ∀ᶠ p : Real × M in 𝓝 (t, x),
      ∀ j : Fin (a + 2), V j p.2 = frame (slots j) p.2 :=
    (continuous_snd.tendsto (t, x)).eventually hev
  filter_upwards [hev'] with p hp
  congr 1
  funext j
  exact (hp j).symm



omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricCov_smooth
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime)
    {Idx : Type*}
    {u : Set M} (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (a : ℕ) (slots : Fin (a + 2) → Idx) :
    ContinuousAt
      (fun p : Real × M =>
        metricCovDeriv (I := I) (G.metric p.1) (G.metric (T : Real)) a p.2
          (fun j => frame (slots j) p.2))
      ((T : Real), x) :=
  metricCov_cont (I := I) G hG (G.metric (T : Real)) T.2
    frame hframe hu hx a slots



omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem metric_c_patch
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) (a : ℕ) (x : M)
    {ε : Real} (hε : 0 < ε) :
    ∃ V : Set Real, V ∈ 𝓝 (T : Real) ∧
      ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
        ∀ t ∈ V, ∀ y ∈ W,
          metricDerivNorm (I := I) a
            (G.metric t) (G.metric (T : Real)) (G.metric (T : Real)) y < ε := by
  classical
  obtain ⟨basisE, u, Cu, huOpen, hxu, huSub, hCu, hnorm⟩ :=
    metricDerivNorm_le_compSq_uniform (I := I) (G.metric (T : Real)) a x
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let frame := e.localFrame basisE
  have hxe : x ∈ e.baseSet := by
    simp [e]
  have hframe :
      IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame e.baseSet := by
    simpa [frame] using
      e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) basisE
  let c :
      (Real × M) →
        (Fin (a + 2) → Fin (Module.finrank Real E)) → Real :=
    fun p I0 =>
      metricCovDeriv (I := I) (G.metric p.1) (G.metric (T : Real)) a p.2
          (fun j => frame (I0 j) p.2) -
        metricCovDeriv (I := I) (G.metric (T : Real)) (G.metric (T : Real)) a p.2
          (fun j => frame (I0 j) p.2)
  let q : Real × M → Real :=
    fun p => Cu * Real.sqrt (∑ I0, (c p I0) ^ 2)
  have hc (I0 : Fin (a + 2) → Fin (Module.finrank Real E)) :
      ContinuousAt (fun p : Real × M => c p I0) ((T : Real), x) := by
    have hmove :=
      metricCov_smooth (I := I) G hG T frame hframe e.open_baseSet hxe a I0
    have hwhole :=
      metricCov_smooth (I := I) G hG T frame hframe e.open_baseSet hxe a I0
    have hfix :
        ContinuousAt
          (fun p : Real × M =>
            metricCovDeriv (I := I) (G.metric (T : Real)) (G.metric (T : Real)) a p.2
              (fun j => frame (I0 j) p.2))
          ((T : Real), x) := by
      have hconst :
          ContinuousAt (fun _ : Real × M => (T : Real)) ((T : Real), x) :=
        continuousAt_const
      have hsnd :
          ContinuousAt (fun p : Real × M => p.2) ((T : Real), x) :=
        continuousAt_snd
      have hmap :
          ContinuousAt (fun p : Real × M => ((T : Real), p.2)) ((T : Real), x) :=
        hconst.prodMk hsnd
      exact ContinuousAt.comp'
        (f := fun p : Real × M => ((T : Real), p.2))
        (g := fun q : Real × M =>
          metricCovDeriv (I := I) (G.metric q.1) (G.metric (T : Real)) a q.2
            (fun j => frame (I0 j) q.2))
        hwhole hmap
    exact hmove.sub hfix
  have hsum :
      ContinuousAt
        (fun p : Real × M => ∑ I0, (c p I0) ^ 2)
        ((T : Real), x) := by
    exact tendsto_finset_sum Finset.univ fun I0 _ => (hc I0).pow 2
  have hq : ContinuousAt q ((T : Real), x) := by
    exact continuousAt_const.mul
      (Real.continuous_sqrt.continuousAt.comp hsum)
  have hq0 : q ((T : Real), x) = 0 := by
    simp [q, c]
  have hsmall : {p : Real × M | q p < ε} ∈ 𝓝 ((T : Real), x) := by
    exact hq.eventually_lt_const (by simpa only [hq0] using hε)
  have huNhd : (Set.univ ×ˢ u : Set (Real × M)) ∈ 𝓝 ((T : Real), x) :=
    prod_mem_nhds Filter.univ_mem (huOpen.mem_nhds hxu)
  have htarget :
      ({p : Real × M | q p < ε} ∩ (Set.univ ×ˢ u)) ∈
        𝓝 ((T : Real), x) :=
    Filter.inter_mem hsmall huNhd
  obtain ⟨V, W, hVOpen, hTV, hWOpen, hxW, hVW⟩ :=
    mem_nhds_prod_iff'.mp htarget
  refine ⟨V, hVOpen.mem_nhds hTV, W, hWOpen, hxW, ?_⟩
  intro t ht y hy
  have hty : (t, y) ∈ V ×ˢ W := ⟨ht, hy⟩
  have hpair := hVW hty
  have hyu : y ∈ u := hpair.2.2
  have hye : y ∈ e.baseSet := by
    simpa only [e] using huSub hyu
  have hle :=
    hnorm (G.metric t) (G.metric (T : Real)) y hyu (by simpa only [e] using hye)
  have hle' :
      metricDerivNorm (I := I) a
          (G.metric t) (G.metric (T : Real)) (G.metric (T : Real)) y
        ≤ q (t, y) := by
    simpa only [q, c, frame, e, Tensor0SBundle.component0S_apply,
      IsLocalFrameOn.toBasisAt_coe] using hle
  exact lt_of_le_of_lt hle' hpair.1



omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem metric_c1_patch
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) (x : M)
    {ε : Real} (hε : 0 < ε) :
    ∃ V : Set Real, V ∈ 𝓝 (T : Real) ∧
      ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
        ∀ t ∈ V, ∀ y ∈ W, ∀ a : ℕ, a ≤ 1 →
          metricDerivNorm (I := I) a
            (G.metric t) (G.metric (T : Real)) (G.metric (T : Real)) y < ε := by
  obtain ⟨V0, hV0, W0, hW0Open, hxW0, h0⟩ :=
    metric_c_patch (I := I) G hG T 0 x hε
  obtain ⟨V1, hV1, W1, hW1Open, hxW1, h1⟩ :=
    metric_c_patch (I := I) G hG T 1 x hε
  refine ⟨V0 ∩ V1, Filter.inter_mem hV0 hV1,
    W0 ∩ W1, hW0Open.inter hW1Open, ⟨hxW0, hxW1⟩, ?_⟩
  intro t ht y hy a ha
  have ha' : a = 0 ∨ a = 1 := by
    omega
  rcases ha' with rfl | rfl
  · exact h0 t ht.1 y hy.1
  · exact h1 t ht.2 y hy.2



omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem metric_b_patch
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) {t : Real} (ht : t ∈ D.regular) (a : ℕ) (x : M) :
    ∃ V : Set Real, V ∈ 𝓝 t ∧
      ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
        ∃ C : Real, 0 ≤ C ∧ ∀ r ∈ V, ∀ y ∈ W,
          metricDerivNorm (I := I) a
            (G.metric r) (G.metric (T : Real)) (G.metric (T : Real)) y ≤ C := by
  classical
  obtain ⟨basisE, u, Cu, huOpen, hxu, huSub, hCu, hnorm⟩ :=
    metricDerivNorm_le_compSq_uniform (I := I) (G.metric (T : Real)) a x
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let frame := e.localFrame basisE
  have hxe : x ∈ e.baseSet := by
    simp [e]
  have hframe :
      IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame e.baseSet := by
    simpa [frame] using
      e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) basisE
  let c :
      (Real × M) →
        (Fin (a + 2) → Fin (Module.finrank Real E)) → Real :=
    fun p I0 =>
      metricCovDeriv (I := I) (G.metric p.1) (G.metric (T : Real)) a p.2
          (fun j => frame (I0 j) p.2) -
        metricCovDeriv (I := I) (G.metric (T : Real)) (G.metric (T : Real)) a p.2
          (fun j => frame (I0 j) p.2)
  let b : Real × M → Real :=
    fun p => Cu * Real.sqrt (∑ I0, (c p I0) ^ 2)
  have hc (I0 : Fin (a + 2) → Fin (Module.finrank Real E)) :
      ContinuousAt (fun p : Real × M => c p I0) (t, x) := by
    have hmove :=
      metricCov_cont (I := I) G hG (G.metric (T : Real)) ht
        frame hframe e.open_baseSet hxe a I0
    have hwhole :=
      metricCov_cont (I := I) G hG (G.metric (T : Real)) T.2
        frame hframe e.open_baseSet hxe a I0
    have hfix :
        ContinuousAt
          (fun p : Real × M =>
            metricCovDeriv (I := I) (G.metric (T : Real)) (G.metric (T : Real)) a p.2
              (fun j => frame (I0 j) p.2))
          (t, x) := by
      have hconst :
          ContinuousAt (fun _ : Real × M => (T : Real)) (t, x) :=
        continuousAt_const
      have hsnd :
          ContinuousAt (fun p : Real × M => p.2) (t, x) :=
        continuousAt_snd
      have hmap :
          ContinuousAt (fun p : Real × M => ((T : Real), p.2)) (t, x) :=
        hconst.prodMk hsnd
      exact ContinuousAt.comp'
        (f := fun p : Real × M => ((T : Real), p.2))
        (g := fun q : Real × M =>
          metricCovDeriv (I := I) (G.metric q.1) (G.metric (T : Real)) a q.2
            (fun j => frame (I0 j) q.2))
        hwhole hmap
    exact hmove.sub hfix
  have hsum :
      ContinuousAt
        (fun p : Real × M => ∑ I0, (c p I0) ^ 2)
        (t, x) := by
    exact tendsto_finset_sum Finset.univ fun I0 _ => (hc I0).pow 2
  have hb : ContinuousAt b (t, x) := by
    exact continuousAt_const.mul
      (Real.continuous_sqrt.continuousAt.comp hsum)
  have hb_nn : 0 ≤ b (t, x) := by
    exact mul_nonneg (zero_le_one.trans hCu) (Real.sqrt_nonneg _)
  have hsmall : {p : Real × M | b p < b (t, x) + 1} ∈ 𝓝 (t, x) := by
    exact hb.eventually_lt_const (by linarith)
  have huNhd : (Set.univ ×ˢ u : Set (Real × M)) ∈ 𝓝 (t, x) :=
    prod_mem_nhds Filter.univ_mem (huOpen.mem_nhds hxu)
  have htarget :
      ({p : Real × M | b p < b (t, x) + 1} ∩ (Set.univ ×ˢ u)) ∈
        𝓝 (t, x) :=
    Filter.inter_mem hsmall huNhd
  obtain ⟨V, W, hVOpen, htV, hWOpen, hxW, hVW⟩ :=
    mem_nhds_prod_iff'.mp htarget
  refine ⟨V, hVOpen.mem_nhds htV, W, hWOpen, hxW,
    b (t, x) + 1, by linarith, ?_⟩
  intro r hr y hy
  have hry : (r, y) ∈ V ×ˢ W := ⟨hr, hy⟩
  have hpair := hVW hry
  have hyu : y ∈ u := hpair.2.2
  have hye : y ∈ e.baseSet := by
    simpa only [e] using huSub hyu
  have hle :=
    hnorm (G.metric r) (G.metric (T : Real)) y hyu (by simpa only [e] using hye)
  have hle' :
      metricDerivNorm (I := I) a
          (G.metric r) (G.metric (T : Real)) (G.metric (T : Real)) y
        ≤ b (r, y) := by
    simpa only [b, c, frame, e, Tensor0SBundle.component0S_apply,
      IsLocalFrameOn.toBasisAt_coe] using hle
  exact hle'.trans hpair.1.le

section Compact

variable [CompactSpace M]



omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem metric_b_event
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) {t : Real} (ht : t ∈ D.regular) (a : ℕ) :
    ∃ C : Real, 0 ≤ C ∧ ∀ᶠ r in 𝓝 t, ∀ y : M,
      metricDerivNorm (I := I) a
        (G.metric r) (G.metric (T : Real)) (G.metric (T : Real)) y ≤ C := by
  classical
  choose V hV W hWOpen hxW C hC hloc using
    fun x : M => metric_b_patch (I := I) G hG T ht a x
  obtain ⟨F, _, hF⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).elim_nhds_subcover W
      (fun x _ => (hWOpen x).mem_nhds (hxW x))
  refine ⟨∑ x ∈ F, C x,
    Finset.sum_nonneg fun x _ => hC x, ?_⟩
  have htime :
      ∀ᶠ r in 𝓝 t, ∀ x ∈ F, r ∈ V x := by
    exact
      (Finset.eventually_all
        (I := F)
        (l := 𝓝 t)
        (p := fun x r => r ∈ V x)).2
        (fun x _ => hV x)
  filter_upwards [htime] with r hr
  intro y
  obtain ⟨x, hxF, hyW⟩ :=
    Set.mem_iUnion₂.mp (hF (Set.mem_univ y))
  exact (hloc x r (hr x hxF) y hyW).trans
    (Finset.single_le_sum (fun z _ => hC z) hxF)



omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem metric_b_compact
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) {K : Set Real} (hK : IsCompact K)
    (hKreg : K ⊆ D.regular) (a : ℕ) :
    ∃ C : Real, 0 ≤ C ∧ ∀ t ∈ K, ∀ y : M,
      metricDerivNorm (I := I) a
        (G.metric t) (G.metric (T : Real)) (G.metric (T : Real)) y ≤ C := by
  classical
  choose C hC hbound using fun t : {t : Real // t ∈ K} =>
    metric_b_event (I := I) G hG T (hKreg t.2) a
  choose O hOsub hOopen htO using fun t : {t : Real // t ∈ K} =>
    mem_nhds_iff.mp (hbound t)
  have hcover : K ⊆ ⋃ t : {t : Real // t ∈ K}, O t := by
    intro t ht
    exact Set.mem_iUnion.2 ⟨⟨t, ht⟩, htO ⟨t, ht⟩⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover O hOopen hcover
  refine ⟨∑ t ∈ F, C t,
    Finset.sum_nonneg fun t _ => hC t, ?_⟩
  intro t ht y
  obtain ⟨r, hrF, htO'⟩ := Set.mem_iUnion₂.mp (hF ht)
  exact (hOsub r htO' y).trans
    (Finset.single_le_sum (fun z _ => hC z) hrF)



omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metric_cp_bdd
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) {K : Set Real} (hK : IsCompact K)
    (hKreg : K ⊆ D.regular) :
    ∃ C : ℕ → Real, (∀ p, 0 ≤ C p) ∧ ∀ (p : ℕ) (t : Real), t ∈ K →
      metricDerivNormSupOn (I := I) Set.univ p
        (G.metric t) (G.metric (T : Real)) (G.metric (T : Real)) ≤ C p := by
  classical
  choose B hB hbound using fun a : ℕ =>
    metric_b_compact (I := I) G hG T hK hKreg a
  refine ⟨fun p => ∑ a ∈ Finset.range (p + 1), B a,
    fun p => Finset.sum_nonneg fun a _ => hB a, ?_⟩
  intro p t ht
  apply metricDerivNormSupOn_le_of_forall
  · exact Finset.sum_nonneg fun a _ => hB a
  · intro a ha y _
    exact (hbound a t ht y).trans
      (Finset.single_le_sum (fun j _ => hB j)
        (by simp only [Finset.mem_range]; omega))



omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem metric_c_event
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) (a : ℕ)
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (T : Real), ∀ y : M,
      metricDerivNorm (I := I) a
        (G.metric t) (G.metric (T : Real)) (G.metric (T : Real)) y < ε := by
  classical
  choose V hV W hWOpen hxW hloc using
    fun x : M => metric_c_patch (I := I) G hG T a x hε
  obtain ⟨F, _, hF⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).elim_nhds_subcover W
      (fun x _ => (hWOpen x).mem_nhds (hxW x))
  have htime :
      ∀ᶠ t in 𝓝 (T : Real), ∀ x ∈ F, t ∈ V x := by
    exact
      (Finset.eventually_all
        (I := F)
        (l := 𝓝 (T : Real))
        (p := fun x t => t ∈ V x)).2
        (fun x _ => hV x)
  filter_upwards [htime] with t ht
  intro y
  obtain ⟨x, hxF, hyW⟩ :=
    Set.mem_iUnion₂.mp (hF (Set.mem_univ y))
  exact hloc x t (ht x hxF) y hyW



omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metric_cp_tendsto
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) (p : ℕ) :
    Filter.Tendsto
      (fun t : Real =>
        metricDerivNormSupOn (I := I) Set.univ p
          (G.metric t) (G.metric (T : Real)) (G.metric (T : Real)))
      (𝓝 (T : Real)) (𝓝 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have htime :
      ∀ᶠ t in 𝓝 (T : Real),
        ∀ a ∈ Finset.range (p + 1), ∀ y : M,
          metricDerivNorm (I := I) a
            (G.metric t) (G.metric (T : Real)) (G.metric (T : Real)) y < ε / 2 := by
    exact
      (Finset.eventually_all
        (I := Finset.range (p + 1))
        (l := 𝓝 (T : Real))
        (p := fun a t => ∀ y : M,
          metricDerivNorm (I := I) a
            (G.metric t) (G.metric (T : Real)) (G.metric (T : Real)) y < ε / 2)).2
        (fun a _ => metric_c_event (I := I) G hG T a hε2)
  filter_upwards [htime] with t ht
  have hpoint :
      ∀ a : ℕ, a ≤ p → ∀ y ∈ (Set.univ : Set M),
        metricDerivNorm (I := I) a
            (G.metric t) (G.metric (T : Real)) (G.metric (T : Real)) y
          ≤ ε / 2 := by
    intro a ha y _
    exact (ht a (by simp only [Finset.mem_range]; omega) y).le
  have hsup :
      metricDerivNormSupOn (I := I) Set.univ p
          (G.metric t) (G.metric (T : Real)) (G.metric (T : Real))
        ≤ ε / 2 :=
    metricDerivNormSupOn_le_of_forall
      (I := I) Set.univ p
      (G.metric t) (G.metric (T : Real)) (G.metric (T : Real))
      (ε / 2) hε2.le hpoint
  have hnonneg :
      0 ≤ metricDerivNormSupOn (I := I) Set.univ p
        (G.metric t) (G.metric (T : Real)) (G.metric (T : Real)) := by
    unfold metricDerivNormSupOn
    apply Real.sSup_nonneg
    rintro r ⟨a, ha, y, hy, rfl⟩
    exact Real.sqrt_nonneg _
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
    hsup.trans_lt (half_lt_self hε)



omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metric_c1_tendsto
    [Module.Finite ℝ E]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    Filter.Tendsto
      (fun t : Real =>
        metricDerivNormSupOn (I := I) Set.univ 1
          (G.metric t) (G.metric (T : Real)) (G.metric (T : Real)))
      (𝓝 (T : Real)) (𝓝 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  choose V hV W hWOpen hxW hloc using
    fun x : M => metric_c1_patch (I := I) G hG T x hε2
  obtain ⟨F, _, hF⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).elim_nhds_subcover W
      (fun x _ => (hWOpen x).mem_nhds (hxW x))
  have htime :
      ∀ᶠ t in 𝓝 (T : Real), ∀ x ∈ F, t ∈ V x := by
    exact
      (Finset.eventually_all
        (I := F)
        (l := 𝓝 (T : Real))
        (p := fun x t => t ∈ V x)).2
        (fun x _ => hV x)
  filter_upwards [htime] with t ht
  have hpoint :
      ∀ a : ℕ, a ≤ 1 → ∀ y ∈ (Set.univ : Set M),
        metricDerivNorm (I := I) a
            (G.metric t) (G.metric (T : Real)) (G.metric (T : Real)) y
          ≤ ε / 2 := by
    intro a ha y _
    obtain ⟨x, hxF, hyW⟩ :=
      Set.mem_iUnion₂.mp (hF (Set.mem_univ y))
    exact (hloc x t (ht x hxF) y hyW a ha).le
  have hsup :
      metricDerivNormSupOn (I := I) Set.univ 1
          (G.metric t) (G.metric (T : Real)) (G.metric (T : Real))
        ≤ ε / 2 :=
    metricDerivNormSupOn_le_of_forall
      (I := I) Set.univ 1
      (G.metric t) (G.metric (T : Real)) (G.metric (T : Real))
      (ε / 2) hε2.le hpoint
  have hnonneg :
      0 ≤ metricDerivNormSupOn (I := I) Set.univ 1
        (G.metric t) (G.metric (T : Real)) (G.metric (T : Real)) := by
    unfold metricDerivNormSupOn
    apply Real.sSup_nonneg
    rintro r ⟨a, ha, y, hy, rfl⟩
    exact Real.sqrt_nonneg _
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
    hsup.trans_lt (half_lt_self hε)

end Compact

end HCGCompactness
end DifferentialGeometry

end
