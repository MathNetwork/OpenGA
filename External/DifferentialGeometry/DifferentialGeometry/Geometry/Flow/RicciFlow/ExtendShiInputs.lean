import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ExtendViaUniqueness
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.CovOrderTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MovingShiProducer
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.ChartGramUniformContinuity
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound













namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]



private theorem hasDerivWithinAt_Ici_boundary {a b : ℝ} (hab : a < b) (f e : ℝ → ℝ)
    (h_cont : ContinuousOn f (Set.Ico a b))
    (h_e_cont : ContinuousWithinAt e (Set.Ioi a) a)
    (h_int : ∀ t ∈ Set.Ioo a b, HasDerivWithinAt f (e t) (Set.Ici a) t) :
    HasDerivWithinAt f (e a) (Set.Ici a) a := by
  have hopen : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have hsub : Set.Ioo a b ⊆ Set.Ici a := fun y hy => le_of_lt hy.1
  have h_within : ∀ t ∈ Set.Ioo a b, HasDerivWithinAt f (e t) (Set.Ioo a b) t :=
    fun t ht => (h_int t ht).mono hsub
  have h_diff : DifferentiableOn ℝ f (Set.Ioo a b) :=
    fun t ht => (h_within t ht).differentiableWithinAt
  have h_derivEq : ∀ t ∈ Set.Ioo a b, deriv f t = e t := by
    intro t ht
    rw [← derivWithin_of_isOpen hopen ht]
    exact (h_within t ht).derivWithin (hopen.uniqueDiffWithinAt ht)
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioo a b) h_diff ?_ ?_ ?_
  · exact (h_cont.continuousWithinAt ⟨le_rfl, hab⟩).mono Set.Ioo_subset_Ico_self
  · exact Ioo_mem_nhdsGT hab
  · exact (h_e_cont.tendsto).congr'
      (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT hab) h_derivEq).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem tensor2_eval_contOn {K : Set ℝ}
    {A : (t : ℝ) → (x : M) →
      Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 x}
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K A)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun s : ℝ => A s x (vec2 v w)) K := by
  rw [continuousOn_iff_continuous_restrict]
  exact hA.eval_continuous (P := {s : ℝ // s ∈ K}) (τ := Subtype.val)
    (b := fun _ => x) continuous_subtype_val (fun p => p.2) continuous_const
    (v := fun i _ => vec2 v w i) (fun _ => continuous_const)







omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ricciFlowPDE_Ici_of_soln
    {alpha omega : ℝ} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen alpha omega hαω)}
    (hS : IsSolutionOn (I := I) S) :
    ∀ t ∈ Set.Ico alpha omega, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (S.base.metric s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (S.base.metric t) x v w) (Set.Ici alpha) t := by
  have hinterior : ∀ t ∈ Set.Ioo alpha omega, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (S.base.metric s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (S.base.metric t) x v w) (Set.Ici alpha) t := by
    intro t ht x v w
    have hval : S.ricciAt t x (vec2 v w) = ricciTensor (I := I) (S.base.metric t) x v w :=
      metricRicciAt_apply_eq_ricciTensor (S.base.metric t) x v w
    have h := metricDerivAt (I := I) S hS ⟨t, ht⟩ x v w
    rw [hval] at h
    exact h.hasDerivWithinAt
  have hric_cont : ∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun s : ℝ => ricciTensor (I := I) (S.base.metric s) x v w)
        (Set.Ico alpha omega) := by
    intro x v w
    refine (tensor2_eval_contOn hS.ricciCont x v w).congr (fun s _ => ?_)
    have e1 : S.ricci s x = metricRicciAt (S.base.metric s) x := by
      simp only [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt]
    rw [e1]
    exact (metricRicciAt_apply_eq_ricciTensor (S.base.metric s) x v w).symm
  intro t ht x v w
  rcases eq_or_lt_of_le ht.1 with rfl | hlt
  · refine hasDerivWithinAt_Ici_boundary hαω
      (fun s => (S.base.metric s).inner x v w)
      (fun s => (-2 : ℝ) * ricciTensor (I := I) (S.base.metric s) x v w) ?_ ?_
      (fun s hs => hinterior s hs x v w)
    · refine (tensor2_eval_contOn hS.smoothMetric.metricTensor_cont x v w).congr
        (fun s _ => ?_)
      simp [Tensor0SBundle.metricTensorField_apply, vec2]
    · have hmem : Set.Ico alpha omega ∈ nhdsWithin alpha (Set.Ioi alpha) :=
        Filter.mem_of_superset (Ioo_mem_nhdsGT hαω) Set.Ioo_subset_Ico_self
      exact (((hric_cont x v w).continuousWithinAt ⟨le_rfl, hαω⟩).mono_of_mem_nhdsWithin
        hmem).const_mul (-2)
  · exact hinterior t ⟨hlt, ht.2⟩ x v w







omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem hell_of_soln
    {alpha omega : ℝ} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen alpha omega hαω)}
    (hS : IsSolutionOn (I := I) S)
    {K : ℝ} (hK : 0 ≤ K)
    (hric : ∀ t ∈ Set.Ico alpha omega, ∀ x : M, ∀ v : TangentSpace I x,
      |ricciTensor (I := I) (S.base.metric t) x v v| ≤ K * (S.base.metric t).inner x v v) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ t₁ ∈ Set.Ico alpha omega, ∀ s ∈ Set.Ico t₁ omega,
      ∀ x : M, ∀ v : TangentSpace I x,
        Λ⁻¹ * (S.base.metric alpha).inner x v v ≤ (S.base.metric s).inner x v v ∧
          (S.base.metric s).inner x v v ≤ Λ * (S.base.metric alpha).inner x v v :=
  metricEquiv_of_ricBound (fun t => S.base.metric t) hαω hK
    (ricciFlowPDE_Ici_of_soln hS) hric





omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem metricInnerSq_le (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    (g.inner x u v) ^ 2 ≤ g.inner x u u * g.inner x v v := by
  have hnn : ∀ w : TangentSpace I x, 0 ≤ g.inner x w w := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · exact (g.pos x w hw).le
  have hquad : ∀ t : ℝ, 0 ≤ g.inner x u u + 2 * t * g.inner x u v + t ^ 2 * g.inner x v v := by
    intro t
    have h := hnn (u + t • v)
    have hexp : g.inner x (u + t • v) (u + t • v)
        = g.inner x u u + 2 * t * g.inner x u v + t ^ 2 * g.inner x v v := by
      have hsym : g.inner x v u = g.inner x u v := g.symm x v u
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hsym]; ring
    rwa [hexp] at h
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hc : 0 < g.inner x v v := g.pos x v hv
    have hval := hquad (-(g.inner x u v) / g.inner x v v)
    have he : g.inner x u u + 2 * (-(g.inner x u v) / g.inner x v v) * g.inner x u v
          + (-(g.inner x u v) / g.inner x v v) ^ 2 * g.inner x v v
        = (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) / g.inner x v v := by
      field_simp; ring
    rw [he] at hval
    have hX : 0 ≤ g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 := by
      have := mul_nonneg hval hc.le
      rwa [div_mul_cancel₀ _ hc.ne'] at this
    linarith












omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem chartGramEntry_le_of_equiv
    (gRef g : SmoothRiemannianMetric I M) {C M0 : ℝ} (hC0 : 0 ≤ C) (hM0 : 0 ≤ M0) (α₀ : M)
    {Q : Set M} (hequiv : MetricUniformEquivalentOn Q gRef g C)
    (hgRef : ∀ (a : Fin (Module.finrank ℝ E)) (b : M), b ∈ Q →
      chartGramMatrix gRef α₀ b a a ≤ M0)
    (i j : Fin (Module.finrank ℝ E)) {x : M} (hx : x ∈ Q) :
    |chartGramMatrix g α₀ x i j| ≤ C * M0 := by

  have hdiag : ∀ a : Fin (Module.finrank ℝ E),
      0 ≤ g.inner x (chartBasisVecFiber (I := I) α₀ a x) (chartBasisVecFiber (I := I) α₀ a x) ∧
        g.inner x (chartBasisVecFiber (I := I) α₀ a x) (chartBasisVecFiber (I := I) α₀ a x) ≤ C * M0 := by
    intro a
    set e := chartBasisVecFiber (I := I) α₀ a x with he
    have hnn : 0 ≤ g.inner x e e := by
      rcases eq_or_ne e 0 with he0 | hne
      · rw [he0]; simp
      · exact (g.pos x e hne).le
    refine ⟨hnn, ?_⟩
    have hup : g.inner x e e ≤ C * gRef.inner x e e := (hequiv.2 x hx e).2
    have hg : gRef.inner x e e = chartGramMatrix gRef α₀ x a a :=
      (chartGramMatrix_apply gRef α₀ x a a).symm
    calc g.inner x e e ≤ C * gRef.inner x e e := hup
      _ = C * chartGramMatrix gRef α₀ x a a := by rw [hg]
      _ ≤ C * M0 := by
        apply mul_le_mul_of_nonneg_left (hgRef a x hx) hC0

  rw [chartGramMatrix_apply]
  set ei := chartBasisVecFiber (I := I) α₀ i x
  set ej := chartBasisVecFiber (I := I) α₀ j x
  have hcs : (g.inner x ei ej) ^ 2 ≤ (C * M0) * (C * M0) := by
    calc (g.inner x ei ej) ^ 2 ≤ g.inner x ei ei * g.inner x ej ej := metricInnerSq_le g x ei ej
      _ ≤ (C * M0) * (C * M0) :=
          mul_le_mul (hdiag i).2 (hdiag j).2 (hdiag j).1 (by positivity)
  have habs : |g.inner x ei ej| ≤ C * M0 := by
    have hCM : (0 : ℝ) ≤ C * M0 := by positivity
    nlinarith [abs_nonneg (g.inner x ei ej), sq_abs (g.inner x ei ej), hcs, hCM]
  exact habs




omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem exists_gRefDiag_bound (gRef : SmoothRiemannianMetric I M) (α₀ : M)
    {Q : Set M} (hQc : IsCompact Q) (hQs : Q ⊆ (chartAt H α₀).source) :
    ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ (a : Fin (Module.finrank ℝ E)) (b : M), b ∈ Q →
      chartGramMatrix gRef α₀ b a a ≤ M0 := by
  classical
  choose Ci hCi_pos hCi using fun a : Fin (Module.finrank ℝ E) =>
    chartGramMatrix_entry_isBounded_on_compact gRef α₀ a a hQc hQs
  refine ⟨∑ a : Fin (Module.finrank ℝ E), Ci a,
    Finset.sum_nonneg (fun a _ => (hCi_pos a).le), ?_⟩
  intro a b hb
  calc chartGramMatrix gRef α₀ b a a ≤ |chartGramMatrix gRef α₀ b a a| := le_abs_self _
    _ ≤ Ci a := hCi a b hb
    _ ≤ ∑ a' : Fin (Module.finrank ℝ E), Ci a' :=
        Finset.single_le_sum (fun i _ => (hCi_pos i).le) (Finset.mem_univ a)


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem goodSet_subset_chartSource (α₀ : M) :
    chartLeviCivitaGoodSet (I := I) α₀ ⊆ (chartAt H α₀).source :=
  fun _ hz => extChartAt_source I α₀ ▸ hz.1.1



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem chartJet0_le_of_equiv
    (gRef g : SmoothRiemannianMetric I M) {C M0 : ℝ} (hC0 : 0 ≤ C) (hM0 : 0 ≤ M0) (α₀ : M)
    {Q : Set M} (hQ : Q ⊆ chartLeviCivitaGoodSet (I := I) α₀)
    (hequiv : MetricUniformEquivalentOn Q gRef g C)
    (hgRef : ∀ (a : Fin (Module.finrank ℝ E)) (b : M), b ∈ Q →
      chartGramMatrix gRef α₀ b a a ≤ M0)
    (i j : Fin (Module.finrank ℝ E)) {x : M} (hx : x ∈ Q) :
    |Integral.DivergenceTheorem.chartGramOnE (I := I) g α₀ i j (extChartAt I α₀ x)| ≤ C * M0 := by
  have hxsrc : x ∈ (extChartAt I α₀).source := by
    rw [extChartAt_source]; exact goodSet_subset_chartSource α₀ (hQ hx)
  have hred : Integral.DivergenceTheorem.chartGramOnE (I := I) g α₀ i j (extChartAt I α₀ x)
      = chartGramMatrix g α₀ x i j := by
    rw [Integral.DivergenceTheorem.chartGramOnE_def, (extChartAt I α₀).left_inv hxsrc]
  rw [hred]
  exact chartGramEntry_le_of_equiv gRef g hC0 hM0 α₀ hequiv hgRef i j hx






omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem ric_quad_le_of_rm04
    (g : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Fin n)))
    (Rm04 : Tensor04At (I := I) (M := M) x) {C : ℝ}
    (htrace : ∀ i j, metricRicciAt g x (vec2 (I := I) (basis i) (basis j))
        = ∑ a, Rm04 (vec4 (I := I) (basis a) (basis i) (basis j) (basis a)))
    (hnorm : Tensor0SBundle.normSq0S (I := I) g x 4 Rm04 ≤ C)
    (v : TangentSpace I x) :
    |ricciTensor (I := I) g x v v| ≤ ((n : ℝ) ^ 2 * Real.sqrt C) * g.inner x v v := by
  have hunit : ∀ u : TangentSpace I x, g.inner x u u = 1 →
      |metricRicciAt g x (vec2 (I := I) u u)| ≤ (n : ℝ) ^ 2 * Real.sqrt C := by
    intro u hu
    have h := ricci_unitQuad_le_of_trace g basis hON hinv (metricRicciAt g x) Rm04 htrace u hu
    exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnorm) (by positivity))
  have hquad := tensor02_quadForm_abs_le_of_unit_bound g (metricRicciAt g x) hunit v
  rw [← metricRicciAt_apply_eq_ricciTensor g x v v]
  exact hquad








omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem ric_quad_le_of_realizes
    (g : SmoothRiemannianMetric I M) (x : M)
    (Rm04sec : Tensor04Section (I := I) (M := M))
    (hreal : Rm04RealizesConnection (I := I) g (metricCov (I := I) (M := M) g) Rm04sec)
    {C : ℝ} (hnorm : Tensor0SBundle.normSq0S (I := I) g x 4 (Rm04sec x) ≤ C)
    (v : TangentSpace I x) :
    |ricciTensor (I := I) g x v v|
      ≤ ((Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 * Real.sqrt C) * g.inner x v v := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hdelta := metricInverseInBasis_of_orthonormal (I := I) g basis hON
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have he : (fun a k : Fin (Module.finrank ℝ (TangentSpace I x)) => if a = k then (1 : ℝ) else 0)
        = identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x))) := by
      funext a k; simp [identityInvMetric, diagonalInvMetric]
    rwa [he] at hdelta
  set Rm13 := CovariantDerivative.rm13Section (I := I) (M := M)
    (metricCov (I := I) (M := M) g) (metricCov_smooth (I := I) (M := M) g) with hRm13def
  have hLower := rm04LowersRm13At_of_realizes (I := I) g
    (metricCov (I := I) (M := M) g) Rm13 Rm04sec
    (rm13Section_realizes (I := I) (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g)) hreal x
  have hmr : metricRicciAt g x = ricciFromRm13At (I := I) (Rm13 x) := by
    rw [hRm13def, CovariantDerivative.rm13Section_apply]
    rfl
  have htrace : ∀ i j, metricRicciAt g x (vec2 (I := I) (basis i) (basis j))
      = ∑ a, Rm04sec x (vec4 (I := I) (basis a) (basis i) (basis j) (basis a)) := by
    intro i j
    have hcomp := ricciFromRm13_comp_eq_rm04_trace (I := I) g basis
      (fun a k => if a = k then (1 : ℝ) else 0) hdelta (Rm13 x) (Rm04sec x) hLower i j
    have hlhs : metricRicciAt g x (vec2 (I := I) (basis i) (basis j))
        = ricciCompAt (I := I) basis (ricciFromRm13At (I := I) (Rm13 x)) i j := by
      rw [ricciCompAt_apply, hmr]
    rw [hlhs, hcomp]
    simp only [rm04CompAt_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  exact ric_quad_le_of_rm04 (I := I) g x basis hON hinv (Rm04sec x) htrace hnorm v






omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem chartGram_smooth_of_soln
    {alpha omega : ℝ} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen alpha omega hαω)}
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M =>
        Integral.Measure.chartGramMatrix (I := I) (S.base.metric p.1) x₀ p.2 i j)
      (Set.Ioo alpha omega ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  set e := trivializationAt E (TangentSpace I) x₀ with he
  have hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) (e.localFrame (chartModelBasis E)) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) (chartModelBasis E)
  have hbridge : ∀ {x : M} (hx : x ∈ e.baseSet) (k : Fin (Module.finrank ℝ E)),
      e.localFrame (chartModelBasis E) k x
        = Integral.Measure.chartBasisVecFiber (I := I) x₀ k x := by
    intro x hx k
    rw [e.localFrame_apply_of_mem_baseSet (chartModelBasis E) hx]
    rfl
  have h := hS.smoothMetric.frameCompSmooth (e.localFrame (chartModelBasis E)) hframe i j
  refine h.congr fun p hp => ?_
  have hx : p.2 ∈ e.baseSet := hp.2
  simp only [Integral.Measure.chartGramMatrix_apply, hbridge hx i, hbridge hx j,
    SolutionOn.family]






omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem chartGram_cont_of_soln
    {alpha omega : ℝ} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen alpha omega hαω)}
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun p : ℝ × M =>
        Integral.Measure.chartGramMatrix (I := I) (S.base.metric p.1) x₀ p.2 i j)
      (Set.Ico alpha omega ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  rw [continuousOn_iff_continuous_restrict]
  set s : Set (ℝ × M) :=
    Set.Ico alpha omega ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet with hs
  have hτ : Continuous (fun q : ↥s => ((q : ℝ × M)).1) :=
    continuous_fst.comp continuous_subtype_val
  have hb : Continuous (fun q : ↥s => ((q : ℝ × M)).2) :=
    continuous_snd.comp continuous_subtype_val
  have hτK : ∀ q : ↥s,
      ((q : ℝ × M)).1 ∈ (RealTimeInterval.closedOpen alpha omega hαω).carrier :=
    fun q => q.2.1
  have hv : ∀ k : Fin 2,
      Continuous (fun q : ↥s =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y)
          ((q : ℝ × M)).2
          (Integral.Measure.chartBasisVecFiber (I := I) x₀
            (if k = 0 then i else j) ((q : ℝ × M)).2)) := by
    intro k
    rw [continuous_iff_continuousAt]
    intro q
    have hframe :=
      (Integral.Measure.chartBasisVec_contMDiffOn (I := I) x₀ (if k = 0 then i else j)).contMDiffAt
        ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds q.2.2)
    exact ContinuousAt.comp
      (g := fun y : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) y
        (Integral.Measure.chartBasisVecFiber (I := I) x₀ (if k = 0 then i else j) y))
      hframe.continuousAt hb.continuousAt
  have heval :=
    (hS.smoothMetric.metricTensor_cont).eval_continuous (P := ↥s) hτ hτK hb hv
  refine heval.congr (fun q => ?_)
  rw [Tensor0SBundle.metricTensorField_apply]
  simp [Integral.Measure.chartGramMatrix_apply, SolutionOn.family]









omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem ric_quad_le_of_soln
    {alpha omega : ℝ} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen alpha omega hαω)}
    {Rm04 : ℝ → Tensor04Section (I := I) (M := M)}
    (hRm : ∀ t ∈ Set.Ico alpha omega,
      Rm04RealizesConnection (I := I) (S.base.metric t)
        (metricCov (I := I) (M := M) (S.base.metric t)) (Rm04 t))
    {K' : ℝ}
    (hbound : ∀ t : ℝ, ∀ x : M, alpha ≤ t → t < omega →
      normSq0S (I := I) (S.base.metric t) x 4 ((Rm04 t) x) ≤ K') :
    ∀ t ∈ Set.Ico alpha omega, ∀ x : M, ∀ v : TangentSpace I x,
      |ricciTensor (I := I) (S.base.metric t) x v v|
        ≤ ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K') * (S.base.metric t).inner x v v := by
  intro t ht x v
  have h := ric_quad_le_of_realizes (I := I) (S.base.metric t) x (Rm04 t) (hRm t ht)
    (hbound t x ht.1 ht.2) v
  rwa [show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl] at h



theorem movingShi_of_soln
    {alpha omega : ℝ} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen alpha omega hαω)}
    (_hdim : Module.finrank ℝ E = 3)
    (_hS : IsSolutionOn (I := I) S)
    (_hbound : ∃ K : ℝ, ∀ t : ℝ, ∀ x : M, alpha ≤ t → t < omega →
      normSq0S (I := I) (S.base.metric t) x 4 ((S.base.rm04 t) x) ≤ K) :
    ∃ KShi : ℝ, 0 ≤ KShi ∧ ∃ tShi ∈ Set.Ico alpha omega,
      ∀ ψ ∈ Set.Ico tShi omega,
        MovingShiBoundOn (I := I) Set.univ tShi ψ
          (fun _ t => S.base.metric t) 3 KShi := by
  exact movingShiBoundSol (I := I) _hdim _hS _hbound




theorem shiCovBound_of_soln
    {alpha omega : ℝ} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen alpha omega hαω)}
    (hdim : Module.finrank ℝ E = 3)
    (_hS : IsSolutionOn (I := I) S)
    (_hbound : ∃ K : ℝ, ∀ t : ℝ, ∀ x : M, alpha ≤ t → t < omega →
      normSq0S (I := I) (S.base.metric t) x 4 ((S.base.rm04 t) x) ≤ K)
    (hEquiv : ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ t₁ ∈ Set.Ico alpha omega,
      ∀ s ∈ Set.Ico t₁ omega, ∀ x : M, ∀ v : TangentSpace I x,
        Λ⁻¹ * (S.base.metric alpha).inner x v v ≤ (S.base.metric s).inner x v v ∧
          (S.base.metric s).inner x v v ≤ Λ * (S.base.metric alpha).inner x v v) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ t₂ ∈ Set.Ico alpha omega, ∀ s ∈ Set.Ico t₂ omega,
      ∀ a : ℕ, a ≤ 3 →
        MetricCovDerivOrderBoundOn Set.univ a (S.base.metric s) (S.base.metric alpha) C := by
  classical
  obtain ⟨Λ, hΛ, t₁, ht₁, hEquivTail⟩ := hEquiv
  obtain ⟨KShi, hKShi0, tShi, htShi, hShi⟩ :=
    movingShi_of_soln (I := I) hdim _hS _hbound
  have hmaxω : max t₁ tShi < omega := max_lt ht₁.2 htShi.2
  obtain ⟨t₂, hmaxt₂, ht₂ω⟩ := exists_between hmaxω
  have ht₁t₂ : t₁ ≤ t₂ := le_trans (le_max_left _ _) hmaxt₂.le
  have htShit₂ : tShi ≤ t₂ := le_trans (le_max_right _ _) hmaxt₂.le
  have hαt₂ : alpha < t₂ :=
    lt_of_le_of_lt (le_trans ht₁.1 (le_max_left _ _)) hmaxt₂
  let D := RealTimeInterval.closedOpen alpha omega hαω
  let gSeq : Nat → ℝ → SmoothRiemannianMetric I M := fun _ t => S.base.metric t
  let gRef : SmoothRiemannianMetric I M := S.base.metric alpha
  have hequivWindow : ∀ ψ ∈ Set.Ico t₂ omega,
      MetricUniformEquivalentOnWindow (I := I) Set.univ t₂ ψ gRef gSeq (fun _ => Λ) := by
    intro ψ hψ i t ht
    refine ⟨hΛ, ?_⟩
    intro x _hx v
    exact hEquivTail t ⟨le_trans ht₁t₂ ht.1, lt_of_le_of_lt ht.2 hψ.2⟩ x v
  have hShiWindow : ∀ ψ ∈ Set.Ico t₂ omega,
      MovingShiBoundOn (I := I) Set.univ t₂ ψ gSeq 3 KShi := by
    intro ψ hψ q hq i t ht x hx
    exact hShi ψ ⟨le_trans htShit₂ hψ.1, hψ.2⟩ q hq i t
      ⟨le_trans htShit₂ ht.1, ht.2⟩ x hx
  have hDreg : ∀ {t : ℝ}, t ∈ D.regular → D.regular ∈ nhds t :=
    fun {_t} ht => D.regular_isOpen.mem_nhds ht
  have hevWindow : ∀ ψ ∈ Set.Ico t₂ omega, ∀ q : Nat, 1 ≤ q → q ≤ 3 →
      ∀ i : Nat, ∀ x ∈ Set.univ, ∀ s ∈ Set.Icc t₂ ψ,
        ∀ v : Fin (q + 2) → TangentSpace I x,
          HasDerivAt
            (fun r : ℝ => metricCovDeriv (I := I) (gSeq i r) gRef q x v)
            (((-2 : ℝ) • nablaRicReal (I := I) gSeq gRef q i s x) v) s := by
    intro ψ hψ q _hq1 _hq3
    exact hevComp_of_solutions (I := I) (K := Set.univ) (β := t₂) (ψ := ψ) (N := q)
      (fun _ => D) (fun _ => S) (fun _ => _hS) (fun _ _ => rfl)
      (fun _ t ht => by
        change t ∈ Set.Ioo alpha omega
        exact ⟨lt_of_lt_of_le hαt₂ ht.1, lt_of_le_of_lt ht.2 hψ.2⟩)
      (fun _ p hp V x₀ => solnTowerSwap_reg (I := I) gRef S _hS q hDreg p hp V x₀)
  obtain ⟨initC, hinitC0, hinit⟩ := exists_initC (I := I) (S.base.metric t₂) gRef
  have htime : ∀ t ∈ Set.Ico t₂ omega, |t - t₂| ≤ omega - t₂ := by
    intro t ht
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have hpos := covOrder_Ico_tail (I := I)
    (K := Set.univ) (U := Set.univ) (t0 := t₂) (omega := omega)
    (gSeq := gSeq) (gRef := gRef)
    isCompact_univ isOpen_univ (subset_refl Set.univ) 3 Λ hΛ KShi hKShi0
    initC hinitC0 (omega - t₂) (fun _ => Λ) hequivWindow
    (fun _ _ => le_rfl) hShiWindow hevWindow
    (fun q _ _ _i x _hx => hinit q x) htime
  obtain ⟨C₁, hC₁⟩ := hpos 1 (by omega) (by omega)
  obtain ⟨C₂, hC₂⟩ := hpos 2 (by omega) (by omega)
  obtain ⟨C₃, hC₃⟩ := hpos 3 (by omega) (by omega)
  let Cpos := max C₁ (max C₂ C₃)
  have hposAll : ∀ s ∈ Set.Ico t₂ omega, ∀ a : Nat, 1 ≤ a → a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a (S.base.metric s) gRef Cpos := by
    intro s hs a ha1 ha3
    have ha : a = 1 ∨ a = 2 ∨ a = 3 := by omega
    rcases ha with rfl | rfl | rfl
    · intro x hx
      exact le_trans (hC₁ 0 s hs x hx) (le_max_left _ _)
    · intro x hx
      exact le_trans (hC₂ 0 s hs x hx) (le_trans (le_max_left _ _) (le_max_right _ _))
    · intro x hx
      exact le_trans (hC₃ 0 s hs x hx) (le_trans (le_max_right _ _) (le_max_right _ _))
  let C₀ := Λ * Real.sqrt (Module.finrank Real E : Real)
  have hC₀ : ∀ s ∈ Set.Ico t₂ omega,
      MetricCovDerivOrderBoundOn (I := I) Set.univ 0 (S.base.metric s) gRef C₀ := by
    intro s hs
    apply covOrder_zero_le (I := I)
    refine ⟨hΛ, ?_⟩
    intro x _hx v
    exact hEquivTail s ⟨le_trans ht₁t₂ hs.1, hs.2⟩ x v
  refine ⟨max 1 (max C₀ Cpos), le_max_left _ _, t₂, ⟨hαt₂.le, ht₂ω⟩, ?_⟩
  intro s hs a ha3
  by_cases ha0 : a = 0
  · subst a
    intro x hx
    exact le_trans (hC₀ s hs x hx) (le_trans (le_max_left _ _) (le_max_right _ _))
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
    intro x hx
    exact le_trans (hposAll s hs a ha1 ha3 x hx)
      (le_trans (le_max_right _ _) (le_max_right _ _))






theorem extendInputs_of_soln
    {alpha omega : ℝ} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen alpha omega hαω)}
    (hdim : Module.finrank ℝ E = 3)
    (hS : IsSolutionOn (I := I) S)
    {K : ℝ} (hK : 0 ≤ K)
    (hric : ∀ t ∈ Set.Ico alpha omega, ∀ x : M, ∀ v : TangentSpace I x,
      |ricciTensor (I := I) (S.base.metric t) x v v| ≤ K * (S.base.metric t).inner x v v)
    (hbound : ∃ K' : ℝ, ∀ t : ℝ, ∀ x : M, alpha ≤ t → t < omega →
      normSq0S (I := I) (S.base.metric t) x 4 ((S.base.rm04 t) x) ≤ K') :
    (∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ t₁ ∈ Set.Ico alpha omega, ∀ s ∈ Set.Ico t₁ omega,
      ∀ x : M, ∀ v : TangentSpace I x,
        Λ⁻¹ * (S.base.metric alpha).inner x v v ≤ (S.base.metric s).inner x v v ∧
          (S.base.metric s).inner x v v ≤ Λ * (S.base.metric alpha).inner x v v) ∧
    (∃ C : ℝ, 1 ≤ C ∧ ∃ t₂ ∈ Set.Ico alpha omega, ∀ s ∈ Set.Ico t₂ omega,
      ∀ a : ℕ, a ≤ 3 →
        MetricCovDerivOrderBoundOn Set.univ a (S.base.metric s) (S.base.metric alpha) C) := by
  have hEquiv := hell_of_soln hS hK hric
  exact ⟨hEquiv, shiCovBound_of_soln hdim hS hbound hEquiv⟩

end DifferentialGeometry.PDE.RicciFlow
