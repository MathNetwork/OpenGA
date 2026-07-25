import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.ChartLocalPicardRegular


namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle Set
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def ChartCoordSpatialC1 (X : ℝ → ∀ x : M, TangentSpace I x) : Prop :=
  ∀ α : M, ∃ (L r : ℝ) (Df : ℝ → E → (E →L[ℝ] E)),
    0 < L ∧ 0 < r ∧
    (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ y ∈ Metric.closedBall (I ((chartAt H α) α)) r,
      HasFDerivWithinAt (fun z : E => (X t ((chartAt H α).symm (I.symm z)) : E))
        (Df t y) (Metric.closedBall (I ((chartAt H α) α)) r) y) ∧
    ContinuousOn (Function.uncurry Df)
      (Set.Icc (0 : ℝ) L ×ˢ Metric.closedBall (I ((chartAt H α) α)) r)

omit [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem exists_uniform_chart_lipschitz_of_spatialC1
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (L r : ℝ) (Df : ℝ → E → (E →L[ℝ] E))
    (hL : 0 < L) (hr : 0 < r)
    (hHasDeriv : ∀ t ∈ Set.Icc (0 : ℝ) L,
      ∀ y ∈ Metric.closedBall (I ((chartAt H α) α)) r,
        HasFDerivWithinAt
          (fun z : E => (X t ((chartAt H α).symm (I.symm z)) : E))
          (Df t y) (Metric.closedBall (I ((chartAt H α) α)) r) y)
    (hDerCont : ContinuousOn (Function.uncurry Df)
      (Set.Icc (0 : ℝ) L ×ˢ Metric.closedBall (I ((chartAt H α) α)) r)) :
    ∃ Lout K r' : ℝ, 0 < Lout ∧ 0 < r' ∧ 0 ≤ K ∧
      ∀ t ∈ Set.Icc (0 : ℝ) Lout,
        LipschitzOnWith (Real.toNNReal K)
          (fun y : E => (X t ((chartAt H α).symm (I.symm y)) : E))
          (Metric.ball (I ((chartAt H α) α)) r') := by
  set c : E := I ((chartAt H α) α) with hc_def
  set Box : Set (ℝ × E) := Set.Icc (0 : ℝ) L ×ˢ Metric.closedBall c r with hBox
  have hBoxCompact : IsCompact Box := by
    rw [hBox]
    exact (isCompact_Icc).prod (isCompact_closedBall c r)
  have hBoxNonempty : Box.Nonempty := by
    refine ⟨(0, c), ?_⟩
    rw [hBox]
    exact ⟨⟨le_refl 0, hL.le⟩, Metric.mem_closedBall_self hr.le⟩
  have hNormCont : ContinuousOn (fun p : ℝ × E => ‖Function.uncurry Df p‖) Box :=
    hDerCont.norm
  obtain ⟨pmax, hpmaxMem, hpmaxMax⟩ :=
    hBoxCompact.exists_isMaxOn hBoxNonempty hNormCont
  set K : ℝ := ‖Function.uncurry Df pmax‖ with hK_def
  have hK_nonneg : 0 ≤ K := by rw [hK_def]; exact norm_nonneg _
  have hKbound : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ y ∈ Metric.closedBall c r,
      ‖Df t y‖ ≤ K := by
    intro t ht y hy
    have hmem : (t, y) ∈ Box := by rw [hBox]; exact ⟨ht, hy⟩
    have := hpmaxMax hmem
    simpa [Function.uncurry, hK_def] using this
  refine ⟨L, K, r, hL, hr, hK_nonneg, ?_⟩
  intro t ht
  have hconv : Convex ℝ (Metric.ball c r) := convex_ball c r
  have hKcoe : (Real.toNNReal K : ℝ) = K := Real.coe_toNNReal K hK_nonneg
  have hder_open : ∀ y ∈ Metric.ball c r,
      HasFDerivWithinAt
        (fun z : E => (X t ((chartAt H α).symm (I.symm z)) : E))
        (Df t y) (Metric.ball c r) y := by
    intro y hy
    have hy_closed : y ∈ Metric.closedBall c r :=
      Metric.ball_subset_closedBall hy
    exact (hHasDeriv t ht y hy_closed).mono Metric.ball_subset_closedBall
  have hbound_open : ∀ y ∈ Metric.ball c r,
      ‖Df t y‖₊ ≤ Real.toNNReal K := by
    intro y hy
    have hy_closed : y ∈ Metric.closedBall c r :=
      Metric.ball_subset_closedBall hy
    have hnorm := hKbound t ht y hy_closed
    rw [← NNReal.coe_le_coe, coe_nnnorm, hKcoe]
    exact hnorm
  exact hconv.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le hder_open hbound_open

omit [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem chartCoordPicardRegular_of_spatialC1
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hCont : ContinuousOn (Function.uncurry (fun t x => X t x))
      (Set.univ : Set (ℝ × M)))
    (hC1 : ChartCoordSpatialC1 (I := I) X) :
    ChartCoordPicardRegular (I := I) X := by
  refine ⟨hCont, ?_⟩
  intro α
  obtain ⟨L, r, Df, hL, hr, hHasDeriv, hDerCont⟩ := hC1 α
  exact exists_uniform_chart_lipschitz_of_spatialC1 X α L r Df hL hr hHasDeriv
    hDerCont

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem chartCoordSpatialC1_neg
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hC1 : ChartCoordSpatialC1 (I := I) X) :
    ChartCoordSpatialC1 (I := I) (fun t x => -(X t x)) := by
  intro α
  obtain ⟨L, r, Df, hL, hr, hHasDeriv, hDerCont⟩ := hC1 α
  refine ⟨L, r, fun t y => -(Df t y), hL, hr, ?_, ?_⟩
  · intro t ht y hy
    have hbase := hHasDeriv t ht y hy
    have hfun :
        (fun z : E => ((-X t ((chartAt H α).symm (I.symm z))) : E))
          = fun z : E => -((X t ((chartAt H α).symm (I.symm z)) : E)) := by
      funext z; rfl
    rw [hfun]
    exact hbase.neg
  · have hfun :
        (Function.uncurry (fun t y => -(Df t y)))
          = fun p : ℝ × E => -(Function.uncurry Df p) := by
      funext p; rfl
    rw [hfun]
    exact hDerCont.neg

noncomputable def chartLocalPicardData_of_spatialC1
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hCont : ContinuousOn (Function.uncurry (fun t x => X t x))
      (Set.univ : Set (ℝ × M)))
    (hC1 : ChartCoordSpatialC1 (I := I) X) :
    (∀ α : M, ChartLocalPicardData X α) ×
      (∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α) := by
  have hReg : ChartCoordPicardRegular (I := I) X :=
    chartCoordPicardRegular_of_spatialC1 X hCont hC1
  have hContNeg :
      ContinuousOn (Function.uncurry (fun t x => -(X t x)))
        (Set.univ : Set (ℝ × M)) := by
    have hfun :
        (Function.uncurry (fun t x => -(X t x)))
          = fun p : ℝ × M => -(Function.uncurry (fun t x => X t x) p) := by
      funext p; rfl
    rw [hfun]
    exact hCont.neg
  have hRegNeg : ChartCoordPicardRegular (I := I) (fun t x => -(X t x)) :=
    chartCoordPicardRegular_of_spatialC1 (fun t x => -(X t x)) hContNeg
      (chartCoordSpatialC1_neg X hC1)
  exact ⟨fun α => chartLocalPicardData_of_regular X hReg α,
    fun α => chartLocalPicardData_of_regular (fun t x => -(X t x)) hRegNeg α⟩

end DifferentialGeometry.PDE.RicciFlow.ODE
