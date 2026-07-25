import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.TensorWeak.Compactness


set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle Tensor0SBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]








def TensorBarrierUniformOnSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (delta t0 : Real) : Prop :=
  ∀ epsilon : Real, SmallBarrierEps epsilon ->
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0)
      (Set.Icc t0 (t0 + delta))





omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem tensorBarrier_limit_on_fixed_slab
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {delta t0 : Real}
    (hdelta : 0 < delta)
    (hbarrier : TensorBarrierUniformOnSlab (I := I) (M := M) G S delta t0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) S
      (Set.Icc t0 (t0 + delta)) := by
  intro t ht x v
  let q : Real := S t x v v
  let c : Real := (delta + t - t0) * (G t).inner x v v
  have htime_nonneg : 0 ≤ delta + t - t0 := by
    have ht_sub : 0 ≤ t - t0 := sub_nonneg.mpr ht.1
    have hsum : 0 ≤ delta + (t - t0) :=
      add_nonneg (le_of_lt hdelta) ht_sub
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsum
  have hmetric_nonneg : 0 ≤ (G t).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact le_of_lt ((G t).pos x v hv)
  have hc_nonneg : 0 ≤ c := by
    simpa [c] using mul_nonneg htime_nonneg hmetric_nonneg
  have hforall : ∀ e : Real, 0 < e -> 0 ≤ q + e := by
    intro e he
    let eta : Real := min 1 (e / (c + 1))
    have hden_pos : 0 < c + 1 :=
      add_pos_of_nonneg_of_pos hc_nonneg zero_lt_one
    have hdiv_pos : 0 < e / (c + 1) :=
      div_pos he hden_pos
    have heta_pos : 0 < eta := by
      dsimp [eta]
      exact lt_min zero_lt_one hdiv_pos
    have heta_le_one : eta ≤ 1 := by
      dsimp [eta]
      exact min_le_left 1 (e / (c + 1))
    have heta_le_div : eta ≤ e / (c + 1) := by
      dsimp [eta]
      exact min_le_right 1 (e / (c + 1))
    have heta_small : SmallBarrierEps eta := ⟨heta_pos, heta_le_one⟩
    have hbar_eta :
        0 ≤
          tensorBarrierFamily (I := I) (M := M) G S eta delta t0 t x v v :=
      hbarrier eta heta_small t ht x v
    have hbar_q : 0 ≤ q + eta * c := by
      simpa [tensorBarrierFamily, q, c, mul_assoc] using hbar_eta
    have heta_nonneg : 0 ≤ eta := le_of_lt heta_pos
    have hcoeff_le : c ≤ c + 1 := le_add_of_nonneg_right zero_le_one
    have hprod_le : eta * c ≤ eta * (c + 1) :=
      mul_le_mul_of_nonneg_left hcoeff_le heta_nonneg
    have hden_ne : c + 1 ≠ 0 := ne_of_gt hden_pos
    have heta_mul_den_le : eta * (c + 1) ≤ e := by
      have hmul_le : eta * (c + 1) ≤ (e / (c + 1)) * (c + 1) :=
        mul_le_mul_of_nonneg_right heta_le_div (le_of_lt hden_pos)
      have hdiv_mul : (e / (c + 1)) * (c + 1) = e := by
        field_simp [hden_ne]
      simpa [hdiv_mul] using hmul_le
    have heta_c_le : eta * c ≤ e := by
      exact le_trans hprod_le heta_mul_den_le
    exact le_trans hbar_q (by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left heta_c_le q)
  have hq_nonneg : 0 ≤ q := le_of_forall_pos_le_add hforall
  simpa [q] using hq_nonneg







def TensorBarrierLimitClosureOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (T : Real) : Prop :=
  TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S 0 ->
  (∀ t0 : Real, t0 ∈ Set.Icc 0 T -> t0 < T ->
    TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t0 ->
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      TensorBarrierUniformOnSlab (I := I) (M := M) G S delta t0) ->
  TwoTensorFamilyNonnegativeOn (I := I) (M := M) S (Set.Icc 0 T)




omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] in
private theorem nonnegativeTime_isClosed
    {S : TwoTensorFamily (I := I) (M := M)}
    {T : Real}
    (hcont : ∀ x, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : Real => S t x v w) (Set.Icc 0 T)) :
    IsClosed ({t : Real | TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      S t} ∩ Set.Icc 0 T) := by
  rw [show
      {t : Real | TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t} ∩
          Set.Icc 0 T =
        Set.Icc 0 T ∩ ⋂ x : M, ⋂ v : TangentSpace I x,
          (Set.Icc 0 T ∩ (fun t : Real => S t x v v) ⁻¹' Set.Ici 0) by
    ext t
    constructor
    · intro ht
      refine ⟨ht.2, ?_⟩
      rw [Set.mem_iInter]
      intro x
      rw [Set.mem_iInter]
      intro v
      exact ⟨ht.2, ht.1 x v⟩
    · intro ht
      refine ⟨?_, ht.1⟩
      intro x v
      exact ((Set.mem_iInter.mp (Set.mem_iInter.mp ht.2 x) v)).2]
  exact isClosed_Icc.inter
    (isClosed_iInter fun x =>
      isClosed_iInter fun v =>
        (hcont x v v).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici)



omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem barrierLimitClosure_of_continuous
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {T : Real}
    (hT : 0 ≤ T)
    (hcont : ∀ x, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : Real => S t x v w) (Set.Icc 0 T)) :
    TensorBarrierLimitClosureOn (I := I) (M := M) G S T := by
  intro hinit hstep
  let P : Set Real := {t : Real | TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t}
  have hclosed : IsClosed (P ∩ Set.Icc 0 T) := by
    simpa [P] using nonnegativeTime_isClosed (I := I) (M := M) (S := S) hcont
  have hP : Set.Icc 0 T ⊆ P := by
    refine hclosed.Icc_subset_of_forall_exists_gt (a := 0) (b := T) ?_ ?_
    · simpa [P] using hinit
    · intro t ht y hy
      have htIcc : t ∈ Set.Icc 0 T := ⟨ht.2.1, le_of_lt ht.2.2⟩
      obtain ⟨delta, hdelta, _hdeltaT, hbarrier⟩ :=
        hstep t htIcc ht.2.2 ht.1
      have hslab : TwoTensorFamilyNonnegativeOn (I := I) (M := M) S
          (Set.Icc t (t + delta)) :=
        tensorBarrier_limit_on_fixed_slab (I := I) (M := M)
          (G := G) (S := S) hdelta hbarrier
      let z : Real := min y (t + delta)
      have htz : t < z := by
        dsimp [z]
        exact lt_min hy (by linarith)
      have hz_le_delta : z ≤ t + delta := by
        dsimp [z]
        exact min_le_right y (t + delta)
      have hz_le_y : z ≤ y := by
        dsimp [z]
        exact min_le_left y (t + delta)
      have hzP : P z :=
        hslab z ⟨le_of_lt htz, hz_le_delta⟩
      exact ⟨z, hzP, htz, hz_le_y⟩
  intro t ht
  exact hP ht


structure TensorWMPCore
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  symmetric : TwoTensorFamilySymmetricOn (I := I) (M := M) S (Set.Icc 0 T)
  bilinear :
    ∀ t, t ∈ Set.Icc 0 T -> ∀ x,
      TwoTensorBilinearAt (I := I) (M := M) (S t) x
  barrierRegularity :
    TensorBarrierRegularityOn (I := I) (M := M) G S X N T
  firstNullCompactness :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      TensorFirstNullCompactnessOn (I := I) (M := M) G S epsilon delta t0








structure TensorWMPRegularityOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  symmetric : TwoTensorFamilySymmetricOn (I := I) (M := M) S (Set.Icc 0 T)
  bilinear :
    ∀ t, t ∈ Set.Icc 0 T -> ∀ x,
      TwoTensorBilinearAt (I := I) (M := M) (S t) x
  barrierRegularity :
    TensorBarrierRegularityOn (I := I) (M := M) G S X N T
  firstNullCompactness :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      TensorFirstNullCompactnessOn (I := I) (M := M) G S epsilon delta t0
  firstNullScalarSigns :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      ∀ (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
        (nablaBarrier : TensorNabla1Family (I := I) (M := M)),
      (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
        G S X N nabla2Barrier nablaBarrier epsilon delta t0) ->
      (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
        G N (Set.Icc t0 (t0 + delta))) ->
      (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0) ->
      TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d

namespace TensorWMPRegularityOn


def toCore
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (h : TensorWMPRegularityOn (I := I) (M := M) G S X N T) :
    TensorWMPCore (I := I) (M := M) G S X N T where
  symmetric := h.symmetric
  bilinear := h.bilinear
  barrierRegularity := h.barrierRegularity
  firstNullCompactness := h.firstNullCompactness

end TensorWMPRegularityOn






structure TensorWMPSectionCore
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  symmetric :
    TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T)
  barrierRegularity :
    TensorBarrierRegularityOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N T
  unitSlabCompact :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
            (Set.Icc t0 (t0 + delta))))
  metricQuadCont :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      Continuous
        (metricBundleQuad (I := I) (M := M) G
          (Set.Icc t0 (t0 + delta)))
  tensorQuadCont :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      Continuous
        (tensorSecBundleQuad (I := I) (M := M) S
          (Set.Icc t0 (t0 + delta)))
  barrierFixedContinuous :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      ∀ x (v : TangentSpace I x),
        ContinuousOn
          (fun t : Real =>
            tensorBarrierFamily (I := I) (M := M) G
              (twoTensorSecToFamily (I := I) (M := M) S)
              epsilon delta t0 t x v v)
          (Set.Icc t0 (t0 + delta))












structure TensorWMPSectionReg
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  symmetric :
    TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T)
  barrierRegularity :
    TensorBarrierRegularityOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N T
  unitSlabCompact :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
            (Set.Icc t0 (t0 + delta))))
  metricQuadCont :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      Continuous
        (metricBundleQuad (I := I) (M := M) G
          (Set.Icc t0 (t0 + delta)))
  tensorQuadCont :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      Continuous
        (tensorSecBundleQuad (I := I) (M := M) S
          (Set.Icc t0 (t0 + delta)))
  barrierFixedContinuous :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      ∀ x (v : TangentSpace I x),
        ContinuousOn
          (fun t : Real =>
            tensorBarrierFamily (I := I) (M := M) G
              (twoTensorSecToFamily (I := I) (M := M) S)
              epsilon delta t0 t x v v)
          (Set.Icc t0 (t0 + delta))
  firstNullScalarSigns :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      ∀ (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
        (nablaBarrier : TensorNabla1Family (I := I) (M := M)),
      (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
        G (twoTensorSecToFamily (I := I) (M := M) S) X N
        nabla2Barrier nablaBarrier epsilon delta t0) ->
      (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
        G N (Set.Icc t0 (t0 + delta))) ->
      (d : TensorFirstNullData (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0) ->
      TensorFirstNullScalarSigns (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N epsilon delta t0 d

namespace TensorWMPSectionCore


omit [IsManifold I 2 M] in
theorem ofCompact
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hMetric :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (metricBundleQuad (I := I) (M := M) G
            (Set.Icc t0 (t0 + delta))))
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (tensorSecBundleQuad (I := I) (M := M) S
            (Set.Icc t0 (t0 + delta))))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) G
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta))) :
    TensorWMPSectionCore (I := I) (M := M) G S X N T where
  symmetric := hsym
  barrierRegularity := hbar
  unitSlabCompact := by
    intro delta t0 hdelta hsub
    exact metricUnitTimeSlab_icc_compact_of_bundle (I := I) (M := M)
      G t0 (t0 + delta) (G t0)
      (by
        simpa [metricBundleQuad] using hMetric delta t0 hdelta hsub)
  metricQuadCont := hMetric
  tensorQuadCont := hTensor
  barrierFixedContinuous := hFixed


omit [IsManifold I 2 M] in
theorem ofTotal
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hMetric :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (metricTensorField (I := I) (G q.1.1) q.2.proj)))
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (S q.1.1 q.2.proj)))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) G
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta))) :
    TensorWMPSectionCore (I := I) (M := M) G S X N T :=
  ofCompact (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N) (T := T)
    hsym hbar
    (fun delta t0 hdelta hsub =>
      DifferentialGeometry.Integral.Connection.metricFamQuadCont (I := I) (M := M)
        G (Set.Icc t0 (t0 + delta))
        (hMetric delta t0 hdelta hsub))
    (fun delta t0 hdelta hsub =>
      DifferentialGeometry.Integral.Connection.tensorQuadCont (I := I) (M := M)
        S (Set.Icc t0 (t0 + delta))
        (hTensor delta t0 hdelta hsub))
    hFixed


omit [IsManifold I 2 M] in
theorem ofSmoothMetric
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) (fun t => G.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (S q.1.1 q.2.proj)))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) (fun t => G.metric t)
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta))) :
    TensorWMPSectionCore (I := I) (M := M) (fun t => G.metric t) S X N T :=
  ofTotal (I := I) (M := M)
    (G := fun t => G.metric t) (S := S) (X := X) (N := N) (T := T)
    hsym hbar
    (fun delta t0 hdelta hsub =>
      metricTensor_tangentBundle_cont_of_metricFamilySmoothOn
        (I := I) (M := M) G hG
        (fun t ht => hTsub (hsub ht)))
    hTensor hFixed


omit [IsManifold I 2 M] in
theorem toRaw
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (h : TensorWMPSectionCore (I := I) (M := M) G S X N T) :
    TensorWMPCore (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N T where
  symmetric := h.symmetric
  bilinear := fun t _ht x => twoTensorSecToFamily_bilin (I := I) (M := M) S t x
  barrierRegularity := h.barrierRegularity
  firstNullCompactness := by
    intro epsilon delta t0 hepsilon hdelta hsub
    exact TensorFirstNullCompactnessOn.of_section_timeSlab (I := I) (M := M)
      G S epsilon delta t0
      (h.unitSlabCompact delta t0 hdelta hsub)
      (barrierTimeCont (I := I) (M := M) G S epsilon delta t0
        (Set.Icc t0 (t0 + delta))
        (h.tensorQuadCont delta t0 hdelta hsub)
        (h.metricQuadCont delta t0 hdelta hsub))
      (h.barrierFixedContinuous epsilon delta t0 hepsilon hdelta hsub)

end TensorWMPSectionCore

namespace TensorWMPSectionReg


def toCore
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (h : TensorWMPSectionReg (I := I) (M := M) G S X N T) :
    TensorWMPSectionCore (I := I) (M := M) G S X N T where
  symmetric := h.symmetric
  barrierRegularity := h.barrierRegularity
  unitSlabCompact := h.unitSlabCompact
  metricQuadCont := h.metricQuadCont
  tensorQuadCont := h.tensorQuadCont
  barrierFixedContinuous := h.barrierFixedContinuous





omit [IsManifold I 2 M] in
theorem ofCompact
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hMetric :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (metricBundleQuad (I := I) (M := M) G
            (Set.Icc t0 (t0 + delta))))
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (tensorSecBundleQuad (I := I) (M := M) S
            (Set.Icc t0 (t0 + delta))))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) G
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta)))
    (hSigns :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
          (nablaBarrier : TensorNabla1Family (I := I) (M := M)),
        (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
          G (twoTensorSecToFamily (I := I) (M := M) S) X N
          nabla2Barrier nablaBarrier epsilon delta t0) ->
        (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
          G N (Set.Icc t0 (t0 + delta))) ->
        (d : TensorFirstNullData (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0) ->
        TensorFirstNullScalarSigns (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S) X N epsilon delta t0 d) :
    TensorWMPSectionReg (I := I) (M := M) G S X N T where
  symmetric := hsym
  barrierRegularity := hbar
  unitSlabCompact := by
    intro delta t0 hdelta hsub
    exact metricUnitTimeSlab_icc_compact_of_bundle (I := I) (M := M)
      G t0 (t0 + delta) (G t0)
      (by
        simpa [metricBundleQuad] using hMetric delta t0 hdelta hsub)
  metricQuadCont := hMetric
  tensorQuadCont := hTensor
  barrierFixedContinuous := hFixed
  firstNullScalarSigns := hSigns



omit [IsManifold I 2 M] in
theorem ofTotal
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hMetric :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (metricTensorField (I := I) (G q.1.1) q.2.proj)))
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (S q.1.1 q.2.proj)))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) G
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta)))
    (hSigns :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
          (nablaBarrier : TensorNabla1Family (I := I) (M := M)),
        (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
          G (twoTensorSecToFamily (I := I) (M := M) S) X N
          nabla2Barrier nablaBarrier epsilon delta t0) ->
        (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
          G N (Set.Icc t0 (t0 + delta))) ->
        (d : TensorFirstNullData (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0) ->
        TensorFirstNullScalarSigns (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S) X N epsilon delta t0 d) :
    TensorWMPSectionReg (I := I) (M := M) G S X N T :=
  ofCompact (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N) (T := T)
    hsym hbar
    (fun delta t0 hdelta hsub =>
      DifferentialGeometry.Integral.Connection.metricFamQuadCont (I := I) (M := M)
        G (Set.Icc t0 (t0 + delta))
        (hMetric delta t0 hdelta hsub))
    (fun delta t0 hdelta hsub =>
      DifferentialGeometry.Integral.Connection.tensorQuadCont (I := I) (M := M)
        S (Set.Icc t0 (t0 + delta))
        (hTensor delta t0 hdelta hsub))
    hFixed hSigns




omit [IsManifold I 2 M] in
theorem ofSmoothMetric
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) (fun t => G.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (S q.1.1 q.2.proj)))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) (fun t => G.metric t)
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta)))
    (hSigns :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
          (nablaBarrier : TensorNabla1Family (I := I) (M := M)),
        (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
          (fun t => G.metric t) (twoTensorSecToFamily (I := I) (M := M) S) X N
          nabla2Barrier nablaBarrier epsilon delta t0) ->
        (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
          (fun t => G.metric t) N (Set.Icc t0 (t0 + delta))) ->
        (d : TensorFirstNullData (I := I) (M := M) (fun t => G.metric t)
          (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0) ->
        TensorFirstNullScalarSigns (I := I) (M := M) (fun t => G.metric t)
          (twoTensorSecToFamily (I := I) (M := M) S) X N epsilon delta t0 d) :
    TensorWMPSectionReg (I := I) (M := M) (fun t => G.metric t) S X N T :=
  ofTotal (I := I) (M := M)
    (G := fun t => G.metric t) (S := S) (X := X) (N := N) (T := T)
    hsym hbar
    (fun delta t0 hdelta hsub =>
      metricTensor_tangentBundle_cont_of_metricFamilySmoothOn
        (I := I) (M := M) G hG
        (fun t ht => hTsub (hsub ht)))
    hTensor hFixed hSigns



omit [IsManifold I 2 M] in
theorem toRaw
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (h : TensorWMPSectionReg (I := I) (M := M) G S X N T) :
    TensorWMPRegularityOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N T where
  symmetric := h.symmetric
  bilinear := fun t _ht x => twoTensorSecToFamily_bilin (I := I) (M := M) S t x
  barrierRegularity := h.barrierRegularity
  firstNullCompactness := by
    intro epsilon delta t0 hepsilon hdelta hsub
    exact TensorFirstNullCompactnessOn.of_section_timeSlab (I := I) (M := M)
      G S epsilon delta t0
      (h.unitSlabCompact delta t0 hdelta hsub)
      (barrierTimeCont (I := I) (M := M) G S epsilon delta t0
        (Set.Icc t0 (t0 + delta))
        (h.tensorQuadCont delta t0 hdelta hsub)
        (h.metricQuadCont delta t0 hdelta hsub))
      (h.barrierFixedContinuous epsilon delta t0 hepsilon hdelta hsub)
  firstNullScalarSigns := h.firstNullScalarSigns

end TensorWMPSectionReg

end

end DifferentialGeometry.Integral.Connection
