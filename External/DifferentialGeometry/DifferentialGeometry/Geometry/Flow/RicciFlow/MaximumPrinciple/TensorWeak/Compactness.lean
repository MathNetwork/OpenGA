import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.TensorWeak.FirstNull


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








structure TensorFirstNullCompactnessOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) : Prop where
  firstNull_of_failure :
    (∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t0) x) ->
    (¬ TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0)
      (Set.Icc t0 (t0 + delta))) ->
    Nonempty (TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)

namespace TensorFirstNullCompactnessOn



omit [IsManifold I 2 M] in
theorem of_section
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real)
    (hcompact :
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentSlab (I := I) (M := M) G t0 (t0 + delta))))
    (hunit_cont :
      Continuous
        (barrierUnitQuad (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0 t0 (t0 + delta)))
    (hfixed_cont :
      ∀ x (v : TangentSpace I x),
        ContinuousOn
          (fun t : Real =>
            tensorBarrierFamily (I := I) (M := M) G
              (twoTensorSecToFamily (I := I) (M := M) S)
              epsilon delta t0 t x v v)
          (Set.Icc t0 (t0 + delta))) :
    TensorFirstNullCompactnessOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0 := by
  classical
  let Sraw : TwoTensorFamily (I := I) (M := M) :=
    twoTensorSecToFamily (I := I) (M := M) S
  let B : TwoTensorFamily (I := I) (M := M) :=
    tensorBarrierFamily (I := I) (M := M) G Sraw epsilon delta t0
  let slab := MetricUnitTangentSlab (I := I) (M := M) G t0 (t0 + delta)
  let φ : slab -> Real :=
    barrierUnitQuad (I := I) (M := M) G Sraw epsilon delta t0 t0 (t0 + delta)
  let Z : Set slab := {p | φ p ≤ 0}
  refine ⟨?_⟩
  intro hinit_pos hfail
  have hZclosed : IsClosed Z := by
    have hclosed : IsClosed ((Set.Iic (0 : Real)) : Set Real) := isClosed_Iic
    simpa [Z, φ] using hclosed.preimage hunit_cont
  have hZcompact : IsCompact Z := by
    simpa [Z] using hcompact.inter_right hZclosed
  obtain ⟨pbad, hpbad_neg⟩ :=
    failure_unitSlab (I := I) (M := M) G S epsilon delta t0 t0
      (t0 + delta) hfail
  have hZne : Z.Nonempty := ⟨pbad, le_of_lt hpbad_neg⟩
  obtain ⟨p1, hp1Z, hmin⟩ :=
    hZcompact.exists_isMinOn hZne
      (metricUnitSlab_timeVal_cont (I := I) (M := M) G t0 (t0 + delta)).continuousOn
  let t1 : Real := p1.1.1
  let x1 : M := MetricUnitTangent.base (I := I) (M := M) p1.2
  let v1 : TangentSpace I x1 := MetricUnitTangent.vec (I := I) (M := M) p1.2
  have hp1_time : t1 ∈ Set.Icc t0 (t0 + delta) := by
    simp [t1]
  have hp1_nonpos : φ p1 ≤ 0 := hp1Z
  have hv1_ne : v1 ≠ 0 := by
    intro hv
    have hbad : (0 : Real) = 1 := by
      simpa [v1, hv] using
        (MetricUnitTangent.unit (I := I) (M := M) p1.2)
    norm_num at hbad
  have ht1_ne_t0 : t1 ≠ t0 := by
    intro ht1eq
    have hpos : 0 < φ p1 := by
      have hpos_raw := hinit_pos x1 v1 hv1_ne
      simpa [φ, barrierUnitQuad, Sraw, B, t1, x1, v1, ht1eq] using hpos_raw
    linarith
  have ht1_gt : t0 < t1 := lt_of_le_of_ne hp1_time.1 (Ne.symm ht1_ne_t0)
  have hnonneg_until :
      ∀ t, t ∈ Set.Icc t0 t1 ->
        ∀ x, TwoTensorNonnegativeAt (I := I) (M := M) (B t) x := by
    intro t ht x v
    by_contra hnot
    have hneg : B t x v v < 0 := lt_of_not_ge hnot
    have ht_full : t ∈ Set.Icc t0 (t0 + delta) :=
      ⟨ht.1, le_trans ht.2 hp1_time.2⟩
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · obtain ⟨q, hq_time, hqneg⟩ :=
        negBarrier_unitSlab (I := I) (M := M) G S epsilon delta t0
          t0 (t0 + delta) t ht_full x v (by simpa [B, Sraw] using hneg)
      have hqZ : q ∈ Z := by
        simpa [Z, φ] using le_of_lt hqneg
      have hmin_q := hmin hqZ
      have hqtime : q.1.1 = t := hq_time
      have ht1_le_t : t1 ≤ t := by
        have ht1_le_q : (p1.1.1 : Real) ≤ q.1.1 := by
          exact (Subtype.coe_le_coe).2 hmin_q
        simpa [t1, hqtime] using ht1_le_q
      linarith
    · have hneg_t1 :
          B t1 x v v < 0 := by
        simpa [heq] using hneg
      obtain ⟨s, hs_full, hs_lt, hsneg⟩ :=
        exists_left_neg_of_continuousOn (a := t0) (b := t1)
          (c := t0 + delta) ht1_gt hp1_time.2
          (by simpa [B, Sraw] using hfixed_cont x v)
          hneg_t1
      obtain ⟨q, hq_time, hqneg⟩ :=
        negBarrier_unitSlab (I := I) (M := M) G S epsilon delta t0
          t0 (t0 + delta) s hs_full x v (by simpa [B, Sraw] using hsneg)
      have hqZ : q ∈ Z := by
        simpa [Z, φ] using le_of_lt hqneg
      have hmin_q := hmin hqZ
      have hqtime : q.1.1 = s := hq_time
      have ht1_le_s : t1 ≤ s := by
        have ht1_le_q : (p1.1.1 : Real) ≤ q.1.1 := by
          exact (Subtype.coe_le_coe).2 hmin_q
        simpa [t1, hqtime] using ht1_le_q
      linarith
  have hnonneg_p1 : 0 ≤ φ p1 := by
    have hquad :=
      hnonneg_until t1 ⟨le_of_lt ht1_gt, le_rfl⟩ x1 v1
    simpa [φ, barrierUnitQuad, B, Sraw, t1, x1, v1] using hquad
  have hnullφ : φ p1 = 0 := le_antisymm hp1_nonpos hnonneg_p1
  refine Nonempty.intro
    { t1 := t1
      x1 := x1
      v := v1
      t1_mem := ⟨ht1_gt, hp1_time.2⟩
      v_ne_zero := hv1_ne
      unit := by
        exact MetricUnitTangent.unit (I := I) (M := M) p1.2
      nonnegative_until := ?_
      null := ?_ }
  · intro t ht x
    simpa [B, Sraw] using hnonneg_until t ht x
  · simpa [φ, barrierUnitQuad, B, Sraw, t1, x1, v1] using hnullφ

end TensorFirstNullCompactnessOn

namespace TensorFirstNullCompactnessOn




omit [IsManifold I 2 M] in
theorem of_section_timeSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real)
    (hcompact :
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
            (Set.Icc t0 (t0 + delta)))))
    (hunit_cont :
      Continuous
        (barrierTimeSlabQuad (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0 (Set.Icc t0 (t0 + delta))))
    (hfixed_cont :
      ∀ x (v : TangentSpace I x),
        ContinuousOn
          (fun t : Real =>
            tensorBarrierFamily (I := I) (M := M) G
              (twoTensorSecToFamily (I := I) (M := M) S)
              epsilon delta t0 t x v v)
          (Set.Icc t0 (t0 + delta))) :
    TensorFirstNullCompactnessOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0 := by
  classical
  let Sraw : TwoTensorFamily (I := I) (M := M) :=
    twoTensorSecToFamily (I := I) (M := M) S
  let B : TwoTensorFamily (I := I) (M := M) :=
    tensorBarrierFamily (I := I) (M := M) G Sraw epsilon delta t0
  let slab := MetricUnitTangentTimeSlab (I := I) (M := M) G
    (Set.Icc t0 (t0 + delta))
  let φ : slab -> Real :=
    barrierTimeSlabQuad (I := I) (M := M) G Sraw epsilon delta t0
      (Set.Icc t0 (t0 + delta))
  let Z : Set slab := {p | φ p ≤ 0}
  refine ⟨?_⟩
  intro hinit_pos hfail
  have hZclosed : IsClosed Z := by
    have hclosed : IsClosed ((Set.Iic (0 : Real)) : Set Real) := isClosed_Iic
    simpa [Z, φ] using hclosed.preimage hunit_cont
  have hZcompact : IsCompact Z := by
    simpa [Z] using hcompact.inter_right hZclosed
  obtain ⟨pbad, hpbad_neg⟩ :=
    failure_timeSlab (I := I) (M := M) G S epsilon delta t0
      (K := Set.Icc t0 (t0 + delta)) hfail
  have hZne : Z.Nonempty := ⟨pbad, le_of_lt hpbad_neg⟩
  obtain ⟨p1, hp1Z, hmin⟩ :=
    hZcompact.exists_isMinOn hZne
      (metricUnitTimeSlab_timeVal_cont (I := I) (M := M)
        G (Set.Icc t0 (t0 + delta))).continuousOn
  let t1 : Real := MetricUnitTangentTimeSlab.time (I := I) (M := M) p1
  let x1 : M := MetricUnitTangentTimeSlab.base (I := I) (M := M) p1
  let v1 : TangentSpace I x1 :=
    MetricUnitTangentTimeSlab.vec (I := I) (M := M) p1
  have hp1_time : t1 ∈ Set.Icc t0 (t0 + delta) := by
    simpa [t1] using
      (MetricUnitTangentTimeSlab.time_mem (I := I) (M := M) p1)
  have hp1_nonpos : φ p1 ≤ 0 := hp1Z
  have hv1_ne : v1 ≠ 0 := by
    intro hv
    have hbad : (0 : Real) = 1 := by
      simpa [v1, hv] using
        (MetricUnitTangentTimeSlab.unit (I := I) (M := M) p1)
    norm_num at hbad
  have ht1_ne_t0 : t1 ≠ t0 := by
    intro ht1eq
    have hpos : 0 < φ p1 := by
      have hpos_raw := hinit_pos x1 v1 hv1_ne
      simpa [φ, barrierTimeSlabQuad, Sraw, B, t1, x1, v1, ht1eq] using hpos_raw
    linarith
  have ht1_gt : t0 < t1 := lt_of_le_of_ne hp1_time.1 (Ne.symm ht1_ne_t0)
  have hnonneg_until :
      ∀ t, t ∈ Set.Icc t0 t1 ->
        ∀ x, TwoTensorNonnegativeAt (I := I) (M := M) (B t) x := by
    intro t ht x v
    by_contra hnot
    have hneg : B t x v v < 0 := lt_of_not_ge hnot
    have ht_full : t ∈ Set.Icc t0 (t0 + delta) :=
      ⟨ht.1, le_trans ht.2 hp1_time.2⟩
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · obtain ⟨q, hq_time, hqneg⟩ :=
        negBarrier_timeSlab (I := I) (M := M) G S epsilon delta t0 t
          (K := Set.Icc t0 (t0 + delta)) ht_full x v
          (by simpa [B, Sraw] using hneg)
      have hqZ : q ∈ Z := by
        simpa [Z, φ] using le_of_lt hqneg
      have hmin_q := hmin hqZ
      have ht1_le_t : t1 ≤ t := by
        simpa [t1, hq_time] using hmin_q
      linarith
    · have hneg_t1 :
          B t1 x v v < 0 := by
        simpa [heq] using hneg
      obtain ⟨s, hs_full, hs_lt, hsneg⟩ :=
        exists_left_neg_of_continuousOn (a := t0) (b := t1)
          (c := t0 + delta) ht1_gt hp1_time.2
          (by simpa [B, Sraw] using hfixed_cont x v)
          hneg_t1
      obtain ⟨q, hq_time, hqneg⟩ :=
        negBarrier_timeSlab (I := I) (M := M) G S epsilon delta t0 s
          (K := Set.Icc t0 (t0 + delta)) hs_full x v
          (by simpa [B, Sraw] using hsneg)
      have hqZ : q ∈ Z := by
        simpa [Z, φ] using le_of_lt hqneg
      have hmin_q := hmin hqZ
      have ht1_le_s : t1 ≤ s := by
        simpa [t1, hq_time] using hmin_q
      linarith
  have hnonneg_p1 : 0 ≤ φ p1 := by
    have hquad :=
      hnonneg_until t1 ⟨le_of_lt ht1_gt, le_rfl⟩ x1 v1
    simpa [φ, barrierTimeSlabQuad, B, Sraw, t1, x1, v1] using hquad
  have hnullφ : φ p1 = 0 := le_antisymm hp1_nonpos hnonneg_p1
  refine Nonempty.intro
    { t1 := t1
      x1 := x1
      v := v1
      t1_mem := ⟨ht1_gt, hp1_time.2⟩
      v_ne_zero := hv1_ne
      unit := by
        exact MetricUnitTangentTimeSlab.unit (I := I) (M := M) p1
      nonnegative_until := ?_
      null := ?_ }
  · intro t ht x
    simpa [B, Sraw] using hnonneg_until t ht x
  · simpa [φ, barrierTimeSlabQuad, B, Sraw, t1, x1, v1] using hnullφ

end TensorFirstNullCompactnessOn








def TensorBarrierStrictSupersolutionOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
    (nablaBarrier : TensorNabla1Family (I := I) (M := M))
    (epsilon delta t0 : Real) : Prop :=
  TensorParabolicStrictInequalityWithDriftOn (I := I) (M := M) G
    (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0) X N
    nabla2Barrier nablaBarrier
    (Set.Ioc t0 (t0 + delta))

omit [IsManifold I 2 M] in
theorem strictBarrier_of_est
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 T : Real}
    (hsub : Set.Ioc t0 (t0 + delta) ⊆ Set.Ioc 0 T)
    (hbase : TensorParabolicInequalityWithDriftOn (I := I) (M := M)
      G S X N nabla2S nablaS T)
    (hest : ∀ timeDerivS : TensorQuadraticFormFamily (I := I) (M := M),
      ∃ timeDerivBarrier : TensorQuadraticFormFamily (I := I) (M := M),
        TensorBarrierLocalEst (I := I) (M := M) G S X N
          nabla2S nablaS nabla2Barrier nablaBarrier epsilon delta t0
          (Set.Ioc t0 (t0 + delta)) timeDerivS timeDerivBarrier) :
    TensorBarrierStrictSupersolutionOn (I := I) (M := M) G S X N
      nabla2Barrier nablaBarrier epsilon delta t0 := by
  exact strictParabolic_of_est (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2S := nabla2S) (nablaS := nablaS)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    (epsilon := epsilon) (delta := delta) (t0 := t0) (T := T)
    (U := Set.Ioc t0 (t0 + delta)) hsub hbase hest







def TensorBarrierUniformStrictOnSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (delta t0 : Real) : Prop :=
  ∀ epsilon : Real, SmallBarrierEps epsilon ->
    ∃ nabla2Barrier : TensorNabla2Family (I := I) (M := M),
    ∃ nablaBarrier : TensorNabla1Family (I := I) (M := M),
      TensorBarrierStrictSupersolutionOn (I := I) (M := M) G S X N
        nabla2Barrier nablaBarrier epsilon delta t0









def TensorFirstNullScalarSigns
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (epsilon delta t0 : Real)
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0) : Prop :=
  ∃ timeDeriv laplacian drift reaction : Real,
    timeDeriv ≤ 0 ∧
    0 ≤ laplacian ∧
    drift = 0 ∧
    0 ≤ reaction ∧
    drift + reaction < timeDeriv - laplacian



structure TensorStrictCert
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (epsilon delta t0 : Real) : Type _ where
  nabla2Barrier : TensorNabla2Family (I := I) (M := M)
  nablaBarrier : TensorNabla1Family (I := I) (M := M)
  strict :
    TensorBarrierStrictSupersolutionOn (I := I) (M := M) G S X N
      nabla2Barrier nablaBarrier epsilon delta t0
  signs :
    TensorNullEigenvectorCondition (I := I) (M := M) G N
      (Set.Icc t0 (t0 + delta)) ->
    ∀ d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0,
      TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d


def TensorStrictCertSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (delta t0 : Real) : Prop :=
  ∀ epsilon : Real, SmallBarrierEps epsilon ->
    Nonempty (TensorStrictCert (I := I) (M := M) G S X N
      epsilon delta t0)











omit [IsManifold I 2 M] in
theorem scalarSigns_of_eval
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (hsym : TwoTensorFamilySymmetricOn (I := I) (M := M) S
      (Set.Icc t0 (t0 + delta)))
    (hbilin :
      ∀ t, t ∈ Set.Icc t0 (t0 + delta) -> ∀ x,
        TwoTensorBilinearAt (I := I) (M := M) (S t) x)
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (laplacian drift : Real)
    (htime_nonpos :
      ∀ timeDeriv : TensorQuadraticFormFamily (I := I) (M := M),
        (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
          ∀ x, ∀ v : TangentSpace I x,
            HasDerivWithinAt
              (fun s : Real =>
                tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
                  s x v v)
              (timeDeriv t x v) (Set.Ioc t0 (t0 + delta)) t) ->
        timeDeriv d.t1 d.x1 d.v ≤ 0)
    (hlaplacian_nonneg : 0 ≤ laplacian)
    (hdrift_zero : drift = 0)
    (hheat_eq :
      tensorHeatWithDrift2QuadMetricAt (I := I) (G d.t1) (X d.t1)
          (nabla2Barrier d.t1 d.x1) (nablaBarrier d.t1 d.x1) d.v =
        laplacian + drift) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  rcases hstrict with ⟨timeDeriv, hderiv, hstrict_eval⟩
  let reaction : Real :=
    N d.t1 (G d.t1)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
      d.x1 d.v d.v
  have ht1_mem_slab : d.t1 ∈ Set.Icc t0 (t0 + delta) :=
    ⟨le_of_lt d.t1_mem.1, d.t1_mem.2⟩
  have ht1_mem_until : d.t1 ∈ Set.Icc t0 d.t1 :=
    ⟨le_of_lt d.t1_mem.1, le_rfl⟩
  have hbarrier_nonnegative :
      TwoTensorNonnegativeAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
        d.x1 :=
    d.nonnegative_until d.t1 ht1_mem_until d.x1
  have hbarrier_symmetric :
      TwoTensorSymmetricAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
        d.x1 :=
    barrierSymmAt (I := I) (M := M)
      (G := G) (S := S) (epsilon := epsilon) (delta := delta)
      (t0 := t0) (t := d.t1) (x := d.x1)
      (hsym d.t1 ht1_mem_slab d.x1)
  have hbarrier_bilinear :
      TwoTensorBilinearAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
        d.x1 :=
    barrierBilinearAt (I := I) (M := M)
      (G := G) (S := S) (epsilon := epsilon) (delta := delta)
      (t0 := t0) (t := d.t1) (x := d.x1)
      (hbilin d.t1 ht1_mem_slab d.x1)
  have hreaction_nonneg : 0 ≤ reaction := by
    simpa [reaction] using
      hnull d.t1 ht1_mem_slab
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
        d.x1 hbarrier_symmetric hbarrier_bilinear hbarrier_nonnegative d.v d.null
  have hstrict_at :
      tensorHeatWithDrift2QuadMetricAt (I := I) (G d.t1) (X d.t1)
          (nabla2Barrier d.t1 d.x1) (nablaBarrier d.t1 d.x1) d.v +
        reaction <
        timeDeriv d.t1 d.x1 d.v := by
    simpa [reaction] using
      hstrict_eval d.t1 d.t1_mem d.x1 d.v d.v_ne_zero
  refine ⟨timeDeriv d.t1 d.x1 d.v, laplacian, drift, reaction,
    htime_nonpos timeDeriv hderiv, hlaplacian_nonneg, hdrift_zero,
    hreaction_nonneg, ?_⟩
  linarith







omit [IsManifold I 2 M] in
theorem scalarSigns_of_parts
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (hsym : TwoTensorFamilySymmetricOn (I := I) (M := M) S
      (Set.Icc t0 (t0 + delta)))
    (hbilin :
      ∀ t, t ∈ Set.Icc t0 (t0 + delta) -> ∀ x,
        TwoTensorBilinearAt (I := I) (M := M) (S t) x)
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (laplacian drift : Real)
    (htime_nonpos :
      ∀ timeDeriv : TensorQuadraticFormFamily (I := I) (M := M),
        (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
          ∀ x, ∀ v : TangentSpace I x,
            HasDerivWithinAt
              (fun s : Real =>
                tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
                  s x v v)
              (timeDeriv t x v) (Set.Ioc t0 (t0 + delta)) t) ->
        timeDeriv d.t1 d.x1 d.v ≤ 0)
    (hlaplacian_nonneg : 0 ≤ laplacian)
    (hdrift_zero : drift = 0)
    (hlap :
      metricTraceFirstTwo0SAt (I := I) (G d.t1)
        (nabla2Barrier d.t1 d.x1) (vec2 d.v d.v) = laplacian)
    (hdrift :
      (nablaBarrier d.t1 d.x1)
        (Fin.cons (X d.t1 d.x1) (vec2 d.v d.v)) = drift) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  exact scalarSigns_of_eval (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    hstrict hnull hsym hbilin d laplacian drift htime_nonpos hlaplacian_nonneg
    hdrift_zero
    (heatQuad_eq_parts (I := I) (G d.t1) (X d.t1)
      (nabla2Barrier d.t1 d.x1) (nablaBarrier d.t1 d.x1) d.v
      laplacian drift hlap hdrift)







omit [IsManifold I 2 M] in
theorem scalarSigns_of_lap
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (hsym : TwoTensorFamilySymmetricOn (I := I) (M := M) S
      (Set.Icc t0 (t0 + delta)))
    (hbilin :
      ∀ t, t ∈ Set.Icc t0 (t0 + delta) -> ∀ x,
        TwoTensorBilinearAt (I := I) (M := M) (S t) x)
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (laplacian : Real)
    (htime_nonpos :
      ∀ timeDeriv : TensorQuadraticFormFamily (I := I) (M := M),
        (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
          ∀ x, ∀ v : TangentSpace I x,
            HasDerivWithinAt
              (fun s : Real =>
                tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
                  s x v v)
              (timeDeriv t x v) (Set.Ioc t0 (t0 + delta)) t) ->
        timeDeriv d.t1 d.x1 d.v ≤ 0)
    (hlaplacian_nonneg : 0 ≤ laplacian)
    (hlap :
      metricTraceFirstTwo0SAt (I := I) (G d.t1)
        (nabla2Barrier d.t1 d.x1) (vec2 d.v d.v) = laplacian)
    (hdrift :
      (nablaBarrier d.t1 d.x1)
        (Fin.cons (X d.t1 d.x1) (vec2 d.v d.v)) = 0) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  exact scalarSigns_of_parts (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    hstrict hnull hsym hbilin d laplacian 0 htime_nonpos
    hlaplacian_nonneg rfl hlap hdrift







omit [IsManifold I 2 M] in
theorem scalarSigns_of_lap_firstNull
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (hsym : TwoTensorFamilySymmetricOn (I := I) (M := M) S
      (Set.Icc t0 (t0 + delta)))
    (hbilin :
      ∀ t, t ∈ Set.Icc t0 (t0 + delta) -> ∀ x,
        TwoTensorBilinearAt (I := I) (M := M) (S t) x)
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (laplacian : Real)
    (hlaplacian_nonneg : 0 ≤ laplacian)
    (hlap :
      metricTraceFirstTwo0SAt (I := I) (G d.t1)
        (nabla2Barrier d.t1 d.x1) (vec2 d.v d.v) = laplacian)
    (hdrift :
      (nablaBarrier d.t1 d.x1)
        (Fin.cons (X d.t1 d.x1) (vec2 d.v d.v)) = 0) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  exact scalarSigns_of_lap (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    hstrict hnull hsym hbilin d laplacian
    (fun timeDeriv hderiv => firstNullTime_nonpos (I := I) (M := M)
      d timeDeriv hderiv)
    hlaplacian_nonneg hlap hdrift






theorem scalarSigns_of_local
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (hsym : TwoTensorFamilySymmetricOn (I := I) (M := M) S
      (Set.Icc t0 (t0 + delta)))
    (hbilin :
      ∀ t, t ∈ Set.Icc t0 (t0 + delta) -> ∀ x,
        TwoTensorBilinearAt (I := I) (M := M) (S t) x)
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (laplacian : Real)
    (hlaplacian_nonneg : 0 ≤ laplacian)
    (hlap :
      metricTraceFirstTwo0SAt (I := I) (G d.t1)
        (nabla2Barrier d.t1 d.x1) (vec2 d.v d.v) = laplacian)
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (Xsec :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hX : X d.t1 d.x1 = Xsec d.x1)
    (hnabla : nablaBarrier d.t1 d.x1 = nablaB d.x1)
    (hV : ∀ q : Fin 2, V q d.x1 = d.v)
    (hphi :
      extDerivFun (I := I) (fun p : M => B p (fun q : Fin 2 => V q p))
        d.x1 (Xsec d.x1) = 0)
    (hcovV :
      ∀ q : Fin 2, ((cov (fun p : M => V q p) d.x1) (Xsec d.x1)) = 0) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  apply scalarSigns_of_lap_firstNull (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    hstrict hnull hsym hbilin d laplacian hlaplacian_nonneg hlap
  rw [hnabla, hX]
  exact nablaEval_zero (I := I) (M := M) hreal Xsec V hV hphi hcovV







theorem scalarSigns_of_local_min
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (hsym : TwoTensorFamilySymmetricOn (I := I) (M := M) S
      (Set.Icc t0 (t0 + delta)))
    (hbilin :
      ∀ t, t ∈ Set.Icc t0 (t0 + delta) -> ∀ x,
        TwoTensorBilinearAt (I := I) (M := M) (S t) x)
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (Xsec :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hlapMin : LaplacianNonnegativeAtSpatialMin (I := I) cov (G d.t1))
    (hlap :
      metricTraceFirstTwo0SAt (I := I) (G d.t1)
        (nabla2Barrier d.t1 d.x1) (vec2 d.v d.v) =
      laplacian (I := I) cov (G d.t1)
        (fun p : M => B p (fun q : Fin 2 => V q p)) d.x1)
    (hX : X d.t1 d.x1 = Xsec d.x1)
    (hnabla : nablaBarrier d.t1 d.x1 = nablaB d.x1)
    (hV : ∀ q : Fin 2, V q d.x1 = d.v)
    (hB :
      ∀ p : M,
        B p (fun q : Fin 2 => V q p) =
          tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
            d.t1 p (V 0 p) (V 0 p))
    (hcovV :
      ∀ q : Fin 2, ((cov (fun p : M => V q p) d.x1) (Xsec d.x1)) = 0)
    (hmdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => B p (fun q : Fin 2 => V q p)) d.x1)
    (hmdiff_near :
      ∀ᶠ y in nhds d.x1,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => B p (fun q : Fin 2 => V q p)) y)
    (hgrad :
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G d.t1)
          (fun p : M => B p (fun q : Fin 2 => V q p)) y) d.x1) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  let phi : M -> Real := fun p => B p (fun q : Fin 2 => V q p)
  have hmin : IsLocalMin phi d.x1 :=
    firstNullLocalMin (I := I) (M := M) d V hV hB
  have hphi :
      extDerivFun (I := I) phi d.x1 (Xsec d.x1) = 0 := by
    have hmf :
        mfderiv I 𝓘(Real, Real) phi d.x1 = 0 :=
      mfderiv_eq_zero_at_spatial_min (I := I) hmin hmdiff
    rw [DifferentialGeometry.extDerivFun_real_eq_mfderiv, hmf]
    rfl
  have hlap_nonneg :
      0 ≤ laplacian (I := I) cov (G d.t1) phi d.x1 :=
    hlapMin hmin hmdiff hmdiff_near hgrad
  exact scalarSigns_of_local (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    (cov := cov) (B := B) (nablaB := nablaB)
    hstrict hnull hsym hbilin d (laplacian (I := I) cov (G d.t1) phi d.x1)
    hlap_nonneg hlap hreal Xsec V hX hnabla hV hphi hcovV





theorem scalarSigns_oneSec
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (hsym : TwoTensorFamilySymmetricOn (I := I) (M := M) S
      (Set.Icc t0 (t0 + delta)))
    (hbilin :
      ∀ t, t ∈ Set.Icc t0 (t0 + delta) -> ∀ x,
        TwoTensorBilinearAt (I := I) (M := M) (S t) x)
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (Xsec Vsec :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hlapMin : LaplacianNonnegativeAtSpatialMin (I := I) cov (G d.t1))
    (hessPhi :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 d.x1)
    (hlap :
      ScalarLaplacianRealizesTraceAt (I := I) cov (G d.t1)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) hessPhi)
    (hslots :
      ∀ U W : TangentSpace I d.x1,
        (nabla2Barrier d.t1 d.x1)
          (metricTraceInput (I := I) U W (vec2 (I := I) d.v d.v)) =
        hessPhi (vec2 (I := I) U W))
    (hX : X d.t1 d.x1 = Xsec d.x1)
    (hnabla : nablaBarrier d.t1 d.x1 = nablaB d.x1)
    (hV : Vsec d.x1 = d.v)
    (hB :
      ∀ p : M,
        B p (vec2 (I := I) (Vsec p) (Vsec p)) =
          tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
            d.t1 p (Vsec p) (Vsec p))
    (hcovV : ((cov (fun p : M => Vsec p) d.x1) (Xsec d.x1)) = 0)
    (hmdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) d.x1)
    (hmdiff_near :
      ∀ᶠ y in nhds d.x1,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) y)
    (hgrad :
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G d.t1)
          (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) y) d.x1) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  let V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun _ => Vsec
  have hV' : ∀ q : Fin 2, V q d.x1 = d.v := by
    intro q
    exact hV
  have hB' :
      ∀ p : M,
        B p (fun q : Fin 2 => V q p) =
          tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
            d.t1 p (V 0 p) (V 0 p) := by
    intro p
    simpa [V, vec2_self_eq_const] using hB p
  have hcovV' :
      ∀ q : Fin 2, ((cov (fun p : M => V q p) d.x1) (Xsec d.x1)) = 0 := by
    intro q
    simpa [V] using hcovV
  have hlap' :
      metricTraceFirstTwo0SAt (I := I) (G d.t1)
        (nabla2Barrier d.t1 d.x1) (vec2 d.v d.v) =
      laplacian (I := I) cov (G d.t1)
        (fun p : M => B p (fun q : Fin 2 => V q p)) d.x1 := by
    have hraw :
        metricTraceFirstTwo0SAt (I := I) (G d.t1)
          (nabla2Barrier d.t1 d.x1) (vec2 d.v d.v) =
        laplacian (I := I) cov (G d.t1)
          (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) d.x1 := by
      exact lapTrace_of_slots (I := I) cov (G d.t1)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p)))
        (nabla2Barrier d.t1 d.x1) (vec2 (I := I) d.v d.v)
        hessPhi hlap hslots
    simpa [V, vec2_self_eq_const] using hraw
  have hmdiff' :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => B p (fun q : Fin 2 => V q p)) d.x1 := by
    simpa [V, vec2_self_eq_const] using hmdiff
  have hmdiff_near' :
      ∀ᶠ y in nhds d.x1,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => B p (fun q : Fin 2 => V q p)) y := by
    simpa [V, vec2_self_eq_const] using hmdiff_near
  have hgrad' :
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G d.t1)
          (fun p : M => B p (fun q : Fin 2 => V q p)) y) d.x1 := by
    simpa [V, vec2_self_eq_const] using hgrad
  exact scalarSigns_of_local_min (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    (cov := cov) (B := B) (nablaB := nablaB)
    hstrict hnull hsym hbilin d hreal Xsec V hlapMin hlap' hX hnabla hV' hB'
    hcovV' hmdiff' hmdiff_near' hgrad'






theorem scalarSigns_hess
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4}
    {du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1}
    {Hess : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (hsym : TwoTensorFamilySymmetricOn (I := I) (M := M) S
      (Set.Icc t0 (t0 + delta)))
    (hbilin :
      ∀ t, t ∈ Set.Icc t0 (t0 + delta) -> ∀ x,
        TwoTensorBilinearAt (I := I) (M := M) (S t) x)
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (hreal1 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (hreal2 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaB nabla2B)
    (Xsec Vsec :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hlapMin : LaplacianNonnegativeAtSpatialMin (I := I) cov (G d.t1))
    (hnabla2 : nabla2Barrier d.t1 d.x1 = nabla2B d.x1)
    (hkerL : ∀ w : TangentSpace I d.x1, B d.x1 (vec2 (I := I) d.v w) = 0)
    (hkerR : ∀ w : TangentSpace I d.x1, B d.x1 (vec2 (I := I) w d.v) = 0)
    (hdu :
      DuFieldRealizes (I := I)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) du)
    (hHess :
      HessianRealizesNablaDuAt (I := I) cov du Hess d.x1)
    (hlap :
      ScalarLaplacianRealizesTraceAt (I := I) cov (G d.t1)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) (Hess d.x1))
    (hAreg :
      ∀ Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _),
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, ((cov (fun q : M => Vsec q) p) (Y p))⟩ :
              TotalSpace E (TangentSpace I : M -> Type _))) d.x1)
    (hX : X d.t1 d.x1 = Xsec d.x1)
    (hnabla : nablaBarrier d.t1 d.x1 = nablaB d.x1)
    (hV : Vsec d.x1 = d.v)
    (hB :
      ∀ p : M,
        B p (vec2 (I := I) (Vsec p) (Vsec p)) =
          tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
            d.t1 p (Vsec p) (Vsec p))
    (hcovV :
      ∀ W : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _),
        ((cov (fun p : M => Vsec p) d.x1) (W d.x1)) = 0)
    (hmdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) d.x1)
    (hmdiff_near :
      ∀ᶠ y in nhds d.x1,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) y)
    (hgrad :
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G d.t1)
          (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) y) d.x1) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  have hslots :
      ∀ U W : TangentSpace I d.x1,
        (nabla2Barrier d.t1 d.x1)
          (metricTraceInput (I := I) U W (vec2 (I := I) d.v d.v)) =
        (Hess d.x1) (vec2 (I := I) U W) := by
    intro U W
    rw [hnabla2]
    exact nabla2Eval_hess_slots (I := I) (M := M)
      hreal1 hreal2 Vsec hV hcovV hkerL hkerR hdu hHess hAreg U W
  exact scalarSigns_oneSec (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    (cov := cov) (B := B) (nablaB := nablaB)
    hstrict hnull hsym hbilin d hreal1 Xsec Vsec hlapMin (Hess d.x1) hlap hslots
    hX hnabla hV hB (hcovV Xsec) hmdiff hmdiff_near hgrad









theorem scalarSigns_covHess
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (hcovInf : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G (twoTensorSecToFamily (I := I) (M := M) S) X N
      nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S)
        (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov (G d.t1))
    (hreal1 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (hreal2 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaB nabla2B)
    (Xsec :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hlapMin : LaplacianNonnegativeAtSpatialMin (I := I) cov (G d.t1))
    (hnabla2 : nabla2Barrier d.t1 d.x1 = nabla2B d.x1)
    (hkerB_left :
      ∀ w : TangentSpace I d.x1,
        B d.x1 (vec2 (I := I) d.v w) =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 d.v w)
    (hkerB_right :
      ∀ w : TangentSpace I d.x1,
        B d.x1 (vec2 (I := I) w d.v) =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 w d.v)
    (hX : X d.t1 d.x1 = Xsec d.x1)
    (hnabla : nablaBarrier d.t1 d.x1 = nablaB d.x1)
    (hB :
      ∀ Vsec :
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        Vsec d.x1 = d.v ->
        ∀ p : M,
          B p (vec2 (I := I) (Vsec p) (Vsec p)) =
            tensorBarrierFamily (I := I) (M := M) G
              (twoTensorSecToFamily (I := I) (M := M) S)
              epsilon delta t0 d.t1 p (Vsec p) (Vsec p)) :
    TensorFirstNullScalarSigns (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N epsilon delta t0 d := by
  obtain ⟨Vsec, hV, hcovVall⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov1 d.x1 d.v
  let phi : M -> Real := fun p => B p (vec2 (I := I) (Vsec p) (Vsec p))
  have hphi :
      ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) phi := by
    let Slots : Fin 2 ->
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      fun _ => Vsec
    have hraw :=
      TensorMultilinear.contMDiff_tensor0SField_apply (I := I) (M := M) B Slots
    simpa [phi, Slots, vec2_self_eq_const] using hraw
  let du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
    duSec (I := I) phi hphi
  let Hess : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y :=
    fun y => hessianSec (I := I) cov hcovInf phi hphi y
  have hdu : DuFieldRealizes (I := I) phi du := by
    simpa [du] using duSec_realizes (I := I) phi hphi
  have hHess : HessianRealizesNablaDuAt (I := I) cov du Hess d.x1 := by
    simpa [du, Hess] using
      hessianSec_realizesAt (I := I) cov hcovInf phi hphi d.x1
  have hlap :
      ScalarLaplacianRealizesTraceAt (I := I) cov (G d.t1) phi (Hess d.x1) := by
    simpa [Hess] using
      scalarLap_smooth (I := I) cov hcovInf (G d.t1) hmc phi hphi
  have hkerL : ∀ w : TangentSpace I d.x1,
      B d.x1 (vec2 (I := I) d.v w) = 0 :=
    firstNullFieldKerL (I := I) (M := M) hsym d hkerB_left
  have hkerR : ∀ w : TangentSpace I d.x1,
      B d.x1 (vec2 (I := I) w d.v) = 0 :=
    firstNullFieldKerR (I := I) (M := M) hsym d hkerB_right
  have hmdiff :
      MDifferentiableAt I 𝓘(Real, Real) phi d.x1 :=
    hphi.contMDiffAt.mdifferentiableAt (by simp)
  have hmdiff_near :
      ∀ᶠ y in nhds d.x1, MDifferentiableAt I 𝓘(Real, Real) phi y := by
    refine Filter.Eventually.of_forall ?_
    intro y
    exact hphi.contMDiffAt.mdifferentiableAt (by simp)
  have hgrad :
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G d.t1) phi y) d.x1 :=
    gradientFun_mdiffAt (I := I) (G d.t1) hphi d.x1
  have hAreg :
      ∀ Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _),
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, ((cov (fun q : M => Vsec q) p) (Y p))⟩ :
              TotalSpace E (TangentSpace I : M -> Type _))) d.x1 := by
    intro Y
    simpa using
      CovariantDerivative.smoothSections_cov_contMDiffAt_one
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        cov hcov1 Y Vsec d.x1
  exact scalarSigns_hess (I := I) (M := M)
    (G := G) (S := twoTensorSecToFamily (I := I) (M := M) S)
    (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    (cov := cov) (B := B) (nablaB := nablaB) (nabla2B := nabla2B)
    (du := du) (Hess := Hess)
    hstrict hnull hsym
    (fun t _ht x => twoTensorSecToFamily_bilin (I := I) (M := M) S t x)
    d hreal1 hreal2 Xsec Vsec hlapMin hnabla2
    hkerL hkerR hdu hHess hlap hAreg
    hX hnabla hV (hB Vsec hV) hcovVall hmdiff hmdiff_near
    (by simpa [phi] using hgrad)






theorem scalarSigns_secHess
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nablaS : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2S : TensorNabla2SecFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    {cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G (twoTensorSecToFamily (I := I) (M := M) S) X N
      (fun t x => nabla2S t x) (fun t x => nablaS t x)
      epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S)
        (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0)
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (cov d.t1) (1 : WithTop ℕ∞))
    (hcovInf : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (cov d.t1) (∞ : WithTop ℕ∞))
    (hmc : ∀ t : Real,
      DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) (cov t) (G t))
    (hS : TensorSpatialDerivs (I := I) (M := M) cov S nablaS nabla2S)
    (Xsec :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hlapMin : LaplacianNonnegativeAtSpatialMin (I := I) (cov d.t1) (G d.t1))
    (hX : X d.t1 d.x1 = Xsec d.x1) :
    TensorFirstNullScalarSigns (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N epsilon delta t0 d := by
  let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0) d.t1
  have hbarDerivs :
      TensorSpatialDerivs (I := I) (M := M) cov
        (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0)
        nablaS nabla2S :=
    barrierDerivs (I := I) (M := M) cov G S nablaS nabla2S
      epsilon delta t0 hmc hS
  have hkerB_left :
      ∀ w : TangentSpace I d.x1,
        B d.x1 (vec2 (I := I) d.v w) =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 d.v w := by
    intro w
    simpa [B] using
      tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0
        d.t1 d.x1 d.v w
  have hkerB_right :
      ∀ w : TangentSpace I d.x1,
        B d.x1 (vec2 (I := I) w d.v) =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 w d.v := by
    intro w
    simpa [B] using
      tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0
        d.t1 d.x1 w d.v
  have hB :
      ∀ Vsec :
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        Vsec d.x1 = d.v ->
        ∀ p : M,
          B p (vec2 (I := I) (Vsec p) (Vsec p)) =
            tensorBarrierFamily (I := I) (M := M) G
              (twoTensorSecToFamily (I := I) (M := M) S)
              epsilon delta t0 d.t1 p (Vsec p) (Vsec p) := by
    intro Vsec _hV p
    simpa [B] using
      tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0
        d.t1 p (Vsec p) (Vsec p)
  exact scalarSigns_covHess (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := fun t x => nabla2S t x)
    (nablaBarrier := fun t x => nablaS t x)
    (cov := cov d.t1) (B := B) (nablaB := nablaS d.t1)
    (nabla2B := nabla2S d.t1)
    hcov1 hcovInf hstrict hnull hsym d (hmc d.t1)
    (hbarDerivs.first d.t1) (hbarDerivs.second d.t1) Xsec hlapMin
    rfl hkerB_left hkerB_right hX rfl hB












theorem scalarSigns_covZero
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (hsym : TwoTensorFamilySymmetricOn (I := I) (M := M) S
      (Set.Icc t0 (t0 + delta)))
    (hbilin :
      ∀ t, t ∈ Set.Icc t0 (t0 + delta) -> ∀ x,
        TwoTensorBilinearAt (I := I) (M := M) (S t) x)
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (Xsec :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hlapMin : LaplacianNonnegativeAtSpatialMin (I := I) cov (G d.t1))
    (hX : X d.t1 d.x1 = Xsec d.x1)
    (hnabla : nablaBarrier d.t1 d.x1 = nablaB d.x1)
    (hessPhi :
      ∀ Vsec :
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        Vsec d.x1 = d.v ->
        Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 d.x1)
    (hlap :
      ∀ (Vsec :
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
        (hV : Vsec d.x1 = d.v),
        ScalarLaplacianRealizesTraceAt (I := I) cov (G d.t1)
          (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p)))
          (hessPhi Vsec hV))
    (hslots :
      ∀ Vsec :
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        ∀ hV : Vsec d.x1 = d.v,
          ∀ U W : TangentSpace I d.x1,
            (nabla2Barrier d.t1 d.x1)
              (metricTraceInput (I := I) U W (vec2 (I := I) d.v d.v)) =
            (hessPhi Vsec hV) (vec2 (I := I) U W))
    (hB :
      ∀ Vsec :
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        Vsec d.x1 = d.v ->
        ∀ p : M,
          B p (vec2 (I := I) (Vsec p) (Vsec p)) =
            tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
              d.t1 p (Vsec p) (Vsec p))
    (hmdiff :
      ∀ Vsec :
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        Vsec d.x1 = d.v ->
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) d.x1)
    (hmdiff_near :
      ∀ Vsec :
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        Vsec d.x1 = d.v ->
        ∀ᶠ y in nhds d.x1,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) y)
    (hgrad :
      ∀ Vsec :
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        Vsec d.x1 = d.v ->
        MDiffAt (T% fun y : M =>
          gradientFun (I := I) (G d.t1)
            (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) y) d.x1) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  obtain ⟨Vsec, hV, hcovVall⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov d.x1 d.v
  exact scalarSigns_oneSec (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    (cov := cov) (B := B) (nablaB := nablaB)
    hstrict hnull hsym hbilin d hreal Xsec Vsec hlapMin (hessPhi Vsec hV)
    (hlap Vsec hV) (hslots Vsec hV) hX hnabla hV (hB Vsec hV) (hcovVall Xsec)
    (hmdiff Vsec hV) (hmdiff_near Vsec hV) (hgrad Vsec hV)

end

end DifferentialGeometry.Integral.Connection
