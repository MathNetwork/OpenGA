import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.TensorWeak.Limit


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








private theorem reaction_bound_of_abs {a b R : Real}
    (h : |a - b| ≤ R) : b ≤ a + R := by
  have hnegR : -R ≤ -|a - b| := neg_le_neg h
  have hnegabs : -|a - b| ≤ a - b := neg_abs_le (a - b)
  have hle : -R ≤ a - b := le_trans hnegR hnegabs
  linarith



private theorem reactionErr_lt_gain
    {K epsilon delta c g : Real}
    (hK : 0 ≤ K)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta)
    (hc_nonneg : 0 ≤ c)
    (hc_le : c ≤ 2 * delta)
    (hsmall : 4 * K * delta < 1)
    (hg : 0 < g) :
    K * |epsilon * c * g| < (epsilon / 2) * g := by
  have harg_nonneg : 0 ≤ epsilon * c * g := by
    exact mul_nonneg (mul_nonneg (le_of_lt hepsilon) hc_nonneg) (le_of_lt hg)
  rw [abs_of_nonneg harg_nonneg]
  have hkc_le : K * c ≤ K * (2 * delta) :=
    mul_le_mul_of_nonneg_left hc_le hK
  have htwo : K * (2 * delta) < 1 / 2 := by
    nlinarith
  have hkc_lt : K * c < 1 / 2 := lt_of_le_of_lt hkc_le htwo
  have hepsg_pos : 0 < epsilon * g := mul_pos hepsilon hg
  have hmul := mul_lt_mul_of_pos_right hkc_lt hepsg_pos
  nlinarith




omit [IsManifold I 2 M] in
theorem strictBarrierBounds
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T t0 : Real}
    (hreg : TensorWMPCore (I := I) (M := M) G S X N T)
    (ht0 : t0 ∈ Set.Icc 0 T)
    (ht0T : t0 < T)
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    (_hbase : TensorParabolicInequalityWithDriftOn (I := I) (M := M)
      G S X N nabla2S nablaS T) :
    ∃ delta0 K : Real,
      0 < delta0 ∧ 0 ≤ K ∧ t0 + delta0 ≤ T ∧
        ∀ delta : Real,
          0 < delta ->
          delta ≤ delta0 ->
          4 * K * delta < 1 ->
          ∀ epsilon : Real,
            SmallBarrierEps epsilon ->
            ∃ metricDeriv : TensorQuadraticFormFamily (I := I) (M := M),
            ∃ reactionErr : TensorQuadraticFormFamily (I := I) (M := M),
            ∃ metricGain : TensorQuadraticFormFamily (I := I) (M := M),
              (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  HasDerivWithinAt (fun s : Real => (G s).inner x v v)
                    (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t) ∧
              (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  metricGain t x v ≤
                    epsilon * ((G t).inner x v v +
                      (delta + t - t0) * metricDeriv t x v)) ∧
              (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  N t (G t)
                      (tensorBarrierFamily (I := I) (M := M)
                        G S epsilon delta t0 t) x v v ≤
                    N t (G t) (S t) x v v + reactionErr t x v) ∧
              (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  v ≠ 0 -> reactionErr t x v < metricGain t x v) := by
  obtain ⟨delta0, hdelta0, hdelta0T, hmetric⟩ :=
    hreg.barrierRegularity.metricGainControl t0 ht0 ht0T
  have hsub0 : Set.Icc t0 (t0 + delta0) ⊆ Set.Icc 0 T := by
    intro t ht
    exact ⟨le_trans ht0.1 ht.1, le_trans ht.2 hdelta0T⟩
  obtain ⟨K, hK, hLip⟩ :=
    hreg.barrierRegularity.smallBarrierLip delta0 t0 hdelta0 hsub0
  refine ⟨delta0, K, hdelta0, hK, hdelta0T, ?_⟩
  intro delta hdelta hdelta_le hsmall epsilon hepsilon
  obtain ⟨metricDeriv, hmetric_deriv, hmetric_gain⟩ :=
    hmetric delta hdelta hdelta_le epsilon hepsilon
  let reactionErr : TensorQuadraticFormFamily (I := I) (M := M) :=
    fun t x v =>
      K * |epsilon * (delta + t - t0) * (G t).inner x v v|
  let metricGain : TensorQuadraticFormFamily (I := I) (M := M) :=
    fun t x v => (epsilon / 2) * (G t).inner x v v
  refine ⟨metricDeriv, reactionErr, metricGain, hmetric_deriv, ?_, ?_, ?_⟩
  · intro t ht x v
    exact hmetric_gain t ht x v
  · intro t ht x v
    have ht_closed : t ∈ Set.Icc t0 (t0 + delta) := ⟨le_of_lt ht.1, ht.2⟩
    have hLip_t := hLip epsilon delta hepsilon hdelta hdelta_le t ht_closed x v
    dsimp [reactionErr]
    exact reaction_bound_of_abs (a := N t (G t) (S t) x v v)
      (b := N t (G t)
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t) x v v)
      hLip_t
  · intro t ht x v hv
    dsimp [reactionErr, metricGain]
    have htime_nonneg : 0 ≤ delta + t - t0 := by
      have ht_sub : 0 ≤ t - t0 := sub_nonneg.mpr (le_of_lt ht.1)
      have hsum : 0 ≤ delta + (t - t0) :=
        add_nonneg (le_of_lt hdelta) ht_sub
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsum
    have htime_le : delta + t - t0 ≤ 2 * delta := by
      have ht_le : t - t0 ≤ delta := by linarith [ht.2]
      linarith
    exact reactionErr_lt_gain (K := K) (epsilon := epsilon) (delta := delta)
      (c := delta + t - t0) (g := (G t).inner x v v)
      hK hepsilon.1 hdelta htime_nonneg htime_le hsmall ((G t).pos x v hv)










structure TensorParabolicSupersolutionWithDriftOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (nabla2S : TensorNabla2Family (I := I) (M := M))
    (nablaS : TensorNabla1Family (I := I) (M := M))
    (T : Real) : Prop where
  evaluatedInequality :
    TensorParabolicInequalityWithDriftOn (I := I) (M := M) G S X N
      nabla2S nablaS T








omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem tensorBarrier_initial_positive
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t0) :
    ∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t0) x := by
  intro x v hv
  have hS : 0 ≤ S t0 x v v := hinit x v
  have hmetric : 0 < (G t0).inner x v v := (G t0).pos x v hv
  have hcoeff : 0 < epsilon * (delta + t0 - t0) := by
    have htime : delta + t0 - t0 = delta := by ring
    rw [htime]
    exact mul_pos hepsilon hdelta
  have hbarrier : 0 < epsilon * (delta + t0 - t0) * (G t0).inner x v v :=
    mul_pos hcoeff hmetric
  exact add_pos_of_nonneg_of_pos hS hbarrier


private theorem exists_small_delta
    {t0 T delta0 K : Real}
    (hroom : t0 < T)
    (hdelta0 : 0 < delta0)
    (hK : 0 ≤ K) :
    ∃ delta : Real,
      0 < delta ∧ delta ≤ delta0 ∧ t0 + delta ≤ T ∧ 4 * K * delta < 1 := by
  let delta : Real :=
    min (min (delta0 / 2) ((T - t0) / 2)) (1 / (4 * K + 1))
  have hdelta0_half_pos : 0 < delta0 / 2 := by positivity
  have hroom_half_pos : 0 < (T - t0) / 2 := by linarith
  have hden_pos : 0 < 4 * K + 1 := by nlinarith
  have hrecip_pos : 0 < 1 / (4 * K + 1) := by positivity
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact lt_min (lt_min hdelta0_half_pos hroom_half_pos) hrecip_pos
  have hdelta_le_half0 : delta ≤ delta0 / 2 := by
    dsimp [delta]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hdelta_le_room_half : delta ≤ (T - t0) / 2 := by
    dsimp [delta]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hdelta_le_recip : delta ≤ 1 / (4 * K + 1) := by
    dsimp [delta]
    exact min_le_right _ _
  have hdelta_le_delta0 : delta ≤ delta0 := by linarith
  have hdelta_le_room : delta ≤ T - t0 := by linarith
  have htime : t0 + delta ≤ T := by linarith
  have hcoef_nonneg : 0 ≤ 4 * K := by nlinarith
  have hmul_le :
      4 * K * delta ≤ 4 * K * (1 / (4 * K + 1)) := by
    exact mul_le_mul_of_nonneg_left hdelta_le_recip hcoef_nonneg
  have hfrac_lt : 4 * K * (1 / (4 * K + 1)) < 1 := by
    field_simp [hden_pos.ne']
    nlinarith
  have hstrict : 4 * K * delta < 1 := lt_of_le_of_lt hmul_le hfrac_lt
  exact Exists.intro delta
    (And.intro hdelta_pos
      (And.intro hdelta_le_delta0 (And.intro htime hstrict)))





omit [IsManifold I 2 M] in
theorem tensorBarrier_strict_supersolution
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {t0 T : Real}
    (ht0 : t0 ∈ Set.Icc 0 T)
    (ht0T : t0 < T)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N nabla2S nablaS T) :
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      TensorBarrierUniformStrictOnSlab (I := I) (M := M) G S X N
        delta t0 := by
  obtain ⟨delta0, K, hdelta0, hK, _hdelta0T, hstrict_bounds⟩ :=
    strictBarrierBounds (I := I) (M := M)
      hreg.toCore ht0 ht0T hparabolic.evaluatedInequality
  obtain ⟨delta, hdelta, hdelta_le_delta0, hdeltaT, hsmall⟩ :=
    exists_small_delta (t0 := t0) (T := T) (delta0 := delta0) (K := K)
      ht0T hdelta0 hK
  refine ⟨delta, hdelta, hdeltaT, ?_⟩
  intro epsilon hepsilon
  obtain ⟨metricDeriv, reactionErr, metricGain,
      hmetric_deriv, hgain, hreaction, hmargin⟩ :=
    hstrict_bounds delta hdelta hdelta_le_delta0 hsmall epsilon hepsilon
  refine ⟨nabla2S, nablaS, ?_⟩
  have hsubInterior : Set.Ioc t0 (t0 + delta) ⊆ Set.Ioc 0 T := by
    intro t ht
    exact ⟨lt_of_le_of_lt ht0.1 ht.1, le_trans ht.2 hdeltaT⟩
  exact strictBarrier_of_derivEst (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2S := nabla2S) (nablaS := nablaS)
    (epsilon := epsilon) (delta := delta) (t0 := t0) (T := T)
    hsubInterior hparabolic.evaluatedInequality
    metricDeriv reactionErr metricGain hmetric_deriv hgain hreaction hmargin









omit [IsManifold I 2 M] in
theorem certSlab_of_reg
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {t0 T : Real}
    (ht0 : t0 ∈ Set.Icc 0 T)
    (ht0T : t0 < T)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N nabla2S nablaS T) :
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      TensorStrictCertSlab (I := I) (M := M) G S X N delta t0 := by
  obtain ⟨delta, hdelta, hdeltaT, hstrict_uniform⟩ :=
    tensorBarrier_strict_supersolution (I := I) (M := M)
      (G := G) (S := S) (X := X) (N := N)
      ht0 ht0T hreg hparabolic
  refine ⟨delta, hdelta, hdeltaT, ?_⟩
  intro epsilon hepsilon
  obtain ⟨nabla2Barrier, nablaBarrier, hstrict⟩ :=
    hstrict_uniform epsilon hepsilon
  refine ⟨?_⟩
  refine
    { nabla2Barrier := nabla2Barrier
      nablaBarrier := nablaBarrier
      strict := hstrict
      signs := ?_ }
  intro hnull d
  have hsub : Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T := by
    intro t ht
    exact ⟨le_trans ht0.1 ht.1, le_trans ht.2 hdeltaT⟩
  exact
    hreg.firstNullScalarSigns epsilon delta t0 hepsilon.1 hdelta hsub
      nabla2Barrier nablaBarrier hstrict hnull d



theorem strictCert_sec
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nablaS : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2S : TensorNabla2SecFamily (I := I) (M := M)}
    {cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {t0 T : Real}
    (ht0 : t0 ∈ Set.Icc 0 T)
    (ht0T : t0 < T)
    (hreg : TensorWMPSectionCore (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G (twoTensorSecToFamily (I := I) (M := M) S) X N
      (fun t x => nabla2S t x) (fun t x => nablaS t x) T)
    (hcov1 : ∀ t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (cov t) (1 : WithTop ℕ∞))
    (hcovInf : ∀ t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (cov t) (∞ : WithTop ℕ∞))
    (hmc : ∀ t : Real,
      DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) (cov t) (G t))
    (hS : TensorSpatialDerivs (I := I) (M := M) cov S nablaS nabla2S) :
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      TensorStrictCertSlab (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N delta t0 := by
  obtain ⟨delta0, K, hdelta0, hK, _hdelta0T, hstrict_bounds⟩ :=
    strictBarrierBounds (I := I) (M := M)
      hreg.toRaw ht0 ht0T hparabolic.evaluatedInequality
  obtain ⟨delta, hdelta, hdelta_le_delta0, hdeltaT, hsmall⟩ :=
    exists_small_delta (t0 := t0) (T := T) (delta0 := delta0) (K := K)
      ht0T hdelta0 hK
  refine ⟨delta, hdelta, hdeltaT, ?_⟩
  intro epsilon hepsilon
  obtain ⟨metricDeriv, reactionErr, metricGain,
      hmetric_deriv, hgain, hreaction, hmargin⟩ :=
    hstrict_bounds delta hdelta hdelta_le_delta0 hsmall epsilon hepsilon
  have hsubInterior : Set.Ioc t0 (t0 + delta) ⊆ Set.Ioc 0 T := by
    intro t ht
    exact ⟨lt_of_le_of_lt ht0.1 ht.1, le_trans ht.2 hdeltaT⟩
  have hsubClosed : Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T := by
    intro t ht
    exact ⟨le_trans ht0.1 ht.1, le_trans ht.2 hdeltaT⟩
  have hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G (twoTensorSecToFamily (I := I) (M := M) S) X N
      (fun t x => nabla2S t x) (fun t x => nablaS t x)
      epsilon delta t0 :=
    strictBarrier_of_derivEst (I := I) (M := M)
      (G := G) (S := twoTensorSecToFamily (I := I) (M := M) S)
      (X := X) (N := N)
      (nabla2S := fun t x => nabla2S t x)
      (nablaS := fun t x => nablaS t x)
      (epsilon := epsilon) (delta := delta) (t0 := t0) (T := T)
      hsubInterior hparabolic.evaluatedInequality
      metricDeriv reactionErr metricGain hmetric_deriv hgain hreaction hmargin
  refine ⟨⟨fun t x => nabla2S t x, fun t x => nablaS t x, hstrict, ?_⟩⟩
  intro hnull d
  obtain ⟨Xsec, hXsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      d.x1 (X d.t1 d.x1)
  have hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S)
        (Set.Icc t0 (t0 + delta)) := by
    intro t ht x
    exact hreg.symmetric t (hsubClosed ht) x
  exact scalarSigns_secHess (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nablaS := nablaS) (nabla2S := nabla2S) (cov := cov)
    hstrict hnull hsym d (hcov1 d.t1) (hcovInf d.t1) hmc hS Xsec
    (laplacianNonnegativeAtSpatialMin_of_metricCompatible
      (I := I) (cov d.t1) (G d.t1) (hmc d.t1))
    hXsec.symm




omit [IsManifold I 2 M] in
theorem certSlab_of_sectionReg
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {t0 T : Real}
    (ht0 : t0 ∈ Set.Icc 0 T)
    (ht0T : t0 < T)
    (hreg : TensorWMPSectionReg (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G (twoTensorSecToFamily (I := I) (M := M) S) X N
      nabla2S nablaS T) :
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      TensorStrictCertSlab (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N delta t0 :=
  certSlab_of_reg (I := I) (M := M)
    (G := G) (S := twoTensorSecToFamily (I := I) (M := M) S)
    (X := X) (N := N) ht0 ht0T hreg.toRaw hparabolic

end

end DifferentialGeometry.Integral.Connection
