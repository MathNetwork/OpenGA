import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.TensorWeak
import DifferentialGeometry.Geometry.Flow.RicciFlow.Realized.RicciFlow
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Unit
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.TimeSlab

set_option autoImplicit false
set_option linter.style.longLine false








noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]



private theorem metric_gain_of_quad_bound
    {epsilon delta c C g dg : Real}
    (hepsilon : 0 < epsilon)
    (hC : 0 ≤ C)
    (hdelta_le : delta ≤ 1 / (4 * C + 1))
    (hc_nonneg : 0 ≤ c)
    (hc_le : c ≤ 2 * delta)
    (hg : 0 ≤ g)
    (hdg : |dg| ≤ C * g) :
    (epsilon / 2) * g ≤ epsilon * (g + c * dg) := by
  have hden_pos : 0 < 4 * C + 1 := by nlinarith
  have hCdelta_le : C * delta ≤ C * (1 / (4 * C + 1)) :=
    mul_le_mul_of_nonneg_left hdelta_le hC
  have hCfrac_le : C * (1 / (4 * C + 1)) ≤ 1 / 4 := by
    field_simp [hden_pos.ne']
    nlinarith [hC]
  have hCdelta_quarter : C * delta ≤ 1 / 4 :=
    le_trans hCdelta_le hCfrac_le
  have hCc_le : C * c ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left hc_le hC
    nlinarith [h, hCdelta_quarter]
  have hCc_g_le : (C * c) * g ≤ (1 / 2) * g :=
    mul_le_mul_of_nonneg_right hCc_le hg
  have hdg_lower : -(C * g) ≤ dg := (abs_le.mp hdg).1
  have hc_dg_lower : c * (-(C * g)) ≤ c * dg :=
    mul_le_mul_of_nonneg_left hdg_lower hc_nonneg
  have hinside : (1 / 2) * g ≤ g + c * dg := by
    nlinarith [hCc_g_le, hc_dg_lower]
  have hmul := mul_le_mul_of_nonneg_left hinside (le_of_lt hepsilon)
  nlinarith



omit [IsManifold I 2 M] in
omit [FiniteDimensional ℝ E] in
theorem metricGainAt_of_timeSlabQuadBound
    (G : Real -> SmoothRiemannianMetric I M)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {T t0 deltaRaw : Real}
    (hdeltaRaw : 0 < deltaRaw)
    (hdeltaRawT : t0 + deltaRaw ≤ T)
    (hderiv :
      ∀ delta : Real, 0 < delta -> delta ≤ deltaRaw ->
        ∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
          ∀ x, ∀ v : TangentSpace I x,
            HasDerivWithinAt (fun s : Real => (G s).inner x v v)
              (quad02 (I := I) (M := M) (A t x) v)
              (Set.Icc t0 (t0 + delta)) t)
    (hcompact : IsCompact
      (Set.univ : Set
        (MetricUnitTangentTimeSlab (I := I) (M := M) G
          (Set.Icc t0 (t0 + deltaRaw)))))
    (hcont : Continuous
      (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G
          (Set.Icc t0 (t0 + deltaRaw)) =>
        |quad02 (I := I) (M := M)
          (A (MetricUnitTangentTimeSlab.time (I := I) (M := M) p)
            (MetricUnitTangentTimeSlab.base (I := I) (M := M) p))
          (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)|)) :
    ∃ delta0 : Real,
      0 < delta0 ∧ t0 + delta0 ≤ T ∧
        ∀ delta : Real,
          0 < delta ->
          delta ≤ delta0 ->
            ∀ epsilon : Real,
              SmallBarrierEps epsilon ->
            ∃ metricDeriv : TensorQuadraticFormFamily (I := I) (M := M),
              (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  HasDerivWithinAt (fun s : Real => (G s).inner x v v)
                    (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t) ∧
              (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  (epsilon / 2) * (G t).inner x v v ≤
                    epsilon * ((G t).inner x v v +
                      (delta + t - t0) * metricDeriv t x v)) := by
  obtain ⟨C, hC, hbound⟩ :=
    compactUnitTimeSlab_absBound (I := I) (M := M) G A
      (Set.Icc t0 (t0 + deltaRaw))
      hcompact hcont
  let delta0 : Real := min deltaRaw (1 / (4 * C + 1))
  have hden_pos : 0 < 4 * C + 1 := by nlinarith
  have hrecip_pos : 0 < 1 / (4 * C + 1) := by positivity
  have hdelta0_pos : 0 < delta0 := by
    dsimp [delta0]
    exact lt_min hdeltaRaw hrecip_pos
  have hdelta0_le_raw : delta0 ≤ deltaRaw := by
    dsimp [delta0]
    exact min_le_left _ _
  have hdelta0_le_recip : delta0 ≤ 1 / (4 * C + 1) := by
    dsimp [delta0]
    exact min_le_right _ _
  have hdelta0T : t0 + delta0 ≤ T := by
    have hle : delta0 ≤ deltaRaw := hdelta0_le_raw
    linarith
  refine ⟨delta0, hdelta0_pos, hdelta0T, ?_⟩
  intro delta hdelta hdelta_le epsilon hepsilon
  have hdelta_le_raw : delta ≤ deltaRaw := le_trans hdelta_le hdelta0_le_raw
  have hdelta_le_recip : delta ≤ 1 / (4 * C + 1) :=
    le_trans hdelta_le hdelta0_le_recip
  let metricDeriv : TensorQuadraticFormFamily (I := I) (M := M) :=
    fun t x v => quad02 (I := I) (M := M) (A t x) v
  refine ⟨metricDeriv, ?_, ?_⟩
  · intro t ht x v
    exact hderiv delta hdelta hdelta_le_raw t ht x v
  · intro t ht x v
    have htime_nonneg : 0 ≤ delta + t - t0 := by
      have ht_sub : 0 ≤ t - t0 := sub_nonneg.mpr (le_of_lt ht.1)
      have hsum : 0 ≤ delta + (t - t0) :=
        add_nonneg (le_of_lt hdelta) ht_sub
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsum
    have htime_le : delta + t - t0 ≤ 2 * delta := by
      have ht_le : t - t0 ≤ delta := by linarith [ht.2]
      linarith
    have hmetric_nonneg : 0 ≤ (G t).inner x v v := by
      by_cases hv : v = 0
      · subst v
        simp
      · exact le_of_lt ((G t).pos x v hv)
    have ht_raw : t ∈ Set.Icc t0 (t0 + deltaRaw) := by
      exact ⟨le_of_lt ht.1, by linarith⟩
    exact metric_gain_of_quad_bound
      (epsilon := epsilon) (delta := delta) (c := delta + t - t0)
      (C := C) (g := (G t).inner x v v)
      (dg := metricDeriv t x v)
      hepsilon.1 hC hdelta_le_recip htime_nonneg htime_le hmetric_nonneg
      (hbound t ht_raw x v)



omit [IsManifold I 2 M] in
theorem metricGainAt_of_totalCont
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    (G : Real -> SmoothRiemannianMetric I M)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {T t0 deltaRaw : Real}
    (hdeltaRaw : 0 < deltaRaw)
    (hdeltaRawT : t0 + deltaRaw ≤ T)
    (hderiv :
      ∀ delta : Real, 0 < delta -> delta ≤ deltaRaw ->
        ∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
          ∀ x, ∀ v : TangentSpace I x,
            HasDerivWithinAt (fun s : Real => (G s).inner x v v)
              (quad02 (I := I) (M := M) (A t x) v)
              (Set.Icc t0 (t0 + delta)) t)
    (hGcont :
      Continuous
        (metricTimeBundleQuad (I := I) (M := M) G
          (Set.Icc t0 (t0 + deltaRaw))))
    (hAcont :
      Continuous (fun q :
          {t : Real // t ∈ Set.Icc t0 (t0 + deltaRaw)} × TangentBundle I M =>
        TotalSpace.mk' (Tensor0SModel 2 Real E)
          (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
          (A q.1.1 q.2.proj))) :
    ∃ delta0 : Real,
      0 < delta0 ∧ t0 + delta0 ≤ T ∧
        ∀ delta : Real,
          0 < delta ->
          delta ≤ delta0 ->
            ∀ epsilon : Real,
              SmallBarrierEps epsilon ->
            ∃ metricDeriv : TensorQuadraticFormFamily (I := I) (M := M),
              (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  HasDerivWithinAt (fun s : Real => (G s).inner x v v)
                    (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t) ∧
              (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  (epsilon / 2) * (G t).inner x v v ≤
                    epsilon * ((G t).inner x v v +
                      (delta + t - t0) * metricDeriv t x v)) := by
  apply metricGainAt_of_timeSlabQuadBound (I := I) (M := M)
    (G := G) (A := A) (T := T) (t0 := t0) (deltaRaw := deltaRaw)
    hdeltaRaw hdeltaRawT hderiv
  · exact metricUnitTimeSlab_icc_compact_of_bundle (I := I) (M := M)
      G t0 (t0 + deltaRaw) (G t0) hGcont
  · exact timeSlabAbsQuadCont (I := I) (M := M)
      G A (Set.Icc t0 (t0 + deltaRaw)) hAcont







omit [IsManifold I 2 M] in
theorem metricGainAt_of_metricVariationDerivAt
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : RicciTensorField (I := I) (M := M) Real)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {T t0 deltaRaw : Real}
    (hdeltaRaw : 0 < deltaRaw)
    (hdeltaRawT : t0 + deltaRaw ≤ T)
    (hEq : ∀ t, t ∈ Set.Ioc t0 (t0 + deltaRaw) ->
      MetricVariationEquationDerivAt (I := I) G Ric t)
    (hA :
      ∀ t, t ∈ Set.Ioc t0 (t0 + deltaRaw) ->
        ∀ x, ∀ v : TangentSpace I x,
          quad02 (I := I) (M := M) (A t x) v =
            (-2 : Real) * Ric t x v v)
    (hGcont :
      Continuous
        (metricTimeBundleQuad (I := I) (M := M) (fun t => G.metric t)
          (Set.Icc t0 (t0 + deltaRaw))))
    (hAcont :
      Continuous (fun q :
          {t : Real // t ∈ Set.Icc t0 (t0 + deltaRaw)} × TangentBundle I M =>
        TotalSpace.mk' (Tensor0SModel 2 Real E)
          (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
          (A q.1.1 q.2.proj))) :
    ∃ delta0 : Real,
      0 < delta0 ∧ t0 + delta0 ≤ T ∧
        ∀ delta : Real,
          0 < delta ->
          delta ≤ delta0 ->
            ∀ epsilon : Real,
              SmallBarrierEps epsilon ->
            ∃ metricDeriv : TensorQuadraticFormFamily (I := I) (M := M),
              (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  HasDerivWithinAt
                    (fun s : Real => (G.metric s).inner x v v)
                    (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t) ∧
              (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  (epsilon / 2) * (G.metric t).inner x v v ≤
                    epsilon * ((G.metric t).inner x v v +
                      (delta + t - t0) * metricDeriv t x v)) := by
  apply metricGainAt_of_totalCont (I := I) (M := M)
    (G := fun t => G.metric t) (A := A)
    (T := T) (t0 := t0) (deltaRaw := deltaRaw)
    hdeltaRaw hdeltaRawT
  · intro delta hdelta hdelta_le t ht x v
    have ht_raw : t ∈ Set.Ioc t0 (t0 + deltaRaw) := ⟨ht.1, by linarith [ht.2, hdelta_le]⟩
    have hderiv := hEq t ht_raw x v v
    have hval := hA t ht_raw x v
    rw [hval]
    exact hderiv.hasDerivWithinAt
  · exact hGcont
  · exact hAcont






omit [IsManifold I 2 M] in
theorem metricGainControl_of_metricVariation
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : RicciTensorField (I := I) (M := M) Real)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {T : Real}
    (hlocal :
      ∀ t0 : Real,
        t0 ∈ Set.Icc 0 T ->
        t0 < T ->
        ∃ deltaRaw : Real,
          0 < deltaRaw ∧ t0 + deltaRaw ≤ T ∧
          (∀ t, t ∈ Set.Ioc t0 (t0 + deltaRaw) ->
            MetricVariationEquationDerivAt (I := I) G Ric t) ∧
          (∀ t, t ∈ Set.Ioc t0 (t0 + deltaRaw) ->
            ∀ x, ∀ v : TangentSpace I x,
              quad02 (I := I) (M := M) (A t x) v =
                (-2 : Real) * Ric t x v v) ∧
          Continuous
            (metricTimeBundleQuad (I := I) (M := M) (fun t => G.metric t)
              (Set.Icc t0 (t0 + deltaRaw))) ∧
          Continuous (fun q :
              {t : Real // t ∈ Set.Icc t0 (t0 + deltaRaw)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (A q.1.1 q.2.proj))) :
    ∀ t0 : Real,
      t0 ∈ Set.Icc 0 T ->
      t0 < T ->
      ∃ delta0 : Real,
        0 < delta0 ∧ t0 + delta0 ≤ T ∧
          ∀ delta : Real,
            0 < delta ->
            delta ≤ delta0 ->
            ∀ epsilon : Real,
              SmallBarrierEps epsilon ->
              ∃ metricDeriv : TensorQuadraticFormFamily (I := I) (M := M),
                (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                  ∀ x, ∀ v : TangentSpace I x,
                    HasDerivWithinAt
                      (fun s : Real => (G.metric s).inner x v v)
                      (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t) ∧
                (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                  ∀ x, ∀ v : TangentSpace I x,
                    (epsilon / 2) * (G.metric t).inner x v v ≤
                      epsilon * ((G.metric t).inner x v v +
                        (delta + t - t0) * metricDeriv t x v)) := by
  intro t0 ht0 ht0T
  rcases hlocal t0 ht0 ht0T with
    ⟨deltaRaw, hdeltaRaw, hdeltaRawT, hEq, hA, hGcont, hAcont⟩
  exact metricGainAt_of_metricVariationDerivAt (I := I) (M := M)
    (G := G) (Ric := Ric) (A := A) (T := T) (t0 := t0) (deltaRaw := deltaRaw)
    hdeltaRaw hdeltaRawT hEq hA hGcont hAcont









omit [IsManifold I 2 M] in
theorem metricGainControl_of_metricVariationOn
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (Ric : RicciTensorField (I := I) (M := M) Real)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {T : Real}
    (hEq : MetricVariationEquationOn (I := I) G Ric)
    (hlocal :
      ∀ t0 : Real,
        t0 ∈ Set.Icc 0 T ->
        t0 < T ->
        ∃ deltaRaw : Real,
          0 < deltaRaw ∧ t0 + deltaRaw ≤ T ∧
          Set.Icc t0 (t0 + deltaRaw) ⊆ D.carrier ∧
          (∀ t, t ∈ Set.Ioc t0 (t0 + deltaRaw) -> t ∈ D.regular) ∧
          (∀ t, t ∈ Set.Ioc t0 (t0 + deltaRaw) ->
            ∀ x, ∀ v : TangentSpace I x,
              quad02 (I := I) (M := M) (A t x) v =
                (-2 : Real) * Ric t x v v) ∧
          Continuous
            (metricTimeBundleQuad (I := I) (M := M) (fun t => G.metric t)
              (Set.Icc t0 (t0 + deltaRaw))) ∧
          Continuous (fun q :
              {t : Real // t ∈ Set.Icc t0 (t0 + deltaRaw)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (A q.1.1 q.2.proj))) :
    ∀ t0 : Real,
      t0 ∈ Set.Icc 0 T ->
      t0 < T ->
      ∃ delta0 : Real,
        0 < delta0 ∧ t0 + delta0 ≤ T ∧
          ∀ delta : Real,
            0 < delta ->
            delta ≤ delta0 ->
            ∀ epsilon : Real,
              SmallBarrierEps epsilon ->
              ∃ metricDeriv : TensorQuadraticFormFamily (I := I) (M := M),
                (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                  ∀ x, ∀ v : TangentSpace I x,
                    HasDerivWithinAt
                      (fun s : Real => (G.metric s).inner x v v)
                      (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t) ∧
                (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                  ∀ x, ∀ v : TangentSpace I x,
                    (epsilon / 2) * (G.metric t).inner x v v ≤
                      epsilon * ((G.metric t).inner x v v +
                        (delta + t - t0) * metricDeriv t x v)) := by
  intro t0 ht0 ht0T
  rcases hlocal t0 ht0 ht0T with
    ⟨deltaRaw, hdeltaRaw, hdeltaRawT, hcarrier, hregular, hA, hGcont, hAcont⟩
  apply metricGainAt_of_totalCont (I := I) (M := M)
    (G := fun t => G.metric t) (A := A)
    (T := T) (t0 := t0) (deltaRaw := deltaRaw)
    hdeltaRaw hdeltaRawT
  · intro delta hdelta hdelta_le t ht x v
    have ht_raw : t ∈ Set.Ioc t0 (t0 + deltaRaw) :=
      ⟨ht.1, by linarith [ht.2, hdelta_le]⟩
    let τ : RealTimeInterval.RegularTime D := ⟨t, hregular t ht_raw⟩
    have hslab : Set.Icc t0 (t0 + delta) ⊆ D.carrier := by
      intro s hs
      exact hcarrier ⟨hs.1, by linarith [hs.2, hdelta_le]⟩
    have hderiv :=
      (hEq τ x v v).mono hslab
    have hval := hA t ht_raw x v
    simpa [τ, hval] using hderiv
  · exact hGcont
  · exact hAcont







omit [IsManifold I 2 M] in
theorem metricGainControl_of_metricVariationOn_closedOpen
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {omega T : Real} (h0ω : 0 < omega) (hTω : T < omega)
    (G : RealizedMetricFamilyOn (I := I) (M := M)
      (RealTimeInterval.closedOpen 0 omega h0ω))
    (Ric : RicciTensorField (I := I) (M := M) Real)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hEq : MetricVariationEquationOn (I := I) G Ric)
    (hSmooth : MetricFamilySmoothOn (I := I) (M := M)
      (RealTimeInterval.closedOpen 0 omega h0ω) G)
    (hA :
      ∀ t, t ∈ Set.Ioc 0 T ->
        ∀ x, ∀ v : TangentSpace I x,
          quad02 (I := I) (M := M) (A t x) v =
            (-2 : Real) * Ric t x v v)
    (hAcont :
      ∀ t0 deltaRaw : Real,
        Continuous (fun q :
            {t : Real // t ∈ Set.Icc t0 (t0 + deltaRaw)} × TangentBundle I M =>
          TotalSpace.mk' (Tensor0SModel 2 Real E)
            (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
            (A q.1.1 q.2.proj))) :
    ∀ t0 : Real,
      t0 ∈ Set.Icc 0 T ->
      t0 < T ->
      ∃ delta0 : Real,
        0 < delta0 ∧ t0 + delta0 ≤ T ∧
          ∀ delta : Real,
            0 < delta ->
            delta ≤ delta0 ->
            ∀ epsilon : Real,
              SmallBarrierEps epsilon ->
              ∃ metricDeriv : TensorQuadraticFormFamily (I := I) (M := M),
                (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                  ∀ x, ∀ v : TangentSpace I x,
                    HasDerivWithinAt
                      (fun s : Real => (G.metric s).inner x v v)
                      (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t) ∧
                (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                  ∀ x, ∀ v : TangentSpace I x,
                    (epsilon / 2) * (G.metric t).inner x v v ≤
                      epsilon * ((G.metric t).inner x v v +
                        (delta + t - t0) * metricDeriv t x v)) := by
  apply metricGainControl_of_metricVariationOn (I := I) (M := M)
    (D := RealTimeInterval.closedOpen 0 omega h0ω)
    (G := G) (Ric := Ric) (A := A) (T := T) hEq
  intro t0 ht0 ht0T
  let deltaRaw : Real := (T - t0) / 2
  have hdeltaRaw : 0 < deltaRaw := by
    dsimp [deltaRaw]
    linarith
  have hdeltaRawT : t0 + deltaRaw ≤ T := by
    dsimp [deltaRaw]
    linarith
  refine ⟨deltaRaw, hdeltaRaw, hdeltaRawT, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact ⟨le_trans ht0.1 hs.1,
      lt_of_le_of_lt (le_trans hs.2 hdeltaRawT) hTω⟩
  · intro t ht
    exact ⟨lt_of_le_of_lt ht0.1 ht.1,
      lt_of_le_of_lt (le_trans ht.2 hdeltaRawT) hTω⟩
  · intro t ht x v
    have ht_global : t ∈ Set.Ioc 0 T :=
      ⟨lt_of_le_of_lt ht0.1 ht.1, le_trans ht.2 hdeltaRawT⟩
    exact hA t ht_global x v
  · exact metricTimeBundleQuad_cont_of_metricFamilySmoothOn (I := I) (M := M)
      G hSmooth (by
        intro s hs
        exact ⟨le_trans ht0.1 hs.1,
          lt_of_le_of_lt (le_trans hs.2 hdeltaRawT) hTω⟩)
  · exact hAcont t0 deltaRaw

end DifferentialGeometry.Integral.Connection
