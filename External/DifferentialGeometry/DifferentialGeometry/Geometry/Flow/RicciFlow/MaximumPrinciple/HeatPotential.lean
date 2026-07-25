import DifferentialGeometry.Analysis.Parabolic.ScalarTimeDependent
import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.ScalarWeak
import DifferentialGeometry.Geometry.Operator.GradientRegularity

set_option autoImplicit false










namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set Filter
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

set_option maxHeartbeats 400000 in



theorem heat_pot_nonneg
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 <= T) (V u : Real -> M -> Real)
    (hsol : IsHeatPotOn (RealTimeInterval.closed 0 T hT) G V u)
    (C : Real)
    (hV : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, V t x <= C)
    (hinit : forall x : M, 0 <= u 0 x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= u t x := by
  by_cases hTzero : T = 0
  · intro t ht x
    have htzero : t = 0 := le_antisymm (by simpa [hTzero] using ht.2) ht.1
    simpa [htzero] using hinit x
  have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hTzero)
  have hshort : forall T' : Real, 0 <= T' -> T' < T ->
      forall t : Real, t ∈ Set.Icc 0 T' -> forall x : M, 0 <= u t x := by
    intro T' hT' hT'lt
    let X : Real -> (x : M) -> TangentSpace I x :=
      fun _ x => (0 : TangentSpace I x)
    let J : Real -> M -> Real := fun t x => Real.exp (-C * t) * u t x
    have hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
        (spacetimeSlab (M := M) T') := by
      apply hsol.jointCont.mono
      intro p hp
      exact ⟨⟨hp.1.1, hp.1.2.trans hT'lt.le⟩, hp.2⟩
    have hJ_cont : ContinuousOn (fun p : Real × M => J p.1 p.2)
        (spacetimeSlab (M := M) T') := by
      have hscale : Continuous (fun p : Real × M => Real.exp (-C * p.1)) := by
        fun_prop
      simpa only [J] using hscale.continuousOn.mul hu_cont
    have hJ0 : forall x : M, 0 <= J 0 x := by
      intro x
      simpa [J] using hinit x
    have hJ_time : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t ->
        forall x : M,
          DifferentiableWithinAt Real (fun s : Real => J s x) (Set.Icc 0 T') t := by
      intro t ht htpos x
      have htreg : t ∈ (RealTimeInterval.closed 0 T hT).regular := by
        change t ∈ Set.Ioo 0 T
        exact ⟨htpos, lt_of_le_of_lt ht.2 hT'lt⟩
      have hscale : DifferentiableAt Real (fun s : Real => Real.exp (-C * s)) t := by
        fun_prop
      exact (hscale.mul (hsol.equation t htreg x).differentiableAt).differentiableWithinAt
    have hJ_mdiff : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t ->
        forall x : M, MDifferentiableAt I 𝓘(Real, Real) (J t) x := by
      intro t ht _htpos x
      have htcarrier : t ∈ (RealTimeInterval.closed 0 T hT).carrier := by
        change t ∈ Set.Icc 0 T
        exact ⟨ht.1, ht.2.trans hT'lt.le⟩
      have hJsmooth : ContMDiff I 𝓘(Real, Real) ∞ (J t) := by
        simpa only [J] using contMDiff_const.mul (hsol.sliceSmooth t htcarrier)
      exact hJsmooth.mdifferentiable (by simp) x
    have hJ_grad : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t ->
        forall x : M, MDiffAt (T% fun y : M =>
          gradientFun (I := I) (G.metric t) (J t) y) x := by
      intro t ht _htpos x
      have htcarrier : t ∈ (RealTimeInterval.closed 0 T hT).carrier := by
        change t ∈ Set.Icc 0 T
        exact ⟨ht.1, ht.2.trans hT'lt.le⟩
      have hJsmooth : ContMDiff I 𝓘(Real, Real) ∞ (J t) := by
        simpa only [J] using contMDiff_const.mul (hsol.sliceSmooth t htcarrier)
      exact gradientFun_mdiffAt (I := I) (G.metric t) hJsmooth x
    have hnegative : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t ->
        forall x : M, J t x < 0 ->
          0 <= parabolicOperatorWithDrift (I := I) G T' X J t x := by
      intro t ht htpos x hJneg
      have hT'pos : 0 < T' := lt_of_lt_of_le htpos ht.2
      have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T') t :=
        uniqueDiffOn_Icc hT'pos t ht
      have htreg : t ∈ (RealTimeInterval.closed 0 T hT).regular := by
        change t ∈ Set.Ioo 0 T
        exact ⟨htpos, lt_of_le_of_lt ht.2 hT'lt⟩
      have htcarrier : t ∈ (RealTimeInterval.closed 0 T hT).carrier :=
        (RealTimeInterval.closed 0 T hT).regular_subset htreg
      have husmooth := hsol.sliceSmooth t htcarrier
      have hu_space : forall y : M,
          MDifferentiableAt I 𝓘(Real, Real) (u t) y :=
        fun y => husmooth.mdifferentiable (by simp) y
      have hu_grad : MDiffAt (T% fun y : M =>
          gradientFun (I := I) (G.metric t) (u t) y) x :=
        gradientFun_mdiffAt (I := I) (G.metric t) husmooth x
      have hu_time : DifferentiableWithinAt Real
          (fun s : Real => u s x) (Set.Icc 0 T') t :=
        (hsol.equation t htreg x).differentiableAt.differentiableWithinAt
      have hscale : DifferentiableWithinAt Real
          (fun s : Real => Real.exp (-C * s)) (Set.Icc 0 T') t := by
        fun_prop
      have hreaction :
          parabolicOperatorWithDrift (I := I) G T' X u t x = V t x * u t x := by
        have hderiv :
            derivWithin (fun s : Real => u s x) (Set.Icc 0 T') t =
              laplacianAt (I := I) G t (u t) x + V t x * u t x :=
          (hsol.equation t htreg x).hasDerivWithinAt.derivWithin huniq
        rw [parabolicOperatorWithDrift_eq, hderiv]
        rw [show X t = (fun y : M => (0 : TangentSpace I y)) from rfl]
        rw [heatOperatorWithDrift_zero_drift, heatOperator_eq_laplacianAt]
        ring
      rw [show J = (fun s y => Real.exp (-C * s) * u s y) from rfl]
      rw [parabolic_exp_rescale_identity (I := I) G T' C X u t ht huniq
        hu_space x hu_grad hu_time hscale]
      rw [hreaction]
      have hu_neg : u t x < 0 :=
        lt_of_mul_lt_mul_left (by simpa [J] using hJneg) (Real.exp_pos (-C * t)).le
      apply mul_nonneg (Real.exp_pos (-C * t)).le
      calc
        V t x * u t x - C * u t x = (V t x - C) * u t x := by ring
        _ >= 0 := mul_nonneg_of_nonpos_of_nonpos
          (sub_nonpos.mpr (hV t ⟨ht.1, ht.2.trans hT'lt.le⟩ x)) hu_neg.le
    have hJ_nonneg : forall t : Real, t ∈ Set.Icc 0 T' ->
        forall x : M, 0 <= J t x :=
      strict_barrier_posReg (I := I) G T' hT' X J hJ_cont hJ0
        hJ_time hJ_mdiff hJ_grad hnegative
    intro t ht x
    have hprod : 0 <= Real.exp (-C * t) * u t x := by
      simpa only [J] using hJ_nonneg t ht x
    exact (mul_nonneg_iff_of_pos_left (Real.exp_pos (-C * t))).mp hprod
  have hIco : forall t : Real, t ∈ Set.Ico 0 T -> forall x : M, 0 <= u t x := by
    intro t ht x
    let T' : Real := (t + T) / 2
    have hT'nonneg : 0 <= T' := by
      dsimp [T']
      linarith [ht.1, hT]
    have hT'lt : T' < T := by
      dsimp [T']
      linarith [ht.2]
    have htT' : t <= T' := by
      dsimp [T']
      linarith [ht.2]
    exact hshort T' hT'nonneg hT'lt t ⟨ht.1, htT'⟩ x
  have hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (Set.Icc (0 : Real) T ×ˢ Set.univ) := by
    simpa only [RealTimeInterval.closed] using hsol.jointCont
  intro t ht x
  rcases eq_or_lt_of_le ht.2 with htT | htT
  · have ht_eq : t = T := htT
    rw [ht_eq]
    have hT_in : (T, x) ∈ Set.Icc (0 : Real) T ×ˢ (Set.univ : Set M) :=
      ⟨right_mem_Icc.mpr hT, Set.mem_univ x⟩
    have h_cont_at := hu_cont (T, x) hT_in
    have h_tend : Filter.Tendsto (fun s : Real => u s x)
        (𝓝[<] T) (𝓝 (u T x)) := by
      have h_pair : Filter.Tendsto (fun s : Real => (s, x))
          (𝓝[<] T) (𝓝 (T, x)) := by
        refine Filter.Tendsto.prodMk_nhds ?_ tendsto_const_nhds
        exact nhdsWithin_le_nhds
      have h_evt : ∀ᶠ s in 𝓝[<] T,
          (s, x) ∈ Set.Icc (0 : Real) T ×ˢ (Set.univ : Set M) := by
        have h0 : Set.Ioi (0 : Real) ∈ 𝓝 T := Ioi_mem_nhds hTpos
        have h0' : Set.Ioi (0 : Real) ∈ 𝓝[<] T := nhdsWithin_le_nhds h0
        filter_upwards [h0', self_mem_nhdsWithin] with s hs hslt
        exact ⟨⟨le_of_lt hs, le_of_lt hslt⟩, Set.mem_univ x⟩
      have h_pair_within : Filter.Tendsto (fun s : Real => (s, x))
          (𝓝[<] T) (𝓝[Set.Icc 0 T ×ˢ Set.univ] (T, x)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨h_pair, h_evt⟩
      exact h_cont_at.tendsto.comp h_pair_within
    have h_tend_neg : Filter.Tendsto (fun s : Real => -u s x)
        (𝓝[<] T) (𝓝 (-u T x)) :=
      (continuous_neg.tendsto (u T x)).comp h_tend
    have h_evt_nonpos : ∀ᶠ s in 𝓝[<] T, -u s x <= 0 := by
      have h0 : Set.Ioi (0 : Real) ∈ 𝓝 T := Ioi_mem_nhds hTpos
      have h0' : Set.Ioi (0 : Real) ∈ 𝓝[<] T := nhdsWithin_le_nhds h0
      filter_upwards [h0', self_mem_nhdsWithin] with s hs hslt
      exact neg_nonpos.mpr (hIco s ⟨le_of_lt hs, hslt⟩ x)
    have h_neBot : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hTpos⟩
    exact neg_nonpos.mp (le_of_tendsto h_tend_neg h_evt_nonpos)
  · exact hIco t ⟨ht.1, htT⟩ x

set_option maxHeartbeats 600000 in



theorem heat_pot_pos
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 <= T) (V u : Real -> M -> Real)
    (hsol : IsHeatPotOn (RealTimeInterval.closed 0 T hT) G V u)
    (C : Real)
    (hV : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, |V t x| <= C)
    (hinit : forall x : M, 0 < u 0 x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 < u t x := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · intro _t _ht x
    exact (hM.false x).elim
  letI : Nonempty M := hM
  by_cases hTzero : T = 0
  · intro t ht x
    have htzero : t = 0 := le_antisymm (by simpa [hTzero] using ht.2) ht.1
    simpa [htzero] using hinit x
  have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hTzero)
  have h0carrier :
      0 ∈ (RealTimeInterval.closed 0 T hT).carrier := by
    change 0 ∈ Set.Icc (0 : Real) T
    exact Set.left_mem_Icc.mpr hT
  have hu0_cont : Continuous (u 0) :=
    (hsol.sliceSmooth 0 h0carrier).continuous
  obtain ⟨x0, _hx0, hx0min⟩ :=
    (isCompact_univ (X := M)).exists_isMinOn
      Set.univ_nonempty hu0_cont.continuousOn
  let c : Real := u 0 x0
  have hcpos : 0 < c := by
    simpa only [c] using hinit x0
  have hc_le (x : M) : c <= u 0 x := by
    exact hx0min (Set.mem_univ x)
  have hVupper : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, V t x <= C := by
    intro t ht x
    exact (le_abs_self (V t x)).trans (hV t ht x)
  have hu_nonneg : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= u t x :=
    heat_pot_nonneg (I := I) G hT V u hsol C hVupper
      (fun x => (hinit x).le)
  let z : Real -> M -> Real := fun t x => Real.exp (C * t) * u t x
  let w : Real -> M -> Real := fun t x => z t x - c
  have hshort : forall T' : Real, 0 <= T' -> T' < T ->
      forall t : Real, t ∈ Set.Icc 0 T' -> forall x : M, c <= z t x := by
    intro T' hT' hT'lt
    let X : Real -> (x : M) -> TangentSpace I x :=
      fun _ x => (0 : TangentSpace I x)
    have hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
        (spacetimeSlab (M := M) T') := by
      apply hsol.jointCont.mono
      intro p hp
      exact ⟨⟨hp.1.1, hp.1.2.trans hT'lt.le⟩, hp.2⟩
    have hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
        (spacetimeSlab (M := M) T') := by
      have hscale : Continuous (fun p : Real × M => Real.exp (C * p.1)) := by
        fun_prop
      simpa only [w, z] using
        (hscale.continuousOn.mul hu_cont).sub continuousOn_const
    have hw0 : forall x : M, 0 <= w 0 x := by
      intro x
      simpa [w, z] using hc_le x
    have hw_time : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t ->
        forall x : M,
          DifferentiableWithinAt Real (fun s : Real => w s x) (Set.Icc 0 T') t := by
      intro t ht htpos x
      have htreg : t ∈ (RealTimeInterval.closed 0 T hT).regular := by
        change t ∈ Set.Ioo 0 T
        exact ⟨htpos, lt_of_le_of_lt ht.2 hT'lt⟩
      have hscale : DifferentiableAt Real (fun s : Real => Real.exp (C * s)) t := by
        fun_prop
      have hdiff : DifferentiableAt Real
          (fun s : Real => Real.exp (C * s) * u s x - c) t :=
        (hscale.mul (hsol.equation t htreg x).differentiableAt).sub_const c
      simpa only [w, z] using hdiff.differentiableWithinAt
    have hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t ->
        forall x : M, MDifferentiableAt I 𝓘(Real, Real) (w t) x := by
      intro t ht _htpos x
      have htcarrier : t ∈ (RealTimeInterval.closed 0 T hT).carrier := by
        change t ∈ Set.Icc 0 T
        exact ⟨ht.1, ht.2.trans hT'lt.le⟩
      have hwsmooth : ContMDiff I 𝓘(Real, Real) ∞ (w t) := by
        simpa only [w, z] using
          (contMDiff_const.mul (hsol.sliceSmooth t htcarrier)).sub_const c
      exact hwsmooth.mdifferentiable (by simp) x
    have hw_grad : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t ->
        forall x : M, MDiffAt (T% fun y : M =>
          gradientFun (I := I) (G.metric t) (w t) y) x := by
      intro t ht _htpos x
      have htcarrier : t ∈ (RealTimeInterval.closed 0 T hT).carrier := by
        change t ∈ Set.Icc 0 T
        exact ⟨ht.1, ht.2.trans hT'lt.le⟩
      have hwsmooth : ContMDiff I 𝓘(Real, Real) ∞ (w t) := by
        simpa only [w, z] using
          (contMDiff_const.mul (hsol.sliceSmooth t htcarrier)).sub_const c
      exact gradientFun_mdiffAt (I := I) (G.metric t) hwsmooth x
    have hnegative : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t ->
        forall x : M, w t x < 0 ->
          0 <= parabolicOperatorWithDrift (I := I) G T' X w t x := by
      intro t ht htpos x _hwneg
      have hT'pos : 0 < T' := lt_of_lt_of_le htpos ht.2
      have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T') t :=
        uniqueDiffOn_Icc hT'pos t ht
      have htreg : t ∈ (RealTimeInterval.closed 0 T hT).regular := by
        change t ∈ Set.Ioo 0 T
        exact ⟨htpos, lt_of_le_of_lt ht.2 hT'lt⟩
      have htcarrier : t ∈ (RealTimeInterval.closed 0 T hT).carrier :=
        (RealTimeInterval.closed 0 T hT).regular_subset htreg
      have husmooth := hsol.sliceSmooth t htcarrier
      have hu_space : forall y : M,
          MDifferentiableAt I 𝓘(Real, Real) (u t) y :=
        fun y => husmooth.mdifferentiable (by simp) y
      have hu_grad : MDiffAt (T% fun y : M =>
          gradientFun (I := I) (G.metric t) (u t) y) x :=
        gradientFun_mdiffAt (I := I) (G.metric t) husmooth x
      have hu_time : DifferentiableWithinAt Real
          (fun s : Real => u s x) (Set.Icc 0 T') t :=
        (hsol.equation t htreg x).differentiableAt.differentiableWithinAt
      have hscale : DifferentiableWithinAt Real
          (fun s : Real => Real.exp (-(-C) * s)) (Set.Icc 0 T') t := by
        fun_prop
      have hz_space : forall y : M,
          MDifferentiableAt I 𝓘(Real, Real) (z t) y := by
        intro y
        have hzsmooth : ContMDiff I 𝓘(Real, Real) ∞ (z t) := by
          simpa only [z] using contMDiff_const.mul husmooth
        exact hzsmooth.mdifferentiable (by simp) y
      have hz_time : DifferentiableWithinAt Real
          (fun s : Real => z s x) (Set.Icc 0 T') t := by
        have hscale' : DifferentiableWithinAt Real
            (fun s : Real => Real.exp (C * s)) (Set.Icc 0 T') t := by
          fun_prop
        simpa only [z] using hscale'.mul hu_time
      have hsub :
          parabolicOperatorWithDrift (I := I) G T' X w t x =
            parabolicOperatorWithDrift (I := I) G T' X z t x -
              derivWithin (fun _s : Real => c) (Set.Icc 0 T') t := by
        simpa only [w] using
          parabolic_sub_time_curve_identity (I := I) G T' X z
            (fun _s : Real => c) t ht hz_space x hz_time
            (differentiableWithinAt_const c)
      have hconst :
          derivWithin (fun _s : Real => c) (Set.Icc 0 T') t = 0 :=
        (hasDerivWithinAt_const (x := t) (s := Set.Icc 0 T') (c := c)).derivWithin huniq
      have hreaction :
          parabolicOperatorWithDrift (I := I) G T' X u t x = V t x * u t x := by
        have hderiv :
            derivWithin (fun s : Real => u s x) (Set.Icc 0 T') t =
              laplacianAt (I := I) G t (u t) x + V t x * u t x :=
          (hsol.equation t htreg x).hasDerivWithinAt.derivWithin huniq
        rw [parabolicOperatorWithDrift_eq, hderiv]
        rw [show X t = (fun y : M => (0 : TangentSpace I y)) from rfl]
        rw [heatOperatorWithDrift_zero_drift, heatOperator_eq_laplacianAt]
        ring
      have hz_reaction :
          parabolicOperatorWithDrift (I := I) G T' X z t x =
            Real.exp (C * t) *
              (parabolicOperatorWithDrift (I := I) G T' X u t x + C * u t x) := by
        simpa only [z, neg_neg, neg_mul, sub_neg_eq_add] using
          parabolic_exp_rescale_identity (I := I) G T' (-C) X u t ht huniq
            hu_space x hu_grad hu_time hscale
      have hlow : 0 <= V t x + C := by
        have := neg_le_of_abs_le
          (hV t ⟨ht.1, ht.2.trans hT'lt.le⟩ x)
        linarith
      have hinside : 0 <= (V t x + C) * u t x :=
        mul_nonneg hlow (hu_nonneg t ⟨ht.1, ht.2.trans hT'lt.le⟩ x)
      rw [hsub, hconst, hz_reaction, hreaction]
      calc
        0 <= Real.exp (C * t) * ((V t x + C) * u t x) :=
          mul_nonneg (Real.exp_pos (C * t)).le hinside
        _ = Real.exp (C * t) * (V t x * u t x + C * u t x) - 0 := by ring
    have hw_nonneg : forall t : Real, t ∈ Set.Icc 0 T' ->
        forall x : M, 0 <= w t x :=
      strict_barrier_posReg (I := I) G T' hT' X w hw_cont hw0
        hw_time hw_mdiff hw_grad hnegative
    intro t ht x
    exact sub_nonneg.mp (by simpa only [w] using hw_nonneg t ht x)
  have hIco : forall t : Real, t ∈ Set.Ico 0 T -> forall x : M, c <= z t x := by
    intro t ht x
    let T' : Real := (t + T) / 2
    have hT'nonneg : 0 <= T' := by
      dsimp [T']
      linarith [ht.1, hT]
    have hT'lt : T' < T := by
      dsimp [T']
      linarith [ht.2]
    have htT' : t <= T' := by
      dsimp [T']
      linarith [ht.2]
    exact hshort T' hT'nonneg hT'lt t ⟨ht.1, htT'⟩ x
  have hpos_of_lower (t : Real) (x : M) (hlower : c <= z t x) : 0 < u t x := by
    have hzpos : 0 < z t x := lt_of_lt_of_le hcpos hlower
    exact (mul_pos_iff_of_pos_left (Real.exp_pos (C * t))).mp (by
      simpa only [z] using hzpos)
  have hz_cont : ContinuousOn (fun p : Real × M => z p.1 p.2)
      (Set.Icc (0 : Real) T ×ˢ Set.univ) := by
    have hscale : Continuous (fun p : Real × M => Real.exp (C * p.1)) := by
      fun_prop
    simpa only [z, RealTimeInterval.closed] using
      hscale.continuousOn.mul hsol.jointCont
  intro t ht x
  rcases eq_or_lt_of_le ht.2 with htT | htT
  · have ht_eq : t = T := htT
    rw [ht_eq]
    have hT_in : (T, x) ∈ Set.Icc (0 : Real) T ×ˢ (Set.univ : Set M) :=
      ⟨Set.right_mem_Icc.mpr hT, Set.mem_univ x⟩
    have h_cont_at := hz_cont (T, x) hT_in
    have h_tend : Filter.Tendsto (fun s : Real => z s x)
        (𝓝[<] T) (𝓝 (z T x)) := by
      have h_pair : Filter.Tendsto (fun s : Real => (s, x))
          (𝓝[<] T) (𝓝 (T, x)) := by
        refine Filter.Tendsto.prodMk_nhds ?_ tendsto_const_nhds
        exact nhdsWithin_le_nhds
      have h_evt : ∀ᶠ s in 𝓝[<] T,
          (s, x) ∈ Set.Icc (0 : Real) T ×ˢ (Set.univ : Set M) := by
        have h0 : Set.Ioi (0 : Real) ∈ 𝓝 T := Ioi_mem_nhds hTpos
        have h0' : Set.Ioi (0 : Real) ∈ 𝓝[<] T := nhdsWithin_le_nhds h0
        filter_upwards [h0', self_mem_nhdsWithin] with s hs hslt
        exact ⟨⟨le_of_lt hs, le_of_lt hslt⟩, Set.mem_univ x⟩
      have h_pair_within : Filter.Tendsto (fun s : Real => (s, x))
          (𝓝[<] T) (𝓝[Set.Icc 0 T ×ˢ Set.univ] (T, x)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨h_pair, h_evt⟩
      exact h_cont_at.tendsto.comp h_pair_within
    have h_tend_neg : Filter.Tendsto (fun s : Real => -z s x)
        (𝓝[<] T) (𝓝 (-z T x)) :=
      (continuous_neg.tendsto (z T x)).comp h_tend
    have h_evt_lower : ∀ᶠ s in 𝓝[<] T, -z s x <= -c := by
      have h0 : Set.Ioi (0 : Real) ∈ 𝓝 T := Ioi_mem_nhds hTpos
      have h0' : Set.Ioi (0 : Real) ∈ 𝓝[<] T := nhdsWithin_le_nhds h0
      filter_upwards [h0', self_mem_nhdsWithin] with s hs hslt
      exact neg_le_neg (hIco s ⟨le_of_lt hs, hslt⟩ x)
    have h_neBot : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hTpos⟩
    have hlower : c <= z T x := by
      have : -z T x <= -c := le_of_tendsto h_tend_neg h_evt_lower
      linarith
    exact hpos_of_lower T x hlower
  · exact hpos_of_lower t x (hIco t ⟨ht.1, htT⟩ x)

end

end DifferentialGeometry.Analysis.Parabolic
