import DifferentialGeometry.Analysis.Parabolic.ScalarTimeDependent
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.FirstVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.PotentialGeometry

set_option autoImplicit false









namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]



theorem potential_slice
    (D : RealTimeInterval)
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (V u : Real -> M -> Real) (n : Nat)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn D G V u)
    {s : Real} (hs : s ∈ D.regular) (hspos : 0 < s)
    (hpos : ∀ y : M, 0 < u s y) :
    ContMDiff I 𝓘(Real, Real) ∞ (perelmanPotential n s (u s)) := by
  have husmooth : ContMDiff I 𝓘(Real, Real) ∞ (u s) :=
    hu.sliceSmooth s (D.regular_subset hs)
  have hpref_pos : 0 < perelmanDensityPrefactor n s := by
    unfold perelmanDensityPrefactor
    exact Real.rpow_pos_of_pos
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) hspos) _
  intro y
  have hquot :
      ContMDiffAt I 𝓘(Real, Real) ∞
        (fun z : M => u s z / perelmanDensityPrefactor n s) y :=
    husmooth.contMDiffAt.div₀ contMDiffAt_const hpref_pos.ne'
  have hlog :
      ContDiffAt Real ∞ Real.log
        (u s y / perelmanDensityPrefactor n s) :=
    Real.contDiffAt_log.2 (div_ne_zero (hpos y).ne' hpref_pos.ne')
  simpa only [perelmanPotential] using
    (hlog.comp_contMDiffAt
      (I := I)
      (f := fun z : M => u s z / perelmanDensityPrefactor n s)
      (x := y) hquot).neg



theorem potential_pde
    (D : RealTimeInterval)
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (V u : Real -> M -> Real) (n : Nat)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn D G V u)
    {s : Real} (hs : s ∈ D.regular) (hspos : 0 < s)
    (hpos : ∀ y : M, 0 < u s y) (x : M) :
    HasDerivAt (fun r : Real => perelmanPotential n r (u r) x)
      (laplacianAt (I := I) G s (perelmanPotential n s (u s)) x -
        (G.metric s).inner x
          (gradientFun (I := I) (G.metric s)
            (perelmanPotential n s (u s)) x)
          (gradientFun (I := I) (G.metric s)
            (perelmanPotential n s (u s)) x) -
        V s x - (n : Real) / (2 * s)) s := by
  let pref : Real := perelmanDensityPrefactor n s
  let logu : M -> Real := fun y => Real.log (u s y)
  have hpref_pos : 0 < pref := by
    dsimp only [pref, perelmanDensityPrefactor]
    exact Real.rpow_pos_of_pos
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) hspos) _
  have hpref_ne : perelmanDensityPrefactor n s ≠ 0 := by
    simpa only [pref] using hpref_pos.ne'
  have husmooth : ContMDiff I 𝓘(Real, Real) ∞ (u s) :=
    hu.sliceSmooth s (D.regular_subset hs)
  have hudiff : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (u s) y := by
    intro y
    exact husmooth.mdifferentiable (by simp) y
  have hugrad :
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric s) (u s) y) x :=
    gradientFun_mdiffAt (I := I) (G.metric s) husmooth x
  have hlog_smooth : ContMDiff I 𝓘(Real, Real) ∞ logu := by
    intro y
    exact (Real.contDiffAt_log.2 (hpos y).ne').comp_contMDiffAt
      husmooth.contMDiffAt
  have hlogdiff :
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) logu y := by
    intro y
    exact hlog_smooth.mdifferentiable (by simp) y
  have hloggrad :
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric s) logu y) x :=
    gradientFun_mdiffAt (I := I) (G.metric s) hlog_smooth x
  have hpot_eq :
      perelmanPotential n s (u s) =
        fun y : M => ((-1 : Real) • logu) y - (-Real.log pref) := by
    funext y
    simp only [perelmanPotential, logu, Pi.smul_apply, smul_eq_mul]
    rw [Real.log_div (hpos y).ne' hpref_pos.ne']
    dsimp only [pref]
    ring
  have hlap_log :
      laplacianAt (I := I) G s logu x =
        (u s x)⁻¹ * laplacianAt (I := I) G s (u s) x -
          (u s x ^ 2)⁻¹ *
            (G.metric s).inner x
              (gradientFun (I := I) (G.metric s) (u s) x)
              (gradientFun (I := I) (G.metric s) (u s) x) := by
    unfold laplacianAt
    simpa only [logu] using
      laplacian_log (I := I) (G.connection s) (G.metric s)
        hudiff hpos hugrad
  have hlap_pot :
      laplacianAt (I := I) G s (perelmanPotential n s (u s)) x =
        -laplacianAt (I := I) G s logu x := by
    rw [hpot_eq]
    unfold laplacianAt
    rw [laplacian_sub_const (I := I) (G.connection s) (G.metric s)
      (-Real.log pref) (fun y => (hlogdiff y).const_smul (-1)) x]
    rw [laplacian_const_smul (I := I) (G.connection s) (G.metric s)
      (-1) hlogdiff hloggrad]
    ring
  have hnorm_pot :
      (G.metric s).inner x
          (gradientFun (I := I) (G.metric s)
            (perelmanPotential n s (u s)) x)
          (gradientFun (I := I) (G.metric s)
            (perelmanPotential n s (u s)) x) =
        (u s x ^ 2)⁻¹ *
          (G.metric s).inner x
            (gradientFun (I := I) (G.metric s) (u s) x)
            (gradientFun (I := I) (G.metric s) (u s) x) := by
    exact potential_grad_sq (I := I) (G.metric s) n husmooth hpos hspos x
  have hspace :
      laplacianAt (I := I) G s (perelmanPotential n s (u s)) x -
          (G.metric s).inner x
            (gradientFun (I := I) (G.metric s)
              (perelmanPotential n s (u s)) x)
            (gradientFun (I := I) (G.metric s)
              (perelmanPotential n s (u s)) x) =
        -(u s x)⁻¹ * laplacianAt (I := I) G s (u s) x := by
    rw [hlap_pot, hlap_log, hnorm_pot]
    ring
  have hpref_deriv :
      HasDerivAt (fun r : Real => perelmanDensityPrefactor n r)
        (-((n : Real) / (2 * s)) * 1 * perelmanDensityPrefactor n s) s := by
    exact perelmanDensityPrefactor_hasDerivAt
      (n := n) (tauPath := fun r : Real => r) (s0 := s) (tau := s)
      (tauVariation := 1) rfl hspos (hasDerivAt_id (x := s))
  have hu_deriv := hu.equation s hs x
  have hquot := hu_deriv.div hpref_deriv hpref_ne
  have hraw :=
    (hquot.log (div_ne_zero (hpos x).ne' hpref_ne)).neg
  have htime :
      HasDerivAt (fun r : Real => perelmanPotential n r (u r) x)
        (-(u s x)⁻¹ * laplacianAt (I := I) G s (u s) x -
          V s x - (n : Real) / (2 * s)) s := by
    convert hraw using 1
    simp only [Pi.div_apply]
    field_simp [hpref_ne, (hpos x).ne', hspos.ne']
    ring
  convert htime using 1
  rw [hspace]



theorem potential_joint
    (D : RealTimeInterval)
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (V u : Real -> M -> Real) (n : Nat)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn D G V u)
    (hpos : ∀ t : Real, t ∈ D.regular ∩ Set.Ioi (0 : Real) →
      ∀ y : M, 0 < u t y) :
    ContMDiffOn
      ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M => perelmanPotential n p.1 (u p.1) p.2)
      ((D.regular ∩ Set.Ioi (0 : Real)) ×ˢ Set.univ) := by
  intro p hp
  have hpreg : p.1 ∈ D.regular := hp.1.1
  have huAt :
      ContMDiffAt
        ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M => u q.1 q.2) p := by
    exact
      (hu.jointSmooth p ⟨hpreg, Set.mem_univ p.2⟩).contMDiffAt
        ((D.regular_isOpen.prod isOpen_univ).mem_nhds
          ⟨hpreg, Set.mem_univ p.2⟩)
  have hbase :
      ContMDiffAt
        ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M => 4 * Real.pi * q.1) p := by
    exact contMDiffAt_const.mul contMDiffAt_fst
  have hbase_pos : 0 < 4 * Real.pi * p.1 :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) hp.1.2
  have hprefAt :
      ContMDiffAt
        ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M => perelmanDensityPrefactor n q.1) p := by
    unfold perelmanDensityPrefactor
    have hpow :
        ContDiffAt Real ∞ (fun z : Real => z ^ (-(n : Real) / 2))
          (4 * Real.pi * p.1) :=
      Real.contDiffAt_rpow_const_of_ne hbase_pos.ne'
    simpa only [Function.comp_apply] using
      hpow.comp_contMDiffAt
        (I := (modelWithCornersSelf Real Real).prod I)
        (f := fun q : Real × M => 4 * Real.pi * q.1) (x := p) hbase
  have hpref_pos : 0 < perelmanDensityPrefactor n p.1 := by
    unfold perelmanDensityPrefactor
    exact Real.rpow_pos_of_pos hbase_pos _
  have hquot :
      ContMDiffAt
        ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M =>
          u q.1 q.2 / perelmanDensityPrefactor n q.1) p :=
    huAt.div₀ hprefAt hpref_pos.ne'
  have hlogAt :
      ContDiffAt Real ∞ Real.log
        (u p.1 p.2 / perelmanDensityPrefactor n p.1) :=
    Real.contDiffAt_log.2
      (div_ne_zero (hpos p.1 hp.1 p.2).ne' hpref_pos.ne')
  have hlog :
      ContMDiffAt
        ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M =>
          Real.log (u q.1 q.2 / perelmanDensityPrefactor n q.1)) p := by
    simpa only [Function.comp_apply] using
      hlogAt.comp_contMDiffAt
        (I := (modelWithCornersSelf Real Real).prod I)
        (f := fun q : Real × M =>
          u q.1 q.2 / perelmanDensityPrefactor n q.1) (x := p) hquot
  simpa only [perelmanPotential] using hlog.neg.contMDiffWithinAt




theorem potential_df_time
    [I.Boundaryless]
    (D : RealTimeInterval)
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (V u : Real -> M -> Real) (n : Nat)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn D G V u)
    (hpos : ∀ t : Real, t ∈ D.regular ∩ Set.Ioi (0 : Real) →
      ∀ y : M, 0 < u t y)
    {s : Real} (hs : s ∈ D.regular) (hspos : 0 < s)
    (x : M) (X : TangentSpace I x) :
    HasDerivAt
      (fun r : Real =>
        extDerivFun (I := I) (perelmanPotential n r (u r)) x X)
      (extDerivFun (I := I)
        (fun y : M =>
          laplacianAt (I := I) G s (perelmanPotential n s (u s)) y -
            (G.metric s).inner y
              (gradientFun (I := I) (G.metric s)
                (perelmanPotential n s (u s)) y)
              (gradientFun (I := I) (G.metric s)
                (perelmanPotential n s (u s)) y) -
            V s y - (n : Real) / (2 * s)) x X) s := by
  let velocity : Real -> M -> Real := fun t y =>
    laplacianAt (I := I) G t (perelmanPotential n t (u t)) y -
      (G.metric t).inner y
        (gradientFun (I := I) (G.metric t)
          (perelmanPotential n t (u t)) y)
        (gradientFun (I := I) (G.metric t)
          (perelmanPotential n t (u t)) y) -
      V t y - (n : Real) / (2 * t)
  have hswap :
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I)
        D.carrier (D.regular ∩ Set.Ioi (0 : Real)) Set.univ
        (fun t : Real => perelmanPotential n t (u t)) velocity := by
    apply fixedBaseOnRegSmooth (I := I) isOpen_univ
      (D.regular_isOpen.inter isOpen_Ioi)
    · intro t ht
      exact D.regular_mem_nhds ht.1
    · intro t ht x _
      have huAt :
          ContMDiffAt
            ((modelWithCornersSelf Real Real).prod I)
            (modelWithCornersSelf Real Real) 2
            (fun p : Real × M => u p.1 p.2) (t, x) := by
        exact
          ((hu.jointSmooth (t, x) ⟨ht.1, Set.mem_univ x⟩).contMDiffAt
            ((D.regular_isOpen.prod isOpen_univ).mem_nhds
              ⟨ht.1, Set.mem_univ x⟩)).of_le
                (by norm_cast : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
      have hbase :
          ContMDiffAt
            ((modelWithCornersSelf Real Real).prod I)
            (modelWithCornersSelf Real Real) 2
            (fun p : Real × M => 4 * Real.pi * p.1) (t, x) := by
        exact (contMDiffAt_const.mul contMDiffAt_fst)
      have hbase_pos : 0 < 4 * Real.pi * t :=
        mul_pos (mul_pos (by norm_num) Real.pi_pos) ht.2
      have hprefAt :
          ContMDiffAt
            ((modelWithCornersSelf Real Real).prod I)
            (modelWithCornersSelf Real Real) 2
            (fun p : Real × M => perelmanDensityPrefactor n p.1) (t, x) := by
        unfold perelmanDensityPrefactor
        have hpow :
            ContDiffAt Real 2 (fun z : Real => z ^ (-(n : Real) / 2))
              (4 * Real.pi * t) :=
          Real.contDiffAt_rpow_const_of_ne hbase_pos.ne'
        simpa only [Function.comp_apply] using
          hpow.comp_contMDiffAt
            (I := (modelWithCornersSelf Real Real).prod I)
            (f := fun p : Real × M => 4 * Real.pi * p.1)
            (x := (t, x)) hbase
      have hpref_pos : 0 < perelmanDensityPrefactor n t := by
        unfold perelmanDensityPrefactor
        exact Real.rpow_pos_of_pos hbase_pos _
      have hquot :
          ContMDiffAt
            ((modelWithCornersSelf Real Real).prod I)
            (modelWithCornersSelf Real Real) 2
            (fun p : Real × M =>
              u p.1 p.2 / perelmanDensityPrefactor n p.1) (t, x) :=
        huAt.div₀ hprefAt hpref_pos.ne'
      have hlog :
          ContMDiffAt
            ((modelWithCornersSelf Real Real).prod I)
            (modelWithCornersSelf Real Real) 2
            (fun p : Real × M =>
              Real.log (u p.1 p.2 / perelmanDensityPrefactor n p.1))
            (t, x) :=
        by
          have hlogAt :
              ContDiffAt Real 2 Real.log
                (u t x / perelmanDensityPrefactor n t) :=
            Real.contDiffAt_log.2
              (div_ne_zero (hpos t ht x).ne' hpref_pos.ne')
          simpa only [Function.comp_apply] using
            hlogAt.comp_contMDiffAt
              (I := (modelWithCornersSelf Real Real).prod I)
              (f := fun p : Real × M =>
                u p.1 p.2 / perelmanDensityPrefactor n p.1)
              (x := (t, x)) hquot
      simpa only [perelmanPotential] using hlog.neg
    · intro t ht x _
      exact
        (potential_pde D G V u n hu ht.1 ht.2 (hpos t ht) x).hasDerivWithinAt
  have hwithin := hswap s ⟨hs, hspos⟩ x (Set.mem_univ x) X
  simpa only [velocity] using
    hwithin.hasDerivAt (D.regular_mem_nhds hs)

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
