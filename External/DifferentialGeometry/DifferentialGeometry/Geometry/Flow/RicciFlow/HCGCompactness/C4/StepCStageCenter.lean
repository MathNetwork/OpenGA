import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCInvVelConv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalCoordDistance

set_option autoImplicit false









noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace DifferentialGeometry
namespace HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}




theorem HasSuppConvData.exists_invVel_core
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r)
    {Y : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hcompletePair : SeqMetricComplete (I := I) Y}
    {hconnPair : ∀ k,
      letI : TopologicalSpace (Y.obj k).M := (Y.obj k).topology
      ConnectedSpace (Y.obj k).M}
    {c : ∀ n : Nat, (Y.obj n).M}
    {qStage qInf : NNReal} {deltaStage deltaInf : Real}
    {e : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    {eInf : OpenPartialHomeomorph (E × E) (E × E)}
    (hpair : HasDiagPairConv (I := I) hcompletePair hconnPair c
      qStage qInf deltaStage deltaInf e eInf)
    (hC1q : C1 alpha ⊆ Metric.ball (0 : E) qInf) :
    let i0 := baseIndex inp.decay inp.realizes inp.pack hr
    let mu : E → Fin (inp.pack.A r) → Real := fun z gamma =>
      rawWeights (cutRaw (aInf alpha i0) (aInf alpha) i0) z gamma
    let swap : E × E → E × E := fun q => (q.2, q.1)
    ∃ (V V0 : Set (E × E)) (W0 : Set E) (PhiInf : E → E),
      IsOpen V ∧ IsCompact (closure V) ∧
      closure V ⊆ eInf.target ∧
      eInf.symm '' closure V ⊆ Metric.ball (0 : E × E) qInf ∧
      Filter.Eventually
        (fun n : Nat ↦ closure V ⊆ (e n).target ∧
          Set.MapsTo (e n).symm (closure V)
            (Metric.ball (0 : E × E) qInf)) Filter.atTop ∧
      MapCInfConvOnCompacts V
        (fun n ↦ ((e n).symm : E × E → E × E)) eInf.symm ∧
      IsOpen V0 ∧ IsCompact (closure V0) ∧
      (fun z : E ↦ (z, z)) '' C1 alpha ⊆ V0 ∧
      closure V0 ⊆ V ∧ closure V0 ⊆ U alpha ×ˢ U alpha ∧
      Set.EqOn PhiInf id (C1 alpha) ∧
      Nonempty
        (Analysis.CompactRootTube
          ((U alpha ×ˢ Set.univ) ∩ swap ⁻¹' V0)
          W0 (C1 alpha)
          (fun q => invVelSum eInf (mu q.1)
            (fun _ : Fin (inp.pack.A r) => q.1) q.2)
          PhiInf) := by
  classical
  dsimp only
  obtain ⟨hU, _hC0, hC1, _hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨hmuC, hmu⟩ :=
    hdata.weight_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨V, hV, hVcpt, _hdiagV, hVtarget, hVsource, hVstage, hVconv⟩ :=
    hpair.exists_diag_inv hC1 hC1q
  let diag : E → E × E := fun z ↦ (z, z)
  let Kdiag : Set (E × E) := diag '' C1 alpha
  let G : Set (E × E) := V ∩ (U alpha ×ˢ U alpha)
  have hKdiag : IsCompact Kdiag :=
    hC1.image_of_continuousOn
      (continuous_id.prodMk continuous_id).continuousOn
  have hG : IsOpen G := hV.inter (hU.prod hU)
  have hKdiagG : Kdiag ⊆ G := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨_hdiagV ⟨z, hz, rfl⟩, hC1U hz, hC1U hz⟩
  obtain ⟨V0, hV0, hdiagV0, hV0G, hV0cpt⟩ :=
    exists_open_between_and_isCompact_closure hKdiag hG hKdiagG
  have hV0target : V0 ⊆ eInf.target := by
    intro w hw
    exact hVtarget (subset_closure (hV0G (subset_closure hw)).1)
  obtain ⟨W0, PhiInf, hPhiInf, hroot⟩ :=
    hpair.exists_invVel_on hU hC1 hV0 hmuC hmu hC1U hC1q
      hV0target (by simpa only [diag, Kdiag] using hdiagV0)
  refine ⟨V, V0, W0, PhiInf, hV, hVcpt, hVtarget, hVsource,
    hVstage, hVconv, hV0, hV0cpt, ?_, ?_, ?_, hPhiInf, ?_⟩
  · simpa only [diag, Kdiag] using hdiagV0
  · exact fun w hw => (hV0G hw).1
  · exact fun w hw => (hV0G hw).2
  · simpa only using hroot

omit [FiniteDimensional Real E] [CompleteSpace E]
    [NeZero (Module.finrank Real E)] in



theorem cfg_pairs_tail
    {ι : Type} [Fintype ι] {S : Set E}
    {pts : Nat → E → ι → E}
    (hpts : MapCInfConvOnCompacts S pts (fun z _ => z))
    {K : Set (E × E)} (hK : IsCompact K)
    (hfst : Set.MapsTo (fun q : E × E => q.1) K S)
    {V : Set (E × E)} (hV : IsOpen V)
    (hlim : Set.MapsTo (fun q : E × E => (q.2, q.1)) K V) :
    ∀ᶠ m in atTop, ∀ q ∈ K, ∀ gamma : ι,
      (q.2, pts m q.1 gamma) ∈ V := by
  have hKfst : IsCompact ((fun q : E × E => q.1) '' K) :=
    hK.image_of_continuousOn continuous_fst.continuousOn
  have hKfstS : (fun q : E × E => q.1) '' K ⊆ S := by
    rintro z ⟨q, hq, rfl⟩
    exact hfst hq
  have hKflip : IsCompact ((fun q : E × E => (q.2, q.1)) '' K) :=
    hK.image_of_continuousOn
      (continuous_snd.prodMk continuous_fst).continuousOn
  have hKflipV : (fun q : E × E => (q.2, q.1)) '' K ⊆ V :=
    Set.image_subset_iff.mpr hlim
  obtain ⟨delta, hdelta, hthick⟩ :=
    hKflip.exists_thickening_subset_open hV hKflipV
  have htu := tendstoUniformlyOn_of_cPConv
    (hpts ((fun q : E × E => q.1) '' K) hKfst hKfstS 0)
  rw [Metric.tendstoUniformlyOn_iff] at htu
  filter_upwards [htu delta hdelta] with m hm
  intro q hq gamma
  apply hthick
  rw [Metric.mem_thickening_iff]
  refine ⟨(q.2, q.1), ⟨q, hq, rfl⟩, ?_⟩
  have hcoord :
      dist (pts m q.1 gamma) q.1 ≤
        dist (pts m q.1) (fun _ : ι => q.1) := by
    exact dist_le_pi_dist (pts m q.1) (fun _ : ι => q.1) gamma
  have hall : dist (pts m q.1) (fun _ : ι => q.1) < delta := by
    simpa only [dist_comm] using hm q.1 ⟨q, hq, rfl⟩
  simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using
    (lt_of_le_of_lt hcoord hall)

omit [FiniteDimensional Real E] [CompleteSpace E]
    [NeZero (Module.finrank Real E)] in


theorem cfg_snd_conv
    {ι : Type} [Fintype ι] {S : Set E} (hS : IsOpen S)
    {cfg : Nat → E → (ι → Real) × (ι → E)}
    {cfgInf : E → (ι → Real) × (ι → E)}
    (hcfgC : ∀ m, ContDiffOn Real (∞ : WithTop ℕ∞) (cfg m) S)
    (hcfgInfC : ContDiffOn Real (∞ : WithTop ℕ∞) cfgInf S)
    (hcfg : MapCInfConvOnCompacts S cfg cfgInf) :
    MapCInfConvOnCompacts S (fun m z => (cfg m z).2)
      (fun z => (cfgInf z).2) :=
  mapCInfConv_clm hS
    (ContinuousLinearMap.snd Real (ι → Real) (ι → E))
    hcfg hcfgC hcfgInfC



noncomputable def stageInvVelSub
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r)
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (n k l : Nat) (q : E × E) : E :=
  invVelSum (e n)
    (stageCfgSub inp P L hr phi hphi alpha k l q.1).1
    (stageCfgSub inp P L hr phi hphi alpha k l q.1).2 q.2



noncomputable def stageRootSub
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r)
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (PhiInf : E → E) (rho : Real) (n k l : Nat) (z : E) : E := by
  classical
  exact if h : ∃ x : E, dist x (PhiInf z) < rho ∧
        stageInvVelSub inp P L hr phi hphi alpha e n k l (z, x) = 0
    then Classical.choose h
    else PhiInf z



theorem stageRootSub_eq
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r)
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (PhiInf : E → E) (rho : Real) (n k l : Nat) (z x : E)
    (hx : dist x (PhiInf z) < rho)
    (hroot : stageInvVelSub inp P L hr phi hphi alpha e n k l
      (z, x) = 0)
    (huniq : ∀ y, dist y (PhiInf z) < rho →
      (stageInvVelSub inp P L hr phi hphi alpha e n k l (z, y) = 0 ↔
        y = x)) :
    stageRootSub inp P L hr phi hphi alpha e PhiInf rho n k l z = x := by
  rw [stageRootSub]
  split
  next h =>
    exact (huniq (Classical.choose h) (Classical.choose_spec h).1).mp
      (Classical.choose_spec h).2
  next h => exact False.elim (h ⟨x, hx, hroot⟩)



def HasStageRootCube
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (C1 : LiveSlot L inp.pack r → Set E)
    (alpha : LiveSlot L inp.pack r)
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (W : Set E) (PhiInf : E → E) (rho : Real)
    (Phi3 : Nat → Nat → Nat → E → E) : Prop :=
  IsOpen W ∧ IsCompact (closure W) ∧ C1 alpha ⊆ W ∧
  0 < rho ∧ Set.EqOn PhiInf id (C1 alpha) ∧
  (∀ (nn kn ln : Nat → Nat), Tendsto nn atTop atTop →
    Tendsto kn atTop atTop → Tendsto ln atTop atTop →
    MapCInfConvOnCompacts W
      (fun m => Phi3 (nn m) (kn m) (ln m)) PhiInf) ∧
  ∃ N : Nat, ∀ n ≥ N, ∀ k ≥ N, ∀ l ≥ N,
    ContDiffOn Real ∞ (Phi3 n k l) W ∧ ∀ z ∈ closure W,
    dist (Phi3 n k l z) (PhiInf z) < rho / 2 ∧
    stageInvVelSub inp P L hr phi hphi alpha e n k l
      (z, Phi3 n k l z) = 0 ∧
    (Analysis.partialFDeriv₂
      (stageInvVelSub inp P L hr phi hphi alpha e n k l)
      z (Phi3 n k l z)).IsInvertible ∧
    (∀ gamma : Fin (inp.pack.A r),
      (Phi3 n k l z,
        (stageCfgSub inp P L hr phi hphi alpha k l z).2 gamma) ∈
          (e n).target) ∧
    ∀ x, dist x (PhiInf z) < rho →
      (stageInvVelSub inp P L hr phi hphi alpha e n k l (z, x) = 0 ↔
        x = Phi3 n k l z)




theorem HasSuppConvData.exists_stage_root
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r)
    {Y : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hcompletePair : SeqMetricComplete (I := I) Y}
    {hconnPair : ∀ k,
      letI : TopologicalSpace (Y.obj k).M := (Y.obj k).topology
      ConnectedSpace (Y.obj k).M}
    {c : ∀ n : Nat, (Y.obj n).M}
    {qStage qInf : NNReal} {deltaStage deltaInf : Real}
    {e : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    {eInf : OpenPartialHomeomorph (E × E) (E × E)}
    (hpair : HasDiagPairConv (I := I) hcompletePair hconnPair c
      qStage qInf deltaStage deltaInf e eInf)
    (hC1q : C1 alpha ⊆ Metric.ball (0 : E) qInf) :
    ∃ (W : Set E) (PhiInf : E → E) (rho : Real),
      IsOpen W ∧ IsCompact (closure W) ∧ C1 alpha ⊆ W ∧
      0 < rho ∧ Set.EqOn PhiInf id (C1 alpha) ∧
      ∀ (nn kn ln : Nat → Nat), Tendsto nn atTop atTop →
        Tendsto kn atTop atTop → Tendsto ln atTop atTop →
        let F : Nat → E × E → E := fun m q =>
          stageInvVelSub inp P L hr phi hphi alpha e
            (nn m) (kn m) (ln m) q
        ∃ N : Nat, ∃ Phi : Nat → E → E,
          MapCInfConvOnCompacts W Phi PhiInf ∧
          (∀ m, ContDiffOn Real ∞ (Phi m) W) ∧
          (∀ m ≥ N, ∀ z ∈ closure W,
            dist (Phi m z) (PhiInf z) < rho / 2 ∧
             F m (z, Phi m z) = 0 ∧
             (Analysis.partialFDeriv₂ (F m) z (Phi m z)).IsInvertible ∧
             ∀ gamma : Fin (inp.pack.A r),
               (Phi m z,
                 (stageCfgSub inp P L hr phi hphi alpha
                   (kn m) (ln m) z).2 gamma) ∈ (e (nn m)).target) ∧
          ∀ m ≥ N, ∀ z ∈ closure W, ∀ x,
            dist x (PhiInf z) < rho →
              (F m (z, x) = 0 ↔ x = Phi m z) := by
  classical
  let i0 := baseIndex inp.decay inp.realizes inp.pack hr
  let mu : E → Fin (inp.pack.A r) → Real := fun z gamma =>
    rawWeights (cutRaw (aInf alpha i0) (aInf alpha) i0) z gamma
  obtain ⟨V, V0, W0, PhiInf, hV, _hVcpt, hVtarget, _hVsource,
      hVstage, hVconv, _hV0, _hV0cpt, _hdiagV0, hV0V, _hV0UU,
      hPhiInf, hT⟩ :=
    hdata.exists_invVel_core inp P L hr phi hphi U C0 C1 aInf
      Jinf Jbarinf alpha hpair hC1q
  let swap : E × E → E × E := fun q => (q.2, q.1)
  let D0 : Set (E × E) :=
    ((U alpha ×ˢ Set.univ) ∩ swap ⁻¹' V0)
  let FInf : E × E → E := fun q =>
    invVelSum eInf (mu q.1)
      (fun _ : Fin (inp.pack.A r) => q.1) q.2
  obtain ⟨T⟩ : Nonempty
      (Analysis.CompactRootTube D0 W0 (C1 alpha) FInf PhiInf) := by
    simpa only [D0, swap, FInf, mu, i0] using hT
  obtain ⟨D, T', hDcpt, hDD0, _hTW, _hTrho⟩ :=
    T.exists_domain_buffer
  refine ⟨T'.W, PhiInf, T'.rho, T'.isOpen_W,
    T'.isCompact_closure_W, T'.K_subset_W, T'.rho_pos, hPhiInf, ?_⟩
  intro nn kn ln hnn hkn hln
  obtain ⟨hU, _hC0, _hC1, _hC01, _hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  have hcfgData := hdata.cfgSub_data inp P L hr phi hphi U C0 C1
    aInf Jinf Jbarinf kn ln hkn hln alpha
  dsimp only at hcfgData
  obtain ⟨hcfgC, hcfgInfC, hcfg⟩ := hcfgData
  have hpts : MapCInfConvOnCompacts (U alpha)
      (fun m z => (stageCfgSub inp P L hr phi hphi alpha
        (kn m) (ln m) z).2)
      (fun z => fun _ : Fin (inp.pack.A r) => z) := by
    simpa only using cfg_snd_conv hU hcfgC hcfgInfC hcfg
  have hDfstC : Set.MapsTo (fun q : E × E => q.1) (closure D) (U alpha) := by
    intro q hq
    exact (hDD0 hq).1.1
  have hlimPairs : Set.MapsTo (fun q : E × E => (q.2, q.1))
      (closure D) V := by
    intro q hq
    exact hV0V (subset_closure (hDD0 hq).2)
  have hmapC := cfg_pairs_tail hpts hDcpt hDfstC hV hlimPairs
  have hmap : ∀ᶠ m in atTop, ∀ q, q ∈ D →
      ∀ gamma : Fin (inp.pack.A r),
        (q.2, (stageCfgSub inp P L hr phi hphi alpha
          (kn m) (ln m) q.1).2 gamma) ∈ V := by
    filter_upwards [hmapC] with m hm
    intro q hq gamma
    exact hm q (subset_closure hq) gamma
  have hDfst : Set.MapsTo (fun q : E × E => q.1) D (U alpha) :=
    fun q hq => hDfstC (subset_closure hq)
  have hmapInf : ∀ q, q ∈ D → (q.2, q.1) ∈ V :=
    fun q hq => hlimPairs (subset_closure hq)
  have hVstageN := hnn.eventually hVstage
  have hnormal : ∀ n, IsNormalDiag (I := I) (Y.obj n)
      (hcompletePair.complete n) (hconnPair n) (c n)
        qStage deltaStage (e n) := by
    exact hpair.2.2.2.2.2.1
  have heC : ∀ᶠ m in atTop, ContDiffOn Real ∞
      ((e (nn m)).symm : E × E → E × E) V := by
    filter_upwards [hVstageN] with m hm
    exact (hnormal (nn m)).2.2.2.2.1.mono fun z hz =>
      hm.1 (subset_closure hz)
  have heInfC : ContDiffOn Real ∞
      (eInf.symm : E × E → E × E) V :=
    (hpair.2.2.2.2.2.2.2.2.2.2.1).mono fun z hz =>
      hVtarget (subset_closure hz)
  have hFconv : MapCInfConvOnCompacts D
      (fun m => stageInvVelSub inp P L hr phi hphi alpha e
        (nn m) (kn m) (ln m)) FInf := by
    simpa only [stageInvVelSub, FInf] using
      invVelSub_conv_on inp P L hr phi hphi alpha kn ln
        hU mu hcfgC hcfgInfC hcfg (fun m => e (nn m)) eInf hV heC
        heInfC (hVconv.comp_tendsto_atTop hnn) T'.isOpen_domain
        hDfst hmap hmapInf
  have hFcd : ∀ᶠ m in atTop, ContDiffOn Real ∞
      (stageInvVelSub inp P L hr phi hphi alpha e
        (nn m) (kn m) (ln m)) D := by
    filter_upwards [heC, hmap] with m hem hmm
    have hcfgD : ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun q : E × E => stageCfgSub inp P L hr phi hphi alpha
          (kn m) (ln m) q.1) D :=
      (hcfgC m).comp contDiff_fst.contDiffOn hDfst
    simpa only [stageInvVelSub] using
      NormalBranchHessian.invVelSum_contDiff hem hcfgD.fst hcfgD.snd
        contDiff_snd.contDiffOn hmm
  obtain ⟨Nroot, Phi, hPhi, hPhiC, hspec, huniq⟩ :=
    T'.exists_cInf_tail hFcd hFconv
  obtain ⟨Nmap, hNmap⟩ := eventually_atTop.mp hmap
  obtain ⟨Nstage, hNstage⟩ := eventually_atTop.mp hVstageN
  let N := max Nroot (max Nmap Nstage)
  refine ⟨N, Phi, hPhi, hPhiC, ?_, ?_⟩
  · intro m hm z hz
    have hmRoot : Nroot ≤ m :=
      (Nat.le_max_left Nroot (max Nmap Nstage)).trans hm
    have hmMap : Nmap ≤ m :=
      (Nat.le_max_left Nmap Nstage).trans
        ((Nat.le_max_right Nroot (max Nmap Nstage)).trans hm)
    have hmStage : Nstage ≤ m :=
      (Nat.le_max_right Nmap Nstage).trans
        ((Nat.le_max_right Nroot (max Nmap Nstage)).trans hm)
    have hs := hspec m hmRoot z hz
    refine ⟨hs.1, hs.2.1, hs.2.2, ?_⟩
    intro gamma
    have hrootD : (z, Phi m z) ∈ D := by
      apply T'.tube_subset z hz
      rw [Metric.mem_closedBall]
      exact hs.1.le.trans (by linarith [T'.rho_pos])
    have hpairV := hNmap m hmMap (z, Phi m z) hrootD gamma
    exact (hNstage m hmStage).1 (subset_closure hpairV)
  · intro m hm z hz x hx
    have hmRoot : Nroot ≤ m :=
      (Nat.le_max_left Nroot (max Nmap Nstage)).trans hm
    exact huniq m hmRoot z hz x hx



theorem HasSuppConvData.exists_stage_cube
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r)
    {Y : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hcompletePair : SeqMetricComplete (I := I) Y}
    {hconnPair : ∀ k,
      letI : TopologicalSpace (Y.obj k).M := (Y.obj k).topology
      ConnectedSpace (Y.obj k).M}
    {c : ∀ n : Nat, (Y.obj n).M}
    {qStage qInf : NNReal} {deltaStage deltaInf : Real}
    {e : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    {eInf : OpenPartialHomeomorph (E × E) (E × E)}
    (hpair : HasDiagPairConv (I := I) hcompletePair hconnPair c
      qStage qInf deltaStage deltaInf e eInf)
    (hC1q : C1 alpha ⊆ Metric.ball (0 : E) qInf) :
    ∃ (W : Set E) (PhiInf : E → E) (rho : Real)
        (Phi3 : Nat → Nat → Nat → E → E),
      HasStageRootCube inp P L hr phi hphi C1 alpha e
        W PhiInf rho Phi3 := by
  classical
  obtain ⟨W, PhiInf, rho, hW, hWcpt, hC1W, hrho, hPhiInf, hseq⟩ :=
    hdata.exists_stage_root inp P L hr phi hphi U C0 C1 aInf
      Jinf Jbarinf alpha hpair hC1q
  let Phi3 : Nat → Nat → Nat → E → E := fun n k l =>
    stageRootSub inp P L hr phi hphi alpha e PhiInf rho n k l
  have htriple : ∀ (nn kn ln : Nat → Nat), Tendsto nn atTop atTop →
      Tendsto kn atTop atTop → Tendsto ln atTop atTop →
      MapCInfConvOnCompacts W
        (fun m => Phi3 (nn m) (kn m) (ln m)) PhiInf := by
    intro nn kn ln hnn hkn hln
    obtain ⟨N, Phi, hPhi, _hPhiC, hspec, huniq⟩ :=
      hseq nn kn ln hnn hkn hln
    apply hPhi.congr_eventually hW
    · filter_upwards [eventually_ge_atTop N] with m hm
      intro z hz
      have hs := hspec m hm z (subset_closure hz)
      dsimp only [Phi3]
      exact stageRootSub_eq inp P L hr phi hphi alpha e PhiInf rho
        (nn m) (kn m) (ln m) z (Phi m z)
        (by linarith [hs.1, hrho]) hs.2.1
        (huniq m hm z (subset_closure hz))
    · intro z hz
      rfl
  let Q : Nat → Nat → Nat → Prop := fun n k l =>
    ContDiffOn Real ∞ (Phi3 n k l) W ∧ ∀ z ∈ closure W,
      dist (Phi3 n k l z) (PhiInf z) < rho / 2 ∧
      stageInvVelSub inp P L hr phi hphi alpha e n k l
        (z, Phi3 n k l z) = 0 ∧
      (Analysis.partialFDeriv₂
        (stageInvVelSub inp P L hr phi hphi alpha e n k l)
        z (Phi3 n k l z)).IsInvertible ∧
      (∀ gamma : Fin (inp.pack.A r),
        (Phi3 n k l z,
          (stageCfgSub inp P L hr phi hphi alpha k l z).2 gamma) ∈
            (e n).target) ∧
      ∀ x, dist x (PhiInf z) < rho →
        (stageInvVelSub inp P L hr phi hphi alpha e n k l (z, x) = 0 ↔
          x = Phi3 n k l z)
  have hQ : ∀ (nn kn ln : Nat → Nat), Tendsto nn atTop atTop →
      Tendsto kn atTop atTop → Tendsto ln atTop atTop →
      ∀ᶠ m in atTop, Q (nn m) (kn m) (ln m) := by
    intro nn kn ln hnn hkn hln
    obtain ⟨N, Phi, _hPhi, hPhiC, hspec, huniq⟩ :=
      hseq nn kn ln hnn hkn hln
    filter_upwards [eventually_ge_atTop N] with m hm
    have heq : Set.EqOn (Phi3 (nn m) (kn m) (ln m)) (Phi m)
        (closure W) := by
      intro z hz
      have hs := hspec m hm z hz
      dsimp only [Phi3]
      exact stageRootSub_eq inp P L hr phi hphi alpha e PhiInf rho
        (nn m) (kn m) (ln m) z (Phi m z)
        (by linarith [hs.1, hrho]) hs.2.1
        (huniq m hm z hz)
    refine ⟨ContDiffOn.congr (hPhiC m) (heq.mono subset_closure), ?_⟩
    intro z hz
    have hs := hspec m hm z hz
    have heqz : Phi3 (nn m) (kn m) (ln m) z = Phi m z :=
      heq hz
    rw [heqz]
    exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, huniq m hm z hz⟩
  obtain ⟨N, hN⟩ := exists_three_tail hQ
  refine ⟨W, PhiInf, rho, Phi3, ?_⟩
  exact ⟨hW, hWcpt, hC1W, hrho, hPhiInf, htriple, N, hN⟩




theorem HasStageRootCube.map_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (C1 : LiveSlot L inp.pack r → Set E)
    (alpha : LiveSlot L inp.pack r)
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (W : Set E) (PhiInf : E → E) (rho : Real)
    (Phi3 : Nat → Nat → Nat → E → E)
    (hroot : HasStageRootCube inp P L hr phi hphi C1 alpha e
      W PhiInf rho Phi3)
    {K : Set E} (hK : IsCompact K) (hKC1 : K ⊆ interior (C1 alpha))
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ n ≥ N, ∀ k ≥ N, ∀ l ≥ N,
      ∀ j ≤ p, ∀ z ∈ K,
        mapDerivNorm j (Phi3 n k l) id z ≤ eps := by
  rcases hroot with
    ⟨hW, _hWcpt, hC1W, _hrho, hPhiInf, htriple, _hrootTail⟩
  have hconvId : ∀ (nn kn ln : Nat → Nat), Tendsto nn atTop atTop →
      Tendsto kn atTop atTop → Tendsto ln atTop atTop →
      MapCInfConvOnCompacts (interior (C1 alpha))
        (fun m => Phi3 (nn m) (kn m) (ln m)) id := by
    intro nn kn ln hnn hkn hln
    have hconvW := htriple nn kn ln hnn hkn hln
    have hconvC1 : MapCInfConvOnCompacts (interior (C1 alpha))
        (fun m => Phi3 (nn m) (kn m) (ln m)) PhiInf :=
      fun K' hK' hK'C1 q =>
        hconvW K' hK'
          (hK'C1.trans (interior_subset.trans hC1W)) q
    apply hconvC1.congr isOpen_interior
    · intro m z hz
      rfl
    · exact (hPhiInf.mono interior_subset).symm
  exact MapCInfConvOnCompacts.three_tail hconvId hK hKC1 p eps heps



theorem HasStageRootCube.at_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (C1 : LiveSlot L inp.pack r → Set E)
    (alpha : LiveSlot L inp.pack r)
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (W : Set E) (PhiInf : E → E) (rho : Real)
    (Phi3 : Nat → Nat → Nat → E → E)
    (hroot : HasStageRootCube inp P L hr phi hphi C1 alpha e
      W PhiInf rho Phi3)
    {K : Set E} (hK : IsCompact K) (hKC1 : K ⊆ interior (C1 alpha))
    (Psi : Nat → Nat → E → E) (S : Nat → E → Prop)
    (hEq : ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ K, S k z →
      Psi k l =ᶠ[nhds z] Phi3 l k l)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ K, S k z →
      ContDiffAt Real ∞ (Psi k l) z ∧
      ∀ j ≤ p, mapDerivNorm j (Psi k l) id z ≤ eps := by
  obtain ⟨Nmap, hmap⟩ := hroot.map_tail inp P L hr phi hphi C1 alpha e
    W PhiInf rho Phi3 hK hKC1 p eps heps
  obtain ⟨Neq, hEqTail⟩ := hEq
  rcases hroot with
    ⟨hW, _hWcpt, hC1W, _hrho, _hPhiInf, _htriple, Nroot, hrootTail⟩
  refine ⟨max Neq (max Nmap Nroot), ?_⟩
  intro k hk l hl z hz hSz
  have hkEq : Neq ≤ k := by omega
  have hlEq : Neq ≤ l := by omega
  have hkMap : Nmap ≤ k := by omega
  have hlMap : Nmap ≤ l := by omega
  have hkRoot : Nroot ≤ k := by omega
  have hlRoot : Nroot ≤ l := by omega
  have hzW : z ∈ W :=
    hC1W (interior_subset (hKC1 hz))
  have hPhiAt : ContDiffAt Real ∞ (Phi3 l k l) z :=
    ((hrootTail l hlRoot k hkRoot l hlRoot).1).contDiffAt
      (hW.mem_nhds hzW)
  have hlocal := hEqTail k hkEq l hlEq z hz hSz
  refine ⟨hPhiAt.congr_of_eventuallyEq hlocal, ?_⟩
  intro j hj
  have hsub : (fun y => Psi k l y - id y) =ᶠ[nhds z]
      (fun y => Phi3 l k l y - id y) := by
    filter_upwards [hlocal] with y hy
    rw [hy]
  calc
    mapDerivNorm j (Psi k l) id z =
        mapDerivNorm j (Phi3 l k l) id z := by
      simp only [mapDerivNorm]
      rw [(Filter.EventuallyEq.iteratedFDeriv Real hsub j).eq_of_nhds]
    _ ≤ eps := hmap l hlMap k hkMap l hlMap j hj z hz



theorem HasStageRootCube.symm_dist_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r)
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (W : Set E) (PhiInf : E → E) (rho : Real)
    (Phi3 : Nat → Nat → Nat → E → E)
    (hroot : HasStageRootCube inp P L hr phi hphi C1 alpha e
      W PhiInf rho Phi3)
    (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ n ≥ N, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
      let Lphi := L.subseq hphi
      let Y := X.obj (Lphi.φ n)
      let c := seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : MetricSpace Y.M := (P (Lphi.φ n)).ms
      dist
          ((Geometry.Riemannian.NormalCoordinates.normalChartAt
            (I := I) Y.metric c).symm (Phi3 n k l z))
          ((Geometry.Riemannian.NormalCoordinates.normalChartAt
            (I := I) Y.metric c).symm z) < eps := by
  obtain ⟨_hU, hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨eta, heta, hetaSub⟩ :=
    hC0.exists_cthickening_subset_open isOpen_interior hC01
  let delta : Real := min eta (eps / 4)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min heta (by positivity)
  obtain ⟨N, hN⟩ := hroot.map_tail inp P L hr phi hphi C1 alpha e
    W PhiInf rho Phi3 hC0 hC01 0 delta hdelta
  refine ⟨N, ?_⟩
  intro n hn k hk l hl z hz
  dsimp only
  let Lphi := L.subseq hphi
  let Y := X.obj (Lphi.φ n)
  let c := seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := (P (Lphi.φ n)).ms
  have hcoord : dist (Phi3 n k l z) z ≤ delta := by
    simpa only [mapDerivNorm, norm_iteratedFDeriv_zero, id_eq, dist_eq_norm] using
      hN n hn k hk l hl 0 le_rfl z hz
  have hdeltaEta : delta ≤ eta := min_le_left _ _
  have hdeltaEps : delta ≤ eps / 4 := min_le_right _ _
  have hseg : segment Real (Phi3 n k l z) z ⊆ U alpha := by
    refine (segment_subset_closedBall_right _ _).trans ?_
    refine (Metric.closedBall_subset_closedBall (hcoord.trans hdeltaEta)).trans ?_
    exact (Metric.closedBall_subset_cthickening hz eta).trans
      (hetaSub.trans (interior_subset.trans hC1U))
  obtain ⟨hRad, hExp, _hMaps⟩ :=
    hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf n alpha
  have hEquiv : NormalCoordMetricEquivOn (I := I) Y c (U alpha) := by
    intro w hw v
    exact inp.normalBounds.metric_equiv (Lphi.φ n) c w (hRad hw) v
  have hUtgt : U alpha ⊆
      (Geometry.Riemannian.NormalCoordinates.normalChartAt
        (I := I) Y.metric c).target := by
    intro w hw
    have hwBall := hExp hw
    have hwNorm : ‖w‖ < Geometry.Riemannian.expMapC2Radius
        (I := I) Y.metric c := by
      simpa only [Metric.mem_ball, dist_zero_right] using hwBall
    exact Geometry.Riemannian.ball_subset_normalChartAt_target
      (I := I) Y.metric c hwNorm
  have hman := NormalCoordMetricEquivOn.symm_dist_le
    (I := I) Y (P (Lphi.φ n)) hEquiv hUtgt hseg
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    linarith [Real.sqrt_two_lt_three_halves]
  have hscaled : Real.sqrt 2 * dist (Phi3 n k l z) z < eps := by
    calc
      Real.sqrt 2 * dist (Phi3 n k l z) z
          ≤ Real.sqrt 2 * delta :=
        mul_le_mul_of_nonneg_left hcoord (Real.sqrt_nonneg 2)
      _ ≤ 2 * delta := mul_le_mul_of_nonneg_right hsqrt hdelta.le
      _ ≤ 2 * (eps / 4) := mul_le_mul_of_nonneg_left hdeltaEps (by norm_num)
      _ < eps := by linarith
  exact hman.trans_lt hscaled



theorem HasSuppConvData.pts_dist_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r)
    (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
      ∀ gamma : Fin (inp.pack.A r),
        let Lphi := L.subseq hphi
        let Y := X.obj (Lphi.φ l)
        let c := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : MetricSpace Y.M := (P (Lphi.φ l)).ms
        dist
            ((Geometry.Riemannian.NormalCoordinates.normalChartAt
              (I := I) Y.metric c).symm z)
            ((Geometry.Riemannian.NormalCoordinates.normalChartAt
              (I := I) Y.metric c).symm
                (stagePtsSub inp P L phi hphi alpha k l z gamma)) < eps := by
  obtain ⟨_hU, hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨eta, heta, hetaSub⟩ :=
    hC0.exists_cthickening_subset_open isOpen_interior hC01
  let delta : Real := min eta (eps / 4)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min heta (by positivity)
  let PhiPts : Nat → Nat → Nat → E → (Fin (inp.pack.A r) → E) :=
    fun _ k l z => stagePtsSub inp P L phi hphi alpha k l z
  have hconv3 : ∀ an kn ln : Nat → Nat,
      Tendsto an atTop atTop → Tendsto kn atTop atTop →
        Tendsto ln atTop atTop →
          MapCInfConvOnCompacts (U alpha)
            (fun m => PhiPts (an m) (kn m) (ln m))
            (fun z _ => z) := by
    intro _an kn ln _han hkn hln
    exact hdata.ptsSub_conv inp P L hr phi hphi U C0 C1 aInf Jinf Jbarinf
      kn ln hkn hln alpha
  obtain ⟨N, hN⟩ := MapCInfConvOnCompacts.three_tail hconv3 hC0
    (hC01.trans (interior_subset.trans hC1U)) 0 delta hdelta
  refine ⟨N, ?_⟩
  intro k hk l hl z hz gamma
  dsimp only
  let Lphi := L.subseq hphi
  let Y := X.obj (Lphi.φ l)
  let c := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := (P (Lphi.φ l)).ms
  have htuple :
      ‖(fun gamma => stagePtsSub inp P L phi hphi alpha k l z gamma - z)‖ ≤
        delta := by
    simpa only [PhiPts, mapDerivNorm, norm_iteratedFDeriv_zero] using
      hN N le_rfl k hk l hl 0 le_rfl z hz
  have hcomp :
      ‖stagePtsSub inp P L phi hphi alpha k l z gamma - z‖ ≤ delta :=
    (norm_le_pi_norm
      (fun gamma => stagePtsSub inp P L phi hphi alpha k l z gamma - z)
      gamma).trans htuple
  have hcoord :
      dist z (stagePtsSub inp P L phi hphi alpha k l z gamma) ≤ delta := by
    simpa only [dist_eq_norm, norm_sub_rev] using hcomp
  have hdeltaEta : delta ≤ eta := min_le_left _ _
  have hdeltaEps : delta ≤ eps / 4 := min_le_right _ _
  have hseg : segment Real z
      (stagePtsSub inp P L phi hphi alpha k l z gamma) ⊆ U alpha := by
    refine (segment_subset_closedBall_left _ _).trans ?_
    refine (Metric.closedBall_subset_closedBall (hcoord.trans hdeltaEta)).trans ?_
    exact (Metric.closedBall_subset_cthickening hz eta).trans
      (hetaSub.trans (interior_subset.trans hC1U))
  obtain ⟨hRad, hExp, _hMaps⟩ :=
    hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf l alpha
  have hEquiv : NormalCoordMetricEquivOn (I := I) Y c (U alpha) := by
    intro w hw v
    exact inp.normalBounds.metric_equiv (Lphi.φ l) c w (hRad hw) v
  have hUtgt : U alpha ⊆
      (Geometry.Riemannian.NormalCoordinates.normalChartAt
        (I := I) Y.metric c).target := by
    intro w hw
    have hwBall := hExp hw
    have hwNorm : ‖w‖ < Geometry.Riemannian.expMapC2Radius
        (I := I) Y.metric c := by
      simpa only [Metric.mem_ball, dist_zero_right] using hwBall
    exact Geometry.Riemannian.ball_subset_normalChartAt_target
      (I := I) Y.metric c hwNorm
  have hman := NormalCoordMetricEquivOn.symm_dist_le
    (I := I) Y (P (Lphi.φ l)) hEquiv hUtgt hseg
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    linarith [Real.sqrt_two_lt_three_halves]
  have hscaled : Real.sqrt 2 *
      dist z (stagePtsSub inp P L phi hphi alpha k l z gamma) < eps := by
    calc
      Real.sqrt 2 * dist z
          (stagePtsSub inp P L phi hphi alpha k l z gamma)
          ≤ Real.sqrt 2 * delta :=
        mul_le_mul_of_nonneg_left hcoord (Real.sqrt_nonneg 2)
      _ ≤ 2 * delta := mul_le_mul_of_nonneg_right hsqrt hdelta.le
      _ ≤ 2 * (eps / 4) := mul_le_mul_of_nonneg_left hdeltaEps (by norm_num)
      _ < eps := by linarith
  exact hman.trans_lt hscaled

end HCGCompactness
end DifferentialGeometry
