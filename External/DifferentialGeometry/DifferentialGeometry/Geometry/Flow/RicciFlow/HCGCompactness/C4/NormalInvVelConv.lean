import DifferentialGeometry.Analysis.Calculus.MapConvergenceComp
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalBranchHessian

set_option autoImplicit false










noncomputable section

open Filter Set
open scoped BigOperators ContDiff Topology

namespace DifferentialGeometry
namespace HCGCompactness
namespace NormalBranchHessian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace Real Q]

omit [FiniteDimensional Real E] in


theorem invVelSum_contDiff
    {ι : Type*} [Fintype ι]
    {U : Set Q} {V : Set (E × E)}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    {mu : Q → ι → Real} {xi : Q → ι → E} {ctr : Q → E}
    (he : ContDiffOn Real (∞ : WithTop ℕ∞)
      (e.symm : E × E → E × E) V)
    (hmu : ContDiffOn Real (∞ : WithTop ℕ∞) mu U)
    (hxi : ContDiffOn Real (∞ : WithTop ℕ∞) xi U)
    (hctr : ContDiffOn Real (∞ : WithTop ℕ∞) ctr U)
    (hmap : ∀ z, z ∈ U → ∀ i, (ctr z, xi z i) ∈ V) :
    ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z => invVelSum e (mu z) (xi z) (ctr z)) U := by
  classical
  simp only [invVelSum]
  refine ContDiffOn.sum fun i _ => ?_
  exact (contDiffOn_pi.mp hmu i).smul
    ((he.comp (hctr.prodMk (contDiffOn_pi.mp hxi i))
      (fun z hz => hmap z hz i)).snd)



theorem invVelSum_conv
    {ι : Type*} [Fintype ι]
    {U : Set Q} (hU : IsOpen U)
    {V : Set (E × E)} (hV : IsOpen V)
    {e : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    {eInf : OpenPartialHomeomorph (E × E) (E × E)}
    {mu : Nat → Q → ι → Real} {muInf : Q → ι → Real}
    {xi : Nat → Q → ι → E} {xiInf : Q → ι → E}
    {ctr : Nat → Q → E} {ctrInf : Q → E}
    (he : MapCInfConvOnCompacts V
      (fun n ↦ ((e n).symm : E × E → E × E)) eInf.symm)
    (hmu : MapCInfConvOnCompacts U mu muInf)
    (hxi : MapCInfConvOnCompacts U xi xiInf)
    (hctr : MapCInfConvOnCompacts U ctr ctrInf)
    (hec : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      ((e n).symm : E × E → E × E) V)
    (heInfC : ContDiffOn Real (∞ : WithTop ℕ∞)
      (eInf.symm : E × E → E × E) V)
    (hmuc : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (mu n) U)
    (hmuInfC : ContDiffOn Real (∞ : WithTop ℕ∞) muInf U)
    (hxic : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (xi n) U)
    (hxiInfC : ContDiffOn Real (∞ : WithTop ℕ∞) xiInf U)
    (hctrC : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (ctr n) U)
    (hctrInfC : ContDiffOn Real (∞ : WithTop ℕ∞) ctrInf U)
    (hmap : ∀ n z, z ∈ U → ∀ i, (ctr n z, xi n z i) ∈ V)
    (hmapInf : ∀ z, z ∈ U → ∀ i, (ctrInf z, xiInf z i) ∈ V) :
    MapCInfConvOnCompacts U
      (fun n z ↦ invVelSum (e n) (mu n z) (xi n z) (ctr n z))
      (fun z ↦ invVelSum eInf (muInf z) (xiInf z) (ctrInf z)) := by
  classical
  have hsummand : ∀ i,
      MapCInfConvOnCompacts U
        (fun n z ↦ mu n z i • ((e n).symm (ctr n z, xi n z i)).2)
        (fun z ↦ muInf z i • (eInf.symm (ctrInf z, xiInf z i)).2) := by
    intro i
    have hmui : MapCInfConvOnCompacts U
        (fun n z ↦ mu n z i) (fun z ↦ muInf z i) :=
      mapCInfConv_clm hU
        (ContinuousLinearMap.proj i : (ι → Real) →L[Real] Real)
        hmu hmuc hmuInfC
    have hxii : MapCInfConvOnCompacts U
        (fun n z ↦ xi n z i) (fun z ↦ xiInf z i) :=
      mapCInfConv_clm hU
        (ContinuousLinearMap.proj i : (ι → E) →L[Real] E)
        hxi hxic hxiInfC
    have hpair : MapCInfConvOnCompacts U
        (fun n z ↦ (ctr n z, xi n z i))
        (fun z ↦ (ctrInf z, xiInf z i)) :=
      mapCInfConv_prodMk hU hctr hxii hctrC hctrInfC
        (fun n ↦ contDiffOn_pi.mp (hxic n) i)
        (contDiffOn_pi.mp hxiInfC i)
    have hpairC : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun z ↦ (ctr n z, xi n z i)) U :=
      fun n ↦ (hctrC n).prodMk (contDiffOn_pi.mp (hxic n) i)
    have hpairInfC : ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun z ↦ (ctrInf z, xiInf z i)) U :=
      hctrInfC.prodMk (contDiffOn_pi.mp hxiInfC i)
    have hinv : MapCInfConvOnCompacts U
        (fun n z ↦ (e n).symm (ctr n z, xi n z i))
        (fun z ↦ eInf.symm (ctrInf z, xiInf z i)) :=
      MapCInfConvOnCompacts.comp hU hV hpair he hpairC hpairInfC
        hec heInfC (fun z hz ↦ hmapInf z hz i)
        (fun n z hz ↦ hmap n z hz i)
    have hinvC : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun z ↦ (e n).symm (ctr n z, xi n z i)) U :=
      fun n ↦ (hec n).comp (hpairC n) (fun z hz ↦ hmap n z hz i)
    have hinvInfC : ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun z ↦ eInf.symm (ctrInf z, xiInf z i)) U :=
      heInfC.comp hpairInfC (fun z hz ↦ hmapInf z hz i)
    have hvel : MapCInfConvOnCompacts U
        (fun n z ↦ ((e n).symm (ctr n z, xi n z i)).2)
        (fun z ↦ (eInf.symm (ctrInf z, xiInf z i)).2) :=
      mapCInfConv_clm hU (ContinuousLinearMap.snd Real E E) hinv
        hinvC hinvInfC
    have hweightVel : MapCInfConvOnCompacts U
        (fun n z ↦ (mu n z i,
          ((e n).symm (ctr n z, xi n z i)).2))
        (fun z ↦ (muInf z i,
          (eInf.symm (ctrInf z, xiInf z i)).2)) :=
      mapCInfConv_prodMk hU hmui hvel
        (fun n ↦ contDiffOn_pi.mp (hmuc n) i)
        (contDiffOn_pi.mp hmuInfC i)
        (fun n ↦ (hinvC n).snd) hinvInfC.snd
    let smulMap : Real × E → E := fun p ↦ p.1 • p.2
    have hsmul : MapCInfConvOnCompacts (Set.univ : Set (Real × E))
        (fun _ : Nat ↦ smulMap) smulMap :=
      mapCInfConv_const smulMap
    have hsmulC : ContDiffOn Real (∞ : WithTop ℕ∞) smulMap Set.univ :=
      contDiff_smul.contDiffOn
    have hcomp : MapCInfConvOnCompacts U
        (fun n z ↦ smulMap
          (mu n z i, ((e n).symm (ctr n z, xi n z i)).2))
        (fun z ↦ smulMap
          (muInf z i, (eInf.symm (ctrInf z, xiInf z i)).2)) :=
      MapCInfConvOnCompacts.comp (E := Q) (F := Real × E) (G := E)
        hU isOpen_univ hweightVel hsmul
        (fun n ↦ (contDiffOn_pi.mp (hmuc n) i).prodMk (hinvC n).snd)
        ((contDiffOn_pi.mp hmuInfC i).prodMk hinvInfC.snd)
        (fun _ ↦ hsmulC) hsmulC
        (fun _ _ ↦ Set.mem_univ _) (fun _ _ _ ↦ Set.mem_univ _)
    simpa only [smulMap] using hcomp
  have hsummandC : ∀ i n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z ↦ mu n z i • ((e n).symm (ctr n z, xi n z i)).2) U := by
    intro i n
    exact (contDiffOn_pi.mp (hmuc n) i).smul
      (((hec n).comp
        ((hctrC n).prodMk (contDiffOn_pi.mp (hxic n) i))
        (fun z hz ↦ hmap n z hz i)).snd)
  have hsummandInfC : ∀ i, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z ↦ muInf z i • (eInf.symm (ctrInf z, xiInf z i)).2) U := by
    intro i
    exact (contDiffOn_pi.mp hmuInfC i).smul
      ((heInfC.comp
        (hctrInfC.prodMk (contDiffOn_pi.mp hxiInfC i))
        (fun z hz ↦ hmapInf z hz i)).snd)
  have hpi := mapCInfConv_pi hU hsummand hsummandC hsummandInfC
  let Lsum : (ι → E) →L[Real] E :=
    ∑ i : ι, ContinuousLinearMap.proj i
  have hpiC : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z i ↦ mu n z i • ((e n).symm (ctr n z, xi n z i)).2) U :=
    fun n ↦ contDiffOn_pi.mpr fun i ↦ hsummandC i n
  have hpiInfC : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z i ↦ muInf z i • (eInf.symm (ctrInf z, xiInf z i)).2) U :=
    contDiffOn_pi.mpr hsummandInfC
  have hsum := mapCInfConv_clm hU Lsum hpi hpiC hpiInfC
  simpa only [invVelSum, Lsum, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.proj_apply] using hsum




theorem invVelCfg_conv
    {ι : Type*} [Fintype ι]
    {U : Set Q} (hU : IsOpen U)
    {V : Set (E × E)} (hV : IsOpen V)
    {e : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    {eInf : OpenPartialHomeomorph (E × E) (E × E)}
    {cfg : Nat → Q → (ι → Real) × (ι → E)}
    {cfgInf : Q → (ι → Real) × (ι → E)}
    {ctr : Nat → Q → E} {ctrInf : Q → E}
    (he : MapCInfConvOnCompacts V
      (fun n ↦ ((e n).symm : E × E → E × E)) eInf.symm)
    (hcfg : MapCInfConvOnCompacts U cfg cfgInf)
    (hctr : MapCInfConvOnCompacts U ctr ctrInf)
    (hec : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      ((e n).symm : E × E → E × E) V)
    (heInfC : ContDiffOn Real (∞ : WithTop ℕ∞)
      (eInf.symm : E × E → E × E) V)
    (hcfgC : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (cfg n) U)
    (hcfgInfC : ContDiffOn Real (∞ : WithTop ℕ∞) cfgInf U)
    (hctrC : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (ctr n) U)
    (hctrInfC : ContDiffOn Real (∞ : WithTop ℕ∞) ctrInf U)
    (hmap : ∀ n z, z ∈ U → ∀ i, (ctr n z, (cfg n z).2 i) ∈ V)
    (hmapInf : ∀ z, z ∈ U → ∀ i, (ctrInf z, (cfgInf z).2 i) ∈ V) :
    MapCInfConvOnCompacts U
      (fun n z ↦ invVelSum (e n) (cfg n z).1 (cfg n z).2 (ctr n z))
      (fun z ↦ invVelSum eInf (cfgInf z).1 (cfgInf z).2 (ctrInf z)) := by
  have hmu : MapCInfConvOnCompacts U
      (fun n z ↦ (cfg n z).1) (fun z ↦ (cfgInf z).1) :=
    mapCInfConv_clm hU
      (ContinuousLinearMap.fst Real (ι → Real) (ι → E))
      hcfg hcfgC hcfgInfC
  have hxi : MapCInfConvOnCompacts U
      (fun n z ↦ (cfg n z).2) (fun z ↦ (cfgInf z).2) :=
    mapCInfConv_clm hU
      (ContinuousLinearMap.snd Real (ι → Real) (ι → E))
      hcfg hcfgC hcfgInfC
  exact invVelSum_conv hU hV he hmu hxi hctr hec heInfC
    (fun n ↦ (hcfgC n).fst) hcfgInfC.fst
    (fun n ↦ (hcfgC n).snd) hcfgInfC.snd
    hctrC hctrInfC hmap hmapInf




theorem invVelCfg_tail
    {ι : Type*} [Fintype ι]
    {U : Set Q} (hU : IsOpen U)
    {V : Set (E × E)} (hV : IsOpen V)
    {e : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    {eInf : OpenPartialHomeomorph (E × E) (E × E)}
    {cfg : Nat → Q → (ι → Real) × (ι → E)}
    {cfgInf : Q → (ι → Real) × (ι → E)}
    {ctr : Nat → Q → E} {ctrInf : Q → E}
    (he : MapCInfConvOnCompacts V
      (fun n ↦ ((e n).symm : E × E → E × E)) eInf.symm)
    (hcfg : MapCInfConvOnCompacts U cfg cfgInf)
    (hctr : MapCInfConvOnCompacts U ctr ctrInf)
    (hec : ∀ᶠ n in atTop, ContDiffOn Real (∞ : WithTop ℕ∞)
      ((e n).symm : E × E → E × E) V)
    (heInfC : ContDiffOn Real (∞ : WithTop ℕ∞)
      (eInf.symm : E × E → E × E) V)
    (hcfgC : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (cfg n) U)
    (hcfgInfC : ContDiffOn Real (∞ : WithTop ℕ∞) cfgInf U)
    (hctrC : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (ctr n) U)
    (hctrInfC : ContDiffOn Real (∞ : WithTop ℕ∞) ctrInf U)
    (hmap : ∀ᶠ n in atTop,
      ∀ z, z ∈ U → ∀ i, (ctr n z, (cfg n z).2 i) ∈ V)
    (hmapInf : ∀ z, z ∈ U → ∀ i,
      (ctrInf z, (cfgInf z).2 i) ∈ V) :
    MapCInfConvOnCompacts U
      (fun n z ↦ invVelSum (e n) (cfg n z).1 (cfg n z).2 (ctr n z))
      (fun z ↦ invVelSum eInf (cfgInf z).1 (cfgInf z).2 (ctrInf z)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hec.and hmap)
  let e' : Nat → OpenPartialHomeomorph (E × E) (E × E) := fun n ↦
    if N ≤ n then e n else eInf
  let cfg' : Nat → Q → (ι → Real) × (ι → E) := fun n ↦
    if N ≤ n then cfg n else cfgInf
  let ctr' : Nat → Q → E := fun n ↦
    if N ≤ n then ctr n else ctrInf
  have he' : MapCInfConvOnCompacts V
      (fun n ↦ ((e' n).symm : E × E → E × E)) eInf.symm := by
    apply he.congr_eventually hV
    · filter_upwards [eventually_ge_atTop N] with n hn
      intro z hz
      simp only [e', if_pos hn]
    · intro z hz
      rfl
  have hcfg' : MapCInfConvOnCompacts U cfg' cfgInf := by
    apply hcfg.congr_eventually hU
    · filter_upwards [eventually_ge_atTop N] with n hn
      intro z hz
      simp only [cfg', if_pos hn]
    · intro z hz
      rfl
  have hctr' : MapCInfConvOnCompacts U ctr' ctrInf := by
    apply hctr.congr_eventually hU
    · filter_upwards [eventually_ge_atTop N] with n hn
      intro z hz
      simp only [ctr', if_pos hn]
    · intro z hz
      rfl
  have hec' : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      ((e' n).symm : E × E → E × E) V := by
    intro n
    by_cases hn : N ≤ n
    · simpa only [e', if_pos hn] using (hN n hn).1
    · simpa only [e', if_neg hn] using heInfC
  have hcfgC' : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (cfg' n) U := by
    intro n
    by_cases hn : N ≤ n
    · simpa only [cfg', if_pos hn] using hcfgC n
    · simpa only [cfg', if_neg hn] using hcfgInfC
  have hctrC' : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (ctr' n) U := by
    intro n
    by_cases hn : N ≤ n
    · simpa only [ctr', if_pos hn] using hctrC n
    · simpa only [ctr', if_neg hn] using hctrInfC
  have hmap' : ∀ n z, z ∈ U → ∀ i,
      (ctr' n z, (cfg' n z).2 i) ∈ V := by
    intro n z hz i
    by_cases hn : N ≤ n
    · simpa only [ctr', cfg', if_pos hn] using (hN n hn).2 z hz i
    · simpa only [ctr', cfg', if_neg hn] using hmapInf z hz i
  have hfilled := invVelCfg_conv hU hV he' hcfg' hctr' hec' heInfC
    hcfgC' hcfgInfC hctrC' hctrInfC hmap' hmapInf
  apply hfilled.congr_eventually hU
  · filter_upwards [eventually_ge_atTop N] with n hn
    intro z hz
    simp only [e', cfg', ctr', if_pos hn]
  · intro z hz
    rfl

end NormalBranchHessian
end HCGCompactness
end DifferentialGeometry
