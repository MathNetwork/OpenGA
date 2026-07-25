import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepB1Producers
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBLocalMetrics
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtoms









noncomputable section

open Set
open scoped ContDiff Topology

namespace DifferentialGeometry
namespace HCGCompactness

universe uX uV

section QuadraticReadout

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace Real X]
variable {V : Type uV} [NormedAddCommGroup V] [NormedSpace Real V]




theorem mapCInf_comp_fd {Y Z : Type*}
    [NormedAddCommGroup Y] [NormedSpace Real Y] [FiniteDimensional Real Y]
    [NormedAddCommGroup Z] [NormedSpace Real Z]
    {U : Set X} {W : Set Y} (hU : IsOpen U) (hW : IsOpen W)
    {B : Nat -> X -> Y} {Binf : X -> Y}
    {A : Nat -> Y -> Z} {Ainf : Y -> Z}
    (hB : MapCInfConvOnCompacts U B Binf)
    (hA : MapCInfConvOnCompacts W A Ainf)
    (hBc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Binf U)
    (hAc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (A k) W)
    (hAinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Ainf W)
    (hmap : Set.MapsTo Binf U W) (hmapk : forall k, Set.MapsTo (B k) U W) :
    MapCInfConvOnCompacts U (fun k x => A k (B k x))
      (fun x => Ainf (Binf x)) := by
  letI : ProperSpace Y := FiniteDimensional.proper Real Y
  exact MapCInfConvOnCompacts.comp hU hW hB hA hBc hBinfc hAc hAinfc hmap hmapk



theorem mapCInf_constArg {Y F : Type*}
    [NormedAddCommGroup Y] [NormedSpace Real Y] [ProperSpace Y]
    [NormedAddCommGroup F] [NormedSpace Real F]
    {U : Set X} {W : Set Y} (hU : IsOpen U) (hW : IsOpen W)
    {A : Nat -> Y -> F} {Ainf : Y -> F} {y0 : Y}
    (hy0 : y0 ∈ W) (hA : MapCInfConvOnCompacts W A Ainf)
    (hAc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (A k) W)
    (hAinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Ainf W) :
    MapCInfConvOnCompacts U (fun k _ => A k y0) (fun _ => Ainf y0) := by
  have hconst : MapCInfConvOnCompacts U
      (fun _ : Nat => fun _ : X => y0) (fun _ : X => y0) :=
    mapCInfConv_const (U := U) (fun _ : X => y0)
  exact MapCInfConvOnCompacts.comp hU hW hconst hA
    (fun _ => contDiffOn_const) contDiffOn_const hAc hAinfc
    (fun _ _ => hy0) (fun _ _ _ => hy0)


def quadRead (B : X -> (V →L[Real] V →L[Real] Real))
    (v : X -> V) (x : X) : Real :=
  B x (v x) (v x)


theorem quadRead_contDiff {B : X -> (V →L[Real] V →L[Real] Real)}
    {v : X -> V} {n : WithTop ℕ∞}
    (hB : ContDiff Real n B) (hv : ContDiff Real n v) :
    ContDiff Real n (quadRead B v) := by
  exact (hB.clm_apply hv).clm_apply hv



theorem quadRead_conv
    [FiniteDimensional Real V]
    {U : Set X} (hU : IsOpen U)
    {B : Nat -> X -> (V →L[Real] V →L[Real] Real)}
    {Binf : X -> (V →L[Real] V →L[Real] Real)}
    {v : Nat -> X -> V} {vinf : X -> V}
    (hB : MapCInfConvOnCompacts U B Binf)
    (hv : MapCInfConvOnCompacts U v vinf)
    (hBc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Binf U)
    (hvc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn Real (∞ : WithTop ℕ∞) vinf U) :
    MapCInfConvOnCompacts U (fun k => quadRead (B k) (v k))
      (quadRead Binf vinf) := by
  let evalQuad : ((V →L[Real] V →L[Real] Real) × V) -> Real :=
    fun q => q.1 q.2 q.2
  have heval : ContDiff Real (∞ : WithTop ℕ∞) evalQuad := by
    exact (contDiff_fst.clm_apply contDiff_snd).clm_apply contDiff_snd
  have hpair := mapCInfConv_prodMk hU hB hv hBc hBinfc hvc hvinfc
  have hcomp := mapCInf_comp_fd hU isOpen_univ hpair
    (mapCInfConv_const (U := (Set.univ : Set ((V →L[Real] V →L[Real] Real) × V)))
      evalQuad)
    (fun k => (hBc k).prodMk (hvc k)) (hBinfc.prodMk hvinfc)
    (fun _ => heval.contDiffOn) heval.contDiffOn
    (Set.mapsTo_univ _ _) (fun _ => Set.mapsTo_univ _ _)
  exact hcomp



theorem quadBump_conv
    [FiniteDimensional Real V]
    {U : Set X} (hU : IsOpen U)
    {B : Nat -> X -> (V →L[Real] V →L[Real] Real)}
    {Binf : X -> (V →L[Real] V →L[Real] Real)}
    {v : Nat -> X -> V} {vinf : X -> V}
    (hB : MapCInfConvOnCompacts U B Binf)
    (hv : MapCInfConvOnCompacts U v vinf)
    (hBc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Binf U)
    (hvc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn Real (∞ : WithTop ℕ∞) vinf U)
    (f : Real -> Real) (hf : ContDiff Real (∞ : WithTop ℕ∞) f) :
    MapCInfConvOnCompacts U
      (fun k x => f (quadRead (B k) (v k) x))
      (fun x => f (quadRead Binf vinf x)) := by
  have hquad := quadRead_conv hU hB hv hBc hBinfc hvc hvinfc
  have hqc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (quadRead (B k) (v k)) U :=
    fun k => (hBc k).clm_apply (hvc k) |>.clm_apply (hvc k)
  have hqinfc : ContDiffOn Real (∞ : WithTop ℕ∞)
      (quadRead Binf vinf) U :=
    hBinfc.clm_apply hvinfc |>.clm_apply hvinfc
  exact MapCInfConvOnCompacts.comp hU isOpen_univ hquad
    (mapCInfConv_const (U := (Set.univ : Set Real)) f)
    hqc hqinfc (fun _ => hf.contDiffOn) hf.contDiffOn
    (Set.mapsTo_univ _ _) (fun _ => Set.mapsTo_univ _ _)



theorem mapCInf_apply {ι Q : Type*} [Fintype ι]
    [NormedAddCommGroup Q] [NormedSpace Real Q]
    {U : Set X} (hU : IsOpen U)
    {u : Nat -> X -> (ι -> Q)} {uinf : X -> (ι -> Q)}
    (hu : MapCInfConvOnCompacts U u uinf)
    (huc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (u k) U)
    (huinfc : ContDiffOn Real (∞ : WithTop ℕ∞) uinf U) (i : ι) :
    MapCInfConvOnCompacts U (fun k x => u k x i) (fun x => uinf x i) := by
  intro K hK hKU p epsilon hepsilon
  obtain ⟨k0, hk0⟩ := hu K hK hKU p epsilon hepsilon
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have hle : ((r : ℕ∞) : WithTop ℕ∞) <= (∞ : WithTop ℕ∞) := by
    exact_mod_cast le_top
  have hcd : forall j : ι, ContDiffAt Real (r : ℕ∞)
      (fun y => u k y j - uinf y j) x := by
    intro j
    exact (((contDiffOn_pi.mp (huc k) j).sub (contDiffOn_pi.mp huinfc j)).contDiffAt
      (hU.mem_nhds hxU)).of_le hle
  have hbase := hk0 k hk r hr x hx
  simp only [mapDerivNorm] at hbase ⊢
  change ‖iteratedFDeriv Real r (fun y j => u k y j - uinf y j) x‖ <= epsilon at hbase
  rw [iteratedFDeriv_pi hcd le_rfl, ContinuousMultilinearMap.opNorm_pi] at hbase
  exact (norm_le_pi_norm (fun j =>
    iteratedFDeriv Real r (fun y => u k y j - uinf y j) x) i).trans hbase




theorem quadPiBump_conv {ι : Type*} [Fintype ι]
    [FiniteDimensional Real V]
    {U : Set X} (hU : IsOpen U)
    {B : Nat -> X -> (ι -> (V →L[Real] V →L[Real] Real))}
    {Binf : X -> (ι -> (V →L[Real] V →L[Real] Real))}
    {v : Nat -> X -> V} {vinf : X -> V}
    (hB : MapCInfConvOnCompacts U B Binf)
    (hv : MapCInfConvOnCompacts U v vinf)
    (hBc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Binf U)
    (hvc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn Real (∞ : WithTop ℕ∞) vinf U)
    (i : ι) (f : Real -> Real) (hf : ContDiff Real (∞ : WithTop ℕ∞) f) :
    MapCInfConvOnCompacts U
      (fun k x => f (B k x i (v k x) (v k x)))
      (fun x => f (Binf x i (vinf x) (vinf x))) := by
  exact quadBump_conv hU (mapCInf_apply hU hB hBc hBinfc i) hv
    (fun k => contDiffOn_pi.mp (hBc k) i) (contDiffOn_pi.mp hBinfc i)
    hvc hvinfc f hf

section WeightConvergence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in

theorem cutRaw_contDiffOn {U : Set X} {a : ι -> X -> Real}
    (ha : forall i, ContDiffOn Real (∞ : WithTop ℕ∞) (a i) U)
    (i0 i : ι) :
    ContDiffOn Real (∞ : WithTop ℕ∞) (cutRaw (a i0) a i0 i) U := by
  by_cases hi : i = i0
  · subst i
    have heq : cutRaw (a i0) a i0 i0 = a i0 := by
      funext x
      exact cutRaw_same (a i0) a i0 x
    rw [heq]
    exact ha i0
  · have hkill : ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun x => (1 : Real) - a i0 x) U :=
      (contDiffOn_const (c := (1 : Real))).sub (ha i0)
    refine ContDiffOn.congr (hkill.mul (ha i)) ?_
    intro x _hx
    exact cutRaw_of_ne (a i0) a i0 i x hi

omit [Fintype ι] in

theorem cutRaw_conv {U : Set X} (hU : IsOpen U)
    {a : Nat -> ι -> X -> Real} {ainf : ι -> X -> Real}
    (hconv : forall i, MapCInfConvOnCompacts U (fun k => a k i) (ainf i))
    (hc : forall k i, ContDiffOn Real (∞ : WithTop ℕ∞) (a k i) U)
    (hcinf : forall i, ContDiffOn Real (∞ : WithTop ℕ∞) (ainf i) U)
    (i0 i : ι) :
    MapCInfConvOnCompacts U
      (fun k => cutRaw (a k i0) (a k) i0 i)
      (cutRaw (ainf i0) ainf i0 i) := by
  by_cases hi : i = i0
  · subst i
    have hseq : (fun k => cutRaw (a k i0) (a k) i0 i0) =
        (fun k => a k i0) := by
      funext k x
      exact cutRaw_same (a k i0) (a k) i0 x
    have hinf : cutRaw (ainf i0) ainf i0 i0 = ainf i0 := by
      funext x
      exact cutRaw_same (ainf i0) ainf i0 x
    rw [hseq, hinf]
    exact hconv i0
  · let oneSub : Real -> Real := fun t => 1 - t
    have hone : ContDiff Real (∞ : WithTop ℕ∞) oneSub :=
      contDiff_const.sub contDiff_id
    have hkill := mapCInf_comp_fd hU isOpen_univ (hconv i0)
      (mapCInfConv_const (U := (Set.univ : Set Real)) oneSub)
      (fun k => hc k i0) (hcinf i0) (fun _ => hone.contDiffOn) hone.contDiffOn
      (Set.mapsTo_univ _ _) (fun _ => Set.mapsTo_univ _ _)
    have hmul := mapCInfConv_mul hU hkill (hconv i)
      (fun k => contDiffOn_const.sub (hc k i0)) (contDiffOn_const.sub (hcinf i0))
      (fun k => hc k i) (hcinf i)
    refine hmul.congr hU (fun k x _ => ?_) (fun x _ => ?_)
    · simp only [oneSub]
      exact cutRaw_of_ne (a k i0) (a k) i0 i x hi
    · simp only [oneSub]
      exact cutRaw_of_ne (ainf i0) ainf i0 i x hi

omit [DecidableEq ι] in


theorem rawWeights_conv {U : Set X} (hU : IsOpen U)
    {num : Nat -> ι -> X -> Real} {numinf : ι -> X -> Real}
    {delta : Real} (hdelta : 0 < delta)
    (hconv : forall i, MapCInfConvOnCompacts U (fun k => num k i) (numinf i))
    (hc : forall k i, ContDiffOn Real (∞ : WithTop ℕ∞) (num k i) U)
    (hcinf : forall i, ContDiffOn Real (∞ : WithTop ℕ∞) (numinf i) U)
    (hlow : forall k, forall z, z ∈ U -> delta < ∑ j, num k j z)
    (hlowinf : forall z, z ∈ U -> delta < ∑ j, numinf j z) (i : ι) :
    MapCInfConvOnCompacts U
      (fun k z => rawWeights (num k) z i) (fun z => rawWeights numinf z i) := by
  simpa only [rawWeights, normWeights] using
    (normWeightsConv hU hdelta hconv hc hcinf hlow hlowinf i)

omit [NormedAddCommGroup X] [NormedSpace Real X] in


theorem cutRaw_sum_half {a : ι -> X -> Real} {i0 : ι} {x : X}
    (hbase : a i0 x ∈ Set.Icc (0 : Real) 1)
    (hnn : forall i, 0 <= a i x) (hcover : exists i, a i x = 1) :
    (1 / 2 : Real) <= ∑ i, cutRaw (a i0) a i0 i x := by
  have hrawnn : forall i, 0 <= cutRaw (a i0) a i0 i x :=
    fun i => cutRaw_nonneg hbase hnn i
  by_cases hhalf : (1 / 2 : Real) <= a i0 x
  · exact hhalf.trans (by
      simpa only [cutRaw_same] using
        (Finset.single_le_sum (fun j _ => hrawnn j) (Finset.mem_univ i0)))
  · obtain ⟨j, hj⟩ := hcover
    have hji : j ≠ i0 := by
      intro h
      subst j
      linarith
    have hjraw : (1 / 2 : Real) <= cutRaw (a i0) a i0 j x := by
      rw [cutRaw_of_ne (a i0) a i0 j x hji, hj, mul_one]
      linarith
    exact hjraw.trans
      (Finset.single_le_sum (fun q _ => hrawnn q) (Finset.mem_univ j))




theorem cutWeights_conv {U : Set X} (hU : IsOpen U)
    {a : Nat -> ι -> X -> Real} {ainf : ι -> X -> Real}
    (hconv : forall i, MapCInfConvOnCompacts U (fun k => a k i) (ainf i))
    (hc : forall k i, ContDiffOn Real (∞ : WithTop ℕ∞) (a k i) U)
    (hcinf : forall i, ContDiffOn Real (∞ : WithTop ℕ∞) (ainf i) U)
    (i0 : ι)
    (hbase : forall k z, z ∈ U -> a k i0 z ∈ Set.Icc (0 : Real) 1)
    (hnn : forall k z, z ∈ U -> forall i, 0 <= a k i z)
    (hcover : forall k z, z ∈ U -> exists i, a k i z = 1)
    (i : ι) :
    MapCInfConvOnCompacts U
      (fun k z => rawWeights (cutRaw (a k i0) (a k) i0) z i)
      (fun z => rawWeights (cutRaw (ainf i0) ainf i0) z i) := by
  have hraw : forall j, MapCInfConvOnCompacts U
      (fun k => cutRaw (a k i0) (a k) i0 j)
      (cutRaw (ainf i0) ainf i0 j) :=
    fun j => cutRaw_conv hU hconv hc hcinf i0 j
  have hrawc : forall k j, ContDiffOn Real (∞ : WithTop ℕ∞)
      (cutRaw (a k i0) (a k) i0 j) U :=
    fun k j => cutRaw_contDiffOn (fun q => hc k q) i0 j
  have hrawcinf : forall j, ContDiffOn Real (∞ : WithTop ℕ∞)
      (cutRaw (ainf i0) ainf i0 j) U :=
    fun j => cutRaw_contDiffOn hcinf i0 j
  have hlow : forall k, forall z, z ∈ U ->
      (1 / 4 : Real) < ∑ j, cutRaw (a k i0) (a k) i0 j z := by
    intro k z hz
    have hhalf := cutRaw_sum_half (hbase k z hz) (hnn k z hz) (hcover k z hz)
    linarith
  have hlowinf : forall z, z ∈ U ->
      (1 / 4 : Real) < ∑ j, cutRaw (ainf i0) ainf i0 j z := by
    intro z hz
    have hsum : Filter.Tendsto
        (fun k => ∑ j, cutRaw (a k i0) (a k) i0 j z) Filter.atTop
        (nhds (∑ j, cutRaw (ainf i0) ainf i0 j z)) :=
      tendsto_finset_sum Finset.univ fun j _ => tendsto_of_cInf (hraw j) hz
    have hhalf : (1 / 2 : Real) <= ∑ j, cutRaw (ainf i0) ainf i0 j z :=
      ge_of_tendsto hsum (Filter.Eventually.of_forall fun k =>
        cutRaw_sum_half (hbase k z hz) (hnn k z hz) (hcover k z hz))
    linarith
  exact rawWeights_conv hU (by norm_num : (0 : Real) < 1 / 4)
    hraw hrawc hrawcinf hlow hlowinf i

end WeightConvergence

end QuadraticReadout

section OriginMetric

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open scoped Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]



omit [NeZero (Module.finrank ℝ E)] in
theorem quadNormal_readout
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (beta gamma : Y.M)
    (f : ContDiffBump (0 : Real)) {z : E}
    (hsrc :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      expMapDiffeo (I := I) Y.metric beta z ∈
        (normalChartAt (I := I) Y.metric gamma).source) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    quadNormal Y.metric gamma f (expMapDiffeo (I := I) Y.metric beta z) =
      f (normalCoordMetric (I := I) Y gamma 0
        (normalTransition (I := I) Y beta gamma z)
        (normalTransition (I := I) Y beta gamma z)) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [quadNormal_of_mem Y.metric gamma f hsrc,
    normalMetric_zero (I := I) Y gamma]
  rfl


omit [NeZero (Module.finrank ℝ E)] in
theorem stepCAtom_readout
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (beta gamma : Y.M)
    (lam : Real) (hlam : 0 < lam) {z : E}
    (hsrc :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      expMapDiffeo (I := I) Y.metric beta z ∈
        (normalChartAt (I := I) Y.metric gamma).source) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    stepCAtom Y gamma lam hlam (expMapDiffeo (I := I) Y.metric beta z) =
      stepCBump lam hlam
        (normalCoordMetric (I := I) Y gamma 0
          (normalTransition (I := I) Y beta gamma z)
          (normalTransition (I := I) Y beta gamma z)) := by
  exact quadNormal_readout (I := I) Y beta gamma (stepCBump lam hlam) hsrc


noncomputable def stepCAtomChart
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (beta gamma : Y.M)
    (lam : Real) (hlam : 0 < lam) (z : E) : Real :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  stepCAtom Y gamma lam hlam (expMapDiffeo (I := I) Y.metric beta z)






noncomputable def seqCenterD
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (k gamma : Nat) : (X.obj (L.φ k)).M :=
  (seqCenter hd D P (L.φ k) gamma).getD (X.obj (L.φ k)).basepoint



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem seqCenterD_dist_eq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (k gamma : Nat) :
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    seqRadius hd D P (L.φ k) gamma =
      dist (seqCenterD hd P L k gamma) (X.obj (L.φ k)).basepoint := by
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  haveI : ProperSpace (X.obj (L.φ k)).M := (P (L.φ k)).proper
  unfold seqRadius seqCenterD seqCenter OrderedNet.netRadius
  cases OrderedNet.netCenter (X.obj (L.φ k)).basepoint (hd.lambda D)
      (hd.lambda_continuous D) gamma <;> simp



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem seqCenterD_subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) {ψ : Nat -> Nat} (hψ : StrictMono ψ)
    (k gamma : Nat) :
    seqCenterD hd P (L.subseq hψ) k gamma = seqCenterD hd P L (ψ k) gamma := rfl



def LiveSlot
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) :=
  {gamma : Fin (pb.A r) // L.alive (gamma : Nat) = true}


noncomputable instance liveSlotFintype
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) :
    Fintype (LiveSlot L pb r) := by
  letI : Finite (LiveSlot L pb r) :=
    Finite.of_injective (fun gamma : LiveSlot L pb r => gamma.1) Subtype.val_injective
  exact Fintype.ofFinite (LiveSlot L pb r)



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem seqCenterD_some
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (k gamma : Nat)
    (h : (seqCenter hd D P (L.φ k) gamma).isSome = true) :
    seqCenter hd D P (L.φ k) gamma = some (seqCenterD hd P L k gamma) := by
  cases hc : seqCenter hd D P (L.φ k) gamma with
  | none => simp [hc] at h
  | some c => simp [seqCenterD, hc]



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem seqCenterD_live
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (gamma : Nat) (hgamma : L.alive gamma = true) :
    ∀ᶠ k in Filter.atTop,
      seqCenter hd D P (L.φ k) gamma = some (seqCenterD hd P L k gamma) :=
  (L.alive_eventually gamma).mono fun k hk =>
    seqCenterD_some hd P L k gamma (hk.trans hgamma)


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem seqCenter_dead
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (gamma : Nat) (hgamma : L.alive gamma = false) :
    ∀ᶠ k in Filter.atTop, seqCenter hd D P (L.φ k) gamma = none :=
  (L.alive_eventually gamma).mono fun k hk => by
    cases hc : seqCenter hd D P (L.φ k) gamma with
    | none => rfl
    | some c => simp [hc, hgamma] at hk



noncomputable def seqAtomChart
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (gamma : Fin (pb.A r))
    (k : Nat) (z : E) : Real :=
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  seqAtom hd hD P L pb r k gamma
    (expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)


omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem seqAtomChart_subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (gamma : Fin (pb.A r))
    {ψ : Nat -> Nat} (hψ : StrictMono ψ) (k : Nat) :
    seqAtomChart (I := I) hd hD P (L.subseq hψ) pb r
        (fun j => beta (ψ j)) gamma k =
      seqAtomChart (I := I) hd hD P L pb r beta gamma (ψ k) := by
  unfold seqAtomChart seqAtom
  simp only [NetLimitData.subseq, NetLimitData.lamInf, Function.comp_apply]
  funext z
  cases hcenter : seqCenter hd D P (L.φ (ψ k)) (gamma : Nat) with
  | none =>
      change (0 : Real) = 0
      rfl
  | some c => congr



theorem seqAtomChart_smooth
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r k)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (gamma : Fin (pb.A r))
    {U : Set E}
    (hUx :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      U ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (beta k))) :
    ContDiffOn Real (∞ : WithTop ℕ∞)
      (seqAtomChart (I := I) hd hD P L pb r beta gamma k) U := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  rw [← contMDiffOn_iff_contDiffOn]
  simpa only [seqAtomChart] using
    (seqAtom_contMDiff (I := I) hd hD P L pb r k hgp gamma).comp_contMDiffOn
      ((expMapDiffeo_contMDiffOn_expBall (I := I) (X.obj (L.φ k)) (beta k)).mono hUx)



omit [NeZero (Module.finrank ℝ E)] in
theorem seqAtom_live_conv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (gamma : Fin (pb.A r))
    {U : Set E} (hU : IsOpen U) {ainf : E -> Real}
    (hgamma : L.alive (gamma : Nat) = true)
    (hconv : MapCInfConvOnCompacts U
      (fun k => stepCAtomChart (I := I) (X.obj (L.φ k)) (beta k)
        (seqCenterD hd P L k (gamma : Nat)) (L.lamInf (gamma : Nat))
        (hd.lambda_pos hD (L.rInf (gamma : Nat)))) ainf) :
    MapCInfConvOnCompacts U
      (fun k => seqAtomChart (I := I) hd hD P L pb r beta gamma k) ainf := by
  refine hconv.congr_eventually hU ?_ fun _ _ => rfl
  filter_upwards [seqCenterD_live hd P L (gamma : Nat) hgamma] with k hk
  intro z _hz
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  simpa only [seqAtomChart, stepCAtomChart] using congrFun
    (seqAtom_some hd hD P L pb r k gamma hk)
    (expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)



omit [NeZero (Module.finrank ℝ E)] in
theorem seqAtom_dead_conv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (gamma : Fin (pb.A r))
    {U : Set E} (hU : IsOpen U) (hgamma : L.alive (gamma : Nat) = false) :
    MapCInfConvOnCompacts U
      (fun k => seqAtomChart (I := I) hd hD P L pb r beta gamma k)
      (fun _ => 0) := by
  have hzero : MapCInfConvOnCompacts U
      (fun _ : Nat => fun _ : E => (0 : Real)) (fun _ => 0) :=
    mapCInfConv_const (fun _ : E => (0 : Real))
  refine hzero.congr_eventually hU ?_ fun _ _ => rfl
  filter_upwards [seqCenter_dead hd P L (gamma : Nat) hgamma] with k hk
  intro z _hz
  simp [seqAtomChart, seqAtom_none hd hD P L pb r k gamma hk]



theorem atom_disjoint_conv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (hgp : Item3GpScaleTail (I := I) hd D P L pb r)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (alpha gamma : Fin (pb.A r))
    {U : Set E} (hU : IsOpen U)
    (hsource : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
        U (L.hatBall hd D P pb r k alpha))
    (hdisjoint : ∀ᶠ k in Filter.atTop,
      ¬ BInter hd D P L.lamInf (alpha : Nat) (gamma : Nat) (L.φ k)) :
    MapCInfConvOnCompacts U
      (fun k => seqAtomChart (I := I) hd hD P L pb r beta gamma k)
      (fun _ => 0) := by
  have hzero : MapCInfConvOnCompacts U
      (fun _ : Nat => fun _ : E => (0 : Real)) (fun _ => 0) :=
    mapCInfConv_const (fun _ : E => (0 : Real))
  refine hzero.congr_eventually hU ?_ fun _ _ => rfl
  filter_upwards [hsource, hdisjoint, hgp] with k hsourceK hdisjointK hgpK
  intro z hz
  by_contra hne
  apply hdisjointK
  exact L.binter_of_mem_hat hd hD P pb r k (hsourceK hz)
    (seqAtom_mem_hat hd hD P L pb r k hgpK gamma (by
      simpa only [seqAtomChart] using hne))





omit [NeZero (Module.finrank ℝ E)] in
theorem seqAtoms_conv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) {U : Set E} (hU : IsOpen U)
    (ainf : Fin (pb.A r) -> E -> Real)
    (hlive : ∀ gamma : Fin (pb.A r), L.alive (gamma : Nat) = true ->
      MapCInfConvOnCompacts U
        (fun k => stepCAtomChart (I := I) (X.obj (L.φ k)) (beta k)
          (seqCenterD hd P L k (gamma : Nat)) (L.lamInf (gamma : Nat))
          (hd.lambda_pos hD (L.rInf (gamma : Nat)))) (ainf gamma)) :
    ∀ gamma : Fin (pb.A r),
      MapCInfConvOnCompacts U
        (fun k => seqAtomChart (I := I) hd hD P L pb r beta gamma k)
        (if L.alive (gamma : Nat) = true then ainf gamma else fun _ => 0) := by
  intro gamma
  cases hgamma : L.alive (gamma : Nat) with
  | false =>
      simpa only [hgamma, Bool.false_eq_true, ↓reduceIte] using
        seqAtom_dead_conv (I := I) hd hD P L pb r beta gamma hU hgamma
  | true =>
      simpa only [hgamma, ↓reduceIte] using
        seqAtom_live_conv (I := I) hd hD P L pb r beta gamma hU hgamma
          (hlive gamma hgamma)




omit [NeZero (Module.finrank ℝ E)] in
theorem stepCAtom_conv {ι : Type*} [Fintype ι]
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (center : ι -> forall k : Nat, (X.obj k).M)
    (beta : forall k : Nat, (X.obj k).M)
    (lam : ι -> Real) (hlam : forall i, 0 < lam i)
    {U : Set E} (hU : IsOpen U)
    {gInf : E -> (ι -> (E →L[Real] E →L[Real] Real))}
    (hg : MapCInfConvOnCompacts U
      (fun k _ i => normalCoordMetric (I := I) (X.obj k) (center i k) 0) gInf)
    (hginf : ContDiffOn Real (∞ : WithTop ℕ∞) gInf U)
    {Jinf : ι -> E -> E}
    (hJ : forall i, MapCInfConvOnCompacts U
      (fun k => normalTransition (I := I) (X.obj k) (beta k) (center i k))
      (Jinf i))
    (hJc : forall i k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (normalTransition (I := I) (X.obj k) (beta k) (center i k)) U)
    (hJinfc : forall i, ContDiffOn Real (∞ : WithTop ℕ∞) (Jinf i) U)
    (hsrc : forall i k z, z ∈ U ->
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      expMapDiffeo (I := I) (X.obj k).metric (beta k) z ∈
        (normalChartAt (I := I) (X.obj k).metric (center i k)).source)
    (i : ι) :
    MapCInfConvOnCompacts U
      (fun k => stepCAtomChart (I := I) (X.obj k) (beta k) (center i k)
        (lam i) (hlam i))
      (fun z => stepCBump (lam i) (hlam i)
        (gInf z i (Jinf i z) (Jinf i z))) := by
  have hraw := quadPiBump_conv hU hg (hJ i)
    (fun _ => contDiffOn_const) hginf (hJc i) (hJinfc i)
    i (stepCBump (lam i) (hlam i)) (stepCBump (lam i) (hlam i)).contDiff
  refine hraw.congr hU (fun k z hz => ?_) (fun _ _ => rfl)
  simpa only [stepCAtomChart] using
    (stepCAtom_readout (I := I) (X.obj k) (beta k) (center i k)
      (lam i) (hlam i) (hsrc i k z hz))





omit [NeZero (Module.finrank ℝ E)] in
theorem existsOriginMetric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : NormalCoordMetricBoundInput (I := I) X)
    (c : forall k : Nat, (X.obj k).M) :
    exists (phi : Nat -> Nat)
        (gInf : E -> (E →L[Real] E →L[Real] Real)),
      StrictMono phi ∧ ContDiffOn Real (∞ : WithTop ℕ∞) gInf Set.univ ∧
        MapCInfConvOnCompacts Set.univ
          (fun k _ => normalCoordMetric (I := I) (X.obj (phi k)) (c (phi k)) 0)
          gInf ∧
        forall z : E, forall v : E,
          (1 / 2 : Real) * ‖v‖ ^ 2 <= gInf z v v ∧
            gInf z v v <= 2 * ‖v‖ ^ 2 := by
  let g0 : Nat -> E -> (E →L[Real] E →L[Real] Real) :=
    fun k _ => normalCoordMetric (I := I) (X.obj k) (c k) 0
  have hzero : forall k, (0 : E) ∈ Metric.ball 0 (input.radius k (c k)) := by
    intro k
    rw [Metric.mem_ball, dist_self]
    exact input.radius_pos k (c k)
  have hsmooth : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (g0 k) Set.univ :=
    fun _ => contDiffOn_const
  have hbdd : forall r : Nat, forall K : Set E, IsCompact K -> K ⊆ Set.univ ->
      exists M : Real, forall k : Nat, forall x, x ∈ K ->
        ‖iteratedFDeriv Real r (g0 k) x‖ <= M := by
    intro r K _hK _hKU
    refine ⟨input.metricC 0, fun k x _hx => ?_⟩
    by_cases hr : r = 0
    · subst r
      simpa only [g0, norm_iteratedFDeriv_zero] using
        (input.metric_deriv k 0 (c k) 0 (hzero k))
    · simp only [g0, iteratedFDeriv_const_of_ne hr, Pi.zero_apply, norm_zero]
      exact input.metricC_nonneg 0
  have hequiv : forall k : Nat, forall z, z ∈ (Set.univ : Set E) -> forall v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 <= g0 k z v v ∧
        g0 k z v v <= 2 * ‖v‖ ^ 2 := by
    intro k _z _hz v
    exact input.metric_equiv k (c k) 0 (hzero k) v
  simpa only [g0, Set.mem_univ, forall_const] using
    (exists_metricLimit_on (E := E) isOpen_univ g0 hsmooth hbdd hequiv)




omit [NeZero (Module.finrank ℝ E)] in
theorem existsMetric0Univ {ι : Type*} [Fintype ι]
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : NormalCoordMetricBoundInput (I := I) X)
    (c : ι -> forall k : Nat, (X.obj k).M) :
    exists (phi : Nat -> Nat)
        (gInf : E -> (ι -> (E →L[Real] E →L[Real] Real))),
      StrictMono phi ∧ ContDiffOn Real (∞ : WithTop ℕ∞) gInf Set.univ ∧
        MapCInfConvOnCompacts Set.univ
          (fun k _ i => normalCoordMetric (I := I) (X.obj (phi k))
            (c i (phi k)) 0)
          gInf := by
  let g0 : Nat -> E -> (ι -> (E →L[Real] E →L[Real] Real)) :=
    fun k _ i => normalCoordMetric (I := I) (X.obj k) (c i k) 0
  have hzero : forall k i,
      (0 : E) ∈ Metric.ball 0 (input.radius k (c i k)) := by
    intro k i
    rw [Metric.mem_ball, dist_self]
    exact input.radius_pos k (c i k)
  have hsmooth : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (g0 k) Set.univ :=
    fun _ => contDiffOn_const
  have hbdd : forall r : Nat, forall K : Set E, IsCompact K -> K ⊆ Set.univ ->
      exists M : Real, forall k : Nat, forall x, x ∈ K ->
        ‖iteratedFDeriv Real r (g0 k) x‖ <= M := by
    intro r K _hK _hKU
    refine ⟨input.metricC 0, fun k x _hx => ?_⟩
    by_cases hr : r = 0
    · subst r
      rw [norm_iteratedFDeriv_zero, pi_norm_le_iff_of_nonneg (input.metricC_nonneg 0)]
      intro i
      simpa only [g0, norm_iteratedFDeriv_zero] using
        (input.metric_deriv k 0 (c i k) 0 (hzero k i))
    · simp only [g0, iteratedFDeriv_const_of_ne hr, Pi.zero_apply, norm_zero]
      exact input.metricC_nonneg 0
  obtain ⟨phi, gInf, hphi, hginf, hconv⟩ :=
    exists_cInf_subseq_on isOpen_univ g0 hsmooth hbdd
  simpa only [g0] using ⟨phi, gInf, hphi, hginf, hconv⟩




omit [NeZero (Module.finrank ℝ E)] in
theorem existsLiveMetric0
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : NormalCoordMetricBoundInput (I := I) X)
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) :
    exists (psi : Nat -> Nat)
        (gInf : E -> (LiveSlot L pb r -> (E →L[Real] E →L[Real] Real))),
      StrictMono psi ∧ ContDiffOn Real (∞ : WithTop ℕ∞) gInf Set.univ ∧
        MapCInfConvOnCompacts Set.univ
          (fun k _ gamma => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
            (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0)
          gInf := by
  classical
  let X' := X.subseq L.φ
  let input' : NormalCoordMetricBoundInput (I := I) X' := input.subseq L.φ
  let c : LiveSlot L pb r -> forall k : Nat, (X'.obj k).M :=
    fun gamma k => seqCenterD hd P L k (gamma.1 : Nat)
  obtain ⟨psi, gInf, hpsi, hginf, hconv⟩ :=
    existsMetric0Univ (I := I) input' c
  refine ⟨psi, gInf, hpsi, hginf, ?_⟩
  simpa only [X', c, PointedRiemannianSeq.subseq] using hconv



omit [NeZero (Module.finrank ℝ E)] in
theorem liveMetric0_equiv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : NormalCoordMetricBoundInput (I := I) X)
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    {psi : Nat → Nat}
    {gInf : E → (LiveSlot L pb r → (E →L[Real] E →L[Real] Real))}
    (hconv : MapCInfConvOnCompacts Set.univ
      (fun k _ gamma => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
        (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0)
      gInf) :
    ∀ gamma : LiveSlot L pb r, ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf 0 gamma v v ∧
        gInf 0 gamma v v ≤ 2 * ‖v‖ ^ 2 := by
  intro gamma v
  have htendAll : Filter.Tendsto
      (fun k gamma => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
        (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0)
      Filter.atTop (𝓝 (gInf 0)) :=
    tendsto_of_cInf hconv (Set.mem_univ 0)
  have htend : Filter.Tendsto
      (fun k => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
        (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0)
      Filter.atTop (𝓝 (gInf 0 gamma)) :=
    (tendsto_pi_nhds.mp htendAll) gamma
  have hcont : Continuous
      (fun c : E →L[Real] E →L[Real] Real => c v v) := by
    fun_prop
  have htendv : Filter.Tendsto
      (fun k => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
        (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0 v v)
      Filter.atTop (𝓝 (gInf 0 gamma v v)) :=
    (hcont.tendsto (gInf 0 gamma)).comp htend
  have hzero : ∀ k : Nat, (0 : E) ∈ Metric.ball 0
      (input.radius (L.φ (psi k))
        (seqCenterD hd P L (psi k) (gamma.1 : Nat))) := by
    intro k
    rw [Metric.mem_ball, dist_self]
    exact input.radius_pos _ _
  exact ⟨
    ge_of_tendsto htendv (Filter.Eventually.of_forall fun k =>
      (input.metric_equiv (L.φ (psi k))
        (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0 (hzero k) v).1),
    le_of_tendsto htendv (Filter.Eventually.of_forall fun k =>
      (input.metric_equiv (L.φ (psi k))
        (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0 (hzero k) v).2)⟩

end OriginMetric

end HCGCompactness
end DifferentialGeometry
