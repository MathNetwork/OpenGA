import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtomPackage

set_option autoImplicit false
set_option linter.style.longLine false









noncomputable section

universe u uE uH uι

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]



def HasAtomWeightLim
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist)
    (pb : hd.PackingBound D) (r : Real) (hr : 0 ≤ r)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (U : Set E)
    (aInf : Fin (pb.A r) → E → Real) : Prop :=
  let atom : Nat → Fin (pb.A r) → E → Real := fun k gamma =>
    seqAtomChart (I := I) hd hD P L pb r beta gamma k
  let atomPi : Nat → E → (Fin (pb.A r) → Real) := fun k z gamma => atom k gamma z
  let atomInf : E → (Fin (pb.A r) → Real) := fun z gamma => aInf gamma z
  let i0 := baseIndex hd hre pb hr
  let weight : Nat → E → (Fin (pb.A r) → Real) := fun k z gamma =>
    rawWeights (cutRaw (atom k i0) (atom k) i0) z gamma
  let weightInf : E → (Fin (pb.A r) → Real) := fun z gamma =>
    rawWeights (cutRaw (aInf i0) aInf i0) z gamma
  (∀ gamma : Fin (pb.A r), L.alive (gamma : Nat) = false → aInf gamma = 0) ∧
    (∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (atomPi k) U) ∧
    ContDiffOn Real (∞ : WithTop ℕ∞) atomInf U ∧
    MapCInfConvOnCompacts U atomPi atomInf ∧
    (∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (weight k) U) ∧
    ContDiffOn Real (∞ : WithTop ℕ∞) weightInf U ∧
    MapCInfConvOnCompacts U weight weightInf



theorem HasAtomWeightLim.of_atoms
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist)
    (pb : hd.PackingBound D) (r : Real) (hr : 0 ≤ r)
    (hgp : ∀ k, Item3GpScaleAt (I := I) hd D P L pb r k)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M)
    (U : Set E) (hU : IsOpen U)
    (hcoverU : ∀ k,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
        U (⋃ gamma : Fin (pb.A r), L.innerBall hd D P pb r k gamma))
    (aInf : Fin (pb.A r) → E → Real)
    (hdead : ∀ gamma : Fin (pb.A r),
      L.alive (gamma : Nat) = false → aInf gamma = 0)
    (hatom : ∀ gamma : Fin (pb.A r),
      MapCInfConvOnCompacts U
        (fun k => seqAtomChart (I := I) hd hD P L pb r beta gamma k)
        (aInf gamma))
    (hatomSmooth : ∀ k (gamma : Fin (pb.A r)),
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (seqAtomChart (I := I) hd hD P L pb r beta gamma k) U)
    (hatomInfSmooth : ∀ gamma : Fin (pb.A r),
      ContDiffOn Real (∞ : WithTop ℕ∞) (aInf gamma) U) :
    HasAtomWeightLim (I := I) hd hD P L hre pb r hr beta U aInf := by
  exact atomWeight_of_atoms (I := I) hD P L hre pb r hr hgp beta U hU hcoverU
    aInf hdead hatom hatomSmooth hatomInfSmooth



omit [NeZero (Module.finrank ℝ E)] in
theorem HasAtomWeightLim.subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real} {hD : 0 < D}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {hre : hd.RealizesEdist}
    {pb : hd.PackingBound D} {r : Real} {hr : 0 ≤ r}
    {beta : ∀ k : Nat, (X.obj (L.φ k)).M} {U : Set E}
    {aInf : Fin (pb.A r) → E → Real}
    (h : HasAtomWeightLim (I := I) hd hD P L hre pb r hr beta U aInf)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    HasAtomWeightLim (I := I) hd hD P (L.subseq hψ) hre pb r hr
      (fun k => beta (ψ k)) U aInf := by
  classical
  dsimp only [HasAtomWeightLim] at h ⊢
  rcases h with
    ⟨hdead, hatomSmooth, hatomInfSmooth, hatomConv,
      hweightSmooth, hweightInfSmooth, hweightConv⟩
  refine ⟨hdead, ?_, hatomInfSmooth, ?_, ?_, hweightInfSmooth, ?_⟩
  · intro k
    simpa only [seqAtomChart_subseq] using hatomSmooth (ψ k)
  · simpa only [seqAtomChart_subseq] using hatomConv.comp_subseq hψ
  · intro k
    simpa only [seqAtomChart_subseq] using hweightSmooth (ψ k)
  · simpa only [seqAtomChart_subseq] using hweightConv.comp_subseq hψ



omit [NeZero (Module.finrank ℝ E)] in
theorem HasAtomWeightLim.weight_ne_tail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real} {hD : 0 < D}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {hre : hd.RealizesEdist}
    {pb : hd.PackingBound D} {r : Real} {hr : 0 ≤ r}
    {beta : ∀ k : Nat, (X.obj (L.φ k)).M} {U : Set E}
    {aInf : Fin (pb.A r) → E → Real}
    (hlim : HasAtomWeightLim (I := I) hd hD P L hre pb r hr beta U aInf)
    {z : E} (hz : z ∈ U) {gamma : Fin (pb.A r)}
    (hweight : rawWeights
      (cutRaw (aInf (baseIndex hd hre pb hr)) aInf (baseIndex hd hre pb hr))
      z gamma ≠ 0) :
    ∀ᶠ k in Filter.atTop,
      rawWeights
        (cutRaw
          (seqAtomChart (I := I) hd hD P L pb r beta
            (baseIndex hd hre pb hr) k)
          (fun target => seqAtomChart (I := I) hd hD P L pb r beta target k)
          (baseIndex hd hre pb hr)) z gamma ≠ 0 := by
  dsimp only [HasAtomWeightLim] at hlim
  rcases hlim with
    ⟨_hdead, _hatomSmooth, _hatomInfSmooth, _hatomConv,
      _hweightSmooth, _hweightInfSmooth, hweightConv⟩
  exact
    ((tendsto_pi_nhds.mp (tendsto_of_cInf hweightConv hz)) gamma).eventually_ne
      hweight



theorem HasAtomWeightLim.weight_data_of_innerCover
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real} {hD : 0 < D}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {hre : hd.RealizesEdist}
    {pb : hd.PackingBound D} {r : Real} {hr : 0 ≤ r}
    {beta : ∀ k : Nat, (X.obj (L.φ k)).M} {U : Set E}
    {aInf : Fin (pb.A r) → E → Real}
    (hlim : HasAtomWeightLim (I := I) hd hD P L hre pb r hr beta U aInf)
    (hgp : Item3GpScaleTail (I := I) hd D P L pb r)
    (hcoverU : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
        U (⋃ gamma : Fin (pb.A r), L.innerBall hd D P pb r k gamma)) :
    centerAverage.WeightDataOn U (fun _ : Fin (pb.A r) => Set.univ)
      (fun z gamma => rawWeights
        (cutRaw (aInf (baseIndex hd hre pb hr)) aInf
          (baseIndex hd hre pb hr)) z gamma) := by
  classical
  let i0 := baseIndex hd hre pb hr
  let weight : Nat → E → (Fin (pb.A r) → Real) := fun k z gamma =>
    rawWeights
      (cutRaw
        (seqAtomChart (I := I) hd hD P L pb r beta i0 k)
        (fun target => seqAtomChart (I := I) hd hD P L pb r beta target k)
        i0) z gamma
  let weightInf : E → (Fin (pb.A r) → Real) := fun z gamma =>
    rawWeights (cutRaw (aInf i0) aInf i0) z gamma
  have hstage : ∀ᶠ k in Filter.atTop,
      centerAverage.WeightDataOn
        (⋃ gamma : Fin (pb.A r), L.innerBall hd D P pb r k gamma)
        (fun gamma : Fin (pb.A r) => L.hatBall hd D P pb r k gamma)
        (rawWeights
          (cutRaw (seqAtom hd hD P L pb r k i0)
            (seqAtom hd hD P L pb r k) i0)) := by
    filter_upwards [hgp] with k hgpK
    exact seqWeights_data hd hD P L pb r k hgpK i0 Set.Subset.rfl
  dsimp only [HasAtomWeightLim] at hlim
  rcases hlim with
    ⟨_hdead, _hatomSmooth, _hatomInfSmooth, _hatomConv,
      _hweightSmooth, _hweightInfSmooth, hweightConv⟩
  have hconv (z : E) (hz : z ∈ U) (gamma : Fin (pb.A r)) :
      Filter.Tendsto (fun k => weight k z gamma) Filter.atTop
        (nhds (weightInf z gamma)) := by
    simpa only [weight, weightInf] using
      (tendsto_pi_nhds.mp (tendsto_of_cInf hweightConv hz)) gamma
  have hnonneg (z : E) (hz : z ∈ U) (gamma : Fin (pb.A r)) :
      0 ≤ weightInf z gamma := by
    apply ge_of_tendsto (hconv z hz gamma)
    filter_upwards [hcoverU, hstage] with k hmap hdata
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    simpa only [weight, seqAtomChart] using
      hdata.nonneg
        (expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
        (hmap hz) gamma
  have hsum (z : E) (hz : z ∈ U) : ∑ gamma, weightInf z gamma = 1 := by
    have hsumConv : Filter.Tendsto (fun k => ∑ gamma, weight k z gamma)
        Filter.atTop (nhds (∑ gamma, weightInf z gamma)) :=
      tendsto_finset_sum Finset.univ fun gamma _ => hconv z hz gamma
    have hsumStage : ∀ᶠ k in Filter.atTop, ∑ gamma, weight k z gamma = 1 := by
      filter_upwards [hcoverU, hstage] with k hmap hdata
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      simpa only [weight, seqAtomChart] using
        hdata.sum_one
          (expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
          (hmap hz)
    have hsumOne : Filter.Tendsto (fun k => ∑ gamma, weight k z gamma)
        Filter.atTop (nhds (1 : Real)) :=
      tendsto_const_nhds.congr' (hsumStage.mono fun _ hk => hk.symm)
    exact tendsto_nhds_unique hsumConv hsumOne
  change centerAverage.WeightDataOn U (fun _ : Fin (pb.A r) => Set.univ) weightInf
  refine
    { nonneg := hnonneg
      pos := ?_
      sum_one := hsum
      active_mem := ?_ }
  · intro z hz
    by_contra hpos
    have hle : ∀ gamma, weightInf z gamma ≤ 0 := by
      intro gamma
      exact le_of_not_gt (fun hgt => hpos ⟨gamma, hgt⟩)
    have hsumNonpos : ∑ gamma, weightInf z gamma ≤ 0 :=
      Finset.sum_nonpos fun gamma _ => hle gamma
    rw [hsum z hz] at hsumNonpos
    norm_num at hsumNonpos
  · intro _z _hz _gamma _hweight
    exact Set.mem_univ _



theorem HasAtomWeightLim.weight_data
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real} {hD : 0 < D}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {hre : hd.RealizesEdist}
    {pb : hd.PackingBound D} {r : Real} {hr : 0 ≤ r}
    {beta : ∀ k : Nat, (X.obj (L.φ k)).M} {U : Set E}
    {aInf : Fin (pb.A r) → E → Real}
    (hlim : HasAtomWeightLim (I := I) hd hD P L hre pb r hr beta U aInf)
    (hgp : Item3GpScaleTail (I := I) hd D P L pb r)
    (hsource : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
        U (L.hatSourceBall hd P r k)) :
    centerAverage.WeightDataOn U (fun _ : Fin (pb.A r) => Set.univ)
      (fun z gamma => rawWeights
        (cutRaw (aInf (baseIndex hd hre pb hr)) aInf
          (baseIndex hd hre pb hr)) z gamma) := by
  have hinner := L.innerBall_cover hd hD P hre pb r
  have hcoverU : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
        U (⋃ gamma : Fin (pb.A r), L.innerBall hd D P pb r k gamma) := by
    filter_upwards [hsource, hinner] with k hmap hcover
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    intro z hz
    apply hcover
    simpa only [NetLimitData.hatSourceBall] using hmap hz
  exact hlim.weight_data_of_innerCover hgp hcoverU



theorem HasAtomWeightLim.binter_of_weight
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real} {hD : 0 < D}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {hre : hd.RealizesEdist}
    {pb : hd.PackingBound D} {r : Real} {hr : 0 ≤ r}
    {beta : ∀ k : Nat, (X.obj (L.φ k)).M} {U : Set E}
    {aInf : Fin (pb.A r) → E → Real}
    (hlim : HasAtomWeightLim (I := I) hd hD P L hre pb r hr beta U aInf)
    (hgp : Item3GpScaleTail (I := I) hd D P L pb r)
    (alpha gamma : Fin (pb.A r)) {z : E} (hz : z ∈ U)
    (hsource : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun w => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) w)
        U (L.hatBall hd D P pb r k alpha))
    (hweight : rawWeights
      (cutRaw (aInf (baseIndex hd hre pb hr)) aInf (baseIndex hd hre pb hr))
      z gamma ≠ 0) :
    ∀ᶠ k in Filter.atTop,
      BInter hd D P L.lamInf (alpha : Nat) (gamma : Nat) (L.φ k) := by
  dsimp only [HasAtomWeightLim] at hlim
  rcases hlim with
    ⟨_hdead, _hatomSmooth, _hatomInfSmooth, _hatomConv,
      _hweightSmooth, _hweightInfSmooth, hweightConv⟩
  have hweightTendsto : Tendsto
      (fun k => rawWeights
        (cutRaw
          (seqAtomChart (I := I) hd hD P L pb r beta
            (baseIndex hd hre pb hr) k)
          (fun target => seqAtomChart (I := I) hd hD P L pb r beta target k)
          (baseIndex hd hre pb hr)) z gamma)
      Filter.atTop
      (𝓝 (rawWeights
        (cutRaw (aInf (baseIndex hd hre pb hr)) aInf (baseIndex hd hre pb hr))
        z gamma)) :=
    (tendsto_pi_nhds.mp (tendsto_of_cInf hweightConv hz)) gamma
  have hweightEventually : ∀ᶠ k in Filter.atTop,
      rawWeights
        (cutRaw
          (seqAtomChart (I := I) hd hD P L pb r beta
            (baseIndex hd hre pb hr) k)
          (fun target => seqAtomChart (I := I) hd hD P L pb r beta target k)
          (baseIndex hd hre pb hr)) z gamma ≠ 0 :=
    hweightTendsto.eventually_ne hweight
  filter_upwards [hsource, hgp, hweightEventually] with k hsourceK hgpK hweightK
  exact L.binter_of_mem_hat hd hD P pb r k (hsourceK hz)
    (seqAtom_mem_hat hd hD P L pb r k hgpK gamma (by
      simpa only [seqAtomChart] using
        (num_ne_of_cut_ne (num_ne_of_raw_ne hweightK))))



theorem exists_atom_lim
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (metricInput : NormalCoordMetricBoundInput (I := I) X)
    {hd : InjRadiusDecayInput (I := I) X} {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist)
    (pb : hd.PackingBound D) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) hd D P L pb r)
    (rho : Real) (beta : ∀ k : Nat, (X.obj (L.φ k)).M)
    (U : Set E) (hU : IsOpen U)
    (hovlJ : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      NormalOverlapOn (I := I) (X.obj (L.φ k)) (beta k)
        (seqCenterD hd P L k (gamma.1 : Nat)) U)
    (hUmetric : ∀ᶠ k in Filter.atTop,
      U ⊆ Metric.ball (0 : E) (metricInput.radius (L.φ k) (beta k)))
    (hUexp : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      U ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (beta k)))
    (hmapsJ : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
        U
        ((fun v : E => (expMap (I := I) (X.obj (L.φ k)).metric
            (seqCenterD hd P L k (gamma.1 : Nat))
            (show TangentSpace I (seqCenterD hd P L k (gamma.1 : Nat)) from v) :
              (X.obj (L.φ k)).M)) ''
          Metric.ball (0 : E) rho))
    (hVmetric : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      Metric.ball (0 : E) rho ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (seqCenterD hd P L k (gamma.1 : Nat))))
    (hVexp : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Metric.ball (0 : E) rho ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric
          (seqCenterD hd P L k (gamma.1 : Nat))))
    (hbetaU : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
        U (L.hatSourceBall hd P r k)) :
    ∃ (ψ : Nat → Nat) (hψ : StrictMono ψ)
        (aInf : Fin (pb.A r) → E → Real),
      HasAtomWeightLim (I := I) hd hD P (L.subseq hψ) hre pb r hr
        (fun k => beta (ψ k)) U aInf := by
  simpa only [HasAtomWeightLim] using
    existsAtomWeightH6 (I := I) metricInput hD P L hre pb r hr hgp rho
      beta U hU hovlJ hUmetric hUexp hmapsJ hVmetric hVexp hbetaU



theorem exists_atom_fin
    {ι : Type uι} (s : Finset ι)
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (metricInput : NormalCoordMetricBoundInput (I := I) X)
    {hd : InjRadiusDecayInput (I := I) X} {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist)
    (pb : hd.PackingBound D) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) hd D P L pb r)
    (rho : Real) (beta : ι → ∀ k : Nat, (X.obj (L.φ k)).M)
    (U : ι → Set E)
    (hU : ∀ i, i ∈ s → IsOpen (U i))
    (hovlJ : ∀ i, i ∈ s → ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      NormalOverlapOn (I := I) (X.obj (L.φ k)) (beta i k)
        (seqCenterD hd P L k (gamma.1 : Nat)) (U i))
    (hUmetric : ∀ i, i ∈ s → ∀ᶠ k in Filter.atTop,
      U i ⊆ Metric.ball (0 : E) (metricInput.radius (L.φ k) (beta i k)))
    (hUexp : ∀ i, i ∈ s → ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      U i ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (beta i k)))
    (hmapsJ : ∀ i, i ∈ s → ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta i k) z)
        (U i)
        ((fun v : E => (expMap (I := I) (X.obj (L.φ k)).metric
            (seqCenterD hd P L k (gamma.1 : Nat))
            (show TangentSpace I (seqCenterD hd P L k (gamma.1 : Nat)) from v) :
              (X.obj (L.φ k)).M)) ''
          Metric.ball (0 : E) rho))
    (hVmetric : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      Metric.ball (0 : E) rho ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (seqCenterD hd P L k (gamma.1 : Nat))))
    (hVexp : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Metric.ball (0 : E) rho ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric
          (seqCenterD hd P L k (gamma.1 : Nat))))
    (hbetaU : ∀ i, i ∈ s → ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta i k) z)
        (U i) (L.hatSourceBall hd P r k)) :
    ∃ (ψ : Nat → Nat) (hψ : StrictMono ψ),
      ∀ i, i ∈ s → ∃ aInf : Fin (pb.A r) → E → Real,
        HasAtomWeightLim (I := I) hd hD P (L.subseq hψ) hre pb r hr
          (fun k => beta i (ψ k)) (U i) aInf := by
  classical
  revert hU hovlJ hUmetric hUexp hmapsJ hbetaU
  induction s using Finset.induction with
  | empty =>
      intro _hU _hovlJ _hUmetric _hUexp _hmapsJ _hbetaU
      exact ⟨id, strictMono_id, fun i hi => by simp at hi⟩
  | @insert a s ha ih =>
      intro hU hovlJ hUmetric hUexp hmapsJ hbetaU
      obtain ⟨ψ₀, hψ₀, hprev⟩ := ih
        (fun i hi => hU i (Finset.mem_insert_of_mem hi))
        (fun i hi => hovlJ i (Finset.mem_insert_of_mem hi))
        (fun i hi => hUmetric i (Finset.mem_insert_of_mem hi))
        (fun i hi => hUexp i (Finset.mem_insert_of_mem hi))
        (fun i hi => hmapsJ i (Finset.mem_insert_of_mem hi))
        (fun i hi => hbetaU i (Finset.mem_insert_of_mem hi))
      let L₀ := L.subseq hψ₀
      have hgp₀ : Item3GpScaleTail (I := I) hd D P L₀ pb r :=
        hgp.subseq hd D P L pb r hψ₀
      have hovl₀ (gamma : LiveSlot L₀ pb r) : ∀ᶠ k in Filter.atTop,
          NormalOverlapOn (I := I) (X.obj (L₀.φ k)) (beta a (ψ₀ k))
            (seqCenterD hd P L₀ k (gamma.1 : Nat)) (U a) := by
        simpa only [L₀, NetLimitData.subseq, Function.comp_apply, seqCenterD_subseq] using
          hψ₀.tendsto_atTop.eventually
            (hovlJ a (Finset.mem_insert_self a s) gamma)
      have hUmetric₀ : ∀ᶠ k in Filter.atTop,
          U a ⊆ Metric.ball (0 : E)
            (metricInput.radius (L₀.φ k) (beta a (ψ₀ k))) := by
        simpa only [L₀, NetLimitData.subseq, Function.comp_apply] using
          hψ₀.tendsto_atTop.eventually
            (hUmetric a (Finset.mem_insert_self a s))
      have hUexp₀ : ∀ᶠ k in Filter.atTop,
          letI : TopologicalSpace (X.obj (L₀.φ k)).M := (X.obj (L₀.φ k)).topology
          letI : ChartedSpace H (X.obj (L₀.φ k)).M := (X.obj (L₀.φ k)).charted
          letI : IsManifold I ∞ (X.obj (L₀.φ k)).M := (X.obj (L₀.φ k)).smooth
          letI : T2Space (TangentBundle I (X.obj (L₀.φ k)).M) :=
            (X.obj (L₀.φ k)).t2TangentBundle
          U a ⊆ Metric.ball (0 : E)
            (expMapC2Radius (I := I) (X.obj (L₀.φ k)).metric
              (beta a (ψ₀ k))) := by
        simpa only [L₀, NetLimitData.subseq, Function.comp_apply] using
          hψ₀.tendsto_atTop.eventually (hUexp a (Finset.mem_insert_self a s))
      have hmaps₀ (gamma : LiveSlot L₀ pb r) : ∀ᶠ k in Filter.atTop,
          letI : TopologicalSpace (X.obj (L₀.φ k)).M := (X.obj (L₀.φ k)).topology
          letI : ChartedSpace H (X.obj (L₀.φ k)).M := (X.obj (L₀.φ k)).charted
          letI : IsManifold I ∞ (X.obj (L₀.φ k)).M := (X.obj (L₀.φ k)).smooth
          letI : T2Space (TangentBundle I (X.obj (L₀.φ k)).M) :=
            (X.obj (L₀.φ k)).t2TangentBundle
          Set.MapsTo
            (fun z => expMapDiffeo (I := I) (X.obj (L₀.φ k)).metric
              (beta a (ψ₀ k)) z)
            (U a)
            ((fun v : E => (expMap (I := I) (X.obj (L₀.φ k)).metric
                (seqCenterD hd P L₀ k (gamma.1 : Nat))
                (show TangentSpace I (seqCenterD hd P L₀ k (gamma.1 : Nat)) from v) :
                  (X.obj (L₀.φ k)).M)) ''
              Metric.ball (0 : E) rho) := by
        simpa only [L₀, NetLimitData.subseq, Function.comp_apply, seqCenterD_subseq] using
          hψ₀.tendsto_atTop.eventually
            (hmapsJ a (Finset.mem_insert_self a s) gamma)
      have hVmetric₀ (gamma : LiveSlot L₀ pb r) : ∀ᶠ k in Filter.atTop,
          Metric.ball (0 : E) rho ⊆ Metric.ball (0 : E)
            (metricInput.radius (L₀.φ k)
              (seqCenterD hd P L₀ k (gamma.1 : Nat))) := by
        simpa only [L₀, NetLimitData.subseq, Function.comp_apply, seqCenterD_subseq] using
          hψ₀.tendsto_atTop.eventually (hVmetric gamma)
      have hVexp₀ (gamma : LiveSlot L₀ pb r) : ∀ᶠ k in Filter.atTop,
          letI : TopologicalSpace (X.obj (L₀.φ k)).M := (X.obj (L₀.φ k)).topology
          letI : ChartedSpace H (X.obj (L₀.φ k)).M := (X.obj (L₀.φ k)).charted
          letI : IsManifold I ∞ (X.obj (L₀.φ k)).M := (X.obj (L₀.φ k)).smooth
          letI : T2Space (TangentBundle I (X.obj (L₀.φ k)).M) :=
            (X.obj (L₀.φ k)).t2TangentBundle
          Metric.ball (0 : E) rho ⊆ Metric.ball (0 : E)
            (expMapC2Radius (I := I) (X.obj (L₀.φ k)).metric
              (seqCenterD hd P L₀ k (gamma.1 : Nat))) := by
        simpa only [L₀, NetLimitData.subseq, Function.comp_apply, seqCenterD_subseq] using
          hψ₀.tendsto_atTop.eventually (hVexp gamma)
      have hbeta₀ : ∀ᶠ k in Filter.atTop,
          letI : TopologicalSpace (X.obj (L₀.φ k)).M := (X.obj (L₀.φ k)).topology
          letI : ChartedSpace H (X.obj (L₀.φ k)).M := (X.obj (L₀.φ k)).charted
          letI : IsManifold I ∞ (X.obj (L₀.φ k)).M := (X.obj (L₀.φ k)).smooth
          letI : T2Space (TangentBundle I (X.obj (L₀.φ k)).M) :=
            (X.obj (L₀.φ k)).t2TangentBundle
          Set.MapsTo
            (fun z => expMapDiffeo (I := I) (X.obj (L₀.φ k)).metric
              (beta a (ψ₀ k)) z)
            (U a) (L₀.hatSourceBall hd P r k) := by
        simpa only [L₀, NetLimitData.subseq, Function.comp_apply,
          NetLimitData.hatSourceBall_subseq] using
          hψ₀.tendsto_atTop.eventually (hbetaU a (Finset.mem_insert_self a s))
      obtain ⟨ψ₁, hψ₁, aInf, haInf⟩ :=
        exists_atom_lim (I := I) metricInput hD P L₀ hre pb r hr hgp₀ rho
          (fun k => beta a (ψ₀ k)) (U a) (hU a (Finset.mem_insert_self a s))
          hovl₀ hUmetric₀ hUexp₀ hmaps₀ hVmetric₀ hVexp₀ hbeta₀
      let ψ := ψ₀ ∘ ψ₁
      have hψ : StrictMono ψ := hψ₀.comp hψ₁
      refine ⟨ψ, hψ, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | his
      · refine ⟨aInf, ?_⟩
        simpa only [ψ, Function.comp_apply, L₀, NetLimitData.subseq] using haInf
      · obtain ⟨prevInf, hprevInf⟩ := hprev i his
        refine ⟨prevInf, ?_⟩
        have hsub := hprevInf.subseq hψ₁
        simpa only [ψ, Function.comp_apply, L₀, NetLimitData.subseq] using hsub

end HCGCompactness
end DifferentialGeometry
