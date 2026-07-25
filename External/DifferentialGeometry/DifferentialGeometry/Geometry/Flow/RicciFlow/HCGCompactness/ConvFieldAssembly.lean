import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SourceDomainFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MovingShiRestrictOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvWindowAll
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricDerivNormRestrict
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivArityBridge
import DifferentialGeometry.Geometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Metric.BumpExtend
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvWindowSolutions

set_option autoImplicit false
set_option linter.style.longLine false











































noncomputable section

open Set Function Filter Bundle Manifold TopologicalSpace
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow (SolutionOn IsSolutionOn)

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section ConvField

variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat -> Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)


def SrcSigma : Prop :=
  forall k : Nat, letI : TopologicalSpace P.M := P.topology; IsSigmaCompact (Φ.source k)


def TgtSigma : Prop :=
  forall k : Nat,
    letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
    IsSigmaCompact (Φ.target k)




noncomputable def srcMetric (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ) (k : Nat) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k) :=
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
  letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k); infer_instance
  fun t => (sourceFlow (I := I) Φ k (hsrc k) (htgt k)).family.metric t





noncomputable def refRes (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (hsrc : SrcSigma Φ) (k : Nat) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    SmoothRiemannianMetric I (SourceDomain (I := I) Φ k) :=
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  let sourceSigma : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) := by
    change SigmaCompactSpace (SourceDomain (I := I) Φ k)
    exact sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceT2 : T2Space ↥(sourceOpen (I := I) Φ k) := by
    change T2Space (SourceDomain (I := I) Φ k)
    exact sourceDomT2 (I := I) Φ k
  @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
    P.M P.topology P.charted P.smooth inferInstance
    R (sourceOpen (I := I) Φ k) sourceSigma sourceT2










structure BumpFamily where

  grow : Nat -> Set P.M

  grow_compact : forall k : Nat,
    letI : TopologicalSpace P.M := P.topology
    IsCompact (grow k)

  grow_subset : forall k : Nat,
    letI : TopologicalSpace P.M := P.topology
    grow k ⊆ Φ.source k

  grow_cover : forall K : Set P.M,
    letI : TopologicalSpace P.M := P.topology
    IsCompact K -> exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ grow k

  chi : Nat -> P.M -> Real

  chi_smooth : forall k : Nat,
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (chi k)

  chi01 : forall (k : Nat) (x : P.M), chi k x ∈ Set.Icc (0 : Real) 1

  chi_supp : forall k : Nat,
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    tsupport (chi k) ⊆ Φ.source k





  chi_one : forall k : Nat,
    letI : TopologicalSpace P.M := P.topology
    exists W : Set P.M, IsOpen W /\ grow k ⊆ W /\ forall x : P.M, x ∈ W -> chi k x = 1







noncomputable def gSeqExt (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (k : Nat) (t : Real) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    SmoothRiemannianMetric I P.M :=
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceSigma : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) := by
    change SigmaCompactSpace (SourceDomain (I := I) Φ k)
    exact sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceT2 : T2Space ↥(sourceOpen (I := I) Φ k) := by
    change T2Space (SourceDomain (I := I) Φ k)
    exact sourceDomT2 (I := I) Φ k
  @SmoothRiemannianMetric.bumpExtendOpen E _ _ _ H _ I P.M _ _ _ R
    (sourceOpen (I := I) Φ k) sourceSigma sourceT2
    (srcMetric (I := I) Φ hsrc htgt k t)
    (bf.chi k) (bf.chi_smooth k) (bf.chi01 k) (bf.chi_supp k)









omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem nonempty_bumpFamily : Nonempty (BumpFamily (I := I) Φ) := by
  classical
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : T2Space P.M := P.t2
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  haveI : LocallyCompactSpace E := inferInstance
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace H P.M
  haveI : WeaklyLocallyCompactSpace P.M := inferInstance
  haveI : NormalSpace P.M := inferInstance

  set Kx : CompactExhaustion P.M := CompactExhaustion.choice P.M with hKxdef

  let Pfit : Nat -> Nat -> Prop := fun k j => (Kx j : Set P.M) ⊆ Φ.source k
  let bidx : Nat -> Nat := fun k => Nat.findGreatest (Pfit k) k
  let fits : Nat -> Prop := fun k => (Kx (bidx k) : Set P.M) ⊆ Φ.source k
  let grow : Nat -> Set P.M := fun k => if fits k then (Kx (bidx k) : Set P.M) else ∅
  have hgrow_subset : forall k, grow k ⊆ Φ.source k := by
    intro k
    simp only [grow]
    by_cases h : fits k
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact Set.empty_subset _
  have hgrow_compact : forall k, IsCompact (grow k) := by
    intro k
    simp only [grow]
    by_cases h : fits k
    · rw [if_pos h]; exact Kx.isCompact _
    · rw [if_neg h]; exact isCompact_empty

  have hgrow_cover : forall K : Set P.M, IsCompact K ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ grow k := by
    intro K hK
    obtain ⟨j0, hj0⟩ := Kx.exists_superset_of_isCompact hK
    obtain ⟨m0, hm0⟩ := Φ.source_subset (K := (Kx j0 : Set P.M)) (Kx.isCompact j0)
    refine ⟨max j0 m0, fun k hk => ?_⟩
    have hj0k : j0 <= k := le_trans (le_max_left j0 m0) hk
    have hm0k : m0 <= k := le_trans (le_max_right j0 m0) hk

    have hPj0 : Pfit k j0 := hm0 k hm0k
    have hle : j0 <= bidx k := Nat.le_findGreatest hj0k hPj0

    have hPbidx : Pfit k (bidx k) := Nat.findGreatest_spec hj0k hPj0
    have hfitsk : fits k := hPbidx
    have hsub : (Kx j0 : Set P.M) ⊆ grow k := by
      simp only [grow]; rw [if_pos hfitsk]; exact Kx.subset hle
    exact hj0.trans hsub

  have hchoice : forall k : Nat, exists f : P.M -> Real,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ f /\ (forall x : P.M, f x ∈ Set.Icc (0 : Real) 1) /\
        tsupport f ⊆ Φ.source k /\
        (exists W : Set P.M, IsOpen W /\ grow k ⊆ W /\ forall x : P.M, x ∈ W -> f x = 1) := by
    intro k
    have hgc : IsClosed (grow k) := (hgrow_compact k).isClosed

    obtain ⟨V, hVopen, hgV, hVcl⟩ :=
      normal_exists_closure_subset hgc (Φ.source_open k) (hgrow_subset k)

    obtain ⟨f, hf1, hfsupp, hf01⟩ :=
      exists_contMDiffMap_one_nhds_of_subset_interior (I := I) (M := P.M) (n := (⊤ : ℕ∞))
        hgc (s := grow k) (t := V)
        (hgV.trans hVopen.interior_eq.ge)
    refine ⟨fun x => f x, f.contMDiff, hf01, ?_, ?_⟩
    ·
      have hsupp : Function.support (fun x => f x) ⊆ V := by
        intro x hx
        by_contra hxV
        exact hx (hfsupp x hxV)
      calc tsupport (fun x => f x) ⊆ closure V := closure_mono hsupp
        _ ⊆ Φ.source k := hVcl
    ·
      have hev : {x : P.M | f x = 1} ∈ nhdsSet (grow k) :=
        hf1.mono fun x hx => by simpa using hx
      obtain ⟨W, hWopen, hgrowW, hWsub⟩ := mem_nhdsSet_iff_exists.mp hev
      exact ⟨W, hWopen, hgrowW, fun x hx => hWsub hx⟩
  choose chi hchi_smooth hchi01 hchi_supp hchi_one using hchoice
  exact ⟨{
    grow := grow
    grow_compact := hgrow_compact
    grow_subset := hgrow_subset
    grow_cover := hgrow_cover
    chi := chi
    chi_smooth := hchi_smooth
    chi01 := hchi01
    chi_supp := hchi_supp
    chi_one := hchi_one }⟩



section Eval

variable (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
  (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem gSeqExt_inner_of_mem (k : Nat) (t : Real)
    (x : P.M) (hx : letI : TopologicalSpace P.M := P.topology; x ∈ Φ.source k)
    (v w : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; TangentSpace I x) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    (gSeqExt (I := I) Φ R bf hsrc htgt k t).inner x v w =
      bf.chi k x • (srcMetric (I := I) Φ hsrc htgt k t).inner ⟨x, hx⟩ v w
        + (1 - bf.chi k x) • R.inner x v w := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceSigma : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) := by
    change SigmaCompactSpace (SourceDomain (I := I) Φ k); exact sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceT2 : T2Space ↥(sourceOpen (I := I) Φ k) := by
    change T2Space (SourceDomain (I := I) Φ k); exact sourceDomT2 (I := I) Φ k
  exact @bumpExtendOpen_inner_of_mem E _ _ _ H _ I P.M _ _ _ R
    (sourceOpen (I := I) Φ k) sourceSigma sourceT2
    (srcMetric (I := I) Φ hsrc htgt k t) (bf.chi k) (bf.chi_smooth k) (bf.chi01 k)
    (bf.chi_supp k) x hx v w



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem gSeqExt_inner_of_notMem (k : Nat) (t : Real)
    (x : P.M) (hx : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      x ∉ tsupport (bf.chi k))
    (v w : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; TangentSpace I x) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    (gSeqExt (I := I) Φ R bf hsrc htgt k t).inner x v w = R.inner x v w := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  let sourceSigma : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) := by
    change SigmaCompactSpace (SourceDomain (I := I) Φ k); exact sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceT2 : T2Space ↥(sourceOpen (I := I) Φ k) := by
    change T2Space (SourceDomain (I := I) Φ k); exact sourceDomT2 (I := I) Φ k
  exact @bumpExtendOpen_inner_of_notMem_tsupport E _ _ _ H _ I P.M _ _ _ R
    (sourceOpen (I := I) Φ k) sourceSigma sourceT2
    (srcMetric (I := I) Φ hsrc htgt k t) (bf.chi k) (bf.chi_smooth k) (bf.chi01 k)
    (bf.chi_supp k) x hx v w

end Eval



section Low







omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem hlow_gSeqExt
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (cLow β ψ : Real) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      forall (k : Nat) (t : Real), t ∈ Set.Icc β ψ ->
        forall (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k;
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k;
            TangentSpace I y),
          cLow * R.inner (y : P.M) v v <=
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
            (srcMetric (I := I) Φ hsrc htgt k t).inner y v v) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    forall rho : Nat -> Nat, StrictMono rho -> forall t, t ∈ Set.Icc β ψ ->
      exists c : Real, 0 < c /\ forall (k : Nat) (x : P.M) (v : TangentSpace I x),
        c * R.inner x v v <= (gSeqExt (I := I) Φ R bf hsrc htgt (rho k) t).inner x v v := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  intro rho _hrho t ht
  refine ⟨min cLow 1, lt_min hcLow one_pos, fun k x v => ?_⟩
  set c := min cLow 1 with hc
  have hc1 : c <= 1 := min_le_right _ _
  have hccLow : c <= cLow := min_le_left _ _

  have hRnn : 0 <= R.inner x v v := by
    by_cases hv : v = 0
    · subst hv; simp
    · exact (R.pos x v hv).le
  by_cases hx : x ∈ Φ.source (rho k)
  ·
    letI : TopologicalSpace (SourceDomain (I := I) Φ (rho k)) := sourceDomTop (I := I) Φ (rho k)
    letI : ChartedSpace H (SourceDomain (I := I) Φ (rho k)) := sourceDomCharted (I := I) Φ (rho k)
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ (rho k)) := sourceDomSmooth (I := I) Φ (rho k)
    rw [gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt (rho k) t x hx v v]
    set χ := bf.chi (rho k) x with hχdef
    have hχ01 := bf.chi01 (rho k) x
    have hχ0 : 0 <= χ := hχ01.1
    have hχ1 : χ <= 1 := hχ01.2

    have hsrc_low := hbound (rho k) t ht ⟨x, hx⟩ v
    set S := (srcMetric (I := I) Φ hsrc htgt (rho k) t).inner ⟨x, hx⟩ v v with hSdef
    set r := R.inner x v v with hrdef

    have hsrc_low' : cLow * r <= S := hsrc_low

    rw [smul_eq_mul, smul_eq_mul]
    have h1 : χ * (cLow * r) <= χ * S := mul_le_mul_of_nonneg_left hsrc_low' hχ0
    have hterm2 : c * ((1 - χ) * r) <= (1 - χ) * r := by
      have h1χ : 0 <= 1 - χ := by linarith
      calc c * ((1 - χ) * r) <= 1 * ((1 - χ) * r) :=
            mul_le_mul_of_nonneg_right hc1 (mul_nonneg h1χ hRnn)
        _ = (1 - χ) * r := one_mul _
    nlinarith [h1, hterm2, mul_le_mul_of_nonneg_left hccLow hχ0, hRnn, hχ0, hRnn]
  ·
    have hxsupp : x ∉ tsupport (bf.chi (rho k)) := fun h => hx (bf.chi_supp (rho k) h)
    rw [gSeqExt_inner_of_notMem (I := I) Φ R bf hsrc htgt (rho k) t x hxsupp v v]
    calc c * R.inner x v v <= 1 * R.inner x v v :=
          mul_le_mul_of_nonneg_right hc1 hRnn
      _ = R.inner x v v := one_mul _

end Low



section Bdd












omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem hbdd_gSeqExt
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real)
    (hcovTail : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall q : Nat, exists C : Real, forall (k : Nat) (t : Real), t ∈ Set.Icc β ψ ->
        forall z : P.M, z ∈ Φ.source k ->
          metricCovDerivNorm (I := I) q (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z <= C) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    forall rho : Nat -> Nat, StrictMono rho -> forall t, t ∈ Set.Icc β ψ ->
      forall q : Nat, forall K' : Set P.M, IsCompact K' -> exists C : Real,
        forall (k : Nat) (z : P.M), z ∈ K' ->
          metricCovDerivNorm (I := I) q (gSeqExt (I := I) Φ R bf hsrc htgt (rho k) t) R z <= C := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  intro rho hrho t ht q K' hK'

  obtain ⟨Ctail, hCtail⟩ := hcovTail q

  obtain ⟨k0, hk0⟩ := bf.grow_cover K' hK'

  have hhead : forall k : Nat, exists Ck : Real, forall z : P.M, z ∈ K' ->
      metricCovDerivNorm (I := I) q (gSeqExt (I := I) Φ R bf hsrc htgt (rho k) t) R z <= Ck := by
    intro k
    exact metricCovDerivNorm_bddOn (I := I) hK' q
      (gSeqExt (I := I) Φ R bf hsrc htgt (rho k) t) R
  choose Chead hChead using hhead

  have hne : (Finset.range (k0 + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos k0)⟩
  refine ⟨max Ctail ((Finset.range (k0 + 1)).sup' hne Chead), fun k z hz => ?_⟩
  by_cases hk : k0 <= k
  ·
    have hk' : k0 <= rho k := le_trans hk (hrho.id_le k)
    have hzsrc : z ∈ Φ.source (rho k) := bf.grow_subset (rho k) (hk0 (rho k) hk' hz)
    exact le_trans (hCtail (rho k) t ht z hzsrc) (le_max_left _ _)
  ·
    have hklt : k < k0 := Nat.lt_of_not_le hk
    refine le_trans (hChead k z hz) (le_trans ?_ (le_max_right _ _))
    exact Finset.le_sup' Chead (Finset.mem_range.2 (by omega))

end Bdd



section Lip

open Tensor0SBundle in
set_option backward.isDefEq.respectTransparency false in




























omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem hgLip_gSeqExt
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real)
    (hlipTail : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall p : Nat, exists Lt : Real, 0 <= Lt /\
        forall (k : Nat) (s t : Real), s ∈ Set.Icc β ψ -> t ∈ Set.Icc β ψ ->
          forall a : Nat, a <= p -> forall z : P.M, z ∈ bf.grow k ->
            metricDerivNorm (I := I) a (gSeqExt (I := I) Φ R bf hsrc htgt k s)
              (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z <= Lt * |s - t|)
    (hlipSrc : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        letI : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        letI : T2Space ↥(sourceOpen (I := I) Φ k) := sourceDomT2 (I := I) Φ k
        forall C : Set (SourceDomain (I := I) Φ k), IsCompact C -> forall p : Nat,
          exists Ls : Real, 0 <= Ls /\
            forall (s t : Real), s ∈ Set.Icc β ψ -> t ∈ Set.Icc β ψ ->
              forall b : Nat, b <= p -> forall y : SourceDomain (I := I) Φ k, y ∈ C ->
                metricDerivNorm (I := I) b (srcMetric (I := I) Φ hsrc htgt k s)
                  (srcMetric (I := I) Φ hsrc htgt k t)
                  (refRes (I := I) Φ R hsrc k) y <= Ls * |s - t|) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    forall K' : Set P.M, IsCompact K' -> forall p : Nat,
      exists Lp : Real, 0 <= Lp /\
        forall k : Nat, forall s, s ∈ Set.Icc β ψ -> forall t, t ∈ Set.Icc β ψ ->
          forall a : Nat, a <= p -> forall x, x ∈ K' ->
            metricDerivNorm (I := I) a (gSeqExt (I := I) Φ R bf hsrc htgt k s)
              (gSeqExt (I := I) Φ R bf hsrc htgt k t) R x <= Lp * |s - t| := by
  classical
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  intro K' hK' p

  obtain ⟨Lt, hLt0, hLt⟩ := hlipTail p
  obtain ⟨k0, hk0⟩ := bf.grow_cover K' hK'

  have hhead : forall k : Nat, exists Lk : Real, 0 <= Lk /\
      forall s, s ∈ Set.Icc β ψ -> forall t, t ∈ Set.Icc β ψ ->
        forall a : Nat, a <= p -> forall x, x ∈ K' ->
          metricDerivNorm (I := I) a (gSeqExt (I := I) Φ R bf hsrc htgt k s)
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R x <= Lk * |s - t| := by
    intro k

    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
    letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) <= ∞)
    letI : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
        (by decide : (2 : WithTop ℕ∞) <= ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
      change IsManifold I ∞ (SourceDomain (I := I) Φ k); infer_instance

    letI : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
    letI : T2Space ↥(sourceOpen (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ ↥(sourceOpen (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : IsManifold I 1 ↥(sourceOpen (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := ↥(sourceOpen (I := I) Φ k)) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) <= ∞)
    letI : IsManifold I 2 ↥(sourceOpen (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := ↥(sourceOpen (I := I) Φ k)) (n := (∞ : WithTop ℕ∞))
        (by decide : (2 : WithTop ℕ∞) <= ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↥(sourceOpen (I := I) Φ k) := by
      change IsManifold I ∞ (SourceDomain (I := I) Φ k); infer_instance

    have hKTc : IsCompact (K' ∩ tsupport (bf.chi k)) :=
      hK'.inter_right (isClosed_tsupport (bf.chi k))
    have hKTsub : K' ∩ tsupport (bf.chi k) ⊆ Φ.source k := fun z hz => bf.chi_supp k hz.2
    have hCc : IsCompact (sourceCompactSet (I := I) Φ k (K' ∩ tsupport (bf.chi k))) :=
      sourceCompactSet_isCompact (I := I) Φ k hKTc hKTsub

    obtain ⟨Ls, hLs0, hLs⟩ :=
      hlipSrc k (sourceCompactSet (I := I) Φ k (K' ∩ tsupport (bf.chi k))) hCc p

    set χ' : SourceDomain (I := I) Φ k -> Real :=
      fun y => bf.chi k (y : P.M) with hχ'def
    have hχ' : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ' :=
      (bf.chi_smooth k).comp (contMDiff_subtype_val (I := I) (U := sourceOpen (I := I) Φ k))

    have hχB : forall c : Nat, exists Cc : Real, 0 <= Cc /\
        forall y, y ∈ sourceCompactSet (I := I) Φ k (K' ∩ tsupport (bf.chi k)) ->
          Real.sqrt (normSq0S (I := I)
            (refRes (I := I) Φ R hsrc k) y (0 + c)
            (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 0
              (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
                (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ') c y)) <= Cc :=
      fun c => sqrtNormSq0S_bddOn (I := I) hCc (0 + c)
        (refRes (I := I) Φ R hsrc k)
        (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 0
          (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
            (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ') c)
    choose Cχ hCχ0 hCχ using hχB
    have hrange : (Finset.range (p + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos p)⟩
    set Cx : Real := (Finset.range (p + 1)).sup' hrange Cχ with hCxdef
    have hCx0 : 0 <= Cx :=
      le_trans (hCχ0 0) (Finset.le_sup' Cχ (Finset.mem_range.2 (Nat.succ_pos p)))
    have hCxge : forall c : Nat, c <= p -> Cχ c <= Cx := fun c hc =>
      Finset.le_sup' Cχ (Finset.mem_range.2 (Nat.lt_succ_of_le hc))
    refine ⟨2 ^ p * Cx * Ls,
      mul_nonneg (mul_nonneg (by positivity) hCx0) hLs0, fun s hs t ht a ha x hx => ?_⟩
    by_cases hxsupp : x ∈ tsupport (bf.chi k)
    ·
      have hxU : x ∈ Φ.source k := bf.chi_supp k hxsupp
      have hyC : (⟨x, hxU⟩ : SourceDomain (I := I) Φ k) ∈
          sourceCompactSet (I := I) Φ k (K' ∩ tsupport (bf.chi k)) := ⟨hx, hxsupp⟩

      obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I)
        (refRes (I := I) Φ R hsrc k)
        (⟨x, hxU⟩ : SourceDomain (I := I) Φ k)
      have hinv : MetricInverseInBasis_gen (I := I)
          (refRes (I := I) Φ R hsrc k)
          (⟨x, hxU⟩ : SourceDomain (I := I) Φ k) basis
          (identityInvMetric (Idx := Fin (Module.finrank Real
            (TangentSpace I (⟨x, hxU⟩ : SourceDomain (I := I) Φ k))))) := by
        have h' := metricInverseInBasis_of_orthonormal (I := I)
          (refRes (I := I) Φ R hsrc k) basis hON
        intro i j
        simpa [identityInvMetric, diagonalInvMetric] using h' i j

      have hsmul : metricTensorField (I := I)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I)
              (sourceOpen (I := I) Φ k))
          - metricTensorField (I := I)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
              (sourceOpen (I := I) Φ k))
          = tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H) (I := I)
              (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ'
              (metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k s)
                - metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k t)) := by
        refine DFunLike.ext _ _ (fun y => ?_)
        refine ContinuousMultilinearMap.ext (fun v => ?_)
        show (metricTensorField (I := I)
              ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I)
                (sourceOpen (I := I) Φ k)) y
            - metricTensorField (I := I)
              ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
                (sourceOpen (I := I) Φ k)) y) v
          = (χ' y • (metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k s) y
              - metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k t) y)) v
        rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply,
          ContinuousMultilinearMap.sub_apply]
        change
          (gSeqExt (I := I) Φ R bf hsrc htgt k s).inner (y : P.M) (v 0) (v 1) -
              (gSeqExt (I := I) Φ R bf hsrc htgt k t).inner (y : P.M) (v 0) (v 1) =
            χ' y *
              ((srcMetric (I := I) Φ hsrc htgt k s).inner y (v 0) (v 1) -
                (srcMetric (I := I) Φ hsrc htgt k t).inner y (v 0) (v 1))
        rw [gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k s (y : P.M) y.2 (v 0) (v 1),
          gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k t (y : P.M) y.2 (v 0) (v 1)]
        simp only [hχ'def, smul_eq_mul]
        ring

      have hres : metricDerivNorm (I := I) a
            ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I)
              (sourceOpen (I := I) Φ k))
            ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
              (sourceOpen (I := I) Φ k))
            (refRes (I := I) Φ R hsrc k)
            (⟨x, hxU⟩ : SourceDomain (I := I) Φ k)
          = metricDerivNorm (I := I) a (gSeqExt (I := I) Φ R bf hsrc htgt k s)
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R x :=
        metricDerivNorm_restrictOpen (I := I) _ _ _ (sourceOpen (I := I) Φ k) a ⟨x, hxU⟩
      rw [← hres,
        metricDerivNorm_eq_iterCov (I := I)
          ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I)
            (sourceOpen (I := I) Φ k))
          ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
            (sourceOpen (I := I) Φ k))
          (refRes (I := I) Φ R hsrc k) a basis hinv,
        hsmul]

      refine le_trans (iterCov_smulF_le (I := I)
        (refRes (I := I) Φ R hsrc k)
        (⟨x, hxU⟩ : SourceDomain (I := I) Φ k) basis hinv a χ' hχ'
        (metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k s)
          - metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k t))) ?_
      have hterm : forall c : Nat, c ∈ Finset.range (a + 1) ->
          (a.choose c : Real) *
            Real.sqrt (normSq0S (I := I)
              (refRes (I := I) Φ R hsrc k) (⟨x, hxU⟩ :
                SourceDomain (I := I) Φ k) (0 + c)
              (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 0
                (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
                  (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ') c ⟨x, hxU⟩)) *
            Real.sqrt (normSq0S (I := I)
              (refRes (I := I) Φ R hsrc k) (⟨x, hxU⟩ :
                SourceDomain (I := I) Φ k) (2 + (a - c))
              (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 2
                (metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k s)
                  - metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k t))
                (a - c) ⟨x, hxU⟩))
          <= (a.choose c : Real) * Cx * (Ls * |s - t|) := by
        intro c hc
        have hcp : c <= p := le_trans (Nat.le_of_lt_succ (Finset.mem_range.1 hc)) ha
        have hχle : Real.sqrt (normSq0S (I := I)
            (refRes (I := I) Φ R hsrc k) (⟨x, hxU⟩ :
              SourceDomain (I := I) Φ k) (0 + c)
            (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 0
              (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
                (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ') c ⟨x, hxU⟩))
            <= Cx := le_trans (hCχ c ⟨x, hxU⟩ hyC) (hCxge c hcp)
        have hsle : Real.sqrt (normSq0S (I := I)
            (refRes (I := I) Φ R hsrc k) (⟨x, hxU⟩ :
              SourceDomain (I := I) Φ k) (2 + (a - c))
            (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 2
              (metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k s)
                - metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k t))
              (a - c) ⟨x, hxU⟩)) <= Ls * |s - t| := by
          rw [← metricDerivNorm_eq_iterCov (I := I) (srcMetric (I := I) Φ hsrc htgt k s)
            (srcMetric (I := I) Φ hsrc htgt k t)
            (refRes (I := I) Φ R hsrc k) (a - c) basis hinv]
          exact hLs s t hs ht (a - c) (le_trans (Nat.sub_le a c) ha) ⟨x, hxU⟩ hyC
        calc (a.choose c : Real) *
              Real.sqrt (normSq0S (I := I)
                (refRes (I := I) Φ R hsrc k) (⟨x, hxU⟩ :
                  SourceDomain (I := I) Φ k) (0 + c)
                (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 0
                  (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
                    (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ') c ⟨x, hxU⟩)) *
              Real.sqrt (normSq0S (I := I)
                (refRes (I := I) Φ R hsrc k) (⟨x, hxU⟩ :
                  SourceDomain (I := I) Φ k) (2 + (a - c))
                (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 2
                  (metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k s)
                    - metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k t))
                  (a - c) ⟨x, hxU⟩))
            <= (a.choose c : Real) * Cx *
              Real.sqrt (normSq0S (I := I)
                (refRes (I := I) Φ R hsrc k) (⟨x, hxU⟩ :
                  SourceDomain (I := I) Φ k) (2 + (a - c))
                (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 2
                  (metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k s)
                    - metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k t))
                  (a - c) ⟨x, hxU⟩)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hχle (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
          _ <= (a.choose c : Real) * Cx * (Ls * |s - t|) :=
              mul_le_mul_of_nonneg_left hsle (mul_nonneg (Nat.cast_nonneg _) hCx0)
      refine le_trans (Finset.sum_le_sum hterm) ?_

      have hsum : (∑ c ∈ Finset.range (a + 1), (a.choose c : Real) * Cx * (Ls * |s - t|))
          = (2 : Real) ^ a * Cx * (Ls * |s - t|) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
      rw [hsum]
      have h2 : (2 : Real) ^ a <= (2 : Real) ^ p := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 <= 2) ha
      have hnn : 0 <= Cx * (Ls * |s - t|) :=
        mul_nonneg hCx0 (mul_nonneg hLs0 (abs_nonneg _))
      calc (2 : Real) ^ a * Cx * (Ls * |s - t|)
          = (2 : Real) ^ a * (Cx * (Ls * |s - t|)) := by ring
        _ <= (2 : Real) ^ p * (Cx * (Ls * |s - t|)) := mul_le_mul_of_nonneg_right h2 hnn
        _ = 2 ^ p * Cx * Ls * |s - t| := by ring
    ·
      set U₀ : TopologicalSpace.Opens P.M :=
        ⟨(tsupport (bf.chi k))ᶜ, (isClosed_tsupport (bf.chi k)).isOpen_compl⟩ with hU₀def
      letI : ChartedSpace H ↥U₀ :=
        TopologicalSpace.Opens.instChartedSpace (H := H) (M := P.M) (s := U₀)
      letI : IsManifold I ∞ ↥U₀ := { U₀.instHasGroupoid (contDiffGroupoid ∞ I) with }
      letI : SigmaCompactSpace ↥U₀ := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I U₀.isOpen)
      letI : IsManifold I 1 ↥U₀ :=
        IsManifold.of_le (I := I) (M := ↥U₀) (n := (∞ : WithTop ℕ∞))
          (by decide : (1 : WithTop ℕ∞) <= ∞)
      letI : IsManifold I 2 ↥U₀ :=
        IsManifold.of_le (I := I) (M := ↥U₀) (n := (∞ : WithTop ℕ∞))
          (by decide : (2 : WithTop ℕ∞) <= ∞)
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↥U₀ := by
        change IsManifold I ∞ ↥U₀; infer_instance
      have hx0 : x ∈ U₀ := hxsupp
      have hres : metricDerivNorm (I := I) a
            ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I) U₀)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I) U₀)
            (R.restrictOpen (I := I) U₀) (⟨x, hx0⟩ : ↥U₀)
          = metricDerivNorm (I := I) a (gSeqExt (I := I) Φ R bf hsrc htgt k s)
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R x :=
        metricDerivNorm_restrictOpen (I := I) _ _ _ U₀ a ⟨x, hx0⟩

      have hmTF : metricTensorField (I := I)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I) U₀)
          = metricTensorField (I := I)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I) U₀) := by
        refine DFunLike.ext _ _ (fun y => ?_)
        refine ContinuousMultilinearMap.ext (fun v => ?_)
        change
          (gSeqExt (I := I) Φ R bf hsrc htgt k s).inner (y : P.M) (v 0) (v 1) =
            (gSeqExt (I := I) Φ R bf hsrc htgt k t).inner (y : P.M) (v 0) (v 1)
        rw [gSeqExt_inner_of_notMem (I := I) Φ R bf hsrc htgt k s (y : P.M) y.2 (v 0) (v 1),
          gSeqExt_inner_of_notMem (I := I) Φ R bf hsrc htgt k t (y : P.M) y.2 (v 0) (v 1)]
      have hswap : metricDerivNorm (I := I) a
            ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I) U₀)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I) U₀)
            (R.restrictOpen (I := I) U₀) (⟨x, hx0⟩ : ↥U₀)
          = metricDerivNorm (I := I) a
            ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I) U₀)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I) U₀)
            (R.restrictOpen (I := I) U₀) (⟨x, hx0⟩ : ↥U₀) := by
        unfold metricDerivNorm metricDiffCovDerivAt
        rw [metricCovDeriv_eq_covDerivOfField (I := I)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I) U₀)
            (R.restrictOpen (I := I) U₀) a,
          metricCovDeriv_eq_covDerivOfField (I := I)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I) U₀)
            (R.restrictOpen (I := I) U₀) a,
          hmTF]
      rw [← hres, hswap, metricDerivNorm_self]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCx0) hLs0) (abs_nonneg _)
  choose Lk hLk0 hLk using hhead
  have hne : (Finset.range (k0 + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos k0)⟩
  refine ⟨max Lt ((Finset.range (k0 + 1)).sup' hne Lk),
    le_trans hLt0 (le_max_left _ _), fun k s hs t ht a ha x hx => ?_⟩
  by_cases hk : k0 <= k
  ·
    exact le_trans (hLt k s t hs ht a ha x (hk0 k hk hx))
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  ·
    refine le_trans (hLk k s hs t ht a ha x hx)
      (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    exact le_trans (Finset.le_sup' Lk (Finset.mem_range.2 (by omega)))
      (le_max_right _ _)

end Lip

end ConvField

end HCGCompactness
end DifferentialGeometry
