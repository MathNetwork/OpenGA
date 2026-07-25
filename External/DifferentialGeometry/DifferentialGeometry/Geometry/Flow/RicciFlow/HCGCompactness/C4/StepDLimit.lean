import DifferentialGeometry.Geometry.Topology.DirectLimitManifold
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedRiemannian
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricDerivNormRestrict
import DifferentialGeometry.Geometry.Comparison.HopfRinowProper
import DifferentialGeometry.Geometry.Topology.SigmaCompactOpen

set_option autoImplicit false
set_option linter.style.longLine false




















noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff





def limitPointed
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
    [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
    [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]
    (S : SmoothSeqSystem I A) (O₀ : A 0)
    (ginf : SmoothRiemannianMetric I S.toSeqSystem.Lim) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) where
  M := S.toSeqSystem.Lim
  basepoint := S.toSeqSystem.incl 0 O₀
  metric := ginf





def limitPointedCoc
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
    [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
    [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]
    (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) :=
  limitPointed S O₀ (S.limitMetric g hg)

section StepD4a

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
  [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]



def factorPointed (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (k : ℕ) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) where
  M := A k
  basepoint := S.toSeqSystem.F (Nat.zero_le k) O₀
  metric := g k


def factorSeq (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) where
  obj := factorPointed S O₀ g




omit [FiniteDimensional ℝ E] [CompleteSpace E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
theorem rangeExhausts (S : SmoothSeqSystem I A) :
    ExhaustsByOpen (fun k => Set.range (S.toSeqSystem.incl k)) where
  isOpen k := (S.toSeqSystem.incl_isOpenEmb k).isOpen_range
  mono_step k := S.toSeqSystem.range_incl_mono (Nat.le_succ k)
  subset K hK := by
    obtain ⟨k₀, Kk, _, hKeq⟩ := S.toSeqSystem.isCompact_exists hK
    refine ⟨k₀, fun k hk => ?_⟩
    rw [hKeq]
    exact (Set.image_subset_range _ _).trans (S.toSeqSystem.range_incl_mono hk)




noncomputable def limitCGMapsOf (S : SmoothSeqSystem I A) (O₀ : A 0)
    (gSeq gLim : ∀ k, SmoothRiemannianMetric I (A k)) (hgLim : S.MetricCocycle gLim) :
    PointedRiemannianCGMaps.{u, uE, uH} (I := I)
      (X := factorSeq S O₀ gSeq)
      (L := (limitPointedCoc S O₀ gLim hgLim :
        PointedRiemannianManifold.{u, uE, uH} (I := I)))
      (subseq := id) where
  partialDiffeomorph k := S.inclPartialDiffeo k
  source_exhausts := rangeExhausts S
  base_mem k := ⟨S.toSeqSystem.F (Nat.zero_le k) O₀, S.toSeqSystem.incl_comp (Nat.zero_le k) O₀⟩
  basepoint_map k := S.invIncl_incl_le (Nat.zero_le k) O₀


noncomputable def limitCGMaps (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g) :
    PointedRiemannianCGMaps.{u, uE, uH} (I := I)
      (X := factorSeq S O₀ g)
      (L := (limitPointedCoc S O₀ g hg : PointedRiemannianManifold.{u, uE, uH} (I := I)))
      (subseq := id) :=
  limitCGMapsOf S O₀ g g hg

end StepD4a

section StepD4bc

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
  [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]

set_option maxHeartbeats 800000 in





def limitCGConverges
    (S : SmoothSeqSystem I A) (O₀ : A 0)
    (gSeq gLim : ∀ k, SmoothRiemannianMetric I (A k))
    (hgLim : S.MetricCocycle gLim)
    (hstage : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ K : Set (A k), IsCompact K →
        metricDerivNormSupOn (I := I) K p (gSeq k) (gLim k) (gLim k) < ε) :
    PointedRiemannianCGConverges (I := I)
      (factorSeq S O₀ gSeq) (limitPointedCoc S O₀ gLim hgLim) id
      (limitCGMapsOf S O₀ gSeq gLim hgLim) := by
  let Φ := limitCGMapsOf S O₀ gSeq gLim hgLim
  have hσsrc : ∀ k : ℕ,
      letI : TopologicalSpace (limitPointedCoc S O₀ gLim hgLim).M :=
        (limitPointedCoc S O₀ gLim hgLim).topology
      IsSigmaCompact (Φ.source k) := by
    intro k
    letI : TopologicalSpace (limitPointedCoc S O₀ gLim hgLim).M :=
      (limitPointedCoc S O₀ gLim hgLim).topology
    letI : ChartedSpace H (limitPointedCoc S O₀ gLim hgLim).M :=
      (limitPointedCoc S O₀ gLim hgLim).charted
    letI : SigmaCompactSpace (limitPointedCoc S O₀ gLim hgLim).M :=
      (limitPointedCoc S O₀ gLim hgLim).sigmaCompact
    exact Geometry.isSigmaCompact_of_isOpen I (Φ.source_open k)
  have hσtgt : ∀ k : ℕ,
      letI : TopologicalSpace ((factorSeq S O₀ gSeq).obj (id k)).M :=
        ((factorSeq S O₀ gSeq).obj (id k)).topology
      IsSigmaCompact (Φ.target k) := by
    intro k
    letI : TopologicalSpace ((factorSeq S O₀ gSeq).obj (id k)).M :=
      ((factorSeq S O₀ gSeq).obj (id k)).topology
    letI : ChartedSpace H ((factorSeq S O₀ gSeq).obj (id k)).M :=
      ((factorSeq S O₀ gSeq).obj (id k)).charted
    letI : SigmaCompactSpace ((factorSeq S O₀ gSeq).obj (id k)).M :=
      ((factorSeq S O₀ gSeq).obj (id k)).sigmaCompact
    exact Geometry.isSigmaCompact_of_isOpen I (Φ.target_open k)
  let refMetric : ∀ k : ℕ,
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomTop (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomSmooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k) := fun k => by
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomTop (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomCharted (I := I) Φ k
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomSigmaOf (I := I) Φ k (hσsrc k)
    letI : T2Space (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomT2 (I := I) Φ k
    let sourceSigma : SigmaCompactSpace (metricSourceOpen (I := I) Φ k) := by
      change SigmaCompactSpace (MetricSourceDomain (I := I) Φ k)
      exact metricSourceDomSigmaOf (I := I) Φ k (hσsrc k)
    let sourceT2 : T2Space (metricSourceOpen (I := I) Φ k) := by
      change T2Space (MetricSourceDomain (I := I) Φ k)
      exact metricSourceDomT2 (I := I) Φ k
    exact @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
      S.toSeqSystem.Lim inferInstance inferInstance inferInstance inferInstance
      (S.limitMetric gLim hgLim) (metricSourceOpen (I := I) Φ k) sourceSigma sourceT2
  refine PointedRiemannianCGConverges.ofRestrictPullback (I := I)
    Φ hσsrc hσtgt refMetric ?_
  intro K hK p ε hε
  obtain ⟨kSrc, hkSrc⟩ := Φ.source_subset hK
  obtain ⟨kConv, hkConv⟩ := hstage ε hε p
  refine ⟨max kSrc kConv, fun k hk => ?_⟩
  have hkS : kSrc ≤ k := le_trans (Nat.le_max_left kSrc kConv) hk
  have hkC : kConv ≤ k := le_trans (Nat.le_max_right kSrc kConv) hk
  letI : TopologicalSpace (limitPointedCoc S O₀ gLim hgLim).M :=
    (limitPointedCoc S O₀ gLim hgLim).topology
  letI : ChartedSpace H (limitPointedCoc S O₀ gLim hgLim).M :=
    (limitPointedCoc S O₀ gLim hgLim).charted
  letI : TopologicalSpace ((factorSeq S O₀ gSeq).obj (id k)).M :=
    ((factorSeq S O₀ gSeq).obj (id k)).topology
  letI : ChartedSpace H ((factorSeq S O₀ gSeq).obj (id k)).M :=
    ((factorSeq S O₀ gSeq).obj (id k)).charted
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomTop (I := I) Φ k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomCharted (I := I) Φ k
  letI : T2Space (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomSigmaOf (I := I) Φ k (hσsrc k)
  letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomTop (I := I) Φ k
  letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomCharted (I := I) Φ k
  letI : T2Space (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomSigmaOf (I := I) Φ k (hσtgt k)
  let F := metricSourceTargetDiff (I := I) Φ k
  let sourceSigma : SigmaCompactSpace (metricSourceOpen (I := I) Φ k) := by
    change SigmaCompactSpace (MetricSourceDomain (I := I) Φ k)
    exact metricSourceDomSigmaOf (I := I) Φ k (hσsrc k)
  let sourceT2 : T2Space (metricSourceOpen (I := I) Φ k) := by
    change T2Space (MetricSourceDomain (I := I) Φ k)
    exact metricSourceDomT2 (I := I) Φ k
  let targetSigma : SigmaCompactSpace (metricTargetOpen (I := I) Φ k) := by
    change SigmaCompactSpace (MetricTargetDomain (I := I) Φ k)
    exact metricTargetDomSigmaOf (I := I) Φ k (hσtgt k)
  let targetT2 : T2Space (metricTargetOpen (I := I) Φ k) := by
    change T2Space (MetricTargetDomain (I := I) Φ k)
    exact metricTargetDomT2 (I := I) Φ k
  let sourceMetric : SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k) :=
    @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
      S.toSeqSystem.Lim inferInstance inferInstance inferInstance inferInstance
      (S.limitMetric gLim hgLim) (metricSourceOpen (I := I) Φ k) sourceSigma sourceT2
  let targetSeq : SmoothRiemannianMetric I (MetricTargetDomain (I := I) Φ k) :=
    @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
      (A k) inferInstance inferInstance inferInstance inferInstance
      (gSeq k) (metricTargetOpen (I := I) Φ k) targetSigma targetT2
  let targetLim : SmoothRiemannianMetric I (MetricTargetDomain (I := I) Φ k) :=
    @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
      (A k) inferInstance inferInstance inferInstance inferInstance
      (gLim k) (metricTargetOpen (I := I) Φ k) targetSigma targetT2
  have hlim : sourceMetric = Diffeomorph.pullbackMetric (I := I) targetLim F := by
    have metric_ext : ∀ (g₁ g₂ : SmoothRiemannianMetric I
        (MetricSourceDomain (I := I) Φ k)),
        (∀ (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
          g₁.inner x v w = g₂.inner x v w) → g₁ = g₂ := by
      intro g₁ g₂ h
      obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g₁
      obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g₂
      have hi : i₁ = i₂ :=
        funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
      subst hi
      rfl
    apply metric_ext
    intro x v w
    dsimp only [sourceMetric, targetLim]
    change (S.limitMetric gLim hgLim).inner (x : (limitPointedCoc S O₀ gLim hgLim).M) v w =
      (gLim k).inner (F x : ((factorSeq S O₀ gSeq).obj (id k)).M)
        (mfderiv I I F x v) (mfderiv I I F x w)
    rw [S.limitMetric_of_mem gLim hgLim k x.2]
    rw [metricSourceTargetDiff_mfderiv (I := I) Φ k x v,
      metricSourceTargetDiff_mfderiv (I := I) Φ k x w]
    rfl
  change metricDerivNormSupOn (I := I)
      (metricSourceCompactSet (I := I) Φ k K) p
      (Diffeomorph.pullbackMetric (I := I) targetSeq F)
      sourceMetric sourceMetric < ε
  rw [hlim, metricDerivNormSupOn_pullback_image (I := I)]
  have hKsource : IsCompact (metricSourceCompactSet (I := I) Φ k K) :=
    metricSourceCompactSet_isCompact (I := I) Φ k hK (hkSrc k hkS)
  have hKtarget : IsCompact (F '' metricSourceCompactSet (I := I) Φ k K) :=
    hKsource.image F.continuous
  let stageVal : MetricTargetDomain (I := I) Φ k → A k := by
    change {x : A k // x ∈ Set.univ} → A k
    exact Subtype.val
  let stageSet : Set (A k) :=
    stageVal '' (F '' metricSourceCompactSet (I := I) Φ k K)
  have hvalCont : Continuous stageVal := by
    dsimp only [stageVal]
    exact continuous_subtype_val
  have hKstage : IsCompact stageSet := hKtarget.image hvalCont
  calc
    metricDerivNormSupOn (I := I)
        (F '' metricSourceCompactSet (I := I) Φ k K) p targetSeq targetLim targetLim =
      metricDerivNormSupOn (I := I) stageSet p (gSeq k) (gLim k) (gLim k) := by
          dsimp only [targetSeq, targetLim]
          dsimp only [stageSet, stageVal]
          exact @metricDerivNormSupOn_restrictOpen E inferInstance inferInstance
            inferInstance inferInstance H inferInstance I
            (A k) inferInstance inferInstance inferInstance inferInstance
            (gSeq k) (gLim k) (gLim k) (metricTargetOpen (I := I) Φ k)
            targetSigma targetT2 (F '' metricSourceCompactSet (I := I) Φ k K) p
    _ < ε := hkConv k hkC stageSet hKstage

end StepD4bc

section StepD5

open Bundle



theorem exists_first_exit
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsClosed K)
    {γ : ℝ → X} (hγ : ContinuousOn γ (Set.Icc 0 1))
    (h0 : γ 0 ∈ interior K) (h1 : γ 1 ∉ K) :
    ∃ t : ℝ, t ∈ Set.Ioc 0 1 ∧
      (∀ s ∈ Set.Icc 0 t, γ s ∈ K) ∧ γ t ∈ frontier K := by
  let T := Set.Icc (0 : ℝ) 1
  letI : CompactSpace T := isCompact_iff_compactSpace.mp isCompact_Icc
  let γT : T → X := fun t => γ t
  let B : Set T := γT ⁻¹' (interior K)ᶜ
  have hγT : Continuous γT := hγ.restrict
  have hBclosed : IsClosed B := by
    exact isOpen_interior.isClosed_compl.preimage hγT
  have honeB : (⟨1, by simp [T]⟩ : T) ∈ B := by
    change γ 1 ∉ interior K
    exact fun h => h1 (interior_subset h)
  have hBne : B.Nonempty := ⟨⟨1, by simp [T]⟩, honeB⟩
  obtain ⟨t, htB, htmin⟩ :=
    hBclosed.isCompact.exists_isMinOn hBne continuous_subtype_val.continuousOn
  have htNot : γ (t : ℝ) ∉ interior K := by
    simpa only [B, γT, Set.mem_preimage, Set.mem_compl_iff] using htB
  have htne : (t : ℝ) ≠ 0 := by
    intro ht
    apply htNot
    simpa only [ht] using h0
  have htpos : (0 : ℝ) < t := lt_of_le_of_ne t.property.1 (Ne.symm htne)
  have hbefore : ∀ s ∈ Set.Ico (0 : ℝ) t, γ s ∈ interior K := by
    intro s hs
    by_contra hsNot
    let sT : T := ⟨s, hs.1, (le_of_lt hs.2).trans t.property.2⟩
    have hsB : sT ∈ B := by
      change γ s ∉ interior K
      exact hsNot
    exact (not_le_of_gt hs.2) (htmin hsB)
  have htClosure : (t : ℝ) ∈ closure (Set.Ico (0 : ℝ) t) := by
    rw [closure_Ico (Ne.symm htne)]
    exact ⟨htpos.le, le_rfl⟩
  have hcont : ContinuousWithinAt γ (Set.Ico (0 : ℝ) t) t :=
    (hγ t t.property).mono fun s hs => ⟨hs.1, (le_of_lt hs.2).trans t.property.2⟩
  have htKclosure : γ t ∈ closure K :=
    hcont.mem_closure htClosure fun s hs => interior_subset (hbefore s hs)
  have htK : γ t ∈ K := by simpa only [hK.closure_eq] using htKclosure
  refine ⟨t, ⟨htpos, t.property.2⟩, ?_, ?_⟩
  · intro s hs
    by_cases hst : s = t
    · simpa only [hst] using htK
    · exact interior_subset (hbefore s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩)
  · rw [frontier, hK.closure_eq]
    exact ⟨htK, htNot⟩


variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
  [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




omit [CompleteSpace E] in
theorem enorm_mfd_incl (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (k : ℕ) (a : A k) (v : TangentSpace I a) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
      ⟨(g k).toRiemannianMetric⟩
    ‖mfderiv I I (S.toSeqSystem.incl k) a v‖ₑ = ‖v‖ₑ := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
    ⟨(g k).toRiemannianMetric⟩
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
    norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  have h1 : (inner ℝ (mfderiv I I (S.toSeqSystem.incl k) a v)
        (mfderiv I I (S.toSeqSystem.incl k) a v) : ℝ)
      = (S.limitMetric g hg).inner (S.toSeqSystem.incl k a)
          (mfderiv I I (S.toSeqSystem.incl k) a v)
          (mfderiv I I (S.toSeqSystem.incl k) a v) := rfl
  have h2 : (inner ℝ v v : ℝ) = (g k).inner a v v := rfl
  rw [h1, h2, S.limitMetric_pullback g hg k a v v]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



omit [CompleteSpace E] in
theorem pathELength_incl (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (k : ℕ) {γ : ℝ → A k} {t₀ t₁ : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc t₀ t₁)) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
      ⟨(g k).toRiemannianMetric⟩
    Manifold.pathELength I (S.toSeqSystem.incl k ∘ γ) t₀ t₁
      = Manifold.pathELength I γ t₀ t₁ := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
    ⟨(g k).toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  have hγt : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    ((hγ.mdifferentiableOn one_ne_zero) t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  have hincl : MDifferentiableAt I I (S.toSeqSystem.incl k) (γ t) :=
    (S.contMDiff_incl k).mdifferentiableAt (by decide)
  have hcomp : mfderiv 𝓘(ℝ, ℝ) I (S.toSeqSystem.incl k ∘ γ) t
      = (mfderiv I I (S.toSeqSystem.incl k) (γ t)).comp (mfderiv 𝓘(ℝ, ℝ) I γ t) :=
    mfderiv_comp t hincl hγt
  rw [hcomp]
  exact enorm_mfd_incl S g hg k (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




omit [CompleteSpace E] in
theorem edist_incl_le (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (k : ℕ) (a b : A k) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
      ⟨(g k).toRiemannianMetric⟩
    Manifold.riemannianEDist I (S.toSeqSystem.incl k a) (S.toSeqSystem.incl k b)
      ≤ Manifold.riemannianEDist I a b := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
    ⟨(g k).toRiemannianMetric⟩
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  obtain ⟨γ, hγ0, hγ1, hγC, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr
  have hle : Manifold.riemannianEDist I (S.toSeqSystem.incl k a) (S.toSeqSystem.incl k b)
      ≤ Manifold.pathELength I (S.toSeqSystem.incl k ∘ γ) 0 1 :=
    Manifold.riemannianEDist_le_pathELength
      (((S.contMDiff_incl k).of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)).comp_contMDiffOn hγC)
      (by rw [Function.comp_apply, hγ0]) (by rw [Function.comp_apply, hγ1]) zero_le_one
  refine hle.trans ?_
  rw [pathELength_incl S g hg k hγC]
  exact hlen.le

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in






omit [CompleteSpace E] in
theorem pathELength_invIncl (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (k : ℕ) {δ : ℝ → S.toSeqSystem.Lim} {t₀ t₁ : ℝ}
    (hδ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 δ (Set.Icc t₀ t₁))
    (hδr : ∀ t ∈ Set.Icc t₀ t₁, δ t ∈ Set.range (S.toSeqSystem.incl k)) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
      ⟨(g k).toRiemannianMetric⟩
    Manifold.pathELength I (Function.invFun (S.toSeqSystem.incl k) ∘ δ) t₀ t₁
      = Manifold.pathELength I δ t₀ t₁ := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
    ⟨(g k).toRiemannianMetric⟩
  have hpull : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (Function.invFun (S.toSeqSystem.incl k) ∘ δ)
      (Set.Icc t₀ t₁) := by
    intro t ht
    exact ContMDiffAt.comp_contMDiffWithinAt t
      ((S.contMDiffAt_invIncl k (hδr t ht)).of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞))
      (hδ t ht)
  have h1 := pathELength_incl S g hg k hpull
  have h2 : Manifold.pathELength I
      (S.toSeqSystem.incl k ∘ (Function.invFun (S.toSeqSystem.incl k) ∘ δ)) t₀ t₁
      = Manifold.pathELength I δ t₀ t₁ :=
    Manifold.pathELength_congr fun t ht => Function.invFun_eq (hδr t ht)
  rw [← h2, h1]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





omit [CompleteSpace E] in
theorem edist_invIncl_le (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (k : ℕ) {x y : S.toSeqSystem.Lim} {r : ENNReal}
    (hxy :
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric g hg).toRiemannianMetric⟩
      Manifold.riemannianEDist I x y < r)
    (hsub : ∀ z : S.toSeqSystem.Lim,
      (letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric g hg).toRiemannianMetric⟩
      Manifold.riemannianEDist I x z ≤ r) → z ∈ Set.range (S.toSeqSystem.incl k)) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    letI : RiemannianBundle (fun a : A k => TangentSpace I a) :=
      ⟨(g k).toRiemannianMetric⟩
    Manifold.riemannianEDist I
        (Function.invFun (S.toSeqSystem.incl k) x) (Function.invFun (S.toSeqSystem.incl k) y)
      ≤ r := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  letI : RiemannianBundle (fun a : A k => TangentSpace I a) :=
    ⟨(g k).toRiemannianMetric⟩
  obtain ⟨γ, hγ0, hγ1, hγC, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hxy

  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Set.range (S.toSeqSystem.incl k) := by
    intro t ht
    refine hsub (γ t) ?_
    have hseg : Manifold.riemannianEDist I x (γ t)
        ≤ Manifold.pathELength I γ 0 t :=
      Manifold.riemannianEDist_le_pathELength
        (hγC.mono (Set.Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1
    refine hseg.trans (le_trans ?_ hlen.le)
    exact Manifold.pathELength_mono le_rfl ht.2

  have hpull1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      (Function.invFun (S.toSeqSystem.incl k) ∘ γ) (Set.Icc 0 1) := by
    intro t ht
    exact ContMDiffAt.comp_contMDiffWithinAt t
      ((S.contMDiffAt_invIncl k (hmem t ht)).of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞))
      (hγC t ht)
  have hle : Manifold.riemannianEDist I
      (Function.invFun (S.toSeqSystem.incl k) x) (Function.invFun (S.toSeqSystem.incl k) y)
      ≤ Manifold.pathELength I (Function.invFun (S.toSeqSystem.incl k) ∘ γ) 0 1 :=
    Manifold.riemannianEDist_le_pathELength hpull1
      (by rw [Function.comp_apply, hγ0]) (by rw [Function.comp_apply, hγ1]) zero_le_one
  refine hle.trans ?_
  rw [pathELength_invIncl S g hg k hγC hmem]
  exact hlen.le

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





omit [CompleteSpace E] in
theorem isCompact_cball_lim (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (hexh : ∀ (z : S.toSeqSystem.Lim) (r : ENNReal),
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric g hg).toRiemannianMetric⟩
      ∃ k, ∀ w : S.toSeqSystem.Lim,
        Manifold.riemannianEDist I z w ≤ r → w ∈ Set.range (S.toSeqSystem.incl k))
    (hcpt : ∀ (k : ℕ) (a : A k) (r : ENNReal),
      letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
        ⟨(g k).toRiemannianMetric⟩
      IsCompact {b : A k | Manifold.riemannianEDist I a b ≤ r})
    (z : S.toSeqSystem.Lim) (r : ENNReal) (hr : r ≠ ⊤) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    IsCompact {w : S.toSeqSystem.Lim | Manifold.riemannianEDist I z w ≤ r} := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  obtain ⟨k, hk⟩ := hexh z (r + 1)
  letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
    ⟨(g k).toRiemannianMetric⟩
  have hz : z ∈ Set.range (S.toSeqSystem.incl k) :=
    hk z (by rw [Manifold.riemannianEDist_self]; exact zero_le _)

  have himg : IsCompact (S.toSeqSystem.incl k ''
      {b : A k | Manifold.riemannianEDist I (Function.invFun (S.toSeqSystem.incl k) z) b
        ≤ r + 1}) :=
    (hcpt k _ (r + 1)).image (S.toSeqSystem.continuous_incl k)
  refine IsCompact.of_isClosed_subset himg ?_ ?_
  ·
    letI : IsManifold I 1 S.toSeqSystem.Lim :=
      IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : TopologicalSpace.MetrizableSpace S.toSeqSystem.Lim :=
      Manifold.metrizableSpace I S.toSeqSystem.Lim
    letI : T3Space S.toSeqSystem.Lim := inferInstance
    letI : IsContinuousRiemannianBundle E (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨⟨(S.limitMetric g hg).inner, (S.limitMetric g hg).contMDiff.continuous,
        by intro x v w; rfl⟩⟩
    letI : EMetricSpace S.toSeqSystem.Lim :=
      EMetricSpace.ofRiemannianMetric I S.toSeqSystem.Lim
    have hcont : Continuous fun w : S.toSeqSystem.Lim => edist z w :=
      continuous_const.edist continuous_id
    have hset : {w : S.toSeqSystem.Lim | Manifold.riemannianEDist I z w ≤ r}
        = (fun w : S.toSeqSystem.Lim => edist z w) ⁻¹' (Set.Iic r) := rfl
    rw [hset]
    exact IsClosed.preimage hcont isClosed_Iic
  ·
    intro w hw
    have hw' : Manifold.riemannianEDist I z w ≤ r := hw
    have hwr : w ∈ Set.range (S.toSeqSystem.incl k) :=
      hk w (hw'.trans le_self_add)
    have hlt : Manifold.riemannianEDist I z w < r + 1 :=
      hw'.trans_lt (ENNReal.lt_add_right hr one_ne_zero)
    have hstage := edist_invIncl_le S g hg k hlt hk
    refine ⟨Function.invFun (S.toSeqSystem.incl k) w, hstage, Function.invFun_eq hwr⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


def HasCompactBallCover (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g) : Prop :=
  ∀ (z : S.toSeqSystem.Lim) (r : ENNReal), r ≠ ⊤ →
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    ∃ k, ∃ K : Set (A k), IsCompact K ∧
      ∀ w : S.toSeqSystem.Lim,
        Manifold.riemannianEDist I z w ≤ r → w ∈ S.toSeqSystem.incl k '' K

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [CompleteSpace E] in
theorem compactCover_of_step (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (hexh : ∀ (z : S.toSeqSystem.Lim) (r : ENNReal),
      r ≠ ⊤ →
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric g hg).toRiemannianMetric⟩
      ∃ k, ∀ w : S.toSeqSystem.Lim,
        Manifold.riemannianEDist I z w ≤ r → w ∈ Set.range (S.toSeqSystem.incl k))
    (hstep : ∀ k, ∃ K : Set (A (k + 1)), IsCompact K ∧
      Set.range (S.toSeqSystem.F (Nat.le_succ k)) ⊆ K) :
    HasCompactBallCover S g hg := by
  intro z r hr
  obtain ⟨k, hk⟩ := hexh z r hr
  obtain ⟨K, hK, hFK⟩ := hstep k
  refine ⟨k + 1, K, hK, fun w hw => ?_⟩
  obtain ⟨a, rfl⟩ := hk w hw
  refine ⟨S.toSeqSystem.F (Nat.le_succ k) a, hFK ⟨a, rfl⟩, ?_⟩
  exact S.toSeqSystem.incl_comp (Nat.le_succ k) a

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [CompleteSpace E] in
theorem compact_cball_cover (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (hcover : HasCompactBallCover S g hg)
    (z : S.toSeqSystem.Lim) (r : ENNReal) (hr : r ≠ ⊤) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    IsCompact {w : S.toSeqSystem.Lim | Manifold.riemannianEDist I z w ≤ r} := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  obtain ⟨k, K, hK, hsub⟩ := hcover z r hr
  have himg : IsCompact (S.toSeqSystem.incl k '' K) :=
    hK.image (S.toSeqSystem.continuous_incl k)
  refine IsCompact.of_isClosed_subset himg ?_ ?_
  · letI : IsManifold I 1 S.toSeqSystem.Lim :=
      IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : TopologicalSpace.MetrizableSpace S.toSeqSystem.Lim :=
      Manifold.metrizableSpace I S.toSeqSystem.Lim
    letI : T3Space S.toSeqSystem.Lim := inferInstance
    letI : IsContinuousRiemannianBundle E
        (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨⟨(S.limitMetric g hg).inner, (S.limitMetric g hg).contMDiff.continuous,
        by intro x v w; rfl⟩⟩
    letI : EMetricSpace S.toSeqSystem.Lim :=
      EMetricSpace.ofRiemannianMetric I S.toSeqSystem.Lim
    have hcont : Continuous fun w : S.toSeqSystem.Lim => edist z w :=
      continuous_const.edist continuous_id
    have hset : {w : S.toSeqSystem.Lim | Manifold.riemannianEDist I z w ≤ r} =
        (fun w : S.toSeqSystem.Lim => edist z w) ⁻¹' Set.Iic r := rfl
    rw [hset]
    exact IsClosed.preimage hcont isClosed_Iic
  · intro w hw
    change Manifold.riemannianEDist I z w ≤ r at hw
    exact hsub w hw

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



theorem limitComplete_cover [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    [∀ k, PreconnectedSpace (A k)]
    (hcover : HasCompactBallCover S g hg) :
    MetricComplete (I := I) (limitPointedCoc S O₀ g hg) := by
  unfold MetricComplete
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  letI : IsManifold I 1 S.toSeqSystem.Lim :=
    IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : TopologicalSpace.MetrizableSpace S.toSeqSystem.Lim :=
    Manifold.metrizableSpace I S.toSeqSystem.Lim
  letI : T3Space S.toSeqSystem.Lim := inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨⟨(S.limitMetric g hg).inner, (S.limitMetric g hg).contMDiff.continuous,
      by intro x v w; rfl⟩⟩
  letI : EMetricSpace S.toSeqSystem.Lim :=
    EMetricSpace.ofRiemannianMetric I S.toSeqSystem.Lim
  letI : MetricSpace S.toSeqSystem.Lim :=
    EMetricSpace.toMetricSpace
      (fun x y => Geometry.Riemannian.Exponential.riemannianEDist_ne_top (I := I) x y)
  haveI : ProperSpace S.toSeqSystem.Lim := by
    refine ProperSpace.of_isCompact_closedBall_of_le 0 (fun z r hr => ?_)
    have h := compact_cball_cover S g hg hcover z (ENNReal.ofReal r) ENNReal.ofReal_ne_top
    have hset : Metric.closedBall z r =
        {w : S.toSeqSystem.Lim |
          Manifold.riemannianEDist I z w ≤ ENNReal.ofReal r} := by
      rw [← Metric.closedEBall_ofReal hr]
      ext w
      exact Metric.mem_closedEBall'
    rw [hset]
    exact h
  exact (complete_of_proper : CompleteSpace S.toSeqSystem.Lim)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





theorem limitComplete [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    [∀ k, PreconnectedSpace (A k)]
    (hexh : ∀ (z : S.toSeqSystem.Lim) (r : ENNReal),
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric g hg).toRiemannianMetric⟩
      ∃ k, ∀ w : S.toSeqSystem.Lim,
        Manifold.riemannianEDist I z w ≤ r → w ∈ Set.range (S.toSeqSystem.incl k))
    (hcpt : ∀ (k : ℕ) (a : A k) (r : ENNReal),
      letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
        ⟨(g k).toRiemannianMetric⟩
      IsCompact {b : A k | Manifold.riemannianEDist I a b ≤ r}) :
    MetricComplete (I := I) (limitPointedCoc S O₀ g hg) := by
  unfold MetricComplete
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  letI : IsManifold I 1 S.toSeqSystem.Lim :=
    IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : TopologicalSpace.MetrizableSpace S.toSeqSystem.Lim :=
    Manifold.metrizableSpace I S.toSeqSystem.Lim
  letI : T3Space S.toSeqSystem.Lim := inferInstance
  letI : IsContinuousRiemannianBundle E (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨⟨(S.limitMetric g hg).inner, (S.limitMetric g hg).contMDiff.continuous,
      by intro x v w; rfl⟩⟩
  letI : EMetricSpace S.toSeqSystem.Lim :=
    EMetricSpace.ofRiemannianMetric I S.toSeqSystem.Lim
  letI : MetricSpace S.toSeqSystem.Lim :=
    EMetricSpace.toMetricSpace
      (fun x y => Geometry.Riemannian.Exponential.riemannianEDist_ne_top (I := I) x y)
  haveI : ProperSpace S.toSeqSystem.Lim := by
    refine ProperSpace.of_isCompact_closedBall_of_le 0 (fun z r hr => ?_)
    have h := isCompact_cball_lim S g hg hexh hcpt z (ENNReal.ofReal r) ENNReal.ofReal_ne_top
    have hset : Metric.closedBall z r
        = {w : S.toSeqSystem.Lim |
            Manifold.riemannianEDist I z w ≤ ENNReal.ofReal r} := by
      rw [← Metric.closedEBall_ofReal hr]
      ext w
      exact Metric.mem_closedEBall'
    rw [hset]
    exact h
  exact (complete_of_proper : CompleteSpace S.toSeqSystem.Lim)

end StepD5

end HCGCompactness
end DifferentialGeometry
