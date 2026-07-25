import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepDLimitMetrics
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCompactnessSubseq

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false









noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless]
variable [NeZero (Module.finrank ℝ E)]

private structure D6ChainData
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
    [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j)) where
  start : ℕ
  one_le : 1 ≤ start
  zero : ∀ n k, BookApproxIsoPartialData (I := I)
    (Metric.closedBall (b (start + n)) ((2 : ℝ) ^ (start + n))) (1 / 2) 0
    (chainComp (I := I) (Mf := M) Ψ (start + n) k)
    (g (start + n)) (g ((start + n) + k))
  source : ∀ n k,
    (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n) : Set (M (start + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (start + n) k).source
  maps : ∀ n,
    (chainComp (I := I) (Mf := M) Ψ (start + n) 1 :
      M (start + n) → M (start + (n + 1))) ''
        (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n) : Set (M (start + n))) ⊆
      (ballOpen b (fun s => (2 : ℝ) ^ s) (start + (n + 1)) :
        Set (M (start + (n + 1))))
  metric : ∀ n, SmoothRiemannianMetric I
    (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n))
  close : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
    ∀ n : ℕ, n₀ ≤ n →
      letI : SigmaCompactSpace
          (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n)) :=
        isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I
            (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n)).isOpen)
      ∀ l q : ℕ, q ≤ p →
        ∀ x : ballOpen b (fun s => (2 : ℝ) ^ s) (start + n),
          metricDerivNorm (I := I) q
            (chainPullbackSeq (I := I) Ψ g
              (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n)) (source n) l)
            (metric n) (metric n) x ≤ ε
  step : ∀ n,
    let F : ballOpen b (fun s => (2 : ℝ) ^ s) (start + n) →
        ballOpen b (fun s => (2 : ℝ) ^ s) (start + (n + 1)) :=
      PartialDiffeomorph.opensMap
        (chainComp (I := I) (Mf := M) Ψ (start + n) 1) (source n 1) (maps n)
    ∀ (x : ballOpen b (fun s => (2 : ℝ) ^ s) (start + n))
      (v w : TangentSpace I x),
      (metric n).inner x v w =
        (metric (n + 1)).inner (F x)
          (mfderiv I I F x v) (mfderiv I I F x w)

@[reducible] private noncomputable def alignedMetric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)} (k : ℕ)
    (P : ProperMetricOn (I := I) (X.obj k)) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    MetricSpace (X.obj k).M := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  exact P.ms.replaceTopology (ProperMetricOn.top_eq (X.obj k) P).symm



omit [I.Boundaryless] in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private theorem alignedProper
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)} (k : ℕ)
    (P : ProperMetricOn (I := I) (X.obj k)) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : MetricSpace (X.obj k).M := alignedMetric (I := I) k P
    ProperSpace (X.obj k).M := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : MetricSpace (X.obj k).M := alignedMetric (I := I) k P
  constructor
  intro x r
  have hcompact :
      @IsCompact (X.obj k).M
        P.ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (letI : MetricSpace (X.obj k).M := P.ms
         Metric.closedBall x r) := by
    letI : MetricSpace (X.obj k).M := P.ms
    letI : ProperSpace (X.obj k).M := P.proper
    exact isCompact_closedBall x r
  rw [ProperMetricOn.top_eq (X.obj k) P] at hcompact
  exact hcompact

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

noncomputable def tailMemberMaps
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) (σ : ℕ → ℕ) :
    letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
    letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
    letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
    letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
    letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
    letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
      alignedMetric (I := I) (σ j) (P (σ j))
    letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
      change IsManifold I ∞ (X.obj (σ j)).M
      infer_instance
    letI : ∀ j, Bundle.RiemannianBundle
        (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
      fun j => (X.obj (σ j)).riemBundle
    letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
      refine ⟨fun x y => ?_⟩
      have hreal := (P (σ j)).realizes x y
      rw [edist_dist, ← hreal]
      rfl
    ∀ (Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M
        (X.obj (σ (j + 1))).M (∞ : WithTop ℕ∞))
      (hbase : ∀ j, (Ψ j : (X.obj (σ j)).M → (X.obj (σ (j + 1))).M)
        (X.obj (σ j)).basepoint = (X.obj (σ (j + 1))).basepoint)
      (j₀ : ℕ)
      (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
        (Metric.closedBall (X.obj (σ (j₀ + n))).basepoint ((2 : ℝ) ^ (j₀ + n)))
        (1 / 2) 0
        (chainComp (I := I) (Mf := fun j => (X.obj (σ j)).M) Ψ (j₀ + n) k)
        (X.obj (σ (j₀ + n))).metric (X.obj (σ ((j₀ + n) + k))).metric),
      let b := fun j => (X.obj (σ j)).basepoint
      let g := fun j => (X.obj (σ j)).metric
      letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
      let S := tailBallSystem (I := I) b Ψ hbase g (by
        intro j x v
        simpa using
          (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) (g j) x v)) j₀ D₀
      letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
        isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
      ∀ (gTail : ∀ n, SmoothRiemannianMetric I (tailBallOpen b j₀ n))
        (hgTail : S.MetricCocycle gTail),
        PointedRiemannianCGMaps (I := I) X
          (limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail)
          (fun n => σ (j₀ + n)) := by
  letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    alignedMetric (I := I) (σ j) (P (σ j))
  letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M
    infer_instance
  letI : ∀ j, Bundle.RiemannianBundle
      (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  intro Ψ hbase j₀ D₀
  let b := fun j => (X.obj (σ j)).basepoint
  let g := fun j => (X.obj (σ j)).metric
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
  let S := tailBallSystem (I := I) b Ψ hbase g (by
    intro j x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (g j) x v)) j₀ D₀
  letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  dsimp only
  intro gTail hgTail
  let Φ : ∀ n, PartialDiffeomorph I I S.toSeqSystem.Lim
      (X.obj (σ (j₀ + n))).M (∞ : WithTop ℕ∞) := fun n =>
    PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo n) rfl
  refine
    { partialDiffeomorph := Φ
      source_exhausts := ?_
      base_mem := fun n => ?_
      basepoint_map := fun n => ?_ }
  · change ExhaustsByOpen (fun k => Set.range (S.toSeqSystem.incl k))
    exact rangeExhausts S
  · change S.toSeqSystem.incl 0 (tailCenter b j₀ 0) ∈
      Set.range (S.toSeqSystem.incl n)
    exact ⟨S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0),
      S.toSeqSystem.incl_comp (Nat.zero_le n) (tailCenter b j₀ 0)⟩
  · calc
      Φ n (S.toSeqSystem.incl 0 (tailCenter b j₀ 0)) =
          (S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0) :
            (X.obj (σ (j₀ + n))).M) :=
        congrArg Subtype.val
          (S.invIncl_incl_le (Nat.zero_le n) (tailCenter b j₀ 0))
      _ = (X.obj (σ (j₀ + n))).basepoint := by
        exact congrArg Subtype.val
          (tailCenter_map (I := I) b Ψ hbase g (by
            intro j x v
            simpa using
              (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
                (I := I) (g j) x v)) j₀ D₀ n)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


noncomputable def tailMemberConv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) (σ : ℕ → ℕ) :
    letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
    letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
    letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
    letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
    letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
    letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
      alignedMetric (I := I) (σ j) (P (σ j))
    letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
      change IsManifold I ∞ (X.obj (σ j)).M
      infer_instance
    letI : ∀ j, Bundle.RiemannianBundle
        (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
      fun j => (X.obj (σ j)).riemBundle
    letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
      refine ⟨fun x y => ?_⟩
      have hreal := (P (σ j)).realizes x y
      rw [edist_dist, ← hreal]
      rfl
    ∀ (Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M
        (X.obj (σ (j + 1))).M (∞ : WithTop ℕ∞))
      (hbase : ∀ j, (Ψ j : (X.obj (σ j)).M → (X.obj (σ (j + 1))).M)
        (X.obj (σ j)).basepoint = (X.obj (σ (j + 1))).basepoint)
      (j₀ : ℕ)
      (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
        (Metric.closedBall (X.obj (σ (j₀ + n))).basepoint ((2 : ℝ) ^ (j₀ + n)))
        (1 / 2) 0
        (chainComp (I := I) (Mf := fun j => (X.obj (σ j)).M) Ψ (j₀ + n) k)
        (X.obj (σ (j₀ + n))).metric (X.obj (σ ((j₀ + n) + k))).metric),
      let b := fun j => (X.obj (σ j)).basepoint
      let g := fun j => (X.obj (σ j)).metric
      letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
      let S := tailBallSystem (I := I) b Ψ hbase g (by
        intro j x v
        simpa using
          (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) (g j) x v)) j₀ D₀
      letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
        isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
      ∀ (gTail : ∀ n, SmoothRiemannianMetric I (tailBallOpen b j₀ n))
        (hgTail : S.MetricCocycle gTail),
        PointedRiemannianCGConverges (I := I)
            (chainAmbientSeq (I := I) j₀ (tailBallOpen b j₀) S
              (tailCenter b j₀ 0) g)
            (limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail) id
            (chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
              (tailCenter b j₀ 0) g gTail hgTail) →
          PointedRiemannianCGConverges (I := I) X
            (limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail)
            (fun n => σ (j₀ + n))
            (tailMemberMaps (I := I) P σ Ψ hbase j₀ D₀ gTail hgTail) := by
  letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    alignedMetric (I := I) (σ j) (P (σ j))
  letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M
    infer_instance
  letI : ∀ j, Bundle.RiemannianBundle
      (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  intro Ψ hbase j₀ D₀
  let b := fun j => (X.obj (σ j)).basepoint
  let g := fun j => (X.obj (σ j)).metric
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
  let S := tailBallSystem (I := I) b Ψ hbase g (by
    intro j x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (g j) x v)) j₀ D₀
  letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  dsimp only
  intro gTail hgTail C
  let XTail := X.subseq (fun n => σ (j₀ + n))
  let bTail : ∀ n, (XTail.obj n).M := fun n =>
    (S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0) :
      (X.obj (σ (j₀ + n))).M)
  let L := limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail
  let Φr : PointedRiemannianCGMaps (I := I) (XTail.repoint bTail) L id := by
    change PointedRiemannianCGMaps (I := I)
      (chainAmbientSeq (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g) L id
    exact chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
      (tailCenter b j₀ 0) g gTail hgTail
  have hbase' : ∀ n,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (XTail.obj (id n)).M := (XTail.obj (id n)).topology
      letI : ChartedSpace H (XTail.obj (id n)).M := (XTail.obj (id n)).charted
      Φr.partialDiffeomorph n L.basepoint = (XTail.obj (id n)).basepoint := by
    intro n
    calc
      Φr.partialDiffeomorph n (S.toSeqSystem.incl 0 (tailCenter b j₀ 0)) =
          (S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0) :
            (X.obj (σ (j₀ + n))).M) :=
        congrArg Subtype.val
          (S.invIncl_incl_le (Nat.zero_le n) (tailCenter b j₀ 0))
      _ = (X.obj (σ (j₀ + n))).basepoint := by
        exact congrArg Subtype.val
          (tailCenter_map (I := I) b Ψ hbase g (by
            intro j x v
            simpa using
              (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
                (I := I) (g j) x v)) j₀ D₀ n)
  have Cr : PointedRiemannianCGConverges (I := I) (XTail.repoint bTail) L id Φr := by
    change PointedRiemannianCGConverges (I := I)
      (chainAmbientSeq (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g) L id
      (chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g gTail hgTail)
    exact C
  have Cu := Cr.unrepoint bTail hbase'
  exact Cu.ofSubseq (fun n => σ (j₀ + n))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



noncomputable def compactness_of_b1
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (B : StepB1RawInput (X := X) P) :
    MetricCompactnessConclusion (I := I) X := by
  classical
  let hdirectedEx := directed_of_b1 (I := I) P B
  let σ := Classical.choose hdirectedEx
  have hσpack := Classical.choose_spec hdirectedEx
  have hσ : StrictMono σ := hσpack.1
  have hdirected := hσpack.2
  letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => (P (σ j)).ms
  let Ψ := Classical.choose hdirected
  have hΨpack := Classical.choose_spec hdirected
  have hbase := hΨpack.1
  have hdata := hΨpack.2
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    alignedMetric (I := I) (σ j) (P (σ j))
  letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M
    infer_instance
  letI : ∀ j, Bundle.RiemannianBundle
      (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  letI : ∀ j, ProperSpace (X.obj (σ j)).M := fun j =>
    alignedProper (I := I) (σ j) (P (σ j))
  let b := fun j => (X.obj (σ j)).basepoint
  let g := fun j => (X.obj (σ j)).metric
  have hD : Nonempty (D6ChainData (I := I) b Ψ g) := by
    obtain ⟨j₀, hj₀, D₀, hU, hmap, _φ, _hφ, gInf, _hconv, hclose, hstep⟩ :=
      exists_limits_close (I := I) b Ψ hbase g (by
        intro j x v
        simpa using
          (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) (g j) x v)) hdata
    exact ⟨
      { start := j₀
        one_le := hj₀
        zero := D₀
        source := hU
        maps := hmap
        metric := gInf
        close := hclose
        step := hstep }⟩
  let D := Classical.choice hD
  let j₀ := D.start
  have hj₀ : 1 ≤ j₀ := D.one_le
  let D₀ := D.zero
  let hU := D.source
  let hmap := D.maps
  let gInf := D.metric
  have hclose := D.close
  have hstep := D.step
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
  letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  let S := tailBallSystem (I := I) b Ψ hbase g (by
    intro j x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (g j) x v)) j₀ D₀
  let gTail := tailMetric (I := I) b j₀ gInf
  let hgTail : S.MetricCocycle gTail :=
    tailMetricCocycle (I := I) b Ψ hbase g (by
      intro j x v
      simpa using
        (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (g j) x v)) j₀ D₀ hU hmap gInf hstep
  let L := limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail
  let maps := tailMemberMaps (I := I) P σ Ψ hbase j₀ D₀ gTail hgTail
  have hcomplete : MetricComplete (I := I) L := by
    exact tailLimitComplete (I := I) b Ψ hbase g (by
      intro j x v
      simpa using
        (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (g j) x v)) j₀ hj₀ D₀
      hU hmap gInf hstep hclose
  have hchain := tailAmbientConv (I := I) b Ψ hbase g (by
    intro j x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (g j) x v)) j₀ D₀
    hU hmap gInf hstep hclose
  have hconverges : PointedRiemannianCGConverges (I := I) X L
      (fun n => σ (j₀ + n)) maps := by
    exact tailMemberConv (I := I) P σ Ψ hbase j₀ D₀ gTail hgTail hchain
  exact
    { subseq := fun n => σ (j₀ + n)
      strictMono := fun _ _ hnm => hσ (Nat.add_lt_add_left hnm j₀)
      limit := L
      limit_complete := hcomplete
      maps := maps
      convergence := hconverges }

end HCGCompactness
end DifferentialGeometry
