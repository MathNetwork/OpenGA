import Mathlib.Geometry.Manifold.PartitionOfUnity
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringSeq

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set
open scoped Topology Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

section FinitePOU

variable {ι M : Type*} [Fintype ι]
variable [TopologicalSpace M] [ChartedSpace H M]




noncomputable def pouOfFinite {s : Set M} (w : ι → M → Real)
    (hw : ∀ i, ContMDiff I 𝓘(Real) ∞ (w i))
    (hnonneg : ∀ i x, 0 ≤ w i x)
    (hsum : ∀ x ∈ s, ∑ i, w i x = 1)
    (hle : ∀ x, ∑ i, w i x ≤ 1) :
    SmoothPartitionOfUnity ι I M s where
  toFun i := ⟨w i, hw i⟩
  locallyFinite' := locallyFinite_of_finite _
  nonneg' := hnonneg
  sum_eq_one' x hx := by
    simpa only [ContMDiffMap.coeFn_mk, finsum_eq_sum_of_fintype] using hsum x hx
  sum_le_one' x := by
    simpa only [ContMDiffMap.coeFn_mk, finsum_eq_sum_of_fintype] using hle x



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem pouOfFinite_sub {s : Set M} {U : ι → Set M} (w : ι → M → Real)
    (hw : ∀ i, ContMDiff I 𝓘(Real) ∞ (w i))
    (hnonneg : ∀ i x, 0 ≤ w i x)
    (hsum : ∀ x ∈ s, ∑ i, w i x = 1)
    (hle : ∀ x, ∑ i, w i x ≤ 1)
    (hsub : ∀ i, tsupport (w i) ⊆ U i) :
    (pouOfFinite (I := I) w hw hnonneg hsum hle).IsSubordinate U := by
  intro i
  simpa only [pouOfFinite, ContMDiffMap.coeFn_mk] using hsub i



noncomputable def cutoffDenom (a : ι → M → Real) (τ : M → Real) (x : M) : Real :=
  τ x * ∑ i, a i x + (1 - τ x)




noncomputable def cutoffWeights (a : ι → M → Real) (τ : M → Real)
    (i : ι) (x : M) : Real :=
  τ x * a i x / cutoffDenom a τ x



omit [TopologicalSpace M] in
theorem cutoffDenom_pos {a : ι → M → Real} {τ : M → Real}
    (hτrange : ∀ x, τ x ∈ Set.Icc (0 : Real) 1)
    (hpos : ∀ x, τ x ≠ 0 → 0 < ∑ i, a i x) (x : M) :
    0 < cutoffDenom a τ x := by
  rcases hτrange x with ⟨hτ0, hτ1⟩
  by_cases hτzero : τ x = 0
  · simp [cutoffDenom, hτzero]
  by_cases hτone : τ x = 1
  · simpa [cutoffDenom, hτone] using hpos x hτzero
  have hsum : 0 < ∑ i, a i x := hpos x hτzero
  have hmul : 0 ≤ τ x * ∑ i, a i x := mul_nonneg hτ0 hsum.le
  have hrest : 0 < 1 - τ x := sub_pos.mpr (lt_of_le_of_ne hτ1 hτone)
  exact add_pos_of_nonneg_of_pos hmul hrest


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem cutoffWeights_smooth {a : ι → M → Real} {τ : M → Real}
    (ha : ∀ i, ContMDiff I 𝓘(Real) ∞ (a i))
    (hτ : ContMDiff I 𝓘(Real) ∞ τ)
    (hτrange : ∀ x, τ x ∈ Set.Icc (0 : Real) 1)
    (hpos : ∀ x, τ x ≠ 0 → 0 < ∑ i, a i x) (i : ι) :
    ContMDiff I 𝓘(Real) ∞ (cutoffWeights a τ i) := by
  classical
  have hsum : ContMDiff I 𝓘(Real) ∞ (fun x => ∑ j, a j x) :=
    ContMDiff.sum fun j _ => ha j
  have hden : ContMDiff I 𝓘(Real) ∞ (cutoffDenom a τ) := by
    simpa only [cutoffDenom] using (hτ.mul hsum).add (contMDiff_const.sub hτ)
  simpa only [cutoffWeights] using
    (hτ.mul (ha i)).div₀ hden (fun x => ne_of_gt (cutoffDenom_pos hτrange hpos x))


omit [TopologicalSpace M] in
theorem cutoffWeights_nonneg {a : ι → M → Real} {τ : M → Real}
    (ha : ∀ i x, 0 ≤ a i x)
    (hτrange : ∀ x, τ x ∈ Set.Icc (0 : Real) 1)
    (hpos : ∀ x, τ x ≠ 0 → 0 < ∑ i, a i x) (i : ι) (x : M) :
    0 ≤ cutoffWeights a τ i x :=
  div_nonneg (mul_nonneg (hτrange x).1 (ha i x))
    (cutoffDenom_pos hτrange hpos x).le



omit [TopologicalSpace M] in
theorem cutoffWeights_sum (a : ι → M → Real) (τ : M → Real) (x : M) :
    ∑ i, cutoffWeights a τ i x =
      τ x * (∑ i, a i x) / cutoffDenom a τ x := by
  simp only [cutoffWeights, ← Finset.sum_div, ← Finset.mul_sum]


omit [TopologicalSpace M] in
theorem cutoffWeights_one {s : Set M} {a : ι → M → Real} {τ : M → Real}
    (hτone : ∀ x ∈ s, τ x = 1)
    (hpos : ∀ x, τ x ≠ 0 → 0 < ∑ i, a i x) {x : M} (hx : x ∈ s) :
    ∑ i, cutoffWeights a τ i x = 1 := by
  rw [cutoffWeights_sum]
  have ht : τ x = 1 := hτone x hx
  have ht0 : τ x ≠ 0 := by rw [ht]; exact one_ne_zero
  have hsum : (∑ i, a i x) ≠ 0 := ne_of_gt (hpos x ht0)
  simp [cutoffDenom, ht, hsum]


omit [TopologicalSpace M] in
theorem cutoffWeights_le {a : ι → M → Real} {τ : M → Real}
    (hτrange : ∀ x, τ x ∈ Set.Icc (0 : Real) 1)
    (hpos : ∀ x, τ x ≠ 0 → 0 < ∑ i, a i x) (x : M) :
    ∑ i, cutoffWeights a τ i x ≤ 1 := by
  rw [cutoffWeights_sum]
  apply (div_le_one (cutoffDenom_pos hτrange hpos x)).2
  unfold cutoffDenom
  linarith [(hτrange x).2]



theorem cutoffWeights_sub (a : ι → M → Real) (τ : M → Real) (i : ι) :
    tsupport (cutoffWeights a τ i) ⊆ tsupport (a i) := by
  apply closure_mono
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro hai
  apply hx
  simp [cutoffWeights, hai]



noncomputable def pouOfCutoff {s : Set M} (a : ι → M → Real) (τ : M → Real)
    (ha : ∀ i, ContMDiff I 𝓘(Real) ∞ (a i))
    (hanonneg : ∀ i x, 0 ≤ a i x)
    (hτ : ContMDiff I 𝓘(Real) ∞ τ)
    (hτrange : ∀ x, τ x ∈ Set.Icc (0 : Real) 1)
    (hτone : ∀ x ∈ s, τ x = 1)
    (hpos : ∀ x, τ x ≠ 0 → 0 < ∑ i, a i x) :
    SmoothPartitionOfUnity ι I M s :=
  pouOfFinite (I := I) (fun i => cutoffWeights a τ i)
    (cutoffWeights_smooth ha hτ hτrange hpos)
    (cutoffWeights_nonneg hanonneg hτrange hpos)
    (fun _ hx => cutoffWeights_one hτone hpos hx)
    (cutoffWeights_le hτrange hpos)



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem pouOfCutoff_sub {s : Set M} {U : ι → Set M}
    (a : ι → M → Real) (τ : M → Real)
    (ha : ∀ i, ContMDiff I 𝓘(Real) ∞ (a i))
    (hanonneg : ∀ i x, 0 ≤ a i x)
    (hτ : ContMDiff I 𝓘(Real) ∞ τ)
    (hτrange : ∀ x, τ x ∈ Set.Icc (0 : Real) 1)
    (hτone : ∀ x ∈ s, τ x = 1)
    (hpos : ∀ x, τ x ≠ 0 → 0 < ∑ i, a i x)
    (hsub : ∀ i, tsupport (a i) ⊆ U i) :
    (pouOfCutoff (I := I) a τ ha hanonneg hτ hτrange hτone hpos).IsSubordinate U := by
  intro i
  simpa only [pouOfCutoff, pouOfFinite, ContMDiffMap.coeFn_mk] using
    (cutoffWeights_sub a τ i).trans (hsub i)

end FinitePOU

namespace NetLimitData






noncomputable def hatBall (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) (k : Nat) (γ : Fin (pb.A r)) :
    Set ((X.obj (L.φ k)).M) :=
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  match seqCenter hd D P (L.φ k) (γ : Nat) with
  | some c => Metric.ball c (4 * L.lamInf (γ : Nat))
  | none => ∅



noncomputable def innerBall (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) (k : Nat) (γ : Fin (pb.A r)) :
    Set ((X.obj (L.φ k)).M) :=
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  match seqCenter hd D P (L.φ k) (γ : Nat) with
  | some c => Metric.ball c (3 * L.lamInf (γ : Nat))
  | none => ∅

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem innerBall_subseq (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) (k : Nat) (γ : Fin (pb.A r))
    {ψ : Nat -> Nat} (hψ : StrictMono ψ) :
    (L.subseq hψ).innerBall hd D P pb r k γ =
      L.innerBall hd D P pb r (ψ k) γ := by
  cases hcenter : seqCenter hd D P (L.φ (ψ k)) (γ : Nat) with
  | none =>
      simp [innerBall, NetLimitData.subseq, Function.comp_apply, hcenter]
      rfl
  | some c =>
      simp [innerBall, NetLimitData.subseq, NetLimitData.lamInf, Function.comp_apply,
        hcenter]
      rfl


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem innerBall_open (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) (k : Nat) (γ : Fin (pb.A r)) :
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    IsOpen (L.innerBall hd D P pb r k γ) := by
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  unfold innerBall
  split
  · exact Metric.isOpen_ball
  · exact isOpen_empty


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem innerBall_subset_hat (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (γ : Fin (pb.A r)) :
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    L.innerBall hd D P pb r k γ ⊆ L.hatBall hd D P pb r k γ := by
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  cases hcenter : seqCenter hd D P (L.φ k) (γ : Nat) with
  | none => simp [innerBall, hatBall, hcenter]
  | some c =>
      simp only [innerBall, hatBall, hcenter]
      apply Metric.ball_subset_ball
      have hpos : 0 < L.lamInf (γ : Nat) := hd.lambda_pos hD (L.rInf (γ : Nat))
      nlinarith

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem hatBall_subseq (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) (k : Nat) (γ : Fin (pb.A r))
    {ψ : Nat -> Nat} (hψ : StrictMono ψ) :
    (L.subseq hψ).hatBall hd D P pb r k γ =
      L.hatBall hd D P pb r (ψ k) γ := by
  cases hcenter : seqCenter hd D P (L.φ (ψ k)) (γ : Nat) with
  | none =>
      simp [hatBall, NetLimitData.subseq, Function.comp_apply, hcenter]
      rfl
  | some c =>
      simp [hatBall, NetLimitData.subseq, NetLimitData.lamInf, Function.comp_apply,
        hcenter]
      rfl


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatBall_open (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) (k : Nat) (γ : Fin (pb.A r)) :
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    IsOpen (L.hatBall hd D P pb r k γ) := by
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  unfold hatBall
  split
  · exact Metric.isOpen_ball
  · exact isOpen_empty




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatBall_cover (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    (r : Real) :
    ∀ᶠ k in atTop,
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      Metric.closedBall (X.obj (L.φ k)).basepoint r ⊆
        ⋃ γ : Fin (pb.A r), L.hatBall hd D P pb r k γ := by
  filter_upwards [L.hat_cover hd hD P hre pb r] with k hk
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  intro p hp
  have hpdist : dist p (X.obj (L.φ k)).basepoint ≤ r := by
    simpa [Metric.mem_closedBall] using hp
  obtain ⟨γ, hγ, c, hc, hpc⟩ := hk p hpdist
  refine mem_iUnion.mpr ⟨⟨γ, hγ⟩, ?_⟩
  simp [hatBall, hc, Metric.mem_ball, hpc]



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem innerBall_cover (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    (r : Real) :
    ∀ᶠ k in atTop,
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      Metric.closedBall (X.obj (L.φ k)).basepoint r ⊆
        ⋃ γ : Fin (pb.A r), L.innerBall hd D P pb r k γ := by
  filter_upwards [L.inner_cover hd hD P hre pb r] with k hcover
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  intro p hp
  have hpdist : dist p (X.obj (L.φ k)).basepoint ≤ r := by
    simpa [Metric.mem_closedBall] using hp
  obtain ⟨γ, hγ, c, hc, hpc⟩ := hcover p hpdist
  refine mem_iUnion.mpr ⟨⟨γ, hγ⟩, ?_⟩
  simp [innerBall, hc, Metric.mem_ball, hpc]



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatPOU_of_cover (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (hcover :
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      Metric.closedBall (X.obj (L.φ k)).basepoint r ⊆
        ⋃ γ : Fin (pb.A r), L.hatBall hd D P pb r k γ) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    ∃ ρ : SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
        (Metric.closedBall (X.obj (L.φ k)).basepoint r),
      ρ.IsSubordinate (fun γ : Fin (pb.A r) => L.hatBall hd D P pb r k γ) := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  have htop := ProperMetricOn.top_eq (X.obj (L.φ k)) (P (L.φ k))
  have hs :
      @IsClosed (X.obj (L.φ k)).M (X.obj (L.φ k)).topology
        (Metric.closedBall (X.obj (L.φ k)).basepoint r) := by
    have hs_metric :
        @IsClosed (X.obj (L.φ k)).M
          (P (L.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (Metric.closedBall (X.obj (L.φ k)).basepoint r) :=
      by simpa using
        (Metric.isClosed_closedBall :
          @IsClosed (X.obj (L.φ k)).M
            (P (L.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
            (Metric.closedBall (X.obj (L.φ k)).basepoint r))
    rw [← htop]
    exact hs_metric
  have ho :
      ∀ γ : Fin (pb.A r),
        @IsOpen (X.obj (L.φ k)).M (X.obj (L.φ k)).topology
          (L.hatBall hd D P pb r k γ) := by
    intro γ
    have ho_metric :
        @IsOpen (X.obj (L.φ k)).M
          (P (L.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (L.hatBall hd D P pb r k γ) :=
      by simpa using
        (L.hatBall_open hd D P pb r k γ :
          @IsOpen (X.obj (L.φ k)).M
            (P (L.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
            (L.hatBall hd D P pb r k γ))
    rw [← htop]
    exact ho_metric
  exact SmoothPartitionOfUnity.exists_isSubordinate
    (I := I)
    (s := Metric.closedBall (X.obj (L.φ k)).basepoint r)
    (U := fun γ : Fin (pb.A r) => L.hatBall hd D P pb r k γ)
    hs
    ho
    hcover


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatPOU_eventually (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    (r : Real) :
    ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      ∃ ρ : SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
          (Metric.closedBall (X.obj (L.φ k)).basepoint r),
        ρ.IsSubordinate (fun γ : Fin (pb.A r) => L.hatBall hd D P pb r k γ) := by
  filter_upwards [L.hatBall_cover hd hD P hre pb r] with k hcover
  exact L.hatPOU_of_cover hd P pb r k hcover


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatPOU_nonneg (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (ρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
        (Metric.closedBall (X.obj (L.φ k)).basepoint r))
    (γ : Fin (pb.A r)) (x : (X.obj (L.φ k)).M) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    0 ≤ ρ γ x := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  exact ρ.nonneg γ x


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatPOU_sum_one (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (ρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
        (Metric.closedBall (X.obj (L.φ k)).basepoint r))
    {x : (X.obj (L.φ k)).M}
    (hx :
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      x ∈ Metric.closedBall (X.obj (L.φ k)).basepoint r) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    ∑ γ : Fin (pb.A r), ρ γ x = 1 := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  have hsum := ρ.sum_eq_one hx
  rw [finsum_eq_sum (fun γ : Fin (pb.A r) => ρ γ x)
    (Finite.subset finite_univ (subset_univ (Function.support fun γ : Fin (pb.A r) => ρ γ x)))] at hsum
  rwa [Fintype.sum_subset (by simp)] at hsum



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatPOU_pos (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (ρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
        (Metric.closedBall (X.obj (L.φ k)).basepoint r))
    {x : (X.obj (L.φ k)).M}
    (hx :
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      x ∈ Metric.closedBall (X.obj (L.φ k)).basepoint r) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    ∃ γ : Fin (pb.A r), 0 < ρ γ x := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  exact ρ.exists_pos_of_mem hx


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatPOU_active_mem (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (ρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
        (Metric.closedBall (X.obj (L.φ k)).basepoint r))
    (hρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      ρ.IsSubordinate (fun γ : Fin (pb.A r) => L.hatBall hd D P pb r k γ))
    {γ : Fin (pb.A r)} {x : (X.obj (L.φ k)).M}
    (hγx :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      ρ γ x ≠ 0) :
    x ∈ L.hatBall hd D P pb r k γ := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  have hx_support : x ∈ Function.support fun y => ρ γ y := by
    simpa [Function.mem_support] using hγx
  exact hρ γ (subset_tsupport (ρ γ) hx_support)



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem binter_of_mem_hat (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    {α β : Fin (pb.A r)} {z : (X.obj (L.φ k)).M}
    (hα : z ∈ L.hatBall hd D P pb r k α)
    (hβ : z ∈ L.hatBall hd D P pb r k β) :
    BInter hd D P L.lamInf (α : Nat) (β : Nat) (L.φ k) := by
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  cases hcα : seqCenter hd D P (L.φ k) (α : Nat) with
  | none => simp [hatBall, hcα] at hα
  | some x =>
      cases hcβ : seqCenter hd D P (L.φ k) (β : Nat) with
      | none => simp [hatBall, hcβ] at hβ
      | some y =>
          have hα' : z ∈ Metric.ball x (4 * L.lamInf (α : Nat)) := by
            simpa only [hatBall, hcα] using hα
          have hβ' : z ∈ Metric.ball y (4 * L.lamInf (β : Nat)) := by
            simpa only [hatBall, hcβ] using hβ
          have hlamAlpha : 0 < L.lamInf (α : Nat) :=
            hd.lambda_pos hD (L.rInf (α : Nat))
          have hlamBeta : 0 < L.lamInf (β : Nat) :=
            hd.lambda_pos hD (L.rInf (β : Nat))
          refine ⟨x, y, hcα, hcβ, Set.not_disjoint_iff.mpr ⟨z, ?_, ?_⟩⟩
          · rw [Metric.mem_ball] at hα' ⊢
            nlinarith
          · rw [Metric.mem_ball] at hβ' ⊢
            nlinarith



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem binter_of_active (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (ρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
        (Metric.closedBall (X.obj (L.φ k)).basepoint r))
    (hρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      ρ.IsSubordinate (fun γ : Fin (pb.A r) => L.hatBall hd D P pb r k γ))
    {β γ : Fin (pb.A r)} {x : (X.obj (L.φ k)).M}
    (hβx :
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      x ∈ L.hatBall hd D P pb r k β)
    (hγx :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      ρ γ x ≠ 0) :
    BInter hd D P L.lamInf (β : Nat) (γ : Nat) (L.φ k) := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  exact L.binter_of_mem_hat hd hD P pb r k hβx
    (L.hatPOU_active_mem hd P pb r k ρ hρ hγx)



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatPOU_weights (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (ρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
        (Metric.closedBall (X.obj (L.φ k)).basepoint r))
    {x : (X.obj (L.φ k)).M}
    (hx :
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      x ∈ Metric.closedBall (X.obj (L.φ k)).basepoint r) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    (∀ γ : Fin (pb.A r), 0 ≤ ρ γ x) ∧
      (∃ γ : Fin (pb.A r), 0 < ρ γ x) ∧
        ∑ γ : Fin (pb.A r), ρ γ x = 1 := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  exact ⟨fun γ => L.hatPOU_nonneg hd P pb r k ρ γ x,
    L.hatPOU_pos hd P pb r k ρ hx,
    L.hatPOU_sum_one hd P pb r k ρ hx⟩



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatPOU_active_data (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (ρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
        (Metric.closedBall (X.obj (L.φ k)).basepoint r))
    (hρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      ρ.IsSubordinate (fun γ : Fin (pb.A r) => L.hatBall hd D P pb r k γ))
    {x : (X.obj (L.φ k)).M}
    (hx :
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      x ∈ Metric.closedBall (X.obj (L.φ k)).basepoint r) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    ((∀ γ : Fin (pb.A r), 0 ≤ ρ γ x) ∧
      (∃ γ : Fin (pb.A r), 0 < ρ γ x) ∧
        ∑ γ : Fin (pb.A r), ρ γ x = 1) ∧
      ∀ γ : Fin (pb.A r), ρ γ x ≠ 0 →
        x ∈ L.hatBall hd D P pb r k γ := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  exact ⟨L.hatPOU_weights hd P pb r k ρ hx,
    fun γ hγx => L.hatPOU_active_mem hd P pb r k ρ hρ hγx⟩

end NetLimitData

end HCGCompactness
end DifferentialGeometry
