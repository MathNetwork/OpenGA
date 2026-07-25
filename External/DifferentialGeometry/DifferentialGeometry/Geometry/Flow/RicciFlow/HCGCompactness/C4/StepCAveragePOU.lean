import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAveraging
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCPartition
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBApproxIso
import DifferentialGeometry.Geometry.Exponential.GaussLemma

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]




omit [Module.Finite ℝ E] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank Real E)] in
theorem chartSymmUnif
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : IsCompact K)
    (hKtarget : K ⊆ (NormalCoordinates.normalChartAt (I := I) g p).target) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    UniformContinuousOn
      (fun v : E => (NormalCoordinates.normalChartAt (I := I) g p).symm v) K := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  let ψ := NormalCoordinates.normalChartAt (I := I) g p
  have hcont : ContinuousOn (fun v : E => ψ.symm v) K := by
    simpa [ψ] using ψ.contMDiffOn_invFun.continuousOn.mono hKtarget
  exact hK.uniformContinuousOn_of_continuous hcont




omit [Module.Finite ℝ E] in
omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartSymmIdConv
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : IsCompact K)
    (hKtarget : K ⊆ (NormalCoordinates.normalChartAt (I := I) g p).target)
    (F : Nat → Nat → E → E)
    (hclose : ∀ δ : Real, δ > 0 → ∃ N : Nat,
      ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ v : E, v ∈ K →
        dist (F a b v) v < δ) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε : Real, ε > 0 → ∃ N : Nat,
      ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ v : E, v ∈ K →
        dist ((NormalCoordinates.normalChartAt (I := I) g p).symm v)
          ((NormalCoordinates.normalChartAt (I := I) g p).symm (F a b v)) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  let ψ := NormalCoordinates.normalChartAt (I := I) g p
  obtain ⟨η, hηpos, hηtarget⟩ :=
    hK.exists_cthickening_subset_open ψ.open_target hKtarget
  let K' : Set E := Metric.cthickening η K
  have hK' : IsCompact K' := hK.cthickening
  have hK'target : K' ⊆ ψ.target := by
    simpa only [K'] using hηtarget
  have huc :
      UniformContinuousOn
        (fun v : E => ψ.symm v) K' :=
    chartSymmUnif (I := I) g p hK' hK'target
  rw [Metric.uniformContinuousOn_iff] at huc
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := huc ε hε
  have hminpos : 0 < min δ η := lt_min hδpos hηpos
  obtain ⟨N, hN⟩ := hclose (min δ η) hminpos
  refine ⟨N, fun a ha b hb v hv => ?_⟩
  have hvK' : v ∈ K' := Metric.self_subset_cthickening K hv
  have hdist : dist (F a b v) v < min δ η := hN a ha b hb v hv
  have hFvK' : F a b v ∈ K' := by
    exact Metric.mem_cthickening_of_dist_le (F a b v) v η K hv
      (le_trans (le_of_lt hdist) (min_le_right δ η))
  simpa [dist_comm] using
    hδ (F a b v) hFvK' v hvK' (lt_of_lt_of_le hdist (min_le_left δ η))



omit [Module.Finite ℝ E] in
omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartPtsConv
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) (p : M)
    {S : Set M} {K : Set E} (hK : IsCompact K)
    (hKtarget : K ⊆ (NormalCoordinates.normalChartAt (I := I) g p).target)
    (hSsource : ∀ x : M, x ∈ S →
      x ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hScoord : ∀ x : M, x ∈ S →
      (NormalCoordinates.normalChartAt (I := I) g p) x ∈ K)
    (F : Nat → Nat → E → E)
    (hclose : ∀ δ : Real, δ > 0 → ∃ N : Nat,
      ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ v : E, v ∈ K →
        dist (F a b v) v < δ) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε : Real, ε > 0 → ∃ N : Nat,
      ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ x : M, x ∈ S →
        dist x ((NormalCoordinates.normalChartAt (I := I) g p).symm
          (F a b ((NormalCoordinates.normalChartAt (I := I) g p) x))) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  let ψ := NormalCoordinates.normalChartAt (I := I) g p
  have hdecoded :
      ∀ ε : Real, ε > 0 → ∃ N : Nat,
        ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ v : E, v ∈ K →
          dist (ψ.symm v) (ψ.symm (F a b v)) < ε := by
    simpa [ψ] using
      chartSymmIdConv (I := I) g p hK hKtarget F hclose
  intro ε hε
  obtain ⟨N, hN⟩ := hdecoded ε hε
  refine ⟨N, fun a ha b hb x hx => ?_⟩
  have hxK : ψ x ∈ K := by
    simpa [ψ] using hScoord x hx
  have hxsrc : x ∈ ψ.source := by
    simpa [ψ] using hSsource x hx
  have hdist : dist (ψ.symm (ψ x)) (ψ.symm (F a b (ψ x))) < ε :=
    hN a ha b hb (ψ x) hxK
  have hleft : ψ.symm (ψ x) = x := by
    simpa [ψ] using NormalCoordinates.normalChartAt_left_inv (I := I) g p hxsrc
  rw [hleft] at hdist
  simpa [ψ] using hdist



omit [Module.Finite ℝ E] in
omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartPtsSrcK
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) (p : M)
    {S Ksrc : Set M} (hKsrc : IsCompact Ksrc) (hSsub : S ⊆ Ksrc)
    (hsrcK : Ksrc ⊆ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (F : Nat -> Nat -> E -> E)
    (hclose : ∀ δ : Real, δ > 0 -> ∃ N : Nat,
      ∀ a : Nat, a ≥ N -> ∀ b : Nat, b ≥ N -> ∀ v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) g p) '' Ksrc ->
          dist (F a b v) v < δ) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε : Real, ε > 0 -> ∃ N : Nat,
      ∀ a : Nat, a ≥ N -> ∀ b : Nat, b ≥ N -> ∀ x : M, x ∈ S ->
        dist x ((NormalCoordinates.normalChartAt (I := I) g p).symm
          (F a b ((NormalCoordinates.normalChartAt (I := I) g p) x))) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  let ψ := NormalCoordinates.normalChartAt (I := I) g p
  have hcont : ContinuousOn (fun x : M => ψ x) Ksrc := by
    exact ψ.contMDiffOn_toFun.continuousOn.mono hsrcK
  have hK : IsCompact (ψ '' Ksrc) := hKsrc.image_of_continuousOn hcont
  have hKtarget : ψ '' Ksrc ⊆ ψ.target := by
    rintro v ⟨x, hx, rfl⟩
    exact ψ.map_source (hsrcK hx)
  have hSsource : ∀ x : M, x ∈ S -> x ∈ ψ.source := by
    intro x hx
    exact hsrcK (hSsub hx)
  have hScoord : ∀ x : M, x ∈ S -> ψ x ∈ ψ '' Ksrc := by
    intro x hx
    exact ⟨x, hSsub hx, rfl⟩
  simpa [ψ] using
    chartPtsConv (I := I) (g := g) (p := p) (S := S) (K := ψ '' Ksrc)
      hK hKtarget hSsource hScoord F hclose





omit [Module.Finite ℝ E] in
theorem properBallSrcOfRad
    [FiniteDimensional Real E]
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {c : Y.M} {R : Real}
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R < expRadiusGp (I := I) Y.metric c) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    Metric.closedBall c R ⊆
      (NormalCoordinates.normalChartAt (I := I) Y.metric c).source := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := P.ms
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm :
      ∀ x : Y.M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)) := by
    intro x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric x v)
  intro y hy
  have hed :
      riemannianEDist I c y =
        ENNReal.ofReal (dist c y) := by
    have h := P.realizes c y
    simpa [PointedRiemannianManifold.emetricSpace] using h
  have hfin : riemannianEDist I c y ≠ (⊤ : ℝ≥0∞) := by
    rw [hed]
    exact ENNReal.ofReal_ne_top
  have hdist_le : dist c y ≤ R := by
    have hdist := (Metric.mem_closedBall.mp hy)
    simpa [dist_comm] using hdist
  have hsmall : (riemannianEDist I c y).toReal < expRadiusGp (I := I) Y.metric c := by
    rw [hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c y)]
    exact lt_of_le_of_lt hdist_le hR
  exact memNChartSrcOfDist (I := I) Y.metric c hEnorm hfin hsmall



omit [Module.Finite ℝ E] in
theorem properBallNormal
    [FiniteDimensional Real E]
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {c y : Y.M} {R : Real}
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R < expRadiusGp (I := I) Y.metric c)
    (hy : letI : MetricSpace Y.M := P.ms; y ∈ Metric.ball c R) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    ∃ v : E,
      v ∈ (NormalCoordinates.normalChartAt (I := I) Y.metric c).target ∧
      (show TangentSpace I c from v) ∈ expDomain (I := I) Y.metric c ∧
      Real.sqrt (Y.metric.inner c v v) = dist c y ∧
      y = expMap (I := I) Y.metric c (show TangentSpace I c from v) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := P.ms
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm : ∀ x : Y.M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x w w)) := by
    intro x w
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric x w)
  have hed : riemannianEDist I c y = ENNReal.ofReal (dist c y) := by
    have h := P.realizes c y
    simpa [PointedRiemannianManifold.emetricSpace] using h
  have hfin : riemannianEDist I c y ≠ (⊤ : ENNReal) := by
    rw [hed]
    exact ENNReal.ofReal_ne_top
  have hdist_lt : dist c y < R := by
    simpa only [Metric.mem_ball, dist_comm] using hy
  have hsmall : (riemannianEDist I c y).toReal <
      expRadiusGp (I := I) Y.metric c := by
    rw [hed, ENNReal.toReal_ofReal dist_nonneg]
    exact hdist_lt.trans hR
  obtain ⟨v, hvtgt, hvdom, hvlen, hyeq⟩ :=
    metricBall_subset_normalBall (I := I) Y.metric c hEnorm hfin hsmall
  refine ⟨v, hvtgt, hvdom, ?_, hyeq⟩
  calc
    Real.sqrt (Y.metric.inner c v v) = (riemannianEDist I c y).toReal := hvlen
    _ = dist c y := by rw [hed, ENNReal.toReal_ofReal dist_nonneg]



omit [Module.Finite ℝ E] in
theorem properExpDist
    [FiniteDimensional Real E]
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (c : Y.M) {v : E}
    (hv :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Real.sqrt (Y.metric.inner c v v) < expRadiusGp (I := I) Y.metric c) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    dist c (expMap (I := I) Y.metric c (show TangentSpace I c from v)) =
      Real.sqrt (Y.metric.inner c v v) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := P.ms
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm : ∀ x : Y.M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x w w)) := by
    intro x w
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric x w)
  have hed := edist_exp_eq_radius (I := I) Y.metric c hEnorm hv
  have hdist :
      riemannianEDist I c
          (expMap (I := I) Y.metric c (show TangentSpace I c from v)) =
        ENNReal.ofReal
          (dist c (expMap (I := I) Y.metric c (show TangentSpace I c from v))) := by
    have h := P.realizes c
      (expMap (I := I) Y.metric c (show TangentSpace I c from v))
    simpa [PointedRiemannianManifold.emetricSpace] using h
  have hofReal :
      ENNReal.ofReal
          (dist c (expMap (I := I) Y.metric c (show TangentSpace I c from v))) =
        ENNReal.ofReal (Real.sqrt (Y.metric.inner c v v)) := by
    rw [← hdist]
    exact hed
  exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg (Real.sqrt_nonneg _)).mp hofReal

namespace NetLimitData



noncomputable def hatSourceBall (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (r : Real) (n : Nat) :
    Set (X.obj (L.φ n)).M :=
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  Metric.closedBall (X.obj (L.φ n)).basepoint r

omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem hatSourceBall_subseq
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (r : Real) (n : Nat) {ψ : Nat -> Nat} (hψ : StrictMono ψ) :
    NetLimitData.hatSourceBall (I := I) (X := X) hd P (L.subseq hψ) r n =
      NetLimitData.hatSourceBall (I := I) (X := X) hd P L r (ψ n) := rfl



omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatSource_nhds
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    {R s : Real} (n : Nat) (hRs : R < s)
    {x : (X.obj (L.φ n)).M}
    (hx : x ∈ hatSourceBall (I := I) (X := X) hd P L R n) :
    letI : TopologicalSpace (X.obj (L.φ n)).M :=
      (X.obj (L.φ n)).topology
    hatSourceBall (I := I) (X := X) hd P L s n ∈ nhds x := by
  let Y := X.obj (L.φ n)
  letI : TopologicalSpace Y.M := Y.topology
  have hopen :
      @IsOpen Y.M Y.topology
        (letI : MetricSpace Y.M := (P (L.φ n)).ms
         Metric.ball Y.basepoint s) := by
    have hb :
        @IsOpen Y.M
          (P (L.φ n)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (letI : MetricSpace Y.M := (P (L.φ n)).ms
           Metric.ball Y.basepoint s) := by
      letI : MetricSpace Y.M := (P (L.φ n)).ms
      exact Metric.isOpen_ball
    rw [ProperMetricOn.top_eq Y (P (L.φ n))] at hb
    exact hb
  have hxopen :
      x ∈ (letI : MetricSpace Y.M := (P (L.φ n)).ms
        Metric.ball Y.basepoint s) := by
    letI : MetricSpace Y.M := (P (L.φ n)).ms
    exact Metric.closedBall_subset_ball hRs
      (by simpa only [hatSourceBall] using hx)
  refine mem_of_superset (hopen.mem_nhds hxopen) ?_
  intro y hy
  letI : MetricSpace Y.M := (P (L.φ n)).ms
  simpa only [hatSourceBall] using (Metric.ball_subset_closedBall hy)


omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatSourceCompact
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (r : Real) (n : Nat) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    IsCompact (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n) := by
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  haveI : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have htop := ProperMetricOn.top_eq (X.obj (L.φ n)) (P (L.φ n))
  have hcompact :
      @IsCompact (X.obj (L.φ n)).M
        (P (L.φ n)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n) := by
    simpa [NetLimitData.hatSourceBall] using
      (isCompact_closedBall (X.obj (L.φ n)).basepoint r)
  rw [← htop]
  exact hcompact



omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem sourceComplete
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (n : Nat) (hX : SeqMetricComplete (I := I) X)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : EMetricSpace (X.obj (L.φ n)).M :=
      EMetricSpace.ofRiemannianMetric I (X.obj (L.φ n)).M
    CompleteSpace (X.obj (L.φ n)).M := by
  have h := MetricComplete.complete (I := I) (X.obj (L.φ n)) (hX.complete (L.φ n))
  simpa using h


omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatBallInCompact
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (k : Nat) (gamma : Fin (pb.A r)) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    exists K : Set (X.obj (L.φ k)).M, IsCompact K ∧
      (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (k := k) (γ := gamma) :
        Set (X.obj (L.φ k)).M) ⊆ K := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  haveI : ProperSpace (X.obj (L.φ k)).M := (P (L.φ k)).proper
  have htop := ProperMetricOn.top_eq (X.obj (L.φ k)) (P (L.φ k))
  cases hcenter : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none =>
      refine ⟨∅, isCompact_empty, ?_⟩
      intro x hx
      simp [NetLimitData.hatBall, hcenter] at hx
  | some c =>
      refine ⟨Metric.closedBall c (4 * L.lamInf (gamma : Nat)), ?_, ?_⟩
      · have hcompact :
            @IsCompact (X.obj (L.φ k)).M
              (P (L.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
              (Metric.closedBall c (4 * L.lamInf (gamma : Nat))) := by
          simpa using (isCompact_closedBall c (4 * L.lamInf (gamma : Nat)))
        rw [← htop]
        exact hcompact
      · intro x hx
        have hdist : dist x c < 4 * L.lamInf (gamma : Nat) := by
          simpa [NetLimitData.hatBall, hcenter, Metric.mem_ball] using hx
        simpa [Metric.mem_closedBall] using le_of_lt hdist




noncomputable def hatSourceCage (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat) (gamma : Fin (pb.A r)) :
    Set (X.obj (L.φ n)).M :=
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  closure
    (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
      (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
        Set (X.obj (L.φ n)).M))

omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem hatSourceCage_subseq
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat) (gamma : Fin (pb.A r))
    {ψ : Nat -> Nat} (hψ : StrictMono ψ) :
    NetLimitData.hatSourceCage (I := I) (X := X) hd P (L.subseq hψ) pb r n gamma =
      NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r (ψ n) gamma := by
  simp [hatSourceCage]
  rfl


omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatCageData
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat) (gamma : Fin (pb.A r)) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    IsCompact (NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma) ∧
      (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)) ⊆
        NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  let S : Set (X.obj (L.φ n)).M :=
    NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n
  let H : Set (X.obj (L.φ n)).M :=
    NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
      (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma)
  have hScompact : IsCompact S := by
    simpa [S] using
      NetLimitData.hatSourceCompact (I := I) (X := X) hd P L r n
  have hclosureS : closure (S ∩ H) ⊆ S := by
    exact closure_minimal inter_subset_left hScompact.isClosed
  have hcompact : IsCompact (closure (S ∩ H)) :=
    hScompact.of_isClosed_subset isClosed_closure hclosureS
  refine ⟨?_, ?_⟩
  · simpa [NetLimitData.hatSourceCage, S, H] using hcompact
  · simpa [NetLimitData.hatSourceCage, S, H] using
      (subset_closure : S ∩ H ⊆ closure (S ∩ H))


omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatCageCompact
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    forall gamma : Fin (pb.A r),
      IsCompact (NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma) := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  intro gamma
  exact (NetLimitData.hatCageData (I := I) (X := X) hd P L pb r n gamma).1



omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatCageSub
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    forall gamma : Fin (pb.A r),
      (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)) ⊆
        NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  intro gamma
  exact (NetLimitData.hatCageData (I := I) (X := X) hd P L pb r n gamma).2



omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatCageInClosed
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat) (gamma : Fin (pb.A r))
    {c : (X.obj (L.φ n)).M}
    (hc : seqCenter hd D P (L.φ n) (gamma : Nat) = some c) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
    NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
      Metric.closedBall c (4 * L.lamInf (gamma : Nat)) := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  have htop := ProperMetricOn.top_eq (X.obj (L.φ n)) (P (L.φ n))
  have hclosed :
      @IsClosed (X.obj (L.φ n)).M (X.obj (L.φ n)).topology
        (Metric.closedBall c (4 * L.lamInf (gamma : Nat))) := by
    have hclosed_metric :
        @IsClosed (X.obj (L.φ n)).M
          (P (L.φ n)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (Metric.closedBall c (4 * L.lamInf (gamma : Nat))) := by
      simpa using
        (Metric.isClosed_closedBall :
          @IsClosed (X.obj (L.φ n)).M
            (P (L.φ n)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
            (Metric.closedBall c (4 * L.lamInf (gamma : Nat))))
    rw [← htop]
    exact hclosed_metric
  have hsub :
      (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)) ⊆
        Metric.closedBall c (4 * L.lamInf (gamma : Nat)) := by
    intro x hx
    have hdist : dist x c < 4 * L.lamInf (gamma : Nat) := by
      simpa [NetLimitData.hatBall, hc, Metric.mem_ball] using hx.2
    simpa [Metric.mem_closedBall] using le_of_lt hdist
  simpa [NetLimitData.hatSourceCage] using closure_minimal hsub hclosed



omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank Real E)] in
theorem hatCageSrcOfBall
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M) (gamma : Fin (pb.A r))
    (hcenter : seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hball :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      Metric.closedBall (center gamma) (4 * L.lamInf (gamma : Nat)) ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
      (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
        (center gamma)).source := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  exact
    (NetLimitData.hatCageInClosed (I := I) (X := X) hd P L pb r n gamma hcenter).trans
      hball





omit [Module.Finite ℝ E] in
theorem hatCageSrcOfRad
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M) (gamma : Fin (pb.A r))
    (hcenter : seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf (gamma : Nat) <
        expRadiusGp (I := I) (X.obj (L.φ n)).metric (center gamma)) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
      (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
        (center gamma)).source := by
  exact
    NetLimitData.hatCageSrcOfBall (I := I) (X := X) hd P L pb r n center gamma
      hcenter
      (properBallSrcOfRad (I := I) (Y := X.obj (L.φ n)) (P := P (L.φ n)) hR)




omit [Module.Finite ℝ E] in
theorem hatCageSrcCases
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall c : (X.obj (L.φ n)).M,
        seqCenter hd D P (L.φ n) (gamma : Nat) = some c ->
          c = center gamma ∧
            4 * L.lamInf (gamma : Nat) <
              expRadiusGp (I := I) (X.obj (L.φ n)).metric c) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    forall gamma : Fin (pb.A r),
      NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source := by
  intro gamma
  cases hc : seqCenter hd D P (L.φ n) (gamma : Nat) with
  | none =>
      simp [NetLimitData.hatSourceCage, NetLimitData.hatBall, hc]
  | some c =>
      rcases hR gamma c hc with ⟨rfl, hrad⟩
      exact NetLimitData.hatCageSrcOfRad (I := I) (X := X) hd P L pb r n center
        gamma hc hrad




omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank Real E)] in
theorem hatSuppCageData
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (_pb : hd.PackingBound D) (_r : Real) (n : Nat)
    {s : Set (X.obj (L.φ n)).M} {ι : Type*}
    (mu : (X.obj (L.φ n)).M -> ι -> Real)
    (center : ι -> (X.obj (L.φ n)).M)
    (sourceCage : ι -> Set (X.obj (L.φ n)).M)
    (U V' : ι -> Set E)
    (Binf : ι -> E -> E)
    (hCageCompact :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      forall gamma : ι, IsCompact (sourceCage gamma))
    (hSuppCage :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      forall gamma : ι, forall x : (X.obj (L.φ n)).M,
        x ∈ s ->
        mu x gamma ≠ 0 -> x ∈ sourceCage gamma)
    (hsrc :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : ι,
        sourceCage gamma ⊆
          (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
            (center gamma)).source)
    (hBcont : forall gamma : ι, ContinuousOn (Binf gamma) (U gamma))
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : ι,
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            sourceCage gamma ⊆
          U gamma)
    (hV'closed : forall gamma : ι, IsClosed (V' gamma))
    (hSuppV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : ι, forall x : (X.obj (L.φ n)).M,
        x ∈ s ->
        mu x gamma ≠ 0 ->
          Binf gamma
              ((NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
                (center gamma)) x) ∈ V' gamma) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    ∃ sourceK : ι -> Set (X.obj (L.φ n)).M,
      (forall gamma : ι, IsCompact (sourceK gamma)) ∧
      (forall gamma : ι, forall x : (X.obj (L.φ n)).M,
        x ∈ s ->
        mu x gamma ≠ 0 -> x ∈ sourceK gamma) ∧
      (forall gamma : ι, sourceK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source) ∧
      (forall gamma : ι,
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma ⊆ U gamma) ∧
      (forall gamma : ι, forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma -> Binf gamma v ∈ V' gamma) := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  let sourceBall : Set (X.obj (L.φ n)).M := s
  let chart : ι -> (X.obj (L.φ n)).M -> E := fun gamma =>
    NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
      (center gamma)
  let support : ι -> Set (X.obj (L.φ n)).M := fun gamma =>
    {x | x ∈ sourceBall ∧ mu x gamma ≠ 0}
  let sourceK : ι -> Set (X.obj (L.φ n)).M := fun gamma =>
    closure (support gamma)
  have hKsub (gamma : ι) : sourceK gamma ⊆ sourceCage gamma := by
    apply closure_minimal
    · intro x hx
      exact hSuppCage gamma x hx.1 hx.2
    · exact (hCageCompact gamma).isClosed
  refine ⟨sourceK, ?_, ?_, ?_, ?_, ?_⟩
  · intro gamma
    exact (hCageCompact gamma).of_isClosed_subset isClosed_closure (hKsub gamma)
  · intro gamma x hx hmu
    exact subset_closure ⟨hx, hmu⟩
  · intro gamma x hx
    exact hsrc gamma (hKsub gamma hx)
  · intro gamma v hv
    rcases hv with ⟨x, hx, rfl⟩
    exact hKU gamma ⟨x, hKsub gamma hx, rfl⟩
  · intro gamma v hv
    rcases hv with ⟨x, hx, rfl⟩
    have hchart : ContinuousOn (chart gamma) (sourceCage gamma) :=
      (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
        (center gamma)).contMDiffOn_toFun.continuousOn.mono (hsrc gamma)
    have hcomp : ContinuousOn (fun y => Binf gamma (chart gamma y))
        (sourceCage gamma) :=
      (hBcont gamma).comp' hchart (by
        intro y hy
        exact hKU gamma ⟨y, hy, rfl⟩)
    have hclosed : IsClosed
        (sourceCage gamma ∩
          (fun y => Binf gamma (chart gamma y)) ⁻¹' V' gamma) :=
      hcomp.preimage_isClosed_of_isClosed (hCageCompact gamma).isClosed
        (hV'closed gamma)
    have hsupp : support gamma ⊆
        sourceCage gamma ∩
          (fun y => Binf gamma (chart gamma y)) ⁻¹' V' gamma := by
      intro y hy
      exact ⟨hSuppCage gamma y hy.1 hy.2, hSuppV gamma y hy.1 hy.2⟩
    exact (closure_minimal hsupp hclosed hx).2



omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatPtsOfCompact
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (ptsSeq :
      Nat -> Nat -> (X.obj (L.φ n)).M -> Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hconv :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall gamma : Fin (pb.A r), forall K : Set (X.obj (L.φ n)).M,
        IsCompact K ->
          (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
            (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
              (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
              Set (X.obj (L.φ n)).M)) ⊆ K ->
          forall eps : Real, eps > 0 -> exists N : Nat,
            forall a : Nat, a >= N -> forall b : Nat, b >= N ->
              forall x : (X.obj (L.φ n)).M, x ∈ K ->
                dist x (ptsSeq a b x gamma) < eps) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall gamma : Fin (pb.A r), forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
              (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
              Set (X.obj (L.φ n)).M) ->
              dist x (ptsSeq a b x gamma) < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  intro gamma eps heps
  obtain ⟨K, hK, hhatK⟩ :=
    NetLimitData.hatBallInCompact (I := I) (X := X) hd P L pb r n gamma
  have hsub :
      (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)) ⊆ K := by
    intro x hx
    exact hhatK hx.2
  obtain ⟨N, hN⟩ := hconv gamma K hK hsub eps heps
  refine ⟨N, fun a ha b hb x hxsrc hxhat => ?_⟩
  exact hN a ha b hb x (hsub ⟨hxsrc, hxhat⟩)





omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem hatChartPts
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (coordK : Fin (pb.A r) -> Set E)
    (F : Fin (pb.A r) -> Nat -> Nat -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hK :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      ∀ gamma : Fin (pb.A r), IsCompact (coordK gamma))
    (hKtarget :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      ∀ gamma : Fin (pb.A r), coordK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).target)
    (hsource :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      ∀ gamma : Fin (pb.A r), ∀ x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M) ->
        x ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source)
    (hcoord :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      ∀ gamma : Fin (pb.A r), ∀ x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M) ->
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) x ∈ coordK gamma)
    (hclose : ∀ gamma : Fin (pb.A r), ∀ δ : Real, δ > 0 -> ∃ N : Nat,
      ∀ a : Nat, a >= N -> ∀ b : Nat, b >= N -> ∀ v : E, v ∈ coordK gamma ->
        dist (F gamma a b v) v < δ) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall gamma : Fin (pb.A r), forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
              (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
              Set (X.obj (L.φ n)).M) ->
              dist x ((NormalCoordinates.normalChartAt (I := I)
                (X.obj (L.φ n)).metric (center gamma)).symm
                  (F gamma a b ((NormalCoordinates.normalChartAt (I := I)
                    (X.obj (L.φ n)).metric (center gamma)) x))) < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  intro gamma eps heps
  let S : Set (X.obj (L.φ n)).M :=
    NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
      (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
        Set (X.obj (L.φ n)).M)
  have hSsource : ∀ x : (X.obj (L.φ n)).M, x ∈ S ->
      x ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
        (center gamma)).source := by
    intro x hx
    exact hsource gamma x hx.1 hx.2
  have hScoord : ∀ x : (X.obj (L.φ n)).M, x ∈ S ->
      (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
        (center gamma)) x ∈ coordK gamma := by
    intro x hx
    exact hcoord gamma x hx.1 hx.2
  obtain ⟨N, hN⟩ :=
    chartPtsConv (I := I) (g := (X.obj (L.φ n)).metric)
      (p := center gamma) (S := S) (K := coordK gamma)
      (hK gamma) (hKtarget gamma) hSsource hScoord (F gamma)
      (hclose gamma) eps heps
  refine ⟨N, fun a ha b hb x hxsrc hxhat => ?_⟩
  exact hN a ha b hb x ⟨hxsrc, hxhat⟩





omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem hatChartPtsSrcK
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (sourceK : Fin (pb.A r) -> Set (X.obj (L.φ n)).M)
    (F : Fin (pb.A r) -> Nat -> Nat -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hKsrc :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ∀ gamma : Fin (pb.A r), IsCompact (sourceK gamma))
    (hSsub :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ∀ gamma : Fin (pb.A r),
        (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
          (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
            (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
            Set (X.obj (L.φ n)).M)) ⊆ sourceK gamma)
    (hsrcK :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      ∀ gamma : Fin (pb.A r), sourceK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source)
    (hclose :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      ∀ gamma : Fin (pb.A r), ∀ δ : Real, δ > 0 -> ∃ N : Nat,
        ∀ a : Nat, a >= N -> ∀ b : Nat, b >= N -> ∀ v : E,
          v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
            (center gamma)) '' sourceK gamma ->
            dist (F gamma a b v) v < δ) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall gamma : Fin (pb.A r), forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
              (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
              Set (X.obj (L.φ n)).M) ->
              dist x ((NormalCoordinates.normalChartAt (I := I)
                (X.obj (L.φ n)).metric (center gamma)).symm
                  (F gamma a b ((NormalCoordinates.normalChartAt (I := I)
                    (X.obj (L.φ n)).metric (center gamma)) x))) < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  intro gamma eps heps
  let S : Set (X.obj (L.φ n)).M :=
    NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
      (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
        Set (X.obj (L.φ n)).M)
  obtain ⟨N, hN⟩ :=
    chartPtsSrcK (I := I) (g := (X.obj (L.φ n)).metric)
      (p := center gamma) (S := S) (Ksrc := sourceK gamma)
      (hKsrc gamma) (hSsub gamma) (hsrcK gamma) (F gamma)
      (hclose gamma) eps heps
  refine ⟨N, fun a ha b hb x hxsrc hxhat => ?_⟩
  exact hN a ha b hb x ⟨hxsrc, hxhat⟩



omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem hatSrcPtsOfComp
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (sourceK : Fin (pb.A r) -> Set (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hKsrc :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ∀ gamma : Fin (pb.A r), IsCompact (sourceK gamma))
    (hSsub :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ∀ gamma : Fin (pb.A r),
        (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
          (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
            (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
            Set (X.obj (L.φ n)).M)) ⊆ sourceK gamma)
    (hsrcK :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      ∀ gamma : Fin (pb.A r), sourceK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source)
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma ⊆ U gamma)
    (hKV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma -> Binf gamma v ∈ V gamma) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall gamma : Fin (pb.A r), forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
              (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
              Set (X.obj (L.φ n)).M) ->
              dist x ((NormalCoordinates.normalChartAt (I := I)
                (X.obj (L.φ n)).metric (center gamma)).symm
                  (A gamma b (B gamma a ((NormalCoordinates.normalChartAt (I := I)
                    (X.obj (L.φ n)).metric (center gamma)) x)))) < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  exact
    NetLimitData.hatChartPtsSrcK (I := I) (X := X) hd P L pb r n center sourceK
      (fun gamma a b v => A gamma b (B gamma a v)) hconn hKsrc hSsub hsrcK
      (fun gamma δ hδ =>
        let ψ := NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)
        have hcont : ContinuousOn (fun x : (X.obj (L.φ n)).M => ψ x)
            (sourceK gamma) := by
          exact ψ.contMDiffOn_toFun.continuousOn.mono (hsrcK gamma)
        have hKimg : IsCompact (ψ '' sourceK gamma) :=
          (hKsrc gamma).image_of_continuousOn hcont
        comp_tendsto_id_on (E := E) (F := E) (U := U gamma) (V := V gamma)
          (K := ψ '' sourceK gamma) (hVopen gamma) (B gamma) (Binf gamma)
          (A gamma) (Ainf gamma) (hB gamma) (hA gamma) (hBcont gamma)
          (hAcont gamma) (hid gamma) hKimg (hKU gamma) (hKV gamma) δ hδ)





omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem hatSuppPtsOfComp
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (_pb : hd.PackingBound D) (_r : Real) (n : Nat)
    {s : Set (X.obj (L.φ n)).M} {ι : Type*}
    (mu : (X.obj (L.φ n)).M -> ι -> Real)
    (center : ι -> (X.obj (L.φ n)).M)
    (sourceK : ι -> Set (X.obj (L.φ n)).M)
    (U V : ι -> Set E)
    (B : ι -> Nat -> E -> E)
    (Binf : ι -> E -> E)
    (A : ι -> Nat -> E -> E)
    (Ainf : ι -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hKsrc :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      forall gamma : ι, IsCompact (sourceK gamma))
    (hSupp :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      forall gamma : ι, forall x : (X.obj (L.φ n)).M,
        x ∈ s ->
        mu x gamma ≠ 0 -> x ∈ sourceK gamma)
    (hsrcK :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : ι, sourceK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source)
    (hVopen : forall gamma : ι, IsOpen (V gamma))
    (hB : forall gamma : ι,
      MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : ι,
      MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : ι, ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : ι, ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : ι, forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : ι,
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma ⊆ U gamma)
    (hKV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : ι, forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma -> Binf gamma v ∈ V gamma) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall gamma : ι, forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ s ->
          mu x gamma ≠ 0 ->
            dist x ((NormalCoordinates.normalChartAt (I := I)
              (X.obj (L.φ n)).metric (center gamma)).symm
                (A gamma b (B gamma a ((NormalCoordinates.normalChartAt (I := I)
                  (X.obj (L.φ n)).metric (center gamma)) x)))) < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  intro gamma eps heps
  let S : Set (X.obj (L.φ n)).M :=
    {x | x ∈ s ∧ mu x gamma ≠ 0}
  have hSsub : S ⊆ sourceK gamma := by
    intro x hx
    exact hSupp gamma x hx.1 hx.2
  let psi := NormalCoordinates.normalChartAt (I := I)
    (X.obj (L.φ n)).metric (center gamma)
  have hcont : ContinuousOn (fun x : (X.obj (L.φ n)).M => psi x)
      (sourceK gamma) :=
    psi.contMDiffOn_toFun.continuousOn.mono (hsrcK gamma)
  have hKimg : IsCompact (psi '' sourceK gamma) :=
    (hKsrc gamma).image_of_continuousOn hcont
  have hclose : forall delta : Real, delta > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N -> forall v : E,
        v ∈ psi '' sourceK gamma -> dist (A gamma b (B gamma a v)) v < delta := by
    intro delta hdelta
    exact comp_tendsto_id_on (E := E) (F := E) (U := U gamma) (V := V gamma)
      (K := psi '' sourceK gamma) (hVopen gamma) (B gamma) (Binf gamma)
      (A gamma) (Ainf gamma) (hB gamma) (hA gamma) (hBcont gamma)
      (hAcont gamma) (hid gamma) hKimg (hKU gamma) (hKV gamma) delta hdelta
  obtain ⟨N, hN⟩ :=
    chartPtsSrcK (I := I) (g := (X.obj (L.φ n)).metric)
      (p := center gamma) (S := S) (Ksrc := sourceK gamma)
      (hKsrc gamma) hSsub (hsrcK gamma)
      (fun a b v => A gamma b (B gamma a v)) (by simpa [psi] using hclose)
      eps heps
  refine ⟨N, fun a ha b hb x hx hmu => ?_⟩
  exact hN a ha b hb x ⟨hx, hmu⟩






omit [Module.Finite ℝ E] in
theorem hatSrcPtsCageComp
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        4 * L.lamInf (gamma : Nat) <
          expRadiusGp (I := I) (X.obj (L.φ n)).metric (center gamma))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
          U gamma)
    (hKV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        Binf gamma v ∈ V gamma) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall gamma : Fin (pb.A r), forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
              (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
              Set (X.obj (L.φ n)).M) ->
              dist x ((NormalCoordinates.normalChartAt (I := I)
                (X.obj (L.φ n)).metric (center gamma)).symm
                  (A gamma b (B gamma a ((NormalCoordinates.normalChartAt (I := I)
                    (X.obj (L.φ n)).metric (center gamma)) x)))) < eps := by
  let sourceK : Fin (pb.A r) -> Set (X.obj (L.φ n)).M :=
    fun gamma =>
      NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma
  exact
    NetLimitData.hatSrcPtsOfComp (I := I) (X := X) hd P L pb r n center sourceK
      U V B Binf A Ainf hconn
      (NetLimitData.hatCageCompact (I := I) (X := X) hd P L pb r n)
      (NetLimitData.hatCageSub (I := I) (X := X) hd P L pb r n)
      (fun gamma =>
        NetLimitData.hatCageSrcOfRad (I := I) (X := X) hd P L pb r n center gamma
          (hcenter gamma) (hR gamma))
      hVopen hB hA hBcont hAcont hid hKU hKV



omit [Module.Finite ℝ E] in
theorem hatPtsCasesComp
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall c : (X.obj (L.φ n)).M,
        seqCenter hd D P (L.φ n) (gamma : Nat) = some c ->
          c = center gamma ∧
            4 * L.lamInf (gamma : Nat) <
              expRadiusGp (I := I) (X.obj (L.φ n)).metric c)
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
          U gamma)
    (hKV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        Binf gamma v ∈ V gamma) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall gamma : Fin (pb.A r), forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
              (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
              Set (X.obj (L.φ n)).M) ->
              dist x ((NormalCoordinates.normalChartAt (I := I)
                (X.obj (L.φ n)).metric (center gamma)).symm
                  (A gamma b (B gamma a ((NormalCoordinates.normalChartAt (I := I)
                    (X.obj (L.φ n)).metric (center gamma)) x)))) < eps := by
  let sourceK : Fin (pb.A r) -> Set (X.obj (L.φ n)).M := fun gamma =>
    NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma
  exact
    NetLimitData.hatSrcPtsOfComp (I := I) (X := X) hd P L pb r n center sourceK
      U V B Binf A Ainf hconn
      (NetLimitData.hatCageCompact (I := I) (X := X) hd P L pb r n)
      (NetLimitData.hatCageSub (I := I) (X := X) hd P L pb r n)
      (NetLimitData.hatCageSrcCases (I := I) (X := X) hd P L pb r n center hR)
      hVopen hB hA hBcont hAcont hid hKU hKV





omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem hatChartPtsOfComp
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (coordK : Fin (pb.A r) -> Set E)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hK :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      forall gamma : Fin (pb.A r), IsCompact (coordK gamma))
    (hKtarget :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), coordK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).target)
    (hsource :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M) ->
        x ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source)
    (hcoord :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M) ->
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) x ∈ coordK gamma)
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU : forall gamma : Fin (pb.A r), coordK gamma ⊆ U gamma)
    (hKV : forall gamma : Fin (pb.A r), forall v : E,
      v ∈ coordK gamma -> Binf gamma v ∈ V gamma) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall gamma : Fin (pb.A r), forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
              (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
              Set (X.obj (L.φ n)).M) ->
              dist x ((NormalCoordinates.normalChartAt (I := I)
                (X.obj (L.φ n)).metric (center gamma)).symm
                  (A gamma b (B gamma a ((NormalCoordinates.normalChartAt (I := I)
                    (X.obj (L.φ n)).metric (center gamma)) x)))) < eps := by
  exact
    NetLimitData.hatChartPts (I := I) (X := X) hd P L pb r n center coordK
      (fun gamma a b v => A gamma b (B gamma a v)) hconn hK hKtarget hsource
      hcoord
      (fun gamma δ hδ =>
        comp_tendsto_id_on (E := E) (F := E) (U := U gamma) (V := V gamma)
          (K := coordK gamma) (hVopen gamma) (B gamma) (Binf gamma) (A gamma)
          (Ainf gamma) (hB gamma) (hA gamma) (hBcont gamma) (hAcont gamma)
          (hid gamma) (hK gamma) (hKU gamma) (hKV gamma) δ hδ)



noncomputable def decodedCompPts (g : SmoothRiemannianMetric I M)
    {ι : Type*} (center : ι -> M)
    (B : ι -> Nat -> E -> E) (A : ι -> Nat -> E -> E) :
    Nat -> Nat -> M -> ι -> M :=
  fun a b x gamma =>
    (NormalCoordinates.normalChartAt (I := I) g (center gamma)).symm
      (A gamma b
        (B gamma a ((NormalCoordinates.normalChartAt (I := I) g (center gamma)) x)))







omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatPOUDataTwo
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (_a _b : Nat) {x : (X.obj (L.φ n)).M}
    (hx : x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
    ((forall gamma : Fin (pb.A r), 0 <= rho gamma x) ∧
      (exists gamma : Fin (pb.A r), 0 < rho gamma x) ∧
        Finset.univ.sum (fun gamma : Fin (pb.A r) => rho gamma x) = 1) ∧
      forall gamma : Fin (pb.A r), rho gamma x ≠ 0 ->
        x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M) := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  change x ∈ Metric.closedBall (X.obj (L.φ n)).basepoint r at hx
  simpa [Finset.sum_apply] using
    (NetLimitData.hatPOU_active_data (I := I) (X := X) (hd := hd) (D := D) (P := P) (L := L) (pb := pb) (r := r) (k := n) (ρ := rho) (hρ := hrho) (x := x) hx)



omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem exists_hat_radius
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (ptsSeq : Nat → Nat → (X.obj (L.φ n)).M → Fin (pb.A r) →
      (X.obj (L.φ n)).M)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hpts :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      ∀ gamma : Fin (pb.A r), ∀ eps : Real, eps > 0 → ∃ N : Nat,
        ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n →
            x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
              (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
              Set (X.obj (L.φ n)).M) →
              dist x (ptsSeq a b x gamma) < eps) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    ∃ radSeq : Nat → Nat → (X.obj (L.φ n)).M → Real,
      (∀ a b : Nat, ∀ x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n →
          0 < radSeq a b x) ∧
      (∀ a b : Nat, ∀ x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n →
          ∀ gamma : Fin (pb.A r), rho gamma x ≠ 0 →
            dist x (ptsSeq a b x gamma) < radSeq a b x) ∧
      ∀ eps : Real, eps > 0 → ∃ N : Nat,
        ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n →
            radSeq a b x < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  obtain ⟨radSeq, hpos, hactive, htail⟩ :=
    centerAverage.exists_active_radius
      (X := (X.obj (L.φ n)).M) (ι := Fin (pb.A r))
      (s := NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
      (target := fun x : (X.obj (L.φ n)).M => x)
      (μSeq := fun _a _b x gamma => rho gamma x) (ptsSeq := ptsSeq) (by
        intro gamma eps heps
        obtain ⟨N, hN⟩ := hpts gamma eps heps
        refine ⟨N, fun a ha b hb x hx hne => ?_⟩
        exact hN a ha b hb x hx
          ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd) (D := D)
            (P := P) (L := L) (pb := pb) (r := r) (n := n) (rho := rho)
            (hrho := hrho) a b hx).2 gamma hne))
  exact ⟨radSeq, fun a b x _hx => hpos a b x, hactive, htail⟩







omit [Module.Finite ℝ E] in
omit [CompleteSpace E] in
theorem unifHatIdOn
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (ptsSeq :
      Nat -> Nat -> (X.obj (L.φ n)).M -> Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (pSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hcomplete :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace (X.obj (L.φ n)).M :=
        EMetricSpace.ofRiemannianMetric I (X.obj (L.φ n)).M
      CompleteSpace (X.obj (L.φ n)).M)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        0 < radSeq a b x)
    (hqstar :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          dist (pSeq a b x) x < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma x ≠ 0 ->
            dist (pSeq a b x) (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
              (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y) x)
            join (pSeq a b x) (radSeq a b x))
    (hpts :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall gamma : Fin (pb.A r), forall eps : Real, eps > 0 -> exists N : Nat,
        forall a : Nat, a >= N -> forall b : Nat, b >= N ->
          forall x : (X.obj (L.φ n)).M,
            x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
              x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
                (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
                Set (X.obj (L.φ n)).M) ->
                dist x (ptsSeq a b x gamma) < eps) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                (fun y : (X.obj (L.φ n)).M =>
                  fun gamma : Fin (pb.A r) => rho gamma y)
                (centerAverage.activeFill
                  (fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y))
                join (pSeq a b) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFill (I := I)
                  (g := (X.obj (L.φ n)).metric)
                  (μ := fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (pts := ptsSeq a b) (join := join) (p := pSeq a b)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy) (hqstar a b y hy)
                  (hactive_mem a b y hy)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.1)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  exact centerAverage.unifTwoIdDataOn (I := I)
    (g := (X.obj (L.φ n)).metric) (join := join)
    (s := NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
    (USeq := fun _ _ gamma =>
      (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
        Set (X.obj (L.φ n)).M))
    (μSeq := fun _ _ y gamma => rho gamma y) (ptsSeq := ptsSeq)
    (pSeq := pSeq) (rSeq := radSeq) hcomplete hrad hqstar hactive_mem
    (fun a b y hy =>
      NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (n := n) (rho := rho)
        (hrho := hrho) a b hy)
    hstrict hpts




omit [Module.Finite ℝ E] in
omit [CompleteSpace E] in
theorem unifHatIdSelfOn
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (ptsSeq :
      Nat -> Nat -> (X.obj (L.φ n)).M -> Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hcomplete :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace (X.obj (L.φ n)).M :=
        EMetricSpace.ofRiemannianMetric I (X.obj (L.φ n)).M
      CompleteSpace (X.obj (L.φ n)).M)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        0 < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma x ≠ 0 ->
            dist x (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
              (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y) x)
            join x (radSeq a b x))
    (hpts :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall gamma : Fin (pb.A r), forall eps : Real, eps > 0 -> exists N : Nat,
        forall a : Nat, a >= N -> forall b : Nat, b >= N ->
          forall x : (X.obj (L.φ n)).M,
            x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
              x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
                (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
                Set (X.obj (L.φ n)).M) ->
                dist x (ptsSeq a b x gamma) < eps) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                (fun y : (X.obj (L.φ n)).M =>
                  fun gamma : Fin (pb.A r) => rho gamma y)
                (centerAverage.activeFill
                  (fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y))
                join (fun y : (X.obj (L.φ n)).M => y) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFillSelf (I := I)
                  (g := (X.obj (L.φ n)).metric)
                  (μ := fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (pts := ptsSeq a b) (join := join)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy)
                  (hactive_mem a b y hy)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.1)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  exact centerAverage.unifTwoIdDataSelf (I := I)
    (g := (X.obj (L.φ n)).metric) (join := join)
    (s := NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
    (USeq := fun _ _ gamma =>
      (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
        Set (X.obj (L.φ n)).M))
    (μSeq := fun _ _ y gamma => rho gamma y) (ptsSeq := ptsSeq)
    (rSeq := radSeq) hcomplete hrad hactive_mem
    (fun a b y hy =>
      NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (n := n) (rho := rho)
        (hrho := hrho) a b hy)
    hstrict hpts





omit [Module.Finite ℝ E] in
theorem unifHatIdOfComp
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (pSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (coordK : Fin (pb.A r) -> Set E)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        0 < radSeq a b x)
    (hqstar :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          dist (pSeq a b x) x < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      let ptsSeq :=
        decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma x ≠ 0 ->
            dist (pSeq a b x) (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq :=
        decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
              (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y) x)
            join (pSeq a b x) (radSeq a b x))
    (hK :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      forall gamma : Fin (pb.A r), IsCompact (coordK gamma))
    (hKtarget :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), coordK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).target)
    (hsource :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M) ->
        x ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source)
    (hcoord :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M) ->
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) x ∈ coordK gamma)
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU : forall gamma : Fin (pb.A r), coordK gamma ⊆ U gamma)
    (hKV : forall gamma : Fin (pb.A r), forall v : E,
      v ∈ coordK gamma -> Binf gamma v ∈ V gamma) :
    let hcomplete :=
      NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    let ptsSeq :=
      decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                (fun y : (X.obj (L.φ n)).M =>
                  fun gamma : Fin (pb.A r) => rho gamma y)
                (centerAverage.activeFill
                  (fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y))
                join (pSeq a b) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFill (I := I)
                  (g := (X.obj (L.φ n)).metric)
                  (μ := fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (pts := ptsSeq a b) (join := join) (p := pSeq a b)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy) (hqstar a b y hy)
                  (hactive_mem a b y hy)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.1)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  let hcomplete :=
    NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
  let ptsSeq :=
    decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
  exact
    NetLimitData.unifHatIdOn (I := I) (X := X) hd P L pb r n rho hrho join
      ptsSeq pSeq radSeq hconn hcomplete hrad hqstar
      (by simpa [ptsSeq] using hactive_mem)
      (by simpa [ptsSeq] using hstrict)
      (by
        simpa [ptsSeq, decodedCompPts] using
          NetLimitData.hatChartPtsOfComp (I := I) (X := X) hd P L pb r n center
            coordK U V B Binf A Ainf hconn hK hKtarget hsource hcoord hVopen
            hB hA hBcont hAcont hid hKU hKV)




omit [Module.Finite ℝ E] in
theorem unifHatIdSelfComp
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (coordK : Fin (pb.A r) -> Set E)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        0 < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      let ptsSeq :=
        decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma x ≠ 0 ->
            dist x (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq :=
        decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
              (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y) x)
            join x (radSeq a b x))
    (hK :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      forall gamma : Fin (pb.A r), IsCompact (coordK gamma))
    (hKtarget :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), coordK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).target)
    (hsource :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M) ->
        x ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source)
    (hcoord :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M) ->
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) x ∈ coordK gamma)
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU : forall gamma : Fin (pb.A r), coordK gamma ⊆ U gamma)
    (hKV : forall gamma : Fin (pb.A r), forall v : E,
      v ∈ coordK gamma -> Binf gamma v ∈ V gamma) :
    let hcomplete :=
      NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    let ptsSeq :=
      decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                (fun y : (X.obj (L.φ n)).M =>
                  fun gamma : Fin (pb.A r) => rho gamma y)
                (centerAverage.activeFill
                  (fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y))
                join (fun y : (X.obj (L.φ n)).M => y) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFillSelf (I := I)
                  (g := (X.obj (L.φ n)).metric)
                  (μ := fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (pts := ptsSeq a b) (join := join)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy)
                  (hactive_mem a b y hy)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.1)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  let hcomplete :=
    NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
  let ptsSeq :=
    decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
  exact
    NetLimitData.unifHatIdSelfOn (I := I) (X := X) hd P L pb r n rho hrho join
      ptsSeq radSeq hconn hcomplete hrad
      (by simpa [ptsSeq] using hactive_mem)
      (by simpa [ptsSeq] using hstrict)
      (by
        simpa [ptsSeq, decodedCompPts] using
          NetLimitData.hatChartPtsOfComp (I := I) (X := X) hd P L pb r n center
            coordK U V B Binf A Ainf hconn hK hKtarget hsource hcoord hVopen
            hB hA hBcont hAcont hid hKU hKV)




omit [Module.Finite ℝ E] in
theorem unifHatSrcOfComp
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (pSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (sourceK : Fin (pb.A r) -> Set (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        0 < radSeq a b x)
    (hqstar :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          dist (pSeq a b x) x < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      let ptsSeq :=
        decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma x ≠ 0 ->
            dist (pSeq a b x) (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq :=
        decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
              (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y) x)
            join (pSeq a b x) (radSeq a b x))
    (hKsrc :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      forall gamma : Fin (pb.A r), IsCompact (sourceK gamma))
    (hSsub :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      forall gamma : Fin (pb.A r),
        (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
          (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
            (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
            Set (X.obj (L.φ n)).M)) ⊆ sourceK gamma)
    (hsrcK :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), sourceK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source)
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma ⊆ U gamma)
    (hKV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma -> Binf gamma v ∈ V gamma) :
    let hcomplete :=
      NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    let ptsSeq :=
      decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                (fun y : (X.obj (L.φ n)).M =>
                  fun gamma : Fin (pb.A r) => rho gamma y)
                (centerAverage.activeFill
                  (fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y))
                join (pSeq a b) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFill (I := I)
                  (g := (X.obj (L.φ n)).metric)
                  (μ := fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (pts := ptsSeq a b) (join := join) (p := pSeq a b)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy) (hqstar a b y hy)
                  (hactive_mem a b y hy)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.1)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  let hcomplete :=
    NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
  let ptsSeq :=
    decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
  exact
    NetLimitData.unifHatIdOn (I := I) (X := X) hd P L pb r n rho hrho join
      ptsSeq pSeq radSeq hconn hcomplete hrad hqstar
      (by simpa [ptsSeq] using hactive_mem)
      (by simpa [ptsSeq] using hstrict)
      (by
        simpa [ptsSeq, decodedCompPts] using
          NetLimitData.hatSrcPtsOfComp (I := I) (X := X) hd P L pb r n center
            sourceK U V B Binf A Ainf hconn hKsrc hSsub hsrcK hVopen hB hA
            hBcont hAcont hid hKU hKV)



omit [Module.Finite ℝ E] in
theorem unifHatSrcSelfComp
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (sourceK : Fin (pb.A r) -> Set (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        0 < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      let ptsSeq :=
        decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma x ≠ 0 ->
            dist x (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq :=
        decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
              (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y) x)
            join x (radSeq a b x))
    (hKsrc :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      forall gamma : Fin (pb.A r), IsCompact (sourceK gamma))
    (hSsub :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      forall gamma : Fin (pb.A r),
        (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
          (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
            (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
            Set (X.obj (L.φ n)).M)) ⊆ sourceK gamma)
    (hsrcK :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), sourceK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source)
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma ⊆ U gamma)
    (hKV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma -> Binf gamma v ∈ V gamma) :
    let hcomplete :=
      NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    let ptsSeq :=
      decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                (fun y : (X.obj (L.φ n)).M =>
                  fun gamma : Fin (pb.A r) => rho gamma y)
                (centerAverage.activeFill
                  (fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y))
                join (fun y : (X.obj (L.φ n)).M => y) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFillSelf (I := I)
                  (g := (X.obj (L.φ n)).metric)
                  (μ := fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (pts := ptsSeq a b) (join := join)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy)
                  (hactive_mem a b y hy)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.1)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  let hcomplete :=
    NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
  let ptsSeq :=
    decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
  exact
    NetLimitData.unifHatIdSelfOn (I := I) (X := X) hd P L pb r n rho hrho join
      ptsSeq radSeq hconn hcomplete hrad
      (by simpa [ptsSeq] using hactive_mem)
      (by simpa [ptsSeq] using hstrict)
      (by
        simpa [ptsSeq, decodedCompPts] using
          NetLimitData.hatSrcPtsOfComp (I := I) (X := X) hd P L pb r n center
            sourceK U V B Binf A Ainf hconn hKsrc hSsub hsrcK hVopen hB hA
            hBcont hAcont hid hKU hKV)






omit [Module.Finite ℝ E] in
theorem unifHatCageComp
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (pSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        4 * L.lamInf (gamma : Nat) <
          expRadiusGp (I := I) (X.obj (L.φ n)).metric (center gamma))
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        0 < radSeq a b x)
    (hqstar :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          dist (pSeq a b x) x < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      let ptsSeq :=
        decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma x ≠ 0 ->
            dist (pSeq a b x) (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq :=
        decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
              (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y) x)
            join (pSeq a b x) (radSeq a b x))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
          U gamma)
    (hKV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        Binf gamma v ∈ V gamma) :
    let hcomplete :=
      NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    let ptsSeq :=
      decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                (fun y : (X.obj (L.φ n)).M =>
                  fun gamma : Fin (pb.A r) => rho gamma y)
                (centerAverage.activeFill
                  (fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y))
                join (pSeq a b) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFill (I := I)
                  (g := (X.obj (L.φ n)).metric)
                  (μ := fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (pts := ptsSeq a b) (join := join) (p := pSeq a b)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy) (hqstar a b y hy)
                  (hactive_mem a b y hy)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.1)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  let sourceK : Fin (pb.A r) -> Set (X.obj (L.φ n)).M :=
    fun gamma => NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma
  exact
    NetLimitData.unifHatSrcOfComp (I := I) (X := X) hd P L pb r n rho hrho join
      pSeq radSeq center sourceK U V B Binf A Ainf hconn hX hrad hqstar
      (by simpa [sourceK] using hactive_mem)
      (by simpa [sourceK] using hstrict)
      (by simpa [sourceK] using
        NetLimitData.hatCageCompact (I := I) (X := X) hd P L pb r n)
      (by simpa [sourceK] using
        NetLimitData.hatCageSub (I := I) (X := X) hd P L pb r n)
      (by
        intro gamma
        simpa [sourceK] using
          NetLimitData.hatCageSrcOfRad (I := I) (X := X) hd P L pb r n center
            gamma (hcenter gamma) (hR gamma))
      hVopen hB hA hBcont hAcont hid
      (by simpa [sourceK] using hKU)
      (by simpa [sourceK] using hKV)





omit [Module.Finite ℝ E] in
theorem unifHatCageSrc
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (mu : (X.obj (L.φ n)).M -> Fin (pb.A r) -> Real)
    (hmu :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      centerAverage.WeightDataOn
        (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
        (fun gamma : Fin (pb.A r) =>
          (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
            (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
            Set (X.obj (L.φ n)).M)) mu)
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hsrcK :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
          (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
            (center gamma)).source)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        0 < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      let ptsSeq :=
        decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), mu x gamma ≠ 0 ->
            dist x (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq :=
        decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill mu (ptsSeq a b)
              (fun y : (X.obj (L.φ n)).M => y) x)
            join x (radSeq a b x))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
          U gamma)
    (hKV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        Binf gamma v ∈ V gamma) :
    let hcomplete :=
      NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    let ptsSeq :=
      decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                mu
                (centerAverage.activeFill mu (ptsSeq a b)
                  (fun y : (X.obj (L.φ n)).M => y))
                join (fun y : (X.obj (L.φ n)).M => y) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFillSelf (I := I)
                  (g := (X.obj (L.φ n)).metric) (μ := mu)
                  (pts := ptsSeq a b) (join := join)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy)
                  (hactive_mem a b y hy)
                  ((hmu.data hy).1.1) ((hmu.data hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  let hcomplete :=
    NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
  let ptsSeq :=
    decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
  let sourceK : Fin (pb.A r) -> Set (X.obj (L.φ n)).M :=
    fun gamma => NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma
  exact centerAverage.unifTwoIdDataSelf (I := I)
    (g := (X.obj (L.φ n)).metric) (join := join)
    (s := NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
    (USeq := fun _ _ gamma =>
      (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
        Set (X.obj (L.φ n)).M))
    (μSeq := fun _ _ => mu) (ptsSeq := ptsSeq) (rSeq := radSeq)
    hcomplete hrad (by simpa [ptsSeq] using hactive_mem)
    (fun _ _ y hy => hmu.data hy)
    (by simpa [ptsSeq] using hstrict)
    (by
      simpa [ptsSeq, decodedCompPts] using
        NetLimitData.hatSrcPtsOfComp (I := I) (X := X) hd P L pb r n center
          sourceK U V B Binf A Ainf hconn
          (by simpa [sourceK] using
            NetLimitData.hatCageCompact (I := I) (X := X) hd P L pb r n)
          (by simpa [sourceK] using
            NetLimitData.hatCageSub (I := I) (X := X) hd P L pb r n)
          (by simpa [sourceK] using hsrcK)
          hVopen hB hA hBcont hAcont hid
          (by simpa [sourceK] using hKU)
          (by simpa [sourceK] using hKV))



omit [Module.Finite ℝ E] in
theorem unifHatCageSelfComp
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        4 * L.lamInf (gamma : Nat) <
          expRadiusGp (I := I) (X.obj (L.φ n)).metric (center gamma))
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        0 < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      let ptsSeq :=
        decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma x ≠ 0 ->
            dist x (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq :=
        decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
              (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y) x)
            join x (radSeq a b x))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
          U gamma)
    (hKV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        Binf gamma v ∈ V gamma) :
    let hcomplete :=
      NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    let ptsSeq :=
      decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                (fun y : (X.obj (L.φ n)).M =>
                  fun gamma : Fin (pb.A r) => rho gamma y)
                (centerAverage.activeFill
                  (fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y))
                join (fun y : (X.obj (L.φ n)).M => y) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFillSelf (I := I)
                  (g := (X.obj (L.φ n)).metric)
                  (μ := fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (pts := ptsSeq a b) (join := join)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy)
                  (hactive_mem a b y hy)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.1)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  let sourceK : Fin (pb.A r) -> Set (X.obj (L.φ n)).M :=
    fun gamma => NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma
  exact
    NetLimitData.unifHatSrcSelfComp (I := I) (X := X) hd P L pb r n rho hrho join
      radSeq center sourceK U V B Binf A Ainf hconn hX hrad
      (by simpa [sourceK] using hactive_mem)
      (by simpa [sourceK] using hstrict)
      (by simpa [sourceK] using
        NetLimitData.hatCageCompact (I := I) (X := X) hd P L pb r n)
      (by simpa [sourceK] using
        NetLimitData.hatCageSub (I := I) (X := X) hd P L pb r n)
      (by
        intro gamma
        simpa [sourceK] using
          NetLimitData.hatCageSrcOfRad (I := I) (X := X) hd P L pb r n center
            gamma (hcenter gamma) (hR gamma))
      hVopen hB hA hBcont hAcont hid
      (by simpa [sourceK] using hKU)
      (by simpa [sourceK] using hKV)



omit [Module.Finite ℝ E] in
theorem unifHatSuppData
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (mu : (X.obj (L.φ n)).M -> Fin (pb.A r) -> Real)
    (hmu :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      centerAverage.WeightDataOn
        (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
        (fun _ : Fin (pb.A r) => Set.univ) mu)
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (sourceK : Fin (pb.A r) -> Set (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hKsrc :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      forall gamma : Fin (pb.A r), IsCompact (sourceK gamma))
    (hSupp :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      forall gamma : Fin (pb.A r), forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        mu x gamma ≠ 0 -> x ∈ sourceK gamma)
    (hsrcK :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), sourceK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        0 < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      let ptsSeq := decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), mu x gamma ≠ 0 ->
            dist x (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq := decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill mu (ptsSeq a b)
              (fun y : (X.obj (L.φ n)).M => y) x)
            join x (radSeq a b x))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma ⊆ U gamma)
    (hKV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma -> Binf gamma v ∈ V gamma) :
    let hcomplete :=
      NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    let ptsSeq := decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                mu
                (centerAverage.activeFill mu (ptsSeq a b)
                  (fun y : (X.obj (L.φ n)).M => y))
                join (fun y : (X.obj (L.φ n)).M => y) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFillSelf (I := I)
                  (g := (X.obj (L.φ n)).metric) (μ := mu)
                  (pts := ptsSeq a b) (join := join)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy)
                  (hactive_mem a b y hy)
                  ((hmu.data hy).1.1) ((hmu.data hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  let hcomplete :=
    NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
  let ptsSeq := decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
  exact centerAverage.unifTwoIdDataSelf (I := I)
    (g := (X.obj (L.φ n)).metric) (join := join)
    (s := NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
    (USeq := fun _ _ gamma => {x | mu x gamma ≠ 0})
    (μSeq := fun _ _ => mu) (ptsSeq := ptsSeq) (rSeq := radSeq)
    hcomplete hrad (by simpa [ptsSeq] using hactive_mem)
    (fun _ _ y hy => ⟨(hmu.data hy).1, fun _ hne => hne⟩)
    (by simpa [ptsSeq] using hstrict)
    (by
      simpa [ptsSeq, decodedCompPts] using
        NetLimitData.hatSuppPtsOfComp (I := I) (X := X) hd P L pb r n mu center
          sourceK U V B Binf A Ainf hconn hKsrc hSupp hsrcK hVopen hB hA
          hBcont hAcont hid hKU hKV)





omit [Module.Finite ℝ E] in
theorem unifHatCageData
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (mu : (X.obj (L.φ n)).M -> Fin (pb.A r) -> Real)
    (hmu :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      centerAverage.WeightDataOn
        (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
        (fun gamma : Fin (pb.A r) =>
          (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
            (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
            Set (X.obj (L.φ n)).M)) mu)
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        4 * L.lamInf (gamma : Nat) <
          expRadiusGp (I := I) (X.obj (L.φ n)).metric (center gamma))
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        0 < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      let ptsSeq :=
        decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), mu x gamma ≠ 0 ->
            dist x (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq :=
        decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill mu (ptsSeq a b)
              (fun y : (X.obj (L.φ n)).M => y) x)
            join x (radSeq a b x))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
          U gamma)
    (hKV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        Binf gamma v ∈ V gamma) :
    let hcomplete :=
      NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    let ptsSeq :=
      decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                mu
                (centerAverage.activeFill mu (ptsSeq a b)
                  (fun y : (X.obj (L.φ n)).M => y))
                join (fun y : (X.obj (L.φ n)).M => y) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFillSelf (I := I)
                  (g := (X.obj (L.φ n)).metric) (μ := mu)
                  (pts := ptsSeq a b) (join := join)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy)
                  (hactive_mem a b y hy)
                  ((hmu.data hy).1.1) ((hmu.data hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  let hcomplete :=
    NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
  let ptsSeq :=
    decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
  let sourceK : Fin (pb.A r) -> Set (X.obj (L.φ n)).M :=
    fun gamma => NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma
  exact centerAverage.unifTwoIdDataSelf (I := I)
    (g := (X.obj (L.φ n)).metric) (join := join)
    (s := NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
    (USeq := fun _ _ gamma =>
      (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
        Set (X.obj (L.φ n)).M))
    (μSeq := fun _ _ => mu) (ptsSeq := ptsSeq) (rSeq := radSeq)
    hcomplete hrad (by simpa [ptsSeq] using hactive_mem)
    (fun _ _ y hy => hmu.data hy)
    (by simpa [ptsSeq] using hstrict)
    (by
      simpa [ptsSeq, decodedCompPts] using
        NetLimitData.hatSrcPtsOfComp (I := I) (X := X) hd P L pb r n center
          sourceK U V B Binf A Ainf hconn
          (by simpa [sourceK] using
            NetLimitData.hatCageCompact (I := I) (X := X) hd P L pb r n)
          (by simpa [sourceK] using
            NetLimitData.hatCageSub (I := I) (X := X) hd P L pb r n)
          (by
            intro gamma
            simpa [sourceK] using
              NetLimitData.hatCageSrcOfRad (I := I) (X := X) hd P L pb r n
                center gamma (hcenter gamma) (hR gamma))
          hVopen hB hA hBcont hAcont hid
          (by simpa [sourceK] using hKU)
          (by simpa [sourceK] using hKV))

end NetLimitData

end HCGCompactness
end DifferentialGeometry
