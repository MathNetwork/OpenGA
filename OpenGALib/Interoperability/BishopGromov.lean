import DifferentialGeometry.Geometry.Comparison.Volume.SegmentBallEuclideanUpper
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Topology.FiberBundleT2
import OpenGALib.Interoperability.DifferentialGeometry

/-!
# Bishop-Gromov comparison from DifferentialGeometry

The distance, volume measure and Ricci tensor below all come from the same
explicit OpenGA metric. The comparison proof is imported from
`DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segBall_vol_rel`.

Upstream: qinz1yang/differential-geometry, Apache-2.0, v0.1.2,
commit 1b535dd102b94cc42b107cca27059687888f08b3.
Copyright 2026 The DifferentialGeometry contributors.

The scope is a complete, connected smooth manifold without boundary with a
global Ricci lower bound `(n - 1) * (-q^2)`, where `q >= 0`. Arbitrary positive
radii are allowed. Positive model curvature and a curvature bound assumed
only on the outer ball are separate extensions.

Reference: Kleiner-Lott, *Notes on Perelman's Papers*, arXiv:math/0605667v5,
Appendix G, equation (G.1), pp. 211-212, in the stated complete-manifold scope.
-/

noncomputable section

set_option autoImplicit false

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace Riemannian.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Math.** The open ball for the distance induced by the specified metric. -/
def geodesicBall (g : RiemannianMetric I M) (p : M) (r : ℝ) : Set M :=
  {x | riemannianEDistOf (I := I) g p x < ENNReal.ofReal r}

/-- **Math.** The Riemannian volume of a geodesic ball for the same metric. -/
def ballVolume (g : RiemannianMetric I M) (p : M) (r : ℝ) : ℝ≥0∞ :=
  g.volumeMeasure (g.geodesicBall p r)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Math.** Every positive-radius ball has positive volume, without completeness
or a curvature assumption. -/
theorem ballVolume_pos (g : RiemannianMetric I M) (p : M) {r : ℝ} (hr : 0 < r) :
    0 < g.ballVolume p r := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : g.volumeMeasure.IsOpenPosMeasure := g.volumeMeasure_isOpenPosMeasure
  change 0 < g.volumeMeasure {x | edist p x < ENNReal.ofReal r}
  simpa only [Metric.eball, edist_comm] using
    Metric.measure_eball_pos g.volumeMeasure p (ENNReal.ofReal_ne_zero_iff.mpr hr)

variable [I.Boundaryless] [ConnectedSpace M] [NeZero (Module.finrank ℝ E)]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Math.** Complete manifolds have finite volume on each finite-radius ball. -/
theorem ballVolume_lt_top (g : RiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) (p : M) (r : ℝ) :
    g.ballVolume p r < ⊤ := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hcomplete.complete
  have hnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  exact segBall_vol_fin (I := I) g hnorm p

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Math.** Bishop-Gromov comparison in cross-multiplied form for model curvature
`-q^2`, using the upstream geometric proof with a single explicit metric. -/
theorem ballVolume_mul_modelVolume_le (g : RiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) (p : M)
    {q r R : ℝ} (hq : 0 ≤ q) (hr : 0 < r) (hrR : r ≤ R)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    g.ballVolume p R * ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) r) ≤
      g.ballVolume p r * ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) R) := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hcomplete.complete
  have hnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  simpa only [ballVolume, geodesicBall, riemannianEDistOf, volumeMeasure,
    mul_comm] using segBall_vol_rel (I := I) g hnorm p hq hr hrR hRic

/-- **Math.** Normalized ball volume is nonincreasing for model curvature `-q^2`. -/
theorem antitoneOn_ballVolume_div_modelVolume (g : RiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) (p : M)
    {q : ℝ} (hq : 0 ≤ q)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    AntitoneOn (fun r => g.ballVolume p r /
      ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) r)) (Ioi 0) := by
  intro r hr R hR hrR
  dsimp only
  have hmr : ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) r) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (hypRadVol_pos hq hr)
  have hmR : ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) R) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (hypRadVol_pos hq hR)
  rw [ENNReal.div_le_iff hmR ENNReal.ofReal_ne_top,
    div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inl hmr) (Or.inl ENNReal.ofReal_ne_top)]
  exact ballVolume_mul_modelVolume_le g hcomplete p hq hr hrR hRic

/-- **Math.** The ratio of concentric ball volumes is bounded by the model-volume
ratio. Positivity and finiteness of the smaller ball justify the division. -/
theorem ballVolume_ratio_le (g : RiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) (p : M)
    {q r R : ℝ} (hq : 0 ≤ q) (hr : 0 < r) (hrR : r ≤ R)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    g.ballVolume p R / g.ballVolume p r ≤
      ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) R) /
        ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) r) := by
  have hvol := (ballVolume_pos g p hr).ne'
  have hvolfin := (ballVolume_lt_top g hcomplete p r).ne
  have hmodel : ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) r) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (hypRadVol_pos hq hr)
  rw [ENNReal.div_le_iff hvol hvolfin,
    div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inl hmodel) (Or.inl ENNReal.ofReal_ne_top)]
  simpa only [mul_comm] using
    ballVolume_mul_modelVolume_le g hcomplete p hq hr hrR hRic

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Math.** Nonnegative Ricci curvature bounds the volume ratio by the Euclidean
power ratio. This reuses the upstream `segBall_vol_pow` specialization. -/
theorem ballVolume_mul_pow_le (g : RiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) (p : M)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g 0) :
    g.ballVolume p R * ENNReal.ofReal (r ^ Module.finrank ℝ E) ≤
      g.ballVolume p r * ENNReal.ofReal (R ^ Module.finrank ℝ E) := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hcomplete.complete
  have hnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  simpa only [ballVolume, geodesicBall, riemannianEDistOf, volumeMeasure,
    mul_comm] using segBall_vol_pow (I := I) g hnorm p hr hrR hRic

/-- **Math.** On a complete manifold with nonnegative Ricci curvature,
`vol(B(p,r)) / r^n` is nonincreasing for positive radii. -/
theorem antitoneOn_ballVolume_div_pow (g : RiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) (p : M)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g 0) :
    AntitoneOn (fun r => g.ballVolume p r /
      ENNReal.ofReal (r ^ Module.finrank ℝ E)) (Ioi 0) := by
  intro r hr R hR hrR
  dsimp only
  have hmr : ENNReal.ofReal (r ^ Module.finrank ℝ E) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hr _)
  have hmR : ENNReal.ofReal (R ^ Module.finrank ℝ E) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hR _)
  rw [ENNReal.div_le_iff hmR ENNReal.ofReal_ne_top,
    div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inl hmr) (Or.inl ENNReal.ofReal_ne_top)]
  exact ballVolume_mul_pow_le g hcomplete p hr hrR hRic

/-- **Math.** Dilation by a factor `c >= 1` increases ball volume by at most `c^n`
when the Ricci curvature is nonnegative. -/
theorem ballVolume_mul_radius_le (g : RiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) (p : M)
    {r c : ℝ} (hr : 0 < r) (hc : 1 ≤ c)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g 0) :
    g.ballVolume p (c * r) ≤
      ENNReal.ofReal (c ^ Module.finrank ℝ E) * g.ballVolume p r := by
  have hrR : r ≤ c * r := le_mul_of_one_le_left hr.le hc
  have hcross := ballVolume_mul_pow_le g hcomplete p hr hrR hRic
  rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg (zero_le_one.trans hc) _)] at hcross
  apply (ENNReal.mul_le_mul_iff_left
    (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hr _)) ENNReal.ofReal_ne_top).mp
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hcross

/-- **Math.** Nonnegative Ricci curvature gives the volume doubling constant `2^n`. -/
theorem ballVolume_two_mul_le (g : RiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) (p : M)
    {r : ℝ} (hr : 0 < r)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g 0) :
    g.ballVolume p (2 * r) ≤ (2 : ℝ≥0∞) ^ Module.finrank ℝ E * g.ballVolume p r := by
  simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    using ballVolume_mul_radius_le g hcomplete p hr (by norm_num : (1 : ℝ) ≤ 2) hRic

end Riemannian.RiemannianMetric
