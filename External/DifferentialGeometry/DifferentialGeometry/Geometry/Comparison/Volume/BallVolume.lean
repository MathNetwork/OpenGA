import DifferentialGeometry.Geometry.Comparison.Volume.JacobianBounds
import DifferentialGeometry.Geometry.Comparison.GeodesicConvexity
import DifferentialGeometry.Geometry.Comparison.HopfRinowProper
import DifferentialGeometry.Geometry.Exponential.JacobiVariation
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic











noncomputable section

open scoped Topology Manifold ContDiff Bundle

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Integral.Measure
open Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section BallUpper

variable [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]






def Rm04GlobalBound (g : SmoothRiemannianMetric I M) (Rm : ℝ) : Prop :=
  ∀ q : M,
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
      (DifferentialGeometry.Integral.Connection.metricRm04At
        (I := I) (M := M) g q)) ≤ Rm




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
lemma modelHaar_ball {R : ℝ} (hR : 0 < R) :
    (modelHaar (E := E)) (Metric.ball (0 : E) R) =
      ENNReal.ofReal (R ^ Module.finrank ℝ E) *
        (modelHaar (E := E)) (Metric.ball (0 : E) 1) := by
  simpa using
    (MeasureTheory.Measure.addHaar_ball_of_pos
      (μ := modelHaar (E := E)) (x := (0 : E)) hR)



omit [T2Space M] [SigmaCompactSpace M] in
lemma ball_tgt_of_radius
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hR : R ≤ expMapC2Radius (I := I) g p) :
    Metric.ball (0 : E) R ⊆ (normalChartAt (I := I) g p).target := by
  intro w hw
  have hwR : ‖w‖ < R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  exact ball_subset_normalChartAt_target (I := I) g p (hwR.trans_le hR)








omit [NeZero (Module.finrank ℝ E)] in
theorem vol_ge_of_density
    (g : SmoothRiemannianMetric I M) (p : M)
    {A : Set M} (hA_meas : MeasurableSet A)
    (hA_source : A ⊆ (normalChartAt (I := I) g p).source)
    {c : ℝ}
    (hdens : ∀ w ∈ (normalChartAt (I := I) g p) '' A,
      c ≤ normalChartDensity (I := I) g p w) :
    ENNReal.ofReal c *
        (modelHaar (E := E)) ((normalChartAt (I := I) g p) '' A) ≤
      riemannianVolumeMeasure (I := I) (M := M) g A := by
  have hA_target : A ⊆ (expMapDiffeo (I := I) g p).target := by
    simpa [normalChartAt_source_eq (I := I) g p] using hA_source
  have hB_meas : MeasurableSet ((normalChartAt (I := I) g p) '' A) := by
    simpa [normalChartAt] using
      DifferentialGeometry.Integral.Measure.measurableSet_symm_image_param
        (I := I) (M := M)
        (Ψ := expMapDiffeo (I := I) g p) hA_meas hA_target
  rw [normalChart_volume_eq (I := I) (M := M) g p hA_meas hA_source]
  calc
    ENNReal.ofReal c *
        (modelHaar (E := E)) ((normalChartAt (I := I) g p) '' A)
        = ∫⁻ _ in (normalChartAt (I := I) g p) '' A,
            ENNReal.ofReal c ∂(modelHaar (E := E)) := by
      rw [MeasureTheory.setLIntegral_const]
    _ ≤ ∫⁻ w in (normalChartAt (I := I) g p) '' A,
          ENNReal.ofReal (normalChartDensity (I := I) g p w)
            ∂(modelHaar (E := E)) := by
      refine MeasureTheory.setLIntegral_mono' hB_meas ?_
      intro w hw
      exact ENNReal.ofReal_le_ofReal (hdens w hw)



omit [NeZero (Module.finrank ℝ E)] in
theorem vol_le_ball_of_density
    (g : SmoothRiemannianMetric I M) (p : M)
    {A : Set M} (hA_meas : MeasurableSet A)
    (hA_source : A ⊆ (normalChartAt (I := I) g p).source)
    {C R : ℝ}
    (hA_ball : (normalChartAt (I := I) g p) '' A ⊆ Metric.ball (0 : E) R)
    (hdens : ∀ w ∈ (normalChartAt (I := I) g p) '' A,
      normalChartDensity (I := I) g p w ≤ C) :
    riemannianVolumeMeasure (I := I) (M := M) g A ≤
      ENNReal.ofReal C * (modelHaar (E := E)) (Metric.ball (0 : E) R) := by
  have hA_target : A ⊆ (expMapDiffeo (I := I) g p).target := by
    simpa [normalChartAt_source_eq (I := I) g p] using hA_source
  have hB_meas : MeasurableSet ((normalChartAt (I := I) g p) '' A) := by
    simpa [normalChartAt] using
      DifferentialGeometry.Integral.Measure.measurableSet_symm_image_param
        (I := I) (M := M)
        (Ψ := expMapDiffeo (I := I) g p) hA_meas hA_target
  rw [normalChart_volume_eq (I := I) (M := M) g p hA_meas hA_source]
  calc
    ∫⁻ w in (normalChartAt (I := I) g p) '' A,
        ENNReal.ofReal (normalChartDensity (I := I) g p w)
          ∂(modelHaar (E := E))
        ≤ ∫⁻ _ in (normalChartAt (I := I) g p) '' A,
            ENNReal.ofReal C ∂(modelHaar (E := E)) := by
      refine MeasureTheory.setLIntegral_mono' hB_meas ?_
      intro w hw
      exact ENNReal.ofReal_le_ofReal (hdens w hw)
    _ = ENNReal.ofReal C *
        (modelHaar (E := E)) ((normalChartAt (I := I) g p) '' A) := by
      rw [MeasureTheory.setLIntegral_const]
    _ ≤ ENNReal.ofReal C * (modelHaar (E := E)) (Metric.ball (0 : E) R) := by
      exact mul_le_mul_right (MeasureTheory.measure_mono hA_ball) (ENNReal.ofReal C)



omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma coordBall_meas
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hball_target : Metric.ball (0 : E) R ⊆ (normalChartAt (I := I) g p).target) :
    MeasurableSet ((normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R) := by
  have hopen : IsOpen
      ((normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R) := by
    exact ((normalChartAt (I := I) g p).symm.toOpenPartialHomeomorph).isOpen_image_of_subset_source
      Metric.isOpen_ball hball_target
  exact hopen.measurableSet







theorem vol_le_ball_of_len
    (g : SmoothRiemannianMetric I M) (p : M)
    {A : Set M} (hA_meas : MeasurableSet A)
    (hA_source : A ⊆ (normalChartAt (I := I) g p).source)
    {B R : ℝ} (hB : 0 ≤ B)
    (hA_rad : (normalChartAt (I := I) g p) '' A ⊆
      Metric.ball (0 : E) (expMapC2Radius (I := I) g p))
    (hA_ball : (normalChartAt (I := I) g p) '' A ⊆ Metric.ball (0 : E) R)
    (hJ : ∀ w ∈ (normalChartAt (I := I) g p) '' A,
      ∀ i : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) :
    riemannianVolumeMeasure (I := I) (M := M) g A ≤
      ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
        (modelHaar (E := E)) (Metric.ball (0 : E) R) := by
  calc
    riemannianVolumeMeasure (I := I) (M := M) g A
        ≤ ENNReal.ofReal
            (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
              (B * B) ^ Module.finrank ℝ E)) *
          (modelHaar (E := E)) ((normalChartAt (I := I) g p) '' A) :=
      normalChart_volume_le_const_mul_of_radial_length_bound
        (I := I) g p hA_meas hA_source hB hA_rad hJ
    _ ≤ ENNReal.ofReal
            (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
              (B * B) ^ Module.finrank ℝ E)) *
          (modelHaar (E := E)) (Metric.ball (0 : E) R) :=
      by
        gcongr





theorem vol_le_ball_of_len_radius
    (g : SmoothRiemannianMetric I M) (p : M)
    {A : Set M} (hA_meas : MeasurableSet A)
    (hA_source : A ⊆ (normalChartAt (I := I) g p).source)
    {B R : ℝ} (hB : 0 ≤ B)
    (hR : R ≤ expMapC2Radius (I := I) g p)
    (hA_ball : (normalChartAt (I := I) g p) '' A ⊆ Metric.ball (0 : E) R)
    (hJ : ∀ w ∈ (normalChartAt (I := I) g p) '' A,
      ∀ i : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) :
    riemannianVolumeMeasure (I := I) (M := M) g A ≤
      ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
        (modelHaar (E := E)) (Metric.ball (0 : E) R) := by
  have hA_rad : (normalChartAt (I := I) g p) '' A ⊆
      Metric.ball (0 : E) (expMapC2Radius (I := I) g p) := by
    intro w hw
    exact Metric.mem_ball.mpr ((Metric.mem_ball.mp (hA_ball hw)).trans_le hR)
  exact vol_le_ball_of_len (I := I) g p hA_meas hA_source hB hA_rad hA_ball hJ







theorem coordBall_vol_le
    (g : SmoothRiemannianMetric I M) (p : M)
    {B R : ℝ} (hB : 0 ≤ B)
    (hR : R ≤ expMapC2Radius (I := I) g p)
    (hball_target : Metric.ball (0 : E) R ⊆ (normalChartAt (I := I) g p).target)
    (hA_meas : MeasurableSet
      ((normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R))
    (hJ : ∀ w ∈ Metric.ball (0 : E) R,
      ∀ i : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) :
    riemannianVolumeMeasure (I := I) (M := M) g
        ((normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R) ≤
      ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
        (modelHaar (E := E)) (Metric.ball (0 : E) R) := by
  let φ := normalChartAt (I := I) g p
  have hA_source : φ.symm '' Metric.ball (0 : E) R ⊆ φ.source := by
    intro q hq
    rcases hq with ⟨w, hw, rfl⟩
    exact φ.map_target (hball_target hw)
  have hA_ball : φ '' (φ.symm '' Metric.ball (0 : E) R) ⊆ Metric.ball (0 : E) R := by
    intro w hw
    rcases hw with ⟨q, hq, rfl⟩
    rcases hq with ⟨v, hv, rfl⟩
    have hright : φ (φ.symm v) = v := by
      simpa [φ] using normalChartAt_right_inv (I := I) g p (hball_target hv)
    rwa [hright]
  exact vol_le_ball_of_len_radius (I := I) g p
    (A := φ.symm '' Metric.ball (0 : E) R)
    hA_meas hA_source hB hR hA_ball
    (fun w hw => hJ w (hA_ball hw))



theorem coordBall_vol_le_tgt
    (g : SmoothRiemannianMetric I M) (p : M)
    {B R : ℝ} (hB : 0 ≤ B)
    (hR : R ≤ expMapC2Radius (I := I) g p)
    (hball_target : Metric.ball (0 : E) R ⊆ (normalChartAt (I := I) g p).target)
    (hJ : ∀ w ∈ Metric.ball (0 : E) R,
      ∀ i : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) :
    riemannianVolumeMeasure (I := I) (M := M) g
        ((normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R) ≤
      ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
        (modelHaar (E := E)) (Metric.ball (0 : E) R) :=
  coordBall_vol_le (I := I) g p hB hR hball_target
    (coordBall_meas (I := I) g p hball_target) hJ





theorem coordBall_vol_scale
    (g : SmoothRiemannianMetric I M) (p : M)
    {B R : ℝ} (hB : 0 ≤ B)
    (hRpos : 0 < R)
    (hR : R ≤ expMapC2Radius (I := I) g p)
    (hball_target : Metric.ball (0 : E) R ⊆ (normalChartAt (I := I) g p).target)
    (hJ : ∀ w ∈ Metric.ball (0 : E) R,
      ∀ i : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) :
    riemannianVolumeMeasure (I := I) (M := M) g
        ((normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R) ≤
      ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
        (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
          (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  simpa [modelHaar_ball (E := E) hRpos] using
    coordBall_vol_le_tgt (I := I) g p hB hR hball_target hJ



theorem coordBall_vol_scale_c2
    (g : SmoothRiemannianMetric I M) (p : M)
    {B R : ℝ} (hB : 0 ≤ B)
    (hRpos : 0 < R)
    (hR : R ≤ expMapC2Radius (I := I) g p)
    (hJ : ∀ w ∈ Metric.ball (0 : E) R,
      ∀ i : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) :
    riemannianVolumeMeasure (I := I) (M := M) g
        ((normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R) ≤
      ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
        (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
          (modelHaar (E := E)) (Metric.ball (0 : E) 1)) :=
  coordBall_vol_scale (I := I) g p hB hRpos hR
    (ball_tgt_of_radius (I := I) g p hR) hJ






omit [NeZero (Module.finrank ℝ E)] in
theorem coordBall_vol_ge
    (g : SmoothRiemannianMetric I M) (p : M)
    {c R : ℝ}
    (hball_target : Metric.ball (0 : E) R ⊆ (normalChartAt (I := I) g p).target)
    (hdens : ∀ w ∈ Metric.ball (0 : E) R,
      c ≤ normalChartDensity (I := I) g p w) :
    ENNReal.ofReal c * (modelHaar (E := E)) (Metric.ball (0 : E) R) ≤
      riemannianVolumeMeasure (I := I) (M := M) g
        ((normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R) := by
  let φ := normalChartAt (I := I) g p
  have hA_source : φ.symm '' Metric.ball (0 : E) R ⊆ φ.source := by
    intro q hq
    rcases hq with ⟨w, hw, rfl⟩
    exact φ.map_target (hball_target hw)
  have hA_image : φ '' (φ.symm '' Metric.ball (0 : E) R) = Metric.ball (0 : E) R := by
    ext w
    constructor
    · intro hw
      rcases hw with ⟨q, hq, rfl⟩
      rcases hq with ⟨v, hv, rfl⟩
      have hright : φ (φ.symm v) = v := by
        simpa [φ] using normalChartAt_right_inv (I := I) g p (hball_target hv)
      rwa [hright]
    · intro hw
      refine ⟨φ.symm w, ⟨w, hw, rfl⟩, ?_⟩
      simpa [φ] using normalChartAt_right_inv (I := I) g p (hball_target hw)
  have hge := vol_ge_of_density (I := I) g p
    (coordBall_meas (I := I) g p hball_target)
    (by simpa [φ] using hA_source)
    (fun w hw => by
      have hw' : w ∈ φ '' (φ.symm '' Metric.ball (0 : E) R) := by
        simpa [φ] using hw
      exact hdens w (by simpa [hA_image] using hw'))
  change ENNReal.ofReal c * (modelHaar (E := E)) (φ '' (φ.symm '' Metric.ball (0 : E) R)) ≤
    riemannianVolumeMeasure (I := I) (M := M) g (φ.symm '' Metric.ball (0 : E) R) at hge
  rw [hA_image] at hge
  simpa [φ] using hge


omit [NeZero (Module.finrank ℝ E)] in
theorem coordBall_vol_ge_sc
    (g : SmoothRiemannianMetric I M) (p : M)
    {c R : ℝ} (hRpos : 0 < R)
    (hball_target : Metric.ball (0 : E) R ⊆ (normalChartAt (I := I) g p).target)
    (hdens : ∀ w ∈ Metric.ball (0 : E) R,
      c ≤ normalChartDensity (I := I) g p w) :
    ENNReal.ofReal c *
        (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
          (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
      riemannianVolumeMeasure (I := I) (M := M) g
        ((normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R) := by
  simpa [modelHaar_ball (E := E) hRpos] using
    coordBall_vol_ge (I := I) g p hball_target hdens



theorem coordBall_vol_ge_sc_c2
    (g : SmoothRiemannianMetric I M) (p : M)
    {c R : ℝ} (hRpos : 0 < R)
    (hR : R ≤ expMapC2Radius (I := I) g p)
    (hdens : ∀ w ∈ Metric.ball (0 : E) R,
      c ≤ normalChartDensity (I := I) g p w) :
    ENNReal.ofReal c *
        (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
          (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
      riemannianVolumeMeasure (I := I) (M := M) g
        ((normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R) :=
  coordBall_vol_ge_sc (I := I) g p hRpos
    (ball_tgt_of_radius (I := I) g p hR) hdens

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in







theorem coordBall_subset_smallNormalBall_of_agree
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {R s : ℝ}
    (hball_target : Metric.ball (0 : E) R ⊆ (normalChartAt (I := I) g p).target)
    (hagree : ∀ w ∈ Metric.ball (0 : E) R,
      expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from w) =
        expMap (I := I) g p (show TangentSpace I p from w))
    (hgs : ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) :
    (normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R ⊆
      smallNormalBall (I := I) p s := by
  intro y hy
  rcases hy with ⟨w, hw, rfl⟩
  have hsymm :
      (normalChartAt (I := I) g p).symm w =
        expMap (I := I) g p (show TangentSpace I p from w) :=
    normalChartAt_symm_apply (I := I) g p (hball_target hw)
  have hconf :=
    smallNormalBall_radial_confined (I := I) g hEnorm p
      (show TangentSpace I p from w) (hgs w hw) (t := 1) ⟨zero_le_one, le_rfl⟩
  have hconf' :
      expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from w) ∈
        smallNormalBall (I := I) p s := by
    simpa [expMapIntrinsic_def] using hconf
  rw [hagree w hw, ← hsymm] at hconf'
  exact hconf'

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in







theorem exists_coordBall_subset_smallNormalBall
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {R s : ℝ},
      Metric.ball (0 : E) R ⊆ (normalChartAt (I := I) g p).target →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      (normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R ⊆
        smallNormalBall (I := I) p s := by
  obtain ⟨ρ, hρpos, hagree⟩ := exists_expMapIntrinsic_eq_expMap_radius (I := I) g hEnorm p
  refine ⟨ρ, hρpos, ?_⟩
  intro R s hball_target hρball hgs
  exact coordBall_subset_smallNormalBall_of_agree (I := I) g hEnorm p
    hball_target (fun w hw => hagree (hρball w hw)) hgs







omit [NeZero (Module.finrank ℝ E)] in
theorem smallNormalBall_vol_ge_sc
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M)
    {c R s : ℝ} (hRpos : 0 < R)
    (hball_target : Metric.ball (0 : E) R ⊆ (normalChartAt (I := I) g p).target)
    (hcoord_subset :
      (normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R ⊆
        smallNormalBall (I := I) p s)
    (hdens : ∀ w ∈ Metric.ball (0 : E) R,
      c ≤ normalChartDensity (I := I) g p w) :
    ENNReal.ofReal c *
        (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
          (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
      riemannianVolumeMeasure (I := I) (M := M) g (smallNormalBall (I := I) p s) := by
  exact le_trans
    (coordBall_vol_ge_sc (I := I) g p hRpos hball_target hdens)
    (MeasureTheory.measure_mono hcoord_subset)



theorem smallNormalBall_vol_ge_sc_c2
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M)
    {c R s : ℝ} (hRpos : 0 < R)
    (hR : R ≤ expMapC2Radius (I := I) g p)
    (hcoord_subset :
      (normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R ⊆
        smallNormalBall (I := I) p s)
    (hdens : ∀ w ∈ Metric.ball (0 : E) R,
      c ≤ normalChartDensity (I := I) g p w) :
    ENNReal.ofReal c *
        (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
          (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
      riemannianVolumeMeasure (I := I) (M := M) g (smallNormalBall (I := I) p s) :=
  smallNormalBall_vol_ge_sc (I := I) g p hRpos
    (ball_tgt_of_radius (I := I) g p hR) hcoord_subset hdens

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in








theorem exists_smallNormalBall_vol_ge_sc
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {c R s : ℝ},
      0 < R →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      (∀ w ∈ Metric.ball (0 : E) R,
        c ≤ normalChartDensity (I := I) g p w) →
      ENNReal.ofReal c *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (smallNormalBall (I := I) p s) := by
  obtain ⟨ρ, hρpos, hsubset⟩ := exists_coordBall_subset_smallNormalBall (I := I) g hEnorm p
  refine ⟨ρ, hρpos, ?_⟩
  intro c R s hRpos hR hρball hgs hdens
  exact smallNormalBall_vol_ge_sc_c2 (I := I) g p hRpos hR
    (hsubset (ball_tgt_of_radius (I := I) g p hR) hρball hgs) hdens

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in






omit [CompleteSpace E] in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem smallNormalBall_subset_metricBall
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    {p : M} {s : ℝ} :
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    smallNormalBall (I := I) p s ⊆ Metric.ball p s := by
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro y hy
  rw [Metric.mem_ball]
  rw [dist_comm]
  rw [HopfRinow.riemMetric_dist_eq (I := I) (M := M) p y]
  exact ENNReal.toReal_lt_of_lt_ofReal hy

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in






omit [CompleteSpace E] in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem metricBall_subset_smallNormalBall
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    {p : M} {s : ℝ} :
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    Metric.ball p s ⊆ smallNormalBall (I := I) p s := by
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro y hy
  rw [Metric.mem_ball] at hy
  rw [dist_comm] at hy
  rw [HopfRinow.riemMetric_dist_eq (I := I) (M := M) p y] at hy
  rw [mem_smallNormalBall]
  exact (ENNReal.lt_ofReal_iff_toReal_lt (riemannianEDist_ne_top (I := I) p y)).mpr hy

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem metricBall_meas
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (p : M) (s : ℝ) :
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    MeasurableSet (Metric.ball p s) := by
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact Metric.isOpen_ball.measurableSet

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in







theorem exists_metricBall_vol_ge_sc_local
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {c R s : ℝ},
      0 < R →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      (∀ w ∈ Metric.ball (0 : E) R,
        c ≤ normalChartDensity (I := I) g p w) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal c *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) := by
  obtain ⟨ρ, hρpos, hsmall⟩ := exists_smallNormalBall_vol_ge_sc (I := I) g hEnorm p
  refine ⟨ρ, hρpos, ?_⟩
  intro c R s hRpos hR hρball hgs hdens
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact le_trans
    (hsmall hRpos hR hρball hgs hdens)
    (MeasureTheory.measure_mono (smallNormalBall_subset_metricBall (I := I) (M := M)))

omit [T2Space M] [SigmaCompactSpace M] in
omit [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
private lemma norm_le_sqrt_div_sqrt_coercive
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    ‖x‖ ≤ Real.sqrt (g.inner p x x) / Real.sqrt (gpCoerciveConst (I := I) g p) := by
  have hc_pos : 0 < gpCoerciveConst (I := I) g p := gpCoerciveConst_pos (I := I) g p
  have hsc_pos : 0 < Real.sqrt (gpCoerciveConst (I := I) g p) := Real.sqrt_pos.mpr hc_pos
  have hcoerc : gpCoerciveConst (I := I) g p * ‖x‖ ^ 2 ≤ g.inner p x x :=
    gpCoerciveConst_le (I := I) g p x
  have hkey : Real.sqrt (gpCoerciveConst (I := I) g p) * ‖x‖ ≤
      Real.sqrt (g.inner p x x) := by
    have hlhs_eq : Real.sqrt (gpCoerciveConst (I := I) g p) * ‖x‖ =
        Real.sqrt (gpCoerciveConst (I := I) g p * ‖x‖ ^ 2) := by
      rw [Real.sqrt_mul hc_pos.le, Real.sqrt_sq (norm_nonneg x)]
    rw [hlhs_eq]
    exact Real.sqrt_le_sqrt hcoerc
  rw [le_div_iff₀ hsc_pos, mul_comm]
  exact hkey

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma sqrt_inner_le_opNorm_const
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    Real.sqrt (g.inner p x x) ≤ (Real.sqrt ‖g.inner p‖ + 1) * ‖x‖ := by
  have hop :
      |g.inner p x x| ≤ ‖g.inner p‖ * ‖x‖ * ‖x‖ := by
    simpa [Real.norm_eq_abs] using (g.inner p).le_opNorm₂ x x
  have hquad :
      g.inner p x x ≤ ‖g.inner p‖ * ‖x‖ ^ 2 := by
    calc
      g.inner p x x ≤ |g.inner p x x| := le_abs_self _
      _ ≤ ‖g.inner p‖ * ‖x‖ * ‖x‖ := hop
      _ = ‖g.inner p‖ * ‖x‖ ^ 2 := by ring
  have hsqrt :
      Real.sqrt (g.inner p x x) ≤ Real.sqrt (‖g.inner p‖ * ‖x‖ ^ 2) :=
    Real.sqrt_le_sqrt hquad
  have hprod :
      Real.sqrt (‖g.inner p‖ * ‖x‖ ^ 2) = Real.sqrt ‖g.inner p‖ * ‖x‖ := by
    rw [Real.sqrt_mul (norm_nonneg (g.inner p)), Real.sqrt_sq (norm_nonneg x)]
  have hmul :
      Real.sqrt ‖g.inner p‖ * ‖x‖ ≤ (Real.sqrt ‖g.inner p‖ + 1) * ‖x‖ := by
    nlinarith [Real.sqrt_nonneg ‖g.inner p‖, norm_nonneg x]
  exact hsqrt.trans (by simpa [hprod] using hmul)

private noncomputable def basisNormSupBV : ℝ :=
  (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup'
    (by
      refine Finset.univ_nonempty_iff.mpr ?_
      exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩)
    (fun k => ‖(chartModelBasis E) k‖)

omit [CompleteSpace E] in
private lemma basisNormSupBV_nonneg : 0 ≤ basisNormSupBV (E := E) := by
  classical
  unfold basisNormSupBV
  have hne : (Finset.univ : Finset (Fin (Module.finrank ℝ E))).Nonempty := by
    refine Finset.univ_nonempty_iff.mpr ?_
    exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  obtain ⟨k₀, hk₀⟩ := hne
  have hnn : (0 : ℝ) ≤ ‖(chartModelBasis E) k₀‖ := norm_nonneg _
  exact hnn.trans (Finset.le_sup'
    (f := fun k => ‖(chartModelBasis E) k‖) hk₀)

omit [CompleteSpace E] in
private lemma norm_basis_le_supBV
    (k : Fin (Module.finrank ℝ E)) :
    ‖(chartModelBasis E) k‖ ≤ basisNormSupBV (E := E) := by
  classical
  unfold basisNormSupBV
  exact Finset.le_sup'
    (f := fun k => ‖(chartModelBasis E) k‖)
    (Finset.mem_univ _)

omit [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma exists_basis_upper_const
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ A : ℝ, ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A := by
  refine ⟨(Real.sqrt ‖g.inner p‖ + 1) * basisNormSupBV (E := E), ?_⟩
  intro k
  exact (sqrt_inner_le_opNorm_const (I := I) g p ((chartModelBasis E) k)).trans
    (mul_le_mul_of_nonneg_left (norm_basis_le_supBV (E := E) k)
      (by nlinarith [Real.sqrt_nonneg ‖g.inner p‖]))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma exists_metric_upper_launch_const
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ {R : ℝ}, 0 ≤ R →
      ∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ C * R := by
  refine ⟨Real.sqrt ‖g.inner p‖ + 1, ?_, ?_⟩
  · nlinarith [Real.sqrt_nonneg ‖g.inner p‖]
  intro R hR w hw
  have hw_norm_le : ‖w‖ ≤ R := by
    exact le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw)
  exact (sqrt_inner_le_opNorm_const (I := I) g p w).trans
    (mul_le_mul_of_nonneg_left hw_norm_le (by nlinarith [Real.sqrt_nonneg ‖g.inner p‖]))

private lemma exists_pos_lt_mul_sq_le {S κ ρ : ℝ}
    (hκ : 0 < κ) (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < ρ ∧ S * ε ^ 2 ≤ κ := by
  let T : ℝ := max S 1
  have hT_pos : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right S 1)
  let ε : ℝ := min (ρ / 2) (Real.sqrt (κ / T))
  have hρ_half_pos : 0 < ρ / 2 := by positivity
  have hκ_div_pos : 0 < κ / T := div_pos hκ hT_pos
  have hsqrt_pos : 0 < Real.sqrt (κ / T) := Real.sqrt_pos.mpr hκ_div_pos
  have hε_pos : 0 < ε := lt_min hρ_half_pos hsqrt_pos
  have hε_lt_ρ : ε < ρ := by
    have hε_le : ε ≤ ρ / 2 := min_le_left _ _
    nlinarith
  have hε_nonneg : 0 ≤ ε := hε_pos.le
  have hε_le_sqrt : ε ≤ Real.sqrt (κ / T) := min_le_right _ _
  have hε_sq_le : ε ^ 2 ≤ κ / T := by
    have h_abs :
        |ε| ≤ |Real.sqrt (κ / T)| := by
      rw [abs_of_nonneg hε_nonneg, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hε_le_sqrt
    have hsq := (sq_le_sq).2 h_abs
    simpa [Real.sq_sqrt (le_of_lt hκ_div_pos)] using hsq
  have hT_mul : T * ε ^ 2 ≤ κ := by
    have hmul := mul_le_mul_of_nonneg_left hε_sq_le hT_pos.le
    have hcancel : T * (κ / T) = κ := by
      field_simp [hT_pos.ne']
    calc
      T * ε ^ 2 ≤ T * (κ / T) := hmul
      _ = κ := hcancel
  have hS_le_T : S ≤ T := le_max_left _ _
  have hS_mul : S * ε ^ 2 ≤ T * ε ^ 2 :=
    mul_le_mul_of_nonneg_right hS_le_T (sq_nonneg ε)
  exact ⟨ε, hε_pos, hε_lt_ρ, hS_mul.trans hT_mul⟩

private lemma exists_radius_coeff_cap {C κ ρ S : ℝ}
    (hC : 0 < C) (hκ : 0 < κ) (hρ : 0 < ρ) :
    ∃ R : ℝ, 0 < R ∧ R < ρ ∧ C * R < ρ ∧ S * (C * R) ^ 2 ≤ κ := by
  have hCρ : 0 < C * ρ := mul_pos hC hρ
  have hcapρ : 0 < min ρ (C * ρ) := lt_min hρ hCρ
  obtain ⟨ε, hε_pos, hεcapρ, hcap⟩ := exists_pos_lt_mul_sq_le (S := S) hκ hcapρ
  refine ⟨ε / C, div_pos hε_pos hC, ?_, ?_, ?_⟩
  · have hε_Cρ : ε < C * ρ := lt_of_lt_of_le hεcapρ (min_le_right _ _)
    rw [div_lt_iff₀ hC]
    simpa [mul_comm] using hε_Cρ
  · field_simp [hC.ne']
    exact lt_of_lt_of_le hεcapρ (min_le_left _ _)
  · have hCR : C * (ε / C) = ε := mul_div_cancel₀ ε hC.ne'
    simpa [hCR] using hcap

private lemma exists_pos_le_mul_lt {C s R : ℝ}
    (hC : 0 < C) (hs : 0 < s) (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ C * r < s := by
  have hsC : 0 < s / C := div_pos hs hC
  have hcap : 0 < min R (s / C) := lt_min hR hsC
  obtain ⟨r, hr_pos, hr_cap, _⟩ :=
    exists_pos_lt_mul_sq_le (S := (0 : ℝ)) zero_lt_one hcap
  refine ⟨r, hr_pos, le_of_lt (lt_of_lt_of_le hr_cap (min_le_left _ _)), ?_⟩
  have hr_sC : r < s / C := lt_of_lt_of_le hr_cap (min_le_right _ _)
  rw [lt_div_iff₀ hC] at hr_sC
  simpa [mul_comm] using hr_sC

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in








theorem metricBall_chartCtrl
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {R s : ℝ},
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      Metric.ball p s ⊆ (normalChartAt (I := I) g p).source ∧
        (normalChartAt (I := I) g p) '' Metric.ball p s ⊆
          Metric.ball (0 : E) R := by
  obtain ⟨ρ₀, hρ₀pos, hagree⟩ := exists_expMapIntrinsic_eq_expMap_radius (I := I) g hEnorm p
  refine ⟨min ρ₀ (expRadiusGp (I := I) g p),
    lt_min hρ₀pos (expRadiusGp_pos (I := I) g p), ?_⟩
  intro R s hsR hsρ hs_div_R
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  let ψ := normalChartAt (I := I) g p
  have hpoint : ∀ y ∈ Metric.ball p s,
      y ∈ ψ.source ∧ ψ y ∈ Metric.ball (0 : E) R := by
    intro y hy
    obtain ⟨v, hv_exp, hv_len⟩ :=
      hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm p y
    set w : E := (v : E) with hw_def
    have hdist_lt_s : dist p y < s := by
      rw [Metric.mem_ball] at hy
      simpa [dist_comm] using hy
    have hv_sqrt_lt_s : Real.sqrt (g.inner p (v : E) (v : E)) < s := by
      rw [hv_len]
      rw [← HopfRinow.riemMetric_dist_eq (I := I) (M := M) p y]
      exact hdist_lt_s
    have hw_norm_lt_R : ‖w‖ < R := by
      have hsc_pos : 0 < Real.sqrt (gpCoerciveConst (I := I) g p) :=
        Real.sqrt_pos.mpr (gpCoerciveConst_pos (I := I) g p)
      have hw_sqrt_div_lt :
          Real.sqrt (g.inner p w w) / Real.sqrt (gpCoerciveConst (I := I) g p) < R := by
        rw [hw_def]
        exact (div_lt_div_of_pos_right hv_sqrt_lt_s hsc_pos).trans hs_div_R
      exact lt_of_le_of_lt (norm_le_sqrt_div_sqrt_coercive (I := I) g p w) hw_sqrt_div_lt
    have hv_sqrt_lt_ρ₀ :
        Real.sqrt (g.inner p (v : E) (v : E)) < ρ₀ := by
      exact lt_trans hv_sqrt_lt_s (lt_of_lt_of_le hsρ (min_le_left _ _))
    have hv_sqrt_lt_gp :
        Real.sqrt (g.inner p (v : E) (v : E)) < expRadiusGp (I := I) g p := by
      exact lt_trans hv_sqrt_lt_s (lt_of_lt_of_le hsρ (min_le_right _ _))
    have hagree_v :
        expMapIntrinsic (I := I) g hEnorm p v = expMap (I := I) g p v :=
      hagree hv_sqrt_lt_ρ₀
    have hw_norm_lt_C2 : ‖w‖ < expMapC2Radius (I := I) g p := by
      apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g p
      simpa [hw_def] using hv_sqrt_lt_gp
    have hw_target : w ∈ ψ.target := by
      simpa [ψ] using ball_subset_normalChartAt_target (I := I) g p hw_norm_lt_C2
    have hexp_y :
        expMap (I := I) g p (show TangentSpace I p from w) = y := by
      rw [hw_def]
      rw [← hagree_v, hv_exp]
    have hsymm :
        ψ.symm w = expMap (I := I) g p (show TangentSpace I p from w) := by
      simpa [ψ] using normalChartAt_symm_apply (I := I) g p (v := w) hw_target
    have hy_eq : y = ψ.symm w := by
      rw [hsymm, hexp_y]
    have hy_source : y ∈ ψ.source := by
      have hsrc : ψ.symm w ∈ ψ.source := ψ.symm.map_source hw_target
      simpa [hy_eq] using hsrc
    have hchart_eq : ψ y = w := by
      rw [hy_eq]
      simpa [ψ] using normalChartAt_right_inv (I := I) g p (y := w) hw_target
    exact ⟨hy_source, by simpa [Metric.mem_ball, dist_zero_right, hchart_eq] using hw_norm_lt_R⟩
  exact ⟨fun y hy => (hpoint y hy).1, by
    rintro z ⟨y, hy, rfl⟩
    exact (hpoint y hy).2⟩









theorem metricBall_vol_le [PseudoMetricSpace M]
    (g : SmoothRiemannianMetric I M) (p : M)
    {B R s : ℝ} (hB : 0 ≤ B)
    (hR : R ≤ expMapC2Radius (I := I) g p)
    (hball_meas : MeasurableSet (Metric.ball p s))
    (hball_source : Metric.ball p s ⊆ (normalChartAt (I := I) g p).source)
    (hball_coord :
      (normalChartAt (I := I) g p) '' Metric.ball p s ⊆ Metric.ball (0 : E) R)
    (hJ : ∀ w ∈ Metric.ball (0 : E) R,
      ∀ i : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) :
    riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
      ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
        (modelHaar (E := E)) (Metric.ball (0 : E) R) :=
  vol_le_ball_of_len_radius (I := I) g p
    (A := Metric.ball p s)
    hball_meas hball_source hB hR hball_coord
    (fun w hw => hJ w (hball_coord hw))







theorem metricBall_vol_scale [PseudoMetricSpace M]
    (g : SmoothRiemannianMetric I M) (p : M)
    {B R s : ℝ} (hB : 0 ≤ B)
    (hRpos : 0 < R)
    (hR : R ≤ expMapC2Radius (I := I) g p)
    (hball_meas : MeasurableSet (Metric.ball p s))
    (hball_source : Metric.ball p s ⊆ (normalChartAt (I := I) g p).source)
    (hball_coord :
      (normalChartAt (I := I) g p) '' Metric.ball p s ⊆ Metric.ball (0 : E) R)
    (hJ : ∀ w ∈ Metric.ball (0 : E) R,
      ∀ i : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) :
    riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
      ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
        (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
          (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  simpa [modelHaar_ball (E := E) hRpos] using
    metricBall_vol_le (I := I) g p hB hR hball_meas hball_source hball_coord hJ


omit [NeZero (Module.finrank ℝ E)] in
theorem metricBall_vol_scale_density [PseudoMetricSpace M]
    (g : SmoothRiemannianMetric I M) (p : M)
    {C R s : ℝ}
    (hRpos : 0 < R)
    (hball_meas : MeasurableSet (Metric.ball p s))
    (hball_source : Metric.ball p s ⊆ (normalChartAt (I := I) g p).source)
    (hball_coord :
      (normalChartAt (I := I) g p) '' Metric.ball p s ⊆ Metric.ball (0 : E) R)
    (hdens : ∀ w ∈ Metric.ball (0 : E) R,
      normalChartDensity (I := I) g p w ≤ C) :
    riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
      ENNReal.ofReal C *
        (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
          (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  simpa [modelHaar_ball (E := E) hRpos] using
    vol_le_ball_of_density (I := I) g p
      (A := Metric.ball p s) hball_meas hball_source hball_coord
      (fun w hw => hdens w (hball_coord hw))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





theorem exists_metricBall_vol_scale_local
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {B R s : ℝ},
      0 ≤ B →
      0 < R →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      R ≤ expMapC2Radius (I := I) g p →
      (letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
       MeasurableSet (Metric.ball p s)) →
      (∀ w ∈ Metric.ball (0 : E) R,
        ∀ i : Fin (Module.finrank ℝ E),
          Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
            (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
            (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
            (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
              (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρpos, hctrl⟩ := metricBall_chartCtrl (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρpos, ?_⟩
  intro B R s hB hRpos hsR hsρ hs_div_R hRC2 hmeas hJ
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  obtain ⟨hsource, hcoord⟩ := hctrl hsR hsρ hs_div_R
  exact metricBall_vol_scale (I := I) g p hB hRpos hRC2 hmeas hsource hcoord hJ

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_metricBall_vol_le_dens_local
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {C R s : ℝ},
      0 < R →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R,
        normalChartDensity (I := I) g p w ≤ C) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal C *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρpos, hctrl⟩ := metricBall_chartCtrl (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρpos, ?_⟩
  intro C R s hRpos hsR hsρ hs_div_R hdens
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  obtain ⟨hsource, hcoord⟩ := hctrl hsR hsρ hs_div_R
  exact metricBall_vol_scale_density (I := I) g p hRpos
    (metricBall_meas (I := I) (M := M) p s) hsource hcoord hdens

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_vol_two_dens
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {c C R s : ℝ},
      0 < R →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      (∀ w ∈ Metric.ball (0 : E) R,
        c ≤ normalChartDensity (I := I) g p w) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R,
        normalChartDensity (I := I) g p w ≤ C) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal c *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal C *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρlo, hρlo_pos, hlower⟩ := exists_metricBall_vol_ge_sc_local (I := I) g hEnorm p
  obtain ⟨ρup, hρup_pos, hupper⟩ := exists_metricBall_vol_le_dens_local (I := I) (M := M) g hEnorm p
  refine ⟨min ρlo ρup, lt_min hρlo_pos hρup_pos, ?_⟩
  intro c C R s hRpos hR hρball hgs hdensLower hsR hsρ hsdiv hdensUpper
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hρlo_ball : ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρlo :=
    fun w hw => lt_of_lt_of_le (hρball w hw) (min_le_left _ _)
  have hsρup : s < ρup := lt_of_lt_of_le hsρ (min_le_right _ _)
  exact ⟨
    hlower hRpos hR hρlo_ball hgs hdensLower,
    hupper hRpos hsR hsρup hsdiv hdensUpper⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



theorem exists_vol_two_dens_pairR
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {c C Rlo Rup s : ℝ},
      0 < Rlo →
      Rlo ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) Rlo,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) Rlo,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      (∀ w ∈ Metric.ball (0 : E) Rlo,
        c ≤ normalChartDensity (I := I) g p w) →
      0 < Rup →
      s < Rup →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < Rup →
      (∀ w ∈ Metric.ball (0 : E) Rup,
        normalChartDensity (I := I) g p w ≤ C) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal c *
          (ENNReal.ofReal (Rlo ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal C *
          (ENNReal.ofReal (Rup ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρlo, hρlo_pos, hlower⟩ := exists_metricBall_vol_ge_sc_local (I := I) g hEnorm p
  obtain ⟨ρup, hρup_pos, hupper⟩ :=
    exists_metricBall_vol_le_dens_local (I := I) (M := M) g hEnorm p
  refine ⟨min ρlo ρup, lt_min hρlo_pos hρup_pos, ?_⟩
  intro c C Rlo Rup s hRlo_pos hRlo hρlo_ball hgs hdensLower hRup_pos hsRup hsρ
    hsdiv hdensUpper
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hρlo_ball' : ∀ w ∈ Metric.ball (0 : E) Rlo,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρlo :=
    fun w hw => lt_of_lt_of_le (hρlo_ball w hw) (min_le_left _ _)
  have hsρup : s < ρup := lt_of_lt_of_le hsρ (min_le_right _ _)
  exact ⟨
    hlower hRlo_pos hRlo hρlo_ball' hgs hdensLower,
    hupper hRup_pos hsRup hsρup hsdiv hdensUpper⟩







structure RadialExtData
    (g : SmoothRiemannianMetric I M) (p : M) (R b : ℝ) where
  gamma : E → ℝ → M
  eps : E → ℝ
  smooth : ∀ w ∈ Metric.ball (0 : E) R,
    ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) (gamma w)
  eps_pos : ∀ w ∈ Metric.ball (0 : E) R, 0 < eps w
  eqOnNbhd : ∀ w ∈ Metric.ball (0 : E) R,
    Set.EqOn (gamma w) (radialCurve (I := I) g p w) (Set.Icc (-(eps w)) (b + eps w))
  eqOn : ∀ w ∈ Metric.ball (0 : E) R,
    Set.EqOn (gamma w) (radialCurve (I := I) g p w) (Set.Icc 0 b)


omit [T2Space M] [SigmaCompactSpace M] in
lemma exists_radialExtData
    (g : SmoothRiemannianMetric I M) (p : M) {R b : ℝ}
    (hb1 : b ≤ 1)
    (hR : R ≤ expMapC2Radius (I := I) g p) :
    Nonempty (RadialExtData (I := I) g p R b) := by
  classical
  have hExt : ∀ w : E, ∃ gamma : ℝ → M,
      w ∈ Metric.ball (0 : E) R →
        ∃ eps : ℝ, 0 < eps ∧
          ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma ∧
          Set.EqOn gamma (radialCurve (I := I) g p w) (Set.Icc (-(eps)) (b + eps)) ∧
          Set.EqOn gamma (radialCurve (I := I) g p w) (Set.Icc 0 b) := by
    intro w
    by_cases hw : w ∈ Metric.ball (0 : E) R
    · have hwR : ‖w‖ < R := by
        simpa [Metric.mem_ball, dist_eq_norm] using hw
      obtain ⟨eps, heps, gamma, hsmooth, heqNbhd⟩ :=
        exists_rext_nbhd (I := I) g p w hb1 (hwR.trans_le hR)
      have heq : Set.EqOn gamma (radialCurve (I := I) g p w) (Set.Icc 0 b) := by
        intro t ht
        exact heqNbhd ⟨by linarith [ht.1, heps], by linarith [ht.2, heps]⟩
      exact ⟨gamma, fun _ => ⟨eps, heps, hsmooth, heqNbhd, heq⟩⟩
    · exact ⟨fun _ => p, fun h => False.elim (hw h)⟩
  choose gamma hgamma using hExt
  let eps : E → ℝ := fun w =>
    if hw : w ∈ Metric.ball (0 : E) R then (hgamma w hw).choose else 1
  let D : RadialExtData (I := I) g p R b := {
    gamma := gamma
    eps := eps
    smooth := fun w hw => (hgamma w hw).choose_spec.2.1
    eps_pos := fun w hw => by
      have heps_eq : eps w = (hgamma w hw).choose := by
        simp only [eps, dif_pos hw]
      rw [heps_eq]
      exact (hgamma w hw).choose_spec.1
    eqOnNbhd := fun w hw => by
      have heps_eq : eps w = (hgamma w hw).choose := by
        simp only [eps, dif_pos hw]
      change Set.EqOn (gamma w) (radialCurve (I := I) g p w)
        (Set.Icc (-(eps w)) (b + eps w))
      rw [heps_eq]
      exact (hgamma w hw).choose_spec.2.2.1
    eqOn := fun w hw => (hgamma w hw).choose_spec.2.2.2 }
  exact ⟨D⟩



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma radialExt_eventuallyEq
    (g : SmoothRiemannianMetric I M) (p : M) {R b : ℝ}
    (D : RadialExtData (I := I) g p R b) :
    ∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b,
      D.gamma w =ᶠ[𝓝 t] radialCurve (I := I) g p w := by
  intro w hw t ht
  have heps := D.eps_pos w hw
  have htopen : t ∈ Set.Ioo (-(D.eps w)) (b + D.eps w) :=
    ⟨by linarith [ht.1, heps], by linarith [ht.2, heps]⟩
  filter_upwards [isOpen_Ioo.mem_nhds htopen] with u hu
  exact D.eqOnNbhd w hw ⟨le_of_lt hu.1, le_of_lt hu.2⟩


structure ExtFrameData
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {p : M} {R b : ℝ}
    (D : RadialExtData (I := I) g p R b) where
  ι : Type*
  [fintype : Fintype ι]
  [decidableEq : DecidableEq ι]
  [nonempty : Nonempty ι]
  F : ∀ w : E, ι → ∀ t : ℝ, TangentSpace I (D.gamma w t)

attribute [instance] ExtFrameData.fintype
attribute [instance] ExtFrameData.decidableEq
attribute [instance] ExtFrameData.nonempty




omit [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
lemma exists_extFrameData
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {p : M} {R b : ℝ}
    (D : RadialExtData (I := I) g p R b) (hb : 0 < b) :
    ∃ Fd : ExtFrameData (I := I) g D,
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t : ℝ,
        Fintype.card Fd.ι =
          Module.finrank ℝ (TangentSpace I (D.gamma w t))) ∧
      (∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ (chartRepAt (I := I) (D.gamma w) (Fd.F w i) t) t) ∧
      (∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (D.gamma w) (Fd.F w i) t = 0) ∧
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
        g.inner (D.gamma w t) (Fd.F w i t) (Fd.F w j t) =
          if i = j then (1 : ℝ) else 0) := by
  classical
  have hframe : ∀ w : E,
      ∃ F : Fin (Module.finrank ℝ E) → ∀ t : ℝ, TangentSpace I (D.gamma w t),
        (w ∈ Metric.ball (0 : E) R →
          (∀ t : ℝ,
            Fintype.card (Fin (Module.finrank ℝ E)) =
              Module.finrank ℝ (TangentSpace I (D.gamma w t))) ∧
          (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
            DifferentiableAt ℝ (chartRepAt (I := I) (D.gamma w) (F i) t) t) ∧
          (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
            covDerivAlong (I := I) g (D.gamma w) (F i) t = 0) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
            g.inner (D.gamma w t) (F i t) (F j t) =
              if i = j then (1 : ℝ) else 0)) := by
    intro w
    by_cases hw : w ∈ Metric.ball (0 : E) R
    · obtain ⟨basis, hON0⟩ :=
        DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis
          (I := I) g (D.gamma w 0)
      obtain ⟨F, _hF0, hFdiff, hFpar, hFON⟩ :=
        DifferentialGeometry.Geometry.Riemannian.exists_parallel_frame
          (I := I) g (D.gamma w) (N := 2) (by norm_num) (D.smooth w hw) hb basis hON0
      refine ⟨F, fun _ => ?_⟩
      exact ⟨fun t => by
        rw [show Module.finrank ℝ (TangentSpace I (D.gamma w t)) =
          Module.finrank ℝ E from rfl]
        simp, hFdiff, hFpar, hFON⟩
    · exact ⟨fun _ t => 0, fun h => False.elim (hw h)⟩
  choose F hF using hframe
  let Fd : ExtFrameData (I := I) g D := {
    ι := ULift (Fin (Module.finrank ℝ E))
    fintype := inferInstance
    decidableEq := inferInstance
    nonempty := inferInstance
    F := fun w i => F w i.down }
  refine ⟨Fd, ?_, ?_, ?_, ?_⟩
  · intro w hw t
    rw [show Module.finrank ℝ (TangentSpace I (D.gamma w t)) =
      Module.finrank ℝ E from rfl]
    simp [Fd]
  · intro w hw i t ht
    exact (hF w hw).2.1 i.down t ht
  · intro w hw i t ht
    exact (hF w hw).2.2.1 i.down t ht
  · intro w hw t ht i j
    simpa [Fd] using (hF w hw).2.2.2 t ht i.down j.down




def radialFrameOfExt
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {p : M} {R b : ℝ}
    (D : RadialExtData (I := I) g p R b) (Fd : ExtFrameData (I := I) g D)
    (w : E) (i : Fd.ι) (t : ℝ) :
    TangentSpace I (radialCurve (I := I) g p w t) := by
  classical
  exact if hw : w ∈ Metric.ball (0 : E) R then
    if ht : t ∈ Set.Icc (-(D.eps w)) (b + D.eps w) then
      show TangentSpace I (radialCurve (I := I) g p w t) from by
        exact (Fd.F w i t : E)
    else 0
  else 0


structure Rm04FrameData
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (R b : ℝ) where
  ι : Type*
  [fintype : Fintype ι]
  [decidableEq : DecidableEq ι]
  [nonempty : Nonempty ι]
  F : ∀ w : E, ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p w t)

attribute [instance] Rm04FrameData.fintype
attribute [instance] Rm04FrameData.decidableEq
attribute [instance] Rm04FrameData.nonempty




def rm04FrameDataOfExt
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {p : M} {R b : ℝ}
    (D : RadialExtData (I := I) g p R b) (Fd : ExtFrameData (I := I) g D) :
    Rm04FrameData (I := I) g p R b where
  ι := Fd.ι
  fintype := inferInstance
  decidableEq := inferInstance
  nonempty := inferInstance
  F := fun w i t => radialFrameOfExt (I := I) g D Fd w i t


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma rm04FrameDataOfExt_card
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {p : M} {R b : ℝ}
    (D : RadialExtData (I := I) g p R b) (Fd : ExtFrameData (I := I) g D)
    (hcard : ∀ w ∈ Metric.ball (0 : E) R, ∀ t : ℝ,
      Fintype.card Fd.ι = Module.finrank ℝ (TangentSpace I (D.gamma w t))) :
    ∀ w ∈ Metric.ball (0 : E) R, ∀ t : ℝ,
      Fintype.card (rm04FrameDataOfExt (I := I) g D Fd).ι =
        Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p w t)) := by
  intro w hw t
  have h := hcard w hw t
  rw [show Module.finrank ℝ (TangentSpace I (D.gamma w t)) =
    Module.finrank ℝ E from rfl] at h
  rw [show Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p w t)) =
    Module.finrank ℝ E from rfl]
  simpa [rm04FrameDataOfExt] using h



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma rm04FrameDataOfExt_ON
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {p : M} {R b : ℝ}
    (D : RadialExtData (I := I) g p R b) (Fd : ExtFrameData (I := I) g D)
    (hON : ∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
      g.inner (D.gamma w t) (Fd.F w i t) (Fd.F w j t) =
        if i = j then (1 : ℝ) else 0) :
    ∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p w t)
        ((rm04FrameDataOfExt (I := I) g D Fd).F w i t)
        ((rm04FrameDataOfExt (I := I) g D Fd).F w j t) =
          if i = j then (1 : ℝ) else 0 := by
  intro w hw t ht i j
  have htN : t ∈ Set.Icc (-(D.eps w)) (b + D.eps w) :=
    ⟨by linarith [ht.1, D.eps_pos w hw], by linarith [ht.2, D.eps_pos w hw]⟩
  have hbase := D.eqOn w hw ht
  rw [← hbase]
  simpa [rm04FrameDataOfExt, radialFrameOfExt, hw, htN] using hON w hw t ht i j



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma radialFrameOfExt_evEq
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {p : M} {R b : ℝ}
    (D : RadialExtData (I := I) g p R b) (Fd : ExtFrameData (I := I) g D) :
    ∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
      (fun s : ℝ => ((rm04FrameDataOfExt (I := I) g D Fd).F w i s : E))
        =ᶠ[𝓝 t] fun s : ℝ => (Fd.F w i s : E) := by
  intro w hw i t ht
  have heps := D.eps_pos w hw
  have htopen : t ∈ Set.Ioo (-(D.eps w)) (b + D.eps w) :=
    ⟨by linarith [ht.1, heps], by linarith [ht.2, heps]⟩
  filter_upwards [isOpen_Ioo.mem_nhds htopen] with s hs
  have hsN : s ∈ Set.Icc (-(D.eps w)) (b + D.eps w) :=
    ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  simp [rm04FrameDataOfExt, radialFrameOfExt, hw, hsN]



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma rm04FrameDataOfExt_par
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {p : M} {R b : ℝ}
    (D : RadialExtData (I := I) g p R b) (Fd : ExtFrameData (I := I) g D)
    (hpar : ∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (D.gamma w) (Fd.F w i) t = 0) :
    ∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p w)
        ((rm04FrameDataOfExt (I := I) g D Fd).F w i) t = 0 := by
  intro w hw i t ht
  have hγ : radialCurve (I := I) g p w =ᶠ[𝓝 t] D.gamma w :=
    (radialExt_eventuallyEq (I := I) g p D w hw t ht).symm
  have hV := radialFrameOfExt_evEq (I := I) g D Fd w hw i t ht
  have hcongr := covDerivAlong_congr_curve (I := I) g
    ((rm04FrameDataOfExt (I := I) g D Fd).F w i) (Fd.F w i) hγ hV
  have hparE : (covDerivAlong (I := I) g (D.gamma w) (Fd.F w i) t : E) = 0 := by
    simpa using congrArg (fun v => (v : E)) (hpar w hw i t ht)
  have hgoalE :
      (covDerivAlong (I := I) g (radialCurve (I := I) g p w)
        ((rm04FrameDataOfExt (I := I) g D Fd).F w i) t : E) = 0 := by
    rw [hcongr, hparE]
    rfl
  simpa using hgoalE



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma rm04FrameDataOfExt_diff
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {p : M} {R b : ℝ}
    (D : RadialExtData (I := I) g p R b) (Fd : ExtFrameData (I := I) g D)
    (hFdiff : ∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) (D.gamma w) (Fd.F w i) t) t) :
    ∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p w)
          ((rm04FrameDataOfExt (I := I) g D Fd).F w i) t) t := by
  intro w hw i t ht
  have hγ : radialCurve (I := I) g p w =ᶠ[𝓝 t] D.gamma w :=
    (radialExt_eventuallyEq (I := I) g p D w hw t ht).symm
  have hV := radialFrameOfExt_evEq (I := I) g D Fd w hw i t ht
  have hrep := chartRep_congr_curve (I := I)
    ((rm04FrameDataOfExt (I := I) g D Fd).F w i) (Fd.F w i) hγ hV
  rw [hrep.differentiableAt_iff]
  exact hFdiff w hw i t ht



omit [T2Space M] [SigmaCompactSpace M] in
lemma exists_rm04FrameData_radius
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) {R b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hR : R ≤ expMapC2Radius (I := I) g p) :
    ∃ D : Rm04FrameData (I := I) g p R b,
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t : ℝ,
        Fintype.card D.ι =
          Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p w t))) ∧
      (∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p w) (D.F w i) t = 0) ∧
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p w t) (D.F w i t) (D.F w j t) =
          if i = j then (1 : ℝ) else 0) ∧
      (∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p w) (D.F w i) t) t) := by
  obtain ⟨Dext⟩ := exists_radialExtData (I := I) g p hb1 hR
  obtain ⟨Fd, hcard, hFdiff, hpar, hON⟩ := exists_extFrameData (I := I) g Dext hb
  refine ⟨rm04FrameDataOfExt (I := I) g Dext Fd, ?_, ?_, ?_, ?_⟩
  · exact rm04FrameDataOfExt_card (I := I) g Dext Fd hcard
  · exact rm04FrameDataOfExt_par (I := I) g Dext Fd hpar
  · exact rm04FrameDataOfExt_ON (I := I) g Dext Fd hON
  · exact rm04FrameDataOfExt_diff (I := I) g Dext Fd hFdiff



omit [CompleteSpace E] in
omit [T2Space M] [SigmaCompactSpace M] in
omit [T2Space (TangentBundle I M)] in
lemma exists_rm04FrameData
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) {R b : ℝ} (hb : 0 < b)
    (hγ2 : ∀ w ∈ Metric.ball (0 : E) R,
      ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) (radialCurve (I := I) g p w)) :
    ∃ D : Rm04FrameData (I := I) g p R b,
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t : ℝ,
        Fintype.card D.ι =
          Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p w t))) ∧
      (∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p w) (D.F w i) t = 0) ∧
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p w t) (D.F w i t) (D.F w j t) =
          if i = j then (1 : ℝ) else 0) ∧
      (∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p w) (D.F w i) t) t) := by
  classical
  have hframe : ∀ w : E,
      ∃ F : Fin (Module.finrank ℝ E) →
          ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p w t),
        (w ∈ Metric.ball (0 : E) R →
          (∀ t ∈ Set.Icc (0 : ℝ) b,
            Fintype.card (Fin (Module.finrank ℝ E)) =
              Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p w t))) ∧
          (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
            DifferentiableAt ℝ
              (chartRepAt (I := I) (radialCurve (I := I) g p w) (F i) t) t) ∧
          (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
            covDerivAlong (I := I) g (radialCurve (I := I) g p w) (F i) t = 0) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
            g.inner (radialCurve (I := I) g p w t) (F i t) (F j t) =
              if i = j then (1 : ℝ) else 0)) := by
    intro w
    by_cases hw : w ∈ Metric.ball (0 : E) R
    · obtain ⟨F, hcard, hFdiff, hpar, hON⟩ :=
        exists_radialFrame (I := I) g p w hb (hγ2 w hw)
      exact ⟨F, fun _ => ⟨hcard, hFdiff, hpar, hON⟩⟩
    · exact ⟨fun _ t => 0, fun h => False.elim (hw h)⟩
  choose F hF using hframe
  let D : Rm04FrameData (I := I) g p R b := {
    ι := ULift (Fin (Module.finrank ℝ E))
    fintype := inferInstance
    decidableEq := inferInstance
    nonempty := inferInstance
    F := fun w i => F w i.down }
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro w hw t
    rw [show Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p w t)) =
      Module.finrank ℝ E from rfl]
    simp [D]
  · intro w hw i t ht
    exact (hF w hw).2.2.1 i.down t ht
  · intro w hw t ht i j
    simpa [D] using (hF w hw).2.2.2 t ht i.down j.down
  · intro w hw i t ht
    exact (hF w hw).2.1 i.down t ht


structure IsRm04VolHyp
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M)
    {R b : ℝ} (D : Rm04FrameData (I := I) g p R b)
    (ρ a K Rm Vb A B s : ℝ) : Prop where
  hBnn : 0 ≤ B
  ha : 0 < a
  hK : 0 ≤ K
  hRm_nonneg : 0 ≤ Rm
  hVb : 0 ≤ Vb
  hb0 : 0 ≤ b
  hb1 : b ≤ 1
  h1b : (1 : ℝ) ≤ b
  hRpos : 0 < R
  hRρ : R ≤ ρ
  hRC2 : R ≤ expMapC2Radius (I := I) g p
  hρball : ∀ w ∈ Metric.ball (0 : E) R,
    Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ
  hgs : ∀ w ∈ Metric.ball (0 : E) R,
    Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s
  hsR : s < R
  hsρ : s < ρ
  hsdiv : s / Real.sqrt (gpCoerciveConst (I := I) g p) < R
  hsmallBasis : ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ
  hsmallDir : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
    ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ
  hlaunch : ∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb
  hKbound : Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
      Rm * Vb ^ 2 ≤ K
  hRm : ∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
      (radialCurve (I := I) g p w t) 4
      (DifferentialGeometry.Integral.Connection.metricRm04At
        (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm
  hγ : ∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b,
    ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p w) t
  hcard : ∀ w ∈ Metric.ball (0 : E) R, ∀ t : ℝ,
    Fintype.card D.ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p w t))
  hpar : ∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
    covDerivAlong (I := I) g (radialCurve (I := I) g p w) (D.F w i) t = 0
  hON : ∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
    g.inner (radialCurve (I := I) g p w t) (D.F w i t) (D.F w j t) =
      if i = j then (1 : ℝ) else 0
  hFdiff : ∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
    DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p w) (D.F w i) t) t
  hinit : ∀ k : Fin (Module.finrank ℝ E),
    Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A
  hmodelLe : A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B
  hmodelGe : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
    a * B ≤ Real.sqrt
        (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
          (a • (∑ i, v i • (chartModelBasis E) i))) -
        gronwallBound 0 (max K 1)
          (K * (b * Real.sqrt
            (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
              (a • (∑ i, v i • (chartModelBasis E) i))))) 1




structure IsRm04VolPairHyp
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M)
    {R b : ℝ} (D : Rm04FrameData (I := I) g p R b)
    (ρ a K Rm Vb A Blo Bhi s : ℝ) : Prop where
  hBlo : 0 ≤ Blo
  hBhi : 0 ≤ Bhi
  ha : 0 < a
  hK : 0 ≤ K
  hRm_nonneg : 0 ≤ Rm
  hVb : 0 ≤ Vb
  hb0 : 0 ≤ b
  hb1 : b ≤ 1
  h1b : (1 : ℝ) ≤ b
  hRpos : 0 < R
  hRρ : R ≤ ρ
  hRC2 : R ≤ expMapC2Radius (I := I) g p
  hρball : ∀ w ∈ Metric.ball (0 : E) R,
    Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ
  hgs : ∀ w ∈ Metric.ball (0 : E) R,
    Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s
  hsR : s < R
  hsρ : s < ρ
  hsdiv : s / Real.sqrt (gpCoerciveConst (I := I) g p) < R
  hsmallBasis : ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ
  hsmallDir : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
    ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ
  hlaunch : ∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb
  hKbound : Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
      Rm * Vb ^ 2 ≤ K
  hRm : ∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
      (radialCurve (I := I) g p w t) 4
      (DifferentialGeometry.Integral.Connection.metricRm04At
        (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm
  hγ : ∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b,
    ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p w) t
  hcard : ∀ w ∈ Metric.ball (0 : E) R, ∀ t : ℝ,
    Fintype.card D.ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p w t))
  hpar : ∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
    covDerivAlong (I := I) g (radialCurve (I := I) g p w) (D.F w i) t = 0
  hON : ∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
    g.inner (radialCurve (I := I) g p w t) (D.F w i t) (D.F w j t) =
      if i = j then (1 : ℝ) else 0
  hFdiff : ∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
    DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p w) (D.F w i) t) t
  hinit : ∀ k : Fin (Module.finrank ℝ E),
    Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A
  hmodelLe : A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * Bhi
  hmodelGe : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
    a * Blo ≤ Real.sqrt
        (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
          (a • (∑ i, v i • (chartModelBasis E) i))) -
        gronwallBound 0 (max K 1)
          (K * (b * Real.sqrt
            (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
              (a • (∑ i, v i • (chartModelBasis E) i))))) 1



omit [T2Space M] [SigmaCompactSpace M] in
lemma IsRm04VolHyp.radialC2
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {p : M}
    {R b ρ a K Rm Vb A B s : ℝ} {D : Rm04FrameData (I := I) g p R b}
    (H : IsRm04VolHyp (I := I) g p D ρ a K Rm Vb A B s) :
    ∀ w ∈ Metric.ball (0 : E) R,
      ContMDiffOn 𝓘(ℝ, ℝ) I (2 : ℕ∞)
        (radialCurve (I := I) g p w) (Set.Icc (0 : ℝ) b) :=
  radialC2OnBallIcc (I := I) g p H.hRC2 H.hb1



omit [T2Space M] [SigmaCompactSpace M] in
lemma IsRm04VolPairHyp.radialC2
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {p : M}
    {R b ρ a K Rm Vb A Blo Bhi s : ℝ} {D : Rm04FrameData (I := I) g p R b}
    (H : IsRm04VolPairHyp (I := I) g p D ρ a K Rm Vb A Blo Bhi s) :
    ∀ w ∈ Metric.ball (0 : E) R,
      ContMDiffOn 𝓘(ℝ, ℝ) I (2 : ℕ∞)
        (radialCurve (I := I) g p w) (Set.Icc (0 : ℝ) b) :=
  radialC2OnBallIcc (I := I) g p H.hRC2 H.hb1



omit [T2Space M] [SigmaCompactSpace M] in
lemma radialC1AtBall
    (g : SmoothRiemannianMetric I M) (p : M) {R b : ℝ}
    (hR : R ≤ expMapC2Radius (I := I) g p) (hb : b ≤ 1) :
    ∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p w) t := by
  intro w hw t ht
  have hwR : ‖w‖ < R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  exact (radialCurve_contMDiffAt_Icc (I := I) g p w hb (hwR.trans_le hR) t ht).of_le
    (by norm_num)




omit [T2Space M] [SigmaCompactSpace M] in
lemma exists_rm04_hyp
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M)
    {R b ρ a K Rm Vb A B s : ℝ}
    (hBnn : 0 ≤ B) (ha : 0 < a) (hK : 0 ≤ K)
    (hRm_nonneg : 0 ≤ Rm) (hVb : 0 ≤ Vb)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (h1b : (1 : ℝ) ≤ b)
    (hRpos : 0 < R) (hRρ : R ≤ ρ)
    (hRC2 : R ≤ expMapC2Radius (I := I) g p)
    (hρball : ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ)
    (hgs : ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s)
    (hsR : s < R) (hsρ : s < ρ)
    (hsdiv : s / Real.sqrt (gpCoerciveConst (I := I) g p) < R)
    (hsmallBasis : ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ)
    (hsmallDir : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ)
    (hlaunch : ∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb)
    (hKbound : Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
        Rm * Vb ^ 2 ≤ K)
    (hRm : ∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p w t) 4
        (DifferentialGeometry.Integral.Connection.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm)
    (hinit : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A)
    (hmodelLe : A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B)
    (hmodelGe : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      a * B ≤ Real.sqrt
          (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
            (a • (∑ i, v i • (chartModelBasis E) i))) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                (a • (∑ i, v i • (chartModelBasis E) i))))) 1) :
    ∃ D : Rm04FrameData (I := I) g p R b,
      IsRm04VolHyp (I := I) g p D ρ a K Rm Vb A B s := by
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one h1b
  obtain ⟨D, hcard, hpar, hON, hFdiff⟩ :=
    exists_rm04FrameData_radius (I := I) g p hb hb1 hRC2
  exact ⟨D, {
    hBnn := hBnn
    ha := ha
    hK := hK
    hRm_nonneg := hRm_nonneg
    hVb := hVb
    hb0 := hb0
    hb1 := hb1
    h1b := h1b
    hRpos := hRpos
    hRρ := hRρ
    hRC2 := hRC2
    hρball := hρball
    hgs := hgs
    hsR := hsR
    hsρ := hsρ
    hsdiv := hsdiv
    hsmallBasis := hsmallBasis
    hsmallDir := hsmallDir
    hlaunch := hlaunch
    hKbound := hKbound
    hRm := hRm
    hγ := radialC1AtBall (I := I) g p hRC2 hb1
    hcard := hcard
    hpar := hpar
    hON := hON
    hFdiff := hFdiff
    hinit := hinit
    hmodelLe := hmodelLe
    hmodelGe := hmodelGe }⟩



omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma scalarModel_smul
    (g : SmoothRiemannianMetric I M) (p : M)
    {a K b A B : ℝ} (ha : 0 < a)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A)
    (hmodelLe : A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B)
    (hmodelGe : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ≤ Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (∑ i, v i • (chartModelBasis E) i)
                (∑ i, v i • (chartModelBasis E) i)))) 1) :
    (∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤
        a * A) ∧
    a * A + gronwallBound 0 (max K 1) (K * (b * (a * A))) 1 ≤ a * B ∧
    (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      a * B ≤ Real.sqrt
          (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
            (a • (∑ i, v i • (chartModelBasis E) i))) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                (a • (∑ i, v i • (chartModelBasis E) i))))) 1) := by
  obtain ⟨hinit, hle⟩ := basisModel_le_smul (I := I) g p ha hbasis hmodelLe
  exact ⟨hinit, hle, dirModel_ge_smul (I := I) g p ha hmodelGe⟩



omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma scalarModel_pair_smul
    (g : SmoothRiemannianMetric I M) (p : M)
    {a K b A Blo Bhi : ℝ} (ha : 0 < a)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A)
    (hmodelLe : A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ Bhi)
    (hmodelGe : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      Blo ≤ Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (∑ i, v i • (chartModelBasis E) i)
                (∑ i, v i • (chartModelBasis E) i)))) 1) :
    (∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤
        a * A) ∧
    a * A + gronwallBound 0 (max K 1) (K * (b * (a * A))) 1 ≤ a * Bhi ∧
    (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      a * Blo ≤ Real.sqrt
          (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
            (a • (∑ i, v i • (chartModelBasis E) i))) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                (a • (∑ i, v i • (chartModelBasis E) i))))) 1) := by
  obtain ⟨hinit, hle⟩ := basisModel_le_smul (I := I) g p ha hbasis hmodelLe
  exact ⟨hinit, hle, dirModel_ge_smul (I := I) g p ha hmodelGe⟩






omit [T2Space M] [SigmaCompactSpace M] in
lemma exists_rm04_scalar
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M)
    {R b ρ a K Rm Vb A B s : ℝ}
    (hBnn : 0 ≤ B) (ha : 0 < a) (hK : 0 ≤ K)
    (hRm_nonneg : 0 ≤ Rm) (hVb : 0 ≤ Vb)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (h1b : (1 : ℝ) ≤ b)
    (hRpos : 0 < R) (hRρ : R ≤ ρ)
    (hRC2 : R ≤ expMapC2Radius (I := I) g p)
    (hρball : ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ)
    (hgs : ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s)
    (hsR : s < R) (hsρ : s < ρ)
    (hsdiv : s / Real.sqrt (gpCoerciveConst (I := I) g p) < R)
    (hsmallBasis : ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ)
    (hsmallDir : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ)
    (hlaunch : ∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb)
    (hKbound : Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
        Rm * Vb ^ 2 ≤ K)
    (hRm : ∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p w t) 4
        (DifferentialGeometry.Integral.Connection.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A)
    (hmodelLe : A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B)
    (hmodelGe : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ≤ Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (∑ i, v i • (chartModelBasis E) i)
                (∑ i, v i • (chartModelBasis E) i)))) 1) :
    ∃ D : Rm04FrameData (I := I) g p R b,
      IsRm04VolHyp (I := I) g p D ρ a K Rm Vb (a * A) B s := by
  obtain ⟨hinit, hmodelLe', hmodelGe'⟩ :=
    scalarModel_smul (I := I) g p ha hbasis hmodelLe hmodelGe
  exact exists_rm04_hyp (I := I) g p hBnn ha hK hRm_nonneg hVb hb0 hb1 h1b
    hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv hsmallBasis hsmallDir hlaunch
    hKbound hRm hinit hmodelLe' hmodelGe'



omit [T2Space M] [SigmaCompactSpace M] in
lemma exists_rm04_pair_hyp
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M)
    {R b ρ a K Rm Vb A Blo Bhi s : ℝ}
    (hBlo : 0 ≤ Blo) (hBhi : 0 ≤ Bhi) (ha : 0 < a) (hK : 0 ≤ K)
    (hRm_nonneg : 0 ≤ Rm) (hVb : 0 ≤ Vb)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (h1b : (1 : ℝ) ≤ b)
    (hRpos : 0 < R) (hRρ : R ≤ ρ)
    (hRC2 : R ≤ expMapC2Radius (I := I) g p)
    (hρball : ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ)
    (hgs : ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s)
    (hsR : s < R) (hsρ : s < ρ)
    (hsdiv : s / Real.sqrt (gpCoerciveConst (I := I) g p) < R)
    (hsmallBasis : ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ)
    (hsmallDir : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ)
    (hlaunch : ∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb)
    (hKbound : Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
        Rm * Vb ^ 2 ≤ K)
    (hRm : ∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p w t) 4
        (DifferentialGeometry.Integral.Connection.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm)
    (hinit : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A)
    (hmodelLe : A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * Bhi)
    (hmodelGe : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      a * Blo ≤ Real.sqrt
          (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
            (a • (∑ i, v i • (chartModelBasis E) i))) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                (a • (∑ i, v i • (chartModelBasis E) i))))) 1) :
    ∃ D : Rm04FrameData (I := I) g p R b,
      IsRm04VolPairHyp (I := I) g p D ρ a K Rm Vb A Blo Bhi s := by
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one h1b
  obtain ⟨D, hcard, hpar, hON, hFdiff⟩ :=
    exists_rm04FrameData_radius (I := I) g p hb hb1 hRC2
  exact ⟨D, {
    hBlo := hBlo
    hBhi := hBhi
    ha := ha
    hK := hK
    hRm_nonneg := hRm_nonneg
    hVb := hVb
    hb0 := hb0
    hb1 := hb1
    h1b := h1b
    hRpos := hRpos
    hRρ := hRρ
    hRC2 := hRC2
    hρball := hρball
    hgs := hgs
    hsR := hsR
    hsρ := hsρ
    hsdiv := hsdiv
    hsmallBasis := hsmallBasis
    hsmallDir := hsmallDir
    hlaunch := hlaunch
    hKbound := hKbound
    hRm := hRm
    hγ := radialC1AtBall (I := I) g p hRC2 hb1
    hcard := hcard
    hpar := hpar
    hON := hON
    hFdiff := hFdiff
    hinit := hinit
    hmodelLe := hmodelLe
    hmodelGe := hmodelGe }⟩




omit [T2Space M] [SigmaCompactSpace M] in
lemma exists_rm04_pair_scalar
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M)
    {R b ρ a K Rm Vb A Blo Bhi s : ℝ}
    (hBlo : 0 ≤ Blo) (hBhi : 0 ≤ Bhi) (ha : 0 < a) (hK : 0 ≤ K)
    (hRm_nonneg : 0 ≤ Rm) (hVb : 0 ≤ Vb)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (h1b : (1 : ℝ) ≤ b)
    (hRpos : 0 < R) (hRρ : R ≤ ρ)
    (hRC2 : R ≤ expMapC2Radius (I := I) g p)
    (hρball : ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ)
    (hgs : ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s)
    (hsR : s < R) (hsρ : s < ρ)
    (hsdiv : s / Real.sqrt (gpCoerciveConst (I := I) g p) < R)
    (hsmallBasis : ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ)
    (hsmallDir : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ)
    (hlaunch : ∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb)
    (hKbound : Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
        Rm * Vb ^ 2 ≤ K)
    (hRm : ∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p w t) 4
        (DifferentialGeometry.Integral.Connection.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A)
    (hmodelLe : A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ Bhi)
    (hmodelGe : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      Blo ≤ Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (∑ i, v i • (chartModelBasis E) i)
                (∑ i, v i • (chartModelBasis E) i)))) 1) :
    ∃ D : Rm04FrameData (I := I) g p R b,
      IsRm04VolPairHyp (I := I) g p D ρ a K Rm Vb (a * A) Blo Bhi s := by
  obtain ⟨hinit, hmodelLe', hmodelGe'⟩ :=
    scalarModel_pair_smul (I := I) g p ha hbasis hmodelLe hmodelGe
  exact exists_rm04_pair_hyp (I := I) g p hBlo hBhi ha hK hRm_nonneg hVb hb0 hb1 h1b
    hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv hsmallBasis hsmallDir hlaunch
    hKbound hRm hinit hmodelLe' hmodelGe'





omit [T2Space M] [SigmaCompactSpace M] in
lemma exists_rm04_scale
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M)
    {R b ρ K Rm Vb A B s : ℝ}
    (D : Rm04FrameData (I := I) g p R b) (hρ : 0 < ρ)
    (H : ∀ a : ℝ, 0 < a →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ) →
      IsRm04VolHyp (I := I) g p D ρ a K Rm Vb A B s) :
    ∃ a : ℝ, IsRm04VolHyp (I := I) g p D ρ a K Rm Vb A B s := by
  obtain ⟨a, ha, hsmallBasis, hsmallDir⟩ := basisUnitScaleSmall (E := E) hρ
  exact ⟨a, H a ha hsmallBasis hsmallDir⟩


omit [T2Space M] [SigmaCompactSpace M] in
lemma exists_rm04_pair_scale
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M)
    {R b ρ K Rm Vb A Blo Bhi s : ℝ}
    (D : Rm04FrameData (I := I) g p R b) (hρ : 0 < ρ)
    (H : ∀ a : ℝ, 0 < a →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ) →
      IsRm04VolPairHyp (I := I) g p D ρ a K Rm Vb A Blo Bhi s) :
    ∃ a : ℝ, IsRm04VolPairHyp (I := I) g p D ρ a K Rm Vb A Blo Bhi s := by
  obtain ⟨a, ha, hsmallBasis, hsmallDir⟩ := basisUnitScaleSmall (E := E) hρ
  exact ⟨a, H a ha hsmallBasis hsmallDir⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_vol_two_rm04_at
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {a K Rm Vb b A B R s : ℝ},
      0 ≤ B → 0 < a → 0 ≤ K → 0 ≤ Rm → 0 ≤ Vb → 0 ≤ b →
      b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R →
      R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb) →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * Vb ^ 2 ≤ K →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b,
        ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p w) t) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p w t))) →
      (F : ∀ w : E, ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p w t)) →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p w) (F w i) t = 0) →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p w t) (F w i t) (F w j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p w) (F w i) t) t) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a * B ≤ Real.sqrt
            (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
              (a • (∑ i, v i • (chartModelBasis E) i))) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                  (a • (∑ i, v i • (chartModelBasis E) i))))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρvol, hρvol_pos, hvol⟩ := exists_vol_two_dens (I := I) (M := M) g hEnorm p
  obtain ⟨ρdens, hρdens_pos, hdens⟩ := exists_dens_two_rm04_at (I := I) g hEnorm p
  refine ⟨min ρvol ρdens, lt_min hρvol_pos hρdens_pos, ?_⟩
  intro a K Rm Vb b A B R s hBnn ha hK hRm_nonneg hVb hb0 hb1 h1b hRpos hRρ
    hRC2 hρball hgs hsR hsρ hsdiv hsmallBasis hsmallDir hlaunch hKbound hRm hγ
    ι _ _ _ hcard F hpar hON hFdiff hinit hmodelLe hmodelGe
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  letI : Fintype ι := ‹Fintype ι›
  letI : DecidableEq ι := ‹DecidableEq ι›
  letI : Nonempty ι := ‹Nonempty ι›
  have hρvol_ball : ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρvol :=
    fun w hw => lt_of_lt_of_le (hρball w hw) (min_le_left _ _)
  have hsρvol : s < ρvol := lt_of_lt_of_le hsρ (min_le_left _ _)
  have hsmallBasis_dens :
      ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρdens :=
    fun k => lt_of_lt_of_le (hsmallBasis k) (min_le_right _ _)
  have hsmallDir_dens :
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρdens :=
    fun v hv => lt_of_lt_of_le (hsmallDir v hv) (min_le_right _ _)
  have hdensPair : ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p w ∧
        normalChartDensity (I := I) g p w ≤
          Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E) := by
    intro w hw
    have hwR : ‖w‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hwdens : ‖w‖ < ρdens :=
      lt_of_lt_of_le hwR (le_trans hRρ (min_le_right ρvol ρdens))
    have hwsrc : w ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source :=
      ball_src_of_radius (I := I) g p hRC2 hw
    have hwrad : ‖w‖ < expMapC2Radius (I := I) g p :=
      lt_of_lt_of_le hwR hRC2
    exact hdens w hwdens hBnn ha hK hVb hb0 hb1 h1b hsmallBasis_dens hsmallDir_dens
      (hlaunch w hw) hKbound (hRm w hw) hwsrc hwrad (hγ w hw)
      (hcard w hw) (F w) (fun i t ht => hpar w hw i t ht)
      (fun t ht i j => hON w hw t ht i j)
      (fun i t ht => hFdiff w hw i t ht) hinit hmodelLe hmodelGe
  exact hvol hRpos hRC2 hρvol_ball hgs
    (fun w hw => (hdensPair w hw).1)
    hsR hsρvol hsdiv
    (fun w hw => (hdensPair w hw).2)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_vol_pair_rm04_at
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {a K Rm Vb b A Blo Bhi R s : ℝ},
      0 ≤ Blo → 0 ≤ Bhi → 0 < a → 0 ≤ K → 0 ≤ Rm → 0 ≤ Vb → 0 ≤ b →
      b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R →
      R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb) →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * Vb ^ 2 ≤ K →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b,
        ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p w) t) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p w t))) →
      (F : ∀ w : E, ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p w t)) →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p w) (F w i) t = 0) →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p w t) (F w i t) (F w j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p w) (F w i) t) t) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a * Blo ≤ Real.sqrt
            (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
              (a • (∑ i, v i • (chartModelBasis E) i))) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                  (a • (∑ i, v i • (chartModelBasis E) i))))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρvol, hρvol_pos, hvol⟩ := exists_vol_two_dens (I := I) (M := M) g hEnorm p
  obtain ⟨ρdens, hρdens_pos, hdens⟩ := exists_dens_pair_rm04_at (I := I) g hEnorm p
  refine ⟨min ρvol ρdens, lt_min hρvol_pos hρdens_pos, ?_⟩
  intro a K Rm Vb b A Blo Bhi R s hBlo hBhi ha hK hRm_nonneg hVb hb0 hb1 h1b
    hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv hsmallBasis hsmallDir hlaunch
    hKbound hRm hγ ι _ _ _ hcard F hpar hON hFdiff hinit hmodelLe hmodelGe
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  letI : Fintype ι := ‹Fintype ι›
  letI : DecidableEq ι := ‹DecidableEq ι›
  letI : Nonempty ι := ‹Nonempty ι›
  have hρvol_ball : ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρvol :=
    fun w hw => lt_of_lt_of_le (hρball w hw) (min_le_left _ _)
  have hsρvol : s < ρvol := lt_of_lt_of_le hsρ (min_le_left _ _)
  have hsmallBasis_dens :
      ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρdens :=
    fun k => lt_of_lt_of_le (hsmallBasis k) (min_le_right _ _)
  have hsmallDir_dens :
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρdens :=
    fun v hv => lt_of_lt_of_le (hsmallDir v hv) (min_le_right _ _)
  have hdensPair : ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p w ∧
        normalChartDensity (I := I) g p w ≤
          Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E) := by
    intro w hw
    have hwR : ‖w‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hwdens : ‖w‖ < ρdens :=
      lt_of_lt_of_le hwR (le_trans hRρ (min_le_right ρvol ρdens))
    have hwsrc : w ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source :=
      ball_src_of_radius (I := I) g p hRC2 hw
    have hwrad : ‖w‖ < expMapC2Radius (I := I) g p :=
      lt_of_lt_of_le hwR hRC2
    exact hdens w hwdens hBlo hBhi ha hK hVb hb0 hb1 h1b hsmallBasis_dens hsmallDir_dens
      (hlaunch w hw) hKbound (hRm w hw) hwsrc hwrad (hγ w hw)
      (hcard w hw) (F w) (fun i t ht => hpar w hw i t ht)
      (fun t ht i j => hON w hw t ht i j)
      (fun i t ht => hFdiff w hw i t ht) hinit hmodelLe hmodelGe
  exact hvol hRpos hRC2 hρvol_ball hgs
    (fun w hw => (hdensPair w hw).1)
    hsR hsρvol hsdiv
    (fun w hw => (hdensPair w hw).2)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





theorem exists_pairR_rm04_at
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {a K Rm Vb b A Blo Bhi Rlo Rup s : ℝ},
      0 ≤ Blo → 0 ≤ Bhi → 0 < a → 0 ≤ K → 0 ≤ Rm → 0 ≤ Vb → 0 ≤ b →
      b ≤ 1 → (1 : ℝ) ≤ b →
      0 < Rlo → Rlo ≤ ρ → Rlo ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) Rlo,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) Rlo,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      0 < Rup → Rup ≤ ρ → Rup ≤ expMapC2Radius (I := I) g p →
      s < Rup →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < Rup →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ) →
      (∀ w, w ∈ Metric.ball (0 : E) Rlo ∨ w ∈ Metric.ball (0 : E) Rup →
        Real.sqrt (g.inner p w w) ≤ Vb) →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * Vb ^ 2 ≤ K →
      (∀ w, w ∈ Metric.ball (0 : E) Rlo ∨ w ∈ Metric.ball (0 : E) Rup →
        ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
            (radialCurve (I := I) g p w t) 4
            (DifferentialGeometry.Integral.Connection.metricRm04At
              (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ w, w ∈ Metric.ball (0 : E) Rlo ∨ w ∈ Metric.ball (0 : E) Rup →
        ∀ t ∈ Set.Icc (0 : ℝ) b,
          ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p w) t) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ w, w ∈ Metric.ball (0 : E) Rlo ∨ w ∈ Metric.ball (0 : E) Rup →
        ∀ t : ℝ,
          Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p w t))) →
      (F : ∀ w : E, ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p w t)) →
      (∀ w, w ∈ Metric.ball (0 : E) Rlo ∨ w ∈ Metric.ball (0 : E) Rup →
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
          covDerivAlong (I := I) g (radialCurve (I := I) g p w) (F w i) t = 0) →
      (∀ w, w ∈ Metric.ball (0 : E) Rlo ∨ w ∈ Metric.ball (0 : E) Rup →
        ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
          g.inner (radialCurve (I := I) g p w t) (F w i t) (F w j t) =
            if i = j then (1 : ℝ) else 0) →
      (∀ w, w ∈ Metric.ball (0 : E) Rlo ∨ w ∈ Metric.ball (0 : E) Rup →
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
          DifferentiableAt ℝ
            (chartRepAt (I := I) (radialCurve (I := I) g p w) (F w i) t) t) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a * Blo ≤ Real.sqrt
            (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
              (a • (∑ i, v i • (chartModelBasis E) i))) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                  (a • (∑ i, v i • (chartModelBasis E) i))))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (Rlo ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (Rup ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρvol, hρvol_pos, hvol⟩ := exists_vol_two_dens_pairR (I := I) (M := M) g hEnorm p
  obtain ⟨ρdens, hρdens_pos, hdens⟩ := exists_dens_pair_rm04_at (I := I) g hEnorm p
  refine ⟨min ρvol ρdens, lt_min hρvol_pos hρdens_pos, ?_⟩
  intro a K Rm Vb b A Blo Bhi Rlo Rup s hBlo hBhi ha hK hRm_nonneg hVb hb0 hb1
    h1b hRlo_pos hRloρ hRloC2 hρlo_ball hgs hRup_pos hRupρ hRupC2 hsRup hsρ hsdiv
    hsmallBasis hsmallDir hlaunch hKbound hRm hγ ι _ _ _ hcard F hpar hON hFdiff
    hinit hmodelLe hmodelGe
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  letI : Fintype ι := ‹Fintype ι›
  letI : DecidableEq ι := ‹DecidableEq ι›
  letI : Nonempty ι := ‹Nonempty ι›
  have hρvol_ball : ∀ w ∈ Metric.ball (0 : E) Rlo,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρvol :=
    fun w hw => lt_of_lt_of_le (hρlo_ball w hw) (min_le_left _ _)
  have hsρvol : s < ρvol := lt_of_lt_of_le hsρ (min_le_left _ _)
  have hsmallBasis_dens :
      ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρdens :=
    fun k => lt_of_lt_of_le (hsmallBasis k) (min_le_right _ _)
  have hsmallDir_dens :
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρdens :=
    fun v hv => lt_of_lt_of_le (hsmallDir v hv) (min_le_right _ _)
  have hdensLower : ∀ w ∈ Metric.ball (0 : E) Rlo,
      Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p w := by
    intro w hw
    have hwR : ‖w‖ < Rlo := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hwdens : ‖w‖ < ρdens :=
      lt_of_lt_of_le hwR (le_trans hRloρ (min_le_right ρvol ρdens))
    have hwsrc : w ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source :=
      ball_src_of_radius (I := I) g p hRloC2 hw
    have hwrad : ‖w‖ < expMapC2Radius (I := I) g p := lt_of_lt_of_le hwR hRloC2
    exact (hdens w hwdens hBlo hBhi ha hK hVb hb0 hb1 h1b hsmallBasis_dens
      hsmallDir_dens (hlaunch w (Or.inl hw)) hKbound (hRm w (Or.inl hw)) hwsrc hwrad
      (hγ w (Or.inl hw)) (hcard w (Or.inl hw)) (F w)
      (fun i t ht => hpar w (Or.inl hw) i t ht)
      (fun t ht i j => hON w (Or.inl hw) t ht i j)
      (fun i t ht => hFdiff w (Or.inl hw) i t ht) hinit hmodelLe hmodelGe).1
  have hdensUpper : ∀ w ∈ Metric.ball (0 : E) Rup,
      normalChartDensity (I := I) g p w ≤
        Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
          (Bhi * Bhi) ^ Module.finrank ℝ E) := by
    intro w hw
    have hwR : ‖w‖ < Rup := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hwdens : ‖w‖ < ρdens :=
      lt_of_lt_of_le hwR (le_trans hRupρ (min_le_right ρvol ρdens))
    have hwsrc : w ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source :=
      ball_src_of_radius (I := I) g p hRupC2 hw
    have hwrad : ‖w‖ < expMapC2Radius (I := I) g p := lt_of_lt_of_le hwR hRupC2
    exact (hdens w hwdens hBlo hBhi ha hK hVb hb0 hb1 h1b hsmallBasis_dens
      hsmallDir_dens (hlaunch w (Or.inr hw)) hKbound (hRm w (Or.inr hw)) hwsrc hwrad
      (hγ w (Or.inr hw)) (hcard w (Or.inr hw)) (F w)
      (fun i t ht => hpar w (Or.inr hw) i t ht)
      (fun t ht i j => hON w (Or.inr hw) t ht i j)
      (fun i t ht => hFdiff w (Or.inr hw) i t ht) hinit hmodelLe hmodelGe).2
  exact hvol hRlo_pos hRloC2 hρvol_ball hgs hdensLower hRup_pos hsRup hsρvol hsdiv
    hdensUpper

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in







theorem exists_pairR_rglobal
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ {Rm b A Blo Bhi Rlo Rup s : ℝ},
      0 ≤ Blo → 0 ≤ Bhi → 0 ≤ Rm → 0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < Rlo → 0 < Rup → Rlo ≤ Rup → Rup ≤ ρ →
      Rup ≤ expMapC2Radius (I := I) g p →
      C * Rlo < ρ →
      C * Rlo < s →
      s < Rup →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < Rup →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * Rup) ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * Rup) ^ 2) * (b * A)) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * (C * Rup) ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * (C * Rup) ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (Rlo ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (Rup ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_pairR_rm04_at (I := I) (M := M) g hEnorm p
  obtain ⟨C, hC, hlaunchC⟩ := exists_metric_upper_launch_const (I := I) g p
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro Rm b A Blo Bhi Rlo Rup s hBlo hBhi hRm_nonneg hb0 hb1 h1b hRlo_pos
    hRup_pos hRlo_le_Rup hRupρ hRupC2 hCRloρ hCRlo_s hsRup hsρ hsdiv
    hRmGlobal hbasis hmodelLe hmodelGe
  let K : ℝ :=
    Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
      Rm * (C * Rup) ^ 2
  let Vb : ℝ := C * Rup
  have hK : 0 ≤ K := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hRm_nonneg) (sq_nonneg (C * Rup))
  have hVb : 0 ≤ Vb := mul_nonneg hC.le hRup_pos.le
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one h1b
  obtain ⟨a, ha, hsmallBasis, hsmallDir⟩ := basisUnitScaleSmall (E := E) hρ
  obtain ⟨hinit, hmodelLe', hmodelGe'⟩ :=
    scalarModel_pair_smul (I := I) g p (a := a) (K := K) (b := b) (A := A)
      (Blo := Blo) (Bhi := Bhi) ha hbasis
      (by simpa [K] using hmodelLe)
      (by
        intro v hv
        simpa [K] using hmodelGe v hv)
  obtain ⟨D, hcard, hpar, hON, hFdiff⟩ :=
    exists_rm04FrameData_radius.{_, _, _, 0} (I := I) g p hb hb1 hRupC2
  have hRloρ : Rlo ≤ ρ := hRlo_le_Rup.trans hRupρ
  have hRloC2 : Rlo ≤ expMapC2Radius (I := I) g p := hRlo_le_Rup.trans hRupC2
  have hmemRup : ∀ w,
      w ∈ Metric.ball (0 : E) Rlo ∨ w ∈ Metric.ball (0 : E) Rup →
        w ∈ Metric.ball (0 : E) Rup := by
    intro w hw
    rcases hw with hwlo | hwup
    · have hwnorm : ‖w‖ < Rlo := by
        simpa [Metric.mem_ball, dist_eq_norm] using hwlo
      have hwnorm_up : ‖w‖ < Rup := lt_of_lt_of_le hwnorm hRlo_le_Rup
      simpa [Metric.mem_ball, dist_eq_norm] using hwnorm_up
    · exact hwup
  have hρlo_ball : ∀ w ∈ Metric.ball (0 : E) Rlo,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ := by
    intro w hw
    exact lt_of_le_of_lt (hlaunchC hRlo_pos.le w hw) hCRloρ
  have hgs : ∀ w ∈ Metric.ball (0 : E) Rlo,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s := by
    intro w hw
    exact lt_of_le_of_lt (hlaunchC hRlo_pos.le w hw) hCRlo_s
  have hlaunch : ∀ w, w ∈ Metric.ball (0 : E) Rlo ∨ w ∈ Metric.ball (0 : E) Rup →
      Real.sqrt (g.inner p w w) ≤ Vb := by
    intro w hw
    exact hlaunchC hRup_pos.le w (hmemRup w hw)
  have hKbound :
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * Vb ^ 2 ≤ K := by
    rfl
  have hRm : ∀ w, w ∈ Metric.ball (0 : E) Rlo ∨ w ∈ Metric.ball (0 : E) Rup →
      ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm := by
    intro w _ t _
    exact hRmGlobal (radialCurve (I := I) g p w t)
  have hγ : ∀ w, w ∈ Metric.ball (0 : E) Rlo ∨ w ∈ Metric.ball (0 : E) Rup →
      ∀ t ∈ Set.Icc (0 : ℝ) b,
        ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p w) t := by
    intro w hw
    exact radialC1AtBall (I := I) g p hRupC2 hb1 w (hmemRup w hw)
  letI : Fintype D.ι := D.fintype
  letI : DecidableEq D.ι := D.decidableEq
  letI : Nonempty D.ι := D.nonempty
  exact hvol (a := a) (K := K) (Rm := Rm) (Vb := Vb) (b := b) (A := a * A)
    (Blo := Blo) (Bhi := Bhi) (Rlo := Rlo) (Rup := Rup) (s := s)
    hBlo hBhi ha hK hRm_nonneg hVb hb0 hb1 h1b hRlo_pos hRloρ hRloC2
    hρlo_ball hgs hRup_pos hRupρ hRupC2 hsRup hsρ hsdiv hsmallBasis hsmallDir
    hlaunch hKbound hRm hγ (ι := D.ι) (fun w hw t => hcard w (hmemRup w hw) t) D.F
    (fun w hw i t ht => hpar w (hmemRup w hw) i t ht)
    (fun w hw t ht i j => hON w (hmemRup w hw) t ht i j)
    (fun w hw i t ht => hFdiff w (hmemRup w hw) i t ht)
    hinit hmodelLe' hmodelGe'

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in







theorem exists_pairR_rm1
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ C κ Blo : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < Blo ∧
      ∀ {Rm A Rlo Rup s : ℝ},
        0 ≤ Rm →
        0 < Rlo → 0 < Rup → Rlo ≤ Rup → Rup ≤ ρ →
        Rup ≤ expMapC2Radius (I := I) g p →
        C * Rlo < ρ →
        C * Rlo < s →
        s < Rup →
        s < ρ →
        s / Real.sqrt (gpCoerciveConst (I := I) g p) < Rup →
        Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
            Rm * (C * Rup) ^ 2 ≤ κ →
        (∀ q : M,
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
            (DifferentialGeometry.Integral.Connection.metricRm04At
              (I := I) (M := M) g q)) ≤ Rm) →
        (∀ k : Fin (Module.finrank ℝ E),
          Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
        let Bhi : ℝ :=
          max
            (A + gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * (C * Rup) ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * (C * Rup) ^ 2) * A) 1)
            0
        letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
        ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
            (ENNReal.ofReal (Rlo ^ Module.finrank ℝ E) *
              (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
          riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
          ENNReal.ofReal
            (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
              (Bhi * Bhi) ^ Module.finrank ℝ E)) *
            (ENNReal.ofReal (Rup ^ Module.finrank ℝ E) *
              (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, C, hρ, hC, hvol⟩ := exists_pairR_rglobal (I := I) (M := M) g hEnorm p
  obtain ⟨κ, Blo, hκ, hBlo, hmodelGe⟩ := exists_dirModel_ge1 (I := I) g p
  refine ⟨ρ, C, κ, Blo, hρ, hC, hκ, hBlo, ?_⟩
  intro Rm A Rlo Rup s hRm_nonneg hRlo_pos hRup_pos hRlo_le_Rup hRupρ hRupC2
    hCRloρ hCRlo_s hsRup hsρ hsdiv hKcap hRmGlobal hbasis
  let K : ℝ :=
    Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
      Rm * (C * Rup) ^ 2
  let Bhi : ℝ :=
    max
      (A + gronwallBound 0
        (max K 1)
        (K * A) 1)
      0
  have hBhi : 0 ≤ Bhi := by
    dsimp [Bhi]
    exact le_max_right _ _
  have hmodelLe :
      A + gronwallBound 0 (max K 1) (K * ((1 : ℝ) * A)) 1 ≤ Bhi := by
    dsimp [Bhi]
    simp [one_mul, le_max_left
      (A + gronwallBound 0 (max K 1) (K * A) 1) (0 : ℝ)
    ]
  have hK_nonneg : 0 ≤ K := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hRm_nonneg) (sq_nonneg (C * Rup))
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact hvol (Rm := Rm) (b := 1) (A := A) (Blo := Blo) (Bhi := Bhi)
    (Rlo := Rlo) (Rup := Rup) (s := s) hBlo.le hBhi hRm_nonneg zero_le_one
    le_rfl le_rfl hRlo_pos hRup_pos hRlo_le_Rup hRupρ hRupC2 hCRloρ
    hCRlo_s hsRup hsρ hsdiv hRmGlobal hbasis
    (by simpa [K] using hmodelLe)
    (by
      intro v hv
      simpa [K] using hmodelGe hK_nonneg hKcap v hv)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in








theorem exists_pairR_small
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ C κ Blo : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < Blo ∧
      ∀ {Rm A : ℝ},
        0 ≤ Rm →
        (∀ q : M,
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
            (DifferentialGeometry.Integral.Connection.metricRm04At
              (I := I) (M := M) g q)) ≤ Rm) →
        (∀ k : Fin (Module.finrank ℝ E),
          Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ}, 0 < s → s < δ →
          ∃ Rlo Rup : ℝ, 0 < Rlo ∧ 0 < Rup ∧ Rlo ≤ Rup ∧
            let Bhi : ℝ :=
              max
                (A + gronwallBound 0
                  (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                    Rm * (C * Rup) ^ 2) 1)
                  ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                    Rm * (C * Rup) ^ 2) * A) 1)
                0
            letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
            ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
                (ENNReal.ofReal (Rlo ^ Module.finrank ℝ E) *
                  (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
              riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
            riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
              ENNReal.ofReal
                (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
                  (Bhi * Bhi) ^ Module.finrank ℝ E)) *
                (ENNReal.ofReal (Rup ^ Module.finrank ℝ E) *
                  (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, C, κ, Blo, hρ, hC, hκ, hBlo, hvol⟩ :=
    exists_pairR_rm1 (I := I) (M := M) g hEnorm p
  refine ⟨ρ, C, κ, Blo, hρ, hC, hκ, hBlo, ?_⟩
  intro Rm A hRm_nonneg hRmGlobal hbasis
  let S : ℝ :=
    Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) * Rm
  have hρcap_pos : 0 < min ρ (expMapC2Radius (I := I) g p) :=
    lt_min hρ (expMapC2Radius_pos (I := I) g p)
  obtain ⟨Rup, hRup_pos, hRup_cap, _hCRup_cap, hKcap⟩ :=
    exists_radius_coeff_cap (C := C) (κ := κ) (ρ := min ρ (expMapC2Radius (I := I) g p))
      (S := S) hC hκ hρcap_pos
  have hRupρ : Rup ≤ ρ := le_trans (le_of_lt hRup_cap) (min_le_left _ _)
  have hRupC2 : Rup ≤ expMapC2Radius (I := I) g p :=
    le_trans (le_of_lt hRup_cap) (min_le_right _ _)
  have hsc_pos : 0 < Real.sqrt (gpCoerciveConst (I := I) g p) :=
    Real.sqrt_pos.mpr (gpCoerciveConst_pos (I := I) g p)
  let δ : ℝ := min ρ (min Rup (Real.sqrt (gpCoerciveConst (I := I) g p) * Rup))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min hρ (lt_min hRup_pos (mul_pos hsc_pos hRup_pos))
  refine ⟨δ, hδ_pos, ?_⟩
  intro s hs_pos hsδ
  have hsρ : s < ρ := lt_of_lt_of_le hsδ (min_le_left _ _)
  have hs_Rup : s < Rup := by
    have hs_min : s < min Rup (Real.sqrt (gpCoerciveConst (I := I) g p) * Rup) :=
      lt_of_lt_of_le hsδ (min_le_right _ _)
    exact lt_of_lt_of_le hs_min (min_le_left _ _)
  have hs_sqrt_Rup : s < Real.sqrt (gpCoerciveConst (I := I) g p) * Rup := by
    have hs_min : s < min Rup (Real.sqrt (gpCoerciveConst (I := I) g p) * Rup) :=
      lt_of_lt_of_le hsδ (min_le_right _ _)
    exact lt_of_lt_of_le hs_min (min_le_right _ _)
  have hsdiv : s / Real.sqrt (gpCoerciveConst (I := I) g p) < Rup := by
    rw [div_lt_iff₀ hsc_pos]
    simpa [mul_comm] using hs_sqrt_Rup
  obtain ⟨Rlo, hRlo_pos, hRlo_le_Rup, hCRlo_s⟩ :=
    exists_pos_le_mul_lt hC hs_pos hRup_pos
  have hCRloρ : C * Rlo < ρ := lt_trans hCRlo_s hsρ
  refine ⟨Rlo, Rup, hRlo_pos, hRup_pos, hRlo_le_Rup, ?_⟩
  exact hvol (Rm := Rm) (A := A) (Rlo := Rlo) (Rup := Rup) (s := s)
    hRm_nonneg hRlo_pos hRup_pos hRlo_le_Rup hRupρ hRupC2 hCRloρ
    hCRlo_s hs_Rup hsρ hsdiv (by simpa [S, mul_assoc] using hKcap) hRmGlobal hbasis

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in







theorem exists_pairR_scaled
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ C D Blo : ℝ, 0 < C ∧ 0 < D ∧ 0 < Blo ∧
      ∀ {Rm A : ℝ},
        0 ≤ Rm →
        (∀ q : M,
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
            (DifferentialGeometry.Integral.Connection.metricRm04At
              (I := I) (M := M) g q)) ≤ Rm) →
        (∀ k : Fin (Module.finrank ℝ E),
          Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ}, 0 < s → s < δ →
          let Rlo : ℝ := s / (2 * C)
          let Rup : ℝ := D * s
          let Bhi : ℝ :=
            max
              (A + gronwallBound 0
                (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                  Rm * (C * Rup) ^ 2) 1)
                ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                  Rm * (C * Rup) ^ 2) * A) 1)
              0
          letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
          ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
              (ENNReal.ofReal (Rlo ^ Module.finrank ℝ E) *
                (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
            riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
          riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
            ENNReal.ofReal
              (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
                (Bhi * Bhi) ^ Module.finrank ℝ E)) *
              (ENNReal.ofReal (Rup ^ Module.finrank ℝ E) *
                (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, C, κ, Blo, hρ, hC, hκ, hBlo, hvol⟩ :=
    exists_pairR_rm1 (I := I) (M := M) g hEnorm p
  have hsc_pos : 0 < Real.sqrt (gpCoerciveConst (I := I) g p) :=
    Real.sqrt_pos.mpr (gpCoerciveConst_pos (I := I) g p)
  let D : ℝ := 1 + 1 / Real.sqrt (gpCoerciveConst (I := I) g p) + 1 / (2 * C)
  have hD_pos : 0 < D := by
    dsimp [D]
    positivity
  have hD_gt_one : 1 < D := by
    dsimp [D]
    have hinv_sc_pos : 0 < 1 / Real.sqrt (gpCoerciveConst (I := I) g p) :=
      one_div_pos.mpr hsc_pos
    have hinv_C_pos : 0 < 1 / (2 * C) := one_div_pos.mpr (mul_pos zero_lt_two hC)
    linarith
  have hD_gt_inv_sqrt :
      1 / Real.sqrt (gpCoerciveConst (I := I) g p) < D := by
    dsimp [D]
    have hinv_C_pos : 0 < 1 / (2 * C) := one_div_pos.mpr (mul_pos zero_lt_two hC)
    linarith
  have hD_ge_inv_twoC : 1 / (2 * C) ≤ D := by
    dsimp [D]
    have htail_nonneg :
        0 ≤ 1 + 1 / Real.sqrt (gpCoerciveConst (I := I) g p) := by
      positivity
    linarith
  refine ⟨C, D, Blo, hC, hD_pos, hBlo, ?_⟩
  intro Rm A hRm_nonneg hRmGlobal hbasis
  let S : ℝ :=
    Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) * Rm
  let T : ℝ := S * (C * D) ^ 2
  have hS_nonneg : 0 ≤ S := mul_nonneg (Real.sqrt_nonneg _) hRm_nonneg
  have hT_nonneg : 0 ≤ T := mul_nonneg hS_nonneg (sq_nonneg (C * D))
  have hbase_pos :
      0 < min ρ (min (ρ / D) (expMapC2Radius (I := I) g p / D)) := by
    exact lt_min hρ
      (lt_min (div_pos hρ hD_pos) (div_pos (expMapC2Radius_pos (I := I) g p) hD_pos))
  obtain ⟨δ, hδ_pos, hδ_base, hδ_cap⟩ :=
    exists_pos_lt_mul_sq_le (S := T) (κ := κ)
      (ρ := min ρ (min (ρ / D) (expMapC2Radius (I := I) g p / D))) hκ hbase_pos
  refine ⟨δ, hδ_pos, ?_⟩
  intro s hs_pos hsδ
  let Rlo : ℝ := s / (2 * C)
  let Rup : ℝ := D * s
  have hsδ_le : s ≤ δ := le_of_lt hsδ
  have hs_sq_le : s ^ 2 ≤ δ ^ 2 := by
    nlinarith [hs_pos.le, hδ_pos.le, hsδ_le]
  have hT_s_le : T * s ^ 2 ≤ T * δ ^ 2 :=
    mul_le_mul_of_nonneg_left hs_sq_le hT_nonneg
  have hcoef_cap :
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * Rup) ^ 2 ≤ κ := by
    have hcoef_eq :
        Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
            Rm * (C * Rup) ^ 2 = T * s ^ 2 := by
      dsimp [T, S, Rup]
      ring
    rw [hcoef_eq]
    exact hT_s_le.trans hδ_cap
  have hsρ : s < ρ := lt_of_lt_of_le hsδ (le_trans (le_of_lt hδ_base) (min_le_left _ _))
  have hs_ρ_div_D : s < ρ / D := by
    have hmin : s < min (ρ / D) (expMapC2Radius (I := I) g p / D) :=
      lt_of_lt_of_le hsδ (le_trans (le_of_lt hδ_base) (min_le_right _ _))
    exact lt_of_lt_of_le hmin (min_le_left _ _)
  have hs_C2_div_D : s < expMapC2Radius (I := I) g p / D := by
    have hmin : s < min (ρ / D) (expMapC2Radius (I := I) g p / D) :=
      lt_of_lt_of_le hsδ (le_trans (le_of_lt hδ_base) (min_le_right _ _))
    exact lt_of_lt_of_le hmin (min_le_right _ _)
  have hRlo_pos : 0 < Rlo := by
    dsimp [Rlo]
    positivity
  have hRup_pos : 0 < Rup := by
    dsimp [Rup]
    exact mul_pos hD_pos hs_pos
  have hRlo_le_Rup : Rlo ≤ Rup := by
    have hmul := mul_le_mul_of_nonneg_right hD_ge_inv_twoC hs_pos.le
    simpa [Rlo, Rup, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
  have hRupρ : Rup ≤ ρ := by
    have hmul : D * s < ρ := by
      have hmul' := (lt_div_iff₀ hD_pos).mp hs_ρ_div_D
      simpa [mul_comm] using hmul'
    exact le_of_lt (by simpa [Rup] using hmul)
  have hRupC2 : Rup ≤ expMapC2Radius (I := I) g p := by
    have hmul : D * s < expMapC2Radius (I := I) g p := by
      have hmul' := (lt_div_iff₀ hD_pos).mp hs_C2_div_D
      simpa [mul_comm] using hmul'
    exact le_of_lt (by simpa [Rup] using hmul)
  have hCRlo_s : C * Rlo < s := by
    have hCRlo_eq : C * Rlo = s / 2 := by
      rw [show Rlo = s / (2 * C) by rfl]
      field_simp [hC.ne']
    rw [hCRlo_eq]
    linarith
  have hCRloρ : C * Rlo < ρ := lt_trans hCRlo_s hsρ
  have hsRup : s < Rup := by
    have hmul := mul_lt_mul_of_pos_right hD_gt_one hs_pos
    simpa [Rup, one_mul, mul_comm] using hmul
  have hsdiv : s / Real.sqrt (gpCoerciveConst (I := I) g p) < Rup := by
    have hmul := mul_lt_mul_of_pos_right hD_gt_inv_sqrt hs_pos
    simpa [Rup, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
  exact hvol (Rm := Rm) (A := A) (Rlo := Rlo) (Rup := Rup) (s := s)
    hRm_nonneg hRlo_pos hRup_pos hRlo_le_Rup hRupρ hRupC2 hCRloρ hCRlo_s
    hsRup hsρ hsdiv hcoef_cap hRmGlobal hbasis

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





theorem exists_pairR_autoA
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ C D Blo A : ℝ, 0 < C ∧ 0 < D ∧ 0 < Blo ∧
      ∀ {Rm : ℝ},
        0 ≤ Rm →
        (∀ q : M,
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
            (DifferentialGeometry.Integral.Connection.metricRm04At
              (I := I) (M := M) g q)) ≤ Rm) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ}, 0 < s → s < δ →
          let Rlo : ℝ := s / (2 * C)
          let Rup : ℝ := D * s
          let Bhi : ℝ :=
            max
              (A + gronwallBound 0
                (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                  Rm * (C * Rup) ^ 2) 1)
                ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                  Rm * (C * Rup) ^ 2) * A) 1)
              0
          letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
          ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
              (ENNReal.ofReal (Rlo ^ Module.finrank ℝ E) *
                (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
            riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
          riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
            ENNReal.ofReal
              (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
                (Bhi * Bhi) ^ Module.finrank ℝ E)) *
              (ENNReal.ofReal (Rup ^ Module.finrank ℝ E) *
                (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨C, D, Blo, hC, hD, hBlo, hscaled⟩ :=
    exists_pairR_scaled (I := I) (M := M) g hEnorm p
  obtain ⟨A, hA⟩ := exists_basis_upper_const (I := I) g p
  refine ⟨C, D, Blo, A, hC, hD, hBlo, ?_⟩
  intro Rm hRm_nonneg hRmGlobal
  exact hscaled (Rm := Rm) (A := A) hRm_nonneg hRmGlobal hA

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





theorem exists_pairR_bound
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ C D Blo A : ℝ, 0 < C ∧ 0 < D ∧ 0 < Blo ∧
      ∀ {Rm : ℝ},
        0 ≤ Rm →
        Rm04GlobalBound (I := I) (M := M) g Rm →
        ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ}, 0 < s → s < δ →
          let Rlo : ℝ := s / (2 * C)
          let Rup : ℝ := D * s
          let Bhi : ℝ :=
            max
              (A + gronwallBound 0
                (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                  Rm * (C * Rup) ^ 2) 1)
                ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                  Rm * (C * Rup) ^ 2) * A) 1)
              0
          letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
          ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
              (ENNReal.ofReal (Rlo ^ Module.finrank ℝ E) *
                (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
            riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
          riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
            ENNReal.ofReal
              (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
                (Bhi * Bhi) ^ Module.finrank ℝ E)) *
              (ENNReal.ofReal (Rup ^ Module.finrank ℝ E) *
                (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨C, D, Blo, A, hC, hD, hBlo, hvol⟩ :=
    exists_pairR_autoA (I := I) (M := M) g hEnorm p
  refine ⟨C, D, Blo, A, hC, hD, hBlo, ?_⟩
  intro Rm hRm_nonneg hRm
  exact hvol (Rm := Rm) hRm_nonneg (by simpa [Rm04GlobalBound] using hRm)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_vol_rm04_pair_pkg
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {a K Rm Vb b A Blo Bhi R s : ℝ},
      (D : Rm04FrameData (I := I) g p R b) →
      IsRm04VolPairHyp (I := I) g p D ρ a K Rm Vb A Blo Bhi s →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_pair_rm04_at (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro a K Rm Vb b A Blo Bhi R s D H
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  letI : Fintype D.ι := D.fintype
  letI : DecidableEq D.ι := D.decidableEq
  letI : Nonempty D.ι := D.nonempty
  exact hvol H.hBlo H.hBhi H.ha H.hK H.hRm_nonneg H.hVb H.hb0 H.hb1 H.h1b
    H.hRpos H.hRρ H.hRC2 H.hρball H.hgs H.hsR H.hsρ H.hsdiv
    H.hsmallBasis H.hsmallDir H.hlaunch H.hKbound H.hRm H.hγ
    H.hcard D.F H.hpar H.hON H.hFdiff H.hinit H.hmodelLe H.hmodelGe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_vol_pair_scale
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {K Rm Vb b A Blo Bhi R s : ℝ},
      (D : Rm04FrameData (I := I) g p R b) →
      (∀ a : ℝ, 0 < a →
        (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ) →
        (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
          ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ) →
        IsRm04VolPairHyp (I := I) g p D ρ a K Rm Vb A Blo Bhi s) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_rm04_pair_pkg (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro K Rm Vb b A Blo Bhi R s D H
  obtain ⟨a, Ha⟩ := exists_rm04_pair_scale (I := I) g p D hρ H
  exact hvol D Ha

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_vol_pair_scalar
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {K Rm Vb b A Blo Bhi R s : ℝ},
      0 ≤ Blo → 0 ≤ Bhi → 0 ≤ K → 0 ≤ Rm → 0 ≤ Vb →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb) →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * Vb ^ 2 ≤ K →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_rm04_pair_pkg.{_, _, _, 0} (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro K Rm Vb b A Blo Bhi R s hBlo hBhi hK hRm_nonneg hVb hb0 hb1 h1b hRpos hRρ
    hRC2 hρball hgs hsR hsρ hsdiv hlaunch hKbound hRm hbasis hmodelLe hmodelGe
  obtain ⟨a, ha, hsmallBasis, hsmallDir⟩ := basisUnitScaleSmall (E := E) hρ
  obtain ⟨D, H⟩ :=
    exists_rm04_pair_scalar.{_, _, _, 0} (I := I) g p hBlo hBhi ha hK hRm_nonneg hVb
      hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv hsmallBasis hsmallDir
      hlaunch hKbound hRm hbasis hmodelLe hmodelGe
  exact hvol D H

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_vol_pair_launch
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {K Rm b A Blo Bhi R s : ℝ},
      0 ≤ Blo → 0 ≤ Bhi → 0 ≤ K → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ K →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_pair_scalar (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro K Rm b A Blo Bhi R s hBlo hBhi hK hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2
    hρball hgs hsR hsρ hsdiv hKbound hRm hbasis hmodelLe hmodelGe
  let Vb : ℝ := ρ
  have hVb : 0 ≤ Vb := hρ.le
  have hlaunch : ∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb := by
    intro w hw
    exact le_of_lt (by simpa [Vb] using hρball w hw)
  exact hvol (K := K) (Rm := Rm) (Vb := Vb) (b := b) (A := A) (Blo := Blo)
    (Bhi := Bhi) (R := R) (s := s) hBlo hBhi hK hRm_nonneg hVb hb0 hb1 h1b
    hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv hlaunch
    (by simpa [Vb] using hKbound) hRm hbasis hmodelLe hmodelGe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in






theorem exists_pair_rlaunch
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ {K Rm b A Blo Bhi R s : ℝ},
      0 ≤ Blo → 0 ≤ Bhi → 0 ≤ K → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      C * R < ρ →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2 ≤ K →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_pair_scalar (I := I) (M := M) g hEnorm p
  obtain ⟨C, hC, hlaunchC⟩ := exists_metric_upper_launch_const (I := I) g p
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro K Rm b A Blo Bhi R s hBlo hBhi hK hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2
    hCRρ hgs hsR hsρ hsdiv hKbound hRm hbasis hmodelLe hmodelGe
  let Vb : ℝ := C * R
  have hVb : 0 ≤ Vb := mul_nonneg hC.le hRpos.le
  have hlaunch : ∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb := by
    intro w hw
    exact hlaunchC hRpos.le w hw
  have hρball : ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ := by
    intro w hw
    exact lt_of_le_of_lt (hlaunch w hw) (by simpa [Vb] using hCRρ)
  exact hvol (K := K) (Rm := Rm) (Vb := Vb) (b := b) (A := A) (Blo := Blo)
    (Bhi := Bhi) (R := R) (s := s) hBlo hBhi hK hRm_nonneg hVb hb0 hb1 h1b
    hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv hlaunch
    (by simpa [Vb] using hKbound) hRm hbasis hmodelLe hmodelGe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_pair_rcoeff
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ {Rm b A Blo Bhi R s : ℝ},
      0 ≤ Blo → 0 ≤ Bhi → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      C * R < ρ →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) * (b * A)) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * (C * R) ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * (C * R) ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, C, hρ, hC, hvol⟩ := exists_pair_rlaunch (I := I) (M := M) g hEnorm p
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro Rm b A Blo Bhi R s hBlo hBhi hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2
    hCRρ hgs hsR hsρ hsdiv hRm hbasis hmodelLe hmodelGe
  let K : ℝ :=
    Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
      Rm * (C * R) ^ 2
  have hK : 0 ≤ K := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hRm_nonneg) (sq_nonneg (C * R))
  have hKbound :
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2 ≤ K := by
    rfl
  exact hvol (K := K) (Rm := Rm) (b := b) (A := A) (Blo := Blo) (Bhi := Bhi)
    (R := R) (s := s) hBlo hBhi hK hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2
    hCRρ hgs hsR hsρ hsdiv hKbound hRm hbasis (by simpa [K] using hmodelLe)
    (by simpa [K] using hmodelGe)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_pair_rglobal
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ {Rm b A Blo Bhi R s : ℝ},
      0 ≤ Blo → 0 ≤ Bhi → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      C * R < ρ →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) * (b * A)) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * (C * R) ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * (C * R) ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, C, hρ, hC, hvol⟩ := exists_pair_rcoeff (I := I) (M := M) g hEnorm p
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro Rm b A Blo Bhi R s hBlo hBhi hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2
    hCRρ hgs hsR hsρ hsdiv hRmGlobal hbasis hmodelLe hmodelGe
  exact hvol (Rm := Rm) (b := b) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R)
    (s := s) hBlo hBhi hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hCRρ hgs hsR
    hsρ hsdiv (fun w _ t _ => hRmGlobal (radialCurve (I := I) g p w t))
    hbasis hmodelLe hmodelGe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_pair_rglobal1
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ {Rm A Blo Bhi R s : ℝ},
      0 ≤ Blo → 0 ≤ Bhi → 0 ≤ Rm →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      C * R < ρ →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) * A) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * (C * R) ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * (C * R) ^ 2) * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, C, hρ, hC, hvol⟩ := exists_pair_rglobal (I := I) (M := M) g hEnorm p
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro Rm A Blo Bhi R s hBlo hBhi hRm_nonneg hRpos hRρ hRC2 hCRρ hgs hsR hsρ
    hsdiv hRmGlobal hbasis hmodelLe hmodelGe
  exact hvol (Rm := Rm) (b := 1) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R) (s := s)
    hBlo hBhi hRm_nonneg zero_le_one le_rfl le_rfl hRpos hRρ hRC2 hCRρ hgs hsR
    hsρ hsdiv hRmGlobal hbasis (by simpa [one_mul] using hmodelLe)
    (fun v hv => by simpa [one_mul] using hmodelGe v hv)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_pair_rrm1_ge
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ C κ Blo : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < Blo ∧ ∀ {Rm A Bhi R s : ℝ},
      0 ≤ Bhi → 0 ≤ Rm →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      C * R < ρ →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2 ≤ κ →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) * A) 1 ≤ Bhi →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, C, hρ, hC, hvol⟩ := exists_pair_rglobal1 (I := I) (M := M) g hEnorm p
  obtain ⟨κ, Blo, hκ, hBlo, hmodelGe⟩ := exists_dirModel_ge1 (I := I) g p
  refine ⟨ρ, C, κ, Blo, hρ, hC, hκ, hBlo, ?_⟩
  intro Rm A Bhi R s hBhi hRm_nonneg hRpos hRρ hRC2 hCRρ hgs hsR hsρ hsdiv
    hKcap hRmGlobal hbasis hmodelLe
  have hK_nonneg :
      0 ≤ Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2 := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hRm_nonneg) (sq_nonneg (C * R))
  exact hvol (Rm := Rm) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R) (s := s)
    hBlo.le hBhi hRm_nonneg hRpos hRρ hRC2 hCRρ hgs hsR hsρ hsdiv
    hRmGlobal hbasis hmodelLe (hmodelGe hK_nonneg hKcap)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_pair_rrm1
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ C κ Blo : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < Blo ∧ ∀ {Rm A R s : ℝ},
      0 ≤ Rm →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      C * R < ρ →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2 ≤ κ →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      let Bhi : ℝ :=
        max
          (A + gronwallBound 0
            (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
              Rm * (C * R) ^ 2) 1)
            ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
              Rm * (C * R) ^ 2) * A) 1)
          0
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, C, κ, Blo, hρ, hC, hκ, hBlo, hvol⟩ :=
    exists_pair_rrm1_ge (I := I) (M := M) g hEnorm p
  refine ⟨ρ, C, κ, Blo, hρ, hC, hκ, hBlo, ?_⟩
  intro Rm A R s hRm_nonneg hRpos hRρ hRC2 hCRρ hgs hsR hsρ hsdiv hKcap
    hRmGlobal hbasis
  let Bhi : ℝ :=
    max
      (A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) * A) 1)
      0
  have hBhi : 0 ≤ Bhi := by
    dsimp [Bhi]
    exact le_max_right _ _
  have hmodelLe :
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) * A) 1 ≤ Bhi := by
    dsimp [Bhi]
    exact le_max_left _ _
  exact hvol (Rm := Rm) (A := A) (Bhi := Bhi) (R := R) (s := s) hBhi
    hRm_nonneg hRpos hRρ hRC2 hCRρ hgs hsR hsρ hsdiv hKcap hRmGlobal hbasis
    hmodelLe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_vol_pair_coeff
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {Rm b A Blo Bhi R s : ℝ},
      0 ≤ Blo → 0 ≤ Bhi → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_pair_launch (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro Rm b A Blo Bhi R s hBlo hBhi hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2
    hρball hgs hsR hsρ hsdiv hRm hbasis hmodelLe hmodelGe
  let K : ℝ :=
    Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) * Rm * ρ ^ 2
  have hK : 0 ≤ K := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hRm_nonneg) (sq_nonneg ρ)
  have hKbound :
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ K := by
    rfl
  exact hvol (K := K) (Rm := Rm) (b := b) (A := A) (Blo := Blo) (Bhi := Bhi)
    (R := R) (s := s) hBlo hBhi hK hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2
    hρball hgs hsR hsρ hsdiv hKbound hRm hbasis (by simpa [K] using hmodelLe)
    (by simpa [K] using hmodelGe)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_vol_pair_regionRm
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {Rm b A Blo Bhi R s : ℝ} {U : Set M},
      0 ≤ Blo → 0 ≤ Bhi → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        radialCurve (I := I) g p w t ∈ U) →
      (∀ q ∈ U,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_pair_coeff (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro Rm b A Blo Bhi R s U hBlo hBhi hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs
    hsR hsρ hsdiv hcurve hRmU hbasis hmodelLe hmodelGe
  refine hvol (Rm := Rm) (b := b) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R)
    (s := s) hBlo hBhi hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs hsR
    hsρ hsdiv ?_ hbasis hmodelLe hmodelGe
  intro w hw t ht
  exact hRmU (radialCurve (I := I) g p w t) (hcurve w hw t ht)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_vol_pair_globalRm
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {Rm b A Blo Bhi R s : ℝ},
      0 ≤ Blo → 0 ≤ Bhi → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_pair_regionRm (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro Rm b A Blo Bhi R s hBlo hBhi hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs
    hsR hsρ hsdiv hRmGlobal hbasis hmodelLe hmodelGe
  exact hvol (Rm := Rm) (b := b) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R)
    (s := s) (U := Set.univ) hBlo hBhi hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2
    hρball hgs hsR hsρ hsdiv (fun _ _ _ _ => Set.mem_univ _) (fun q _ => hRmGlobal q)
    hbasis hmodelLe hmodelGe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_vol_pair_globalRm1
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {Rm A Blo Bhi R s : ℝ},
      0 ≤ Blo → 0 ≤ Bhi → 0 ≤ Rm →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * A) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_pair_globalRm (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro Rm A Blo Bhi R s hBlo hBhi hRm_nonneg hRpos hRρ hRC2 hρball hgs hsR hsρ
    hsdiv hRmGlobal hbasis hmodelLe hmodelGe
  exact hvol (Rm := Rm) (b := 1) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R) (s := s)
    hBlo hBhi hRm_nonneg zero_le_one le_rfl le_rfl hRpos hRρ hRC2 hρball hgs
    hsR hsρ hsdiv hRmGlobal hbasis (by simpa [one_mul] using hmodelLe)
    (fun v hv => by simpa [one_mul] using hmodelGe v hv)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_vol_pair_rm1_ge
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ κ Blo : ℝ, 0 < ρ ∧ 0 < κ ∧ 0 < Blo ∧ ∀ {Rm A Bhi R s : ℝ},
      0 ≤ Bhi → 0 ≤ Rm →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ κ →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * A) 1 ≤ Bhi →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_pair_globalRm1 (I := I) (M := M) g hEnorm p
  obtain ⟨κ, Blo, hκ, hBlo, hmodelGe⟩ := exists_dirModel_ge1 (I := I) g p
  refine ⟨ρ, κ, Blo, hρ, hκ, hBlo, ?_⟩
  intro Rm A Bhi R s hBhi hRm_nonneg hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv
    hKcap hRmGlobal hbasis hmodelLe
  have hK_nonneg :
      0 ≤ Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hRm_nonneg) (sq_nonneg ρ)
  exact hvol (Rm := Rm) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R) (s := s)
    hBlo.le hBhi hRm_nonneg hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv
    hRmGlobal hbasis hmodelLe (hmodelGe hK_nonneg hKcap)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




theorem exists_vol_pair_rm1_auto
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ κ Blo : ℝ, 0 < ρ ∧ 0 < κ ∧ 0 < Blo ∧ ∀ {Rm A R s : ℝ},
      0 ≤ Rm →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ κ →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      let Bhi : ℝ :=
        max
          (A + gronwallBound 0
            (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
              Rm * ρ ^ 2) 1)
            ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
              Rm * ρ ^ 2) * A) 1)
          0
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, κ, Blo, hρ, hκ, hBlo, hvol⟩ :=
    exists_vol_pair_rm1_ge (I := I) (M := M) g hEnorm p
  refine ⟨ρ, κ, Blo, hρ, hκ, hBlo, ?_⟩
  intro Rm A R s hRm_nonneg hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv hKcap
    hRmGlobal hbasis
  let Bhi : ℝ :=
    max
      (A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * A) 1)
      0
  have hBhi : 0 ≤ Bhi := by
    dsimp [Bhi]
    exact le_max_right _ _
  have hmodelLe :
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * A) 1 ≤ Bhi := by
    dsimp [Bhi]
    exact le_max_left _ _
  exact hvol (Rm := Rm) (A := A) (Bhi := Bhi) (R := R) (s := s) hBhi
    hRm_nonneg hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv hKcap hRmGlobal hbasis
    hmodelLe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_vol_two_rm04
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {a K Rm Vb b A B R s : ℝ},
      0 ≤ B → 0 < a → 0 ≤ K → 0 ≤ Rm → 0 ≤ Vb → 0 ≤ b →
      b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R →
      R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb) →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * Vb ^ 2 ≤ K →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ w ∈ Metric.ball (0 : E) R,
        ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p w)) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p w t))) →
      (F : ∀ w : E, ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p w t)) →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p w) (F w i) t = 0) →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p w t) (F w i t) (F w j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p w) (F w i) t) t) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a * B ≤ Real.sqrt
            (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
              (a • (∑ i, v i • (chartModelBasis E) i))) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                  (a • (∑ i, v i • (chartModelBasis E) i))))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, h⟩ := exists_vol_two_rm04_at (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro a K Rm Vb b A B R s hBnn ha hK hRm_nonneg hVb hb0 hb1 h1b hRpos hRρ
    hRC2 hρball hgs hsR hsρ hsdiv hsmallBasis hsmallDir hlaunch hKbound hRm hγ
    ι _ _ _ hcard F hpar hON hFdiff hinit hmodelLe hmodelGe
  exact h hBnn ha hK hRm_nonneg hVb hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs
    hsR hsρ hsdiv hsmallBasis hsmallDir hlaunch hKbound hRm
    (fun w hw _ _ => (hγ w hw).contMDiffAt) hcard F hpar hON hFdiff
    hinit hmodelLe hmodelGe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_vol_rm04_pkg
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {a K Rm Vb b A B R s : ℝ},
      (D : Rm04FrameData (I := I) g p R b) →
      IsRm04VolHyp (I := I) g p D ρ a K Rm Vb A B s →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_two_rm04_at (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro a K Rm Vb b A B R s D H
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  letI : Fintype D.ι := D.fintype
  letI : DecidableEq D.ι := D.decidableEq
  letI : Nonempty D.ι := D.nonempty
  exact hvol H.hBnn H.ha H.hK H.hRm_nonneg H.hVb H.hb0 H.hb1 H.h1b
    H.hRpos H.hRρ H.hRC2 H.hρball H.hgs H.hsR H.hsρ H.hsdiv
    H.hsmallBasis H.hsmallDir H.hlaunch H.hKbound H.hRm H.hγ
    H.hcard D.F H.hpar H.hON H.hFdiff H.hinit H.hmodelLe H.hmodelGe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




theorem exists_vol_scale
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {K Rm Vb b A B R s : ℝ},
      (D : Rm04FrameData (I := I) g p R b) →
      (∀ a : ℝ, 0 < a →
        (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ) →
        (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
          ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ) →
        IsRm04VolHyp (I := I) g p D ρ a K Rm Vb A B s) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_rm04_pkg (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro K Rm Vb b A B R s D H
  obtain ⟨a, Ha⟩ := exists_rm04_scale (I := I) g p D hρ H
  exact hvol D Ha

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in






theorem exists_vol_scalar
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {K Rm Vb b A B R s : ℝ},
      0 ≤ B → 0 ≤ K → 0 ≤ Rm → 0 ≤ Vb →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb) →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * Vb ^ 2 ≤ K →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_rm04_pkg.{_, _, _, 0} (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro K Rm Vb b A B R s hBnn hK hRm_nonneg hVb hb0 hb1 h1b hRpos hRρ
    hRC2 hρball hgs hsR hsρ hsdiv hlaunch hKbound hRm hbasis hmodelLe hmodelGe
  obtain ⟨a, ha, hsmallBasis, hsmallDir⟩ := basisUnitScaleSmall (E := E) hρ
  obtain ⟨D, H⟩ :=
    exists_rm04_scalar.{_, _, _, 0} (I := I) g p hBnn ha hK hRm_nonneg hVb hb0 hb1 h1b
      hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv hsmallBasis hsmallDir hlaunch
      hKbound hRm hbasis hmodelLe hmodelGe
  exact hvol D H

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





theorem exists_vol_launch
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {K Rm b A B R s : ℝ},
      0 ≤ B → 0 ≤ K → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ K →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_scalar (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro K Rm b A B R s hBnn hK hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2
    hρball hgs hsR hsρ hsdiv hKbound hRm hbasis hmodelLe hmodelGe
  let Vb : ℝ := ρ
  have hVb : 0 ≤ Vb := by
    exact hρ.le
  have hlaunch : ∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb := by
    intro w hw
    exact le_of_lt (by simpa [Vb] using hρball w hw)
  exact hvol (K := K) (Rm := Rm) (Vb := Vb) (b := b) (A := A) (B := B)
    (R := R) (s := s) hBnn hK hRm_nonneg hVb hb0 hb1 h1b hRpos hRρ hRC2
    hρball hgs hsR hsρ hsdiv hlaunch (by simpa [Vb] using hKbound) hRm hbasis
    hmodelLe hmodelGe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





theorem exists_vol_coeff
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {Rm b A B R s : ℝ},
      0 ≤ B → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_launch (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro Rm b A B R s hBnn hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs
    hsR hsρ hsdiv hRm hbasis hmodelLe hmodelGe
  let K : ℝ :=
    Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) * Rm * ρ ^ 2
  have hK : 0 ≤ K := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hRm_nonneg) (sq_nonneg ρ)
  have hKbound :
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ K := by
    rfl
  exact hvol (K := K) (Rm := Rm) (b := b) (A := A) (B := B) (R := R) (s := s)
    hBnn hK hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv
    hKbound hRm hbasis (by simpa [K] using hmodelLe)
    (by simpa [K] using hmodelGe)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_vol_regionRm
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {Rm b A B R s : ℝ} {U : Set M},
      0 ≤ B → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        radialCurve (I := I) g p w t ∈ U) →
      (∀ q ∈ U,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_coeff (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro Rm b A B R s U hBnn hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs
    hsR hsρ hsdiv hcurve hRmU hbasis hmodelLe hmodelGe
  refine hvol (Rm := Rm) (b := b) (A := A) (B := B) (R := R) (s := s)
    hBnn hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv ?_
    hbasis hmodelLe hmodelGe
  intro w hw t ht
  exact hRmU (radialCurve (I := I) g p w t) (hcurve w hw t ht)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_vol_globalRm
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {Rm b A B R s : ℝ},
      0 ≤ B → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_regionRm (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro Rm b A B R s hBnn hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs
    hsR hsρ hsdiv hRmGlobal hbasis hmodelLe hmodelGe
  exact hvol (Rm := Rm) (b := b) (A := A) (B := B) (R := R) (s := s)
    (U := Set.univ) hBnn hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs
    hsR hsρ hsdiv (fun _ _ _ _ => Set.mem_univ _) (fun q _ => hRmGlobal q)
    hbasis hmodelLe hmodelGe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





theorem exists_vol_globalRm1
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {Rm A B R s : ℝ},
      0 ≤ B → 0 ≤ Rm →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * A) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_globalRm (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro Rm A B R s hBnn hRm_nonneg hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv
    hRmGlobal hbasis hmodelLe hmodelGe
  exact hvol (Rm := Rm) (b := 1) (A := A) (B := B) (R := R) (s := s)
    hBnn hRm_nonneg (by norm_num) (by norm_num) (by norm_num) hRpos hRρ hRC2
    hρball hgs hsR hsρ hsdiv hRmGlobal hbasis
    (by simpa [one_mul] using hmodelLe)
    (by
      intro v hv
      simpa [one_mul] using hmodelGe v hv)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in






theorem exists_vol_rm1_ge
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ κ B : ℝ, 0 < ρ ∧ 0 < κ ∧ 0 < B ∧ ∀ {Rm A R s : ℝ},
      0 ≤ Rm →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ κ →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * A) 1 ≤ B →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_globalRm1 (I := I) (M := M) g hEnorm p
  obtain ⟨κ, B, hκ, hB, hmodelGe⟩ := exists_dirModel_ge1 (I := I) g p
  refine ⟨ρ, κ, B, hρ, hκ, hB, ?_⟩
  intro Rm A R s hRm_nonneg hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv hKcap
    hRmGlobal hbasis hmodelLe
  have hK_nonneg :
      0 ≤ Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hRm_nonneg) (sq_nonneg ρ)
  exact hvol (Rm := Rm) (A := A) (B := B) (R := R) (s := s) hB.le hRm_nonneg
    hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv hRmGlobal hbasis hmodelLe
    (hmodelGe hK_nonneg hKcap)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





theorem exists_vol_frame
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {K Rm Vb b A B R s : ℝ},
      0 ≤ B → 0 ≤ K → 0 ≤ Rm → 0 ≤ Vb →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb) →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * Vb ^ 2 ≤ K →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ a : ℝ, 0 < a →
        (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ) →
        (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
          ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ) →
        (∀ k : Fin (Module.finrank ℝ E),
          Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A) ∧
        A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B ∧
        (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
          a * B ≤ Real.sqrt
              (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                (a • (∑ i, v i • (chartModelBasis E) i))) -
              gronwallBound 0 (max K 1)
                (K * (b * Real.sqrt
                  (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                    (a • (∑ i, v i • (chartModelBasis E) i))))) 1)) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_scale.{_, _, _, 0} (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro K Rm Vb b A B R s hBnn hK hRm_nonneg hVb hb0 hb1 h1b hRpos hRρ
    hRC2 hρball hgs hsR hsρ hsdiv hlaunch hKbound hRm hscalar
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one h1b
  obtain ⟨D, hcard, hpar, hON, hFdiff⟩ :=
    exists_rm04FrameData_radius.{_, _, _, 0} (I := I) g p hb hb1 hRC2
  refine hvol (K := K) (Rm := Rm) (Vb := Vb) (b := b) (A := A)
    (B := B) (R := R) (s := s) D ?_
  intro a ha hsmallBasis hsmallDir
  obtain ⟨hinit, hmodelLe, hmodelGe⟩ := hscalar a ha hsmallBasis hsmallDir
  exact {
    hBnn := hBnn
    ha := ha
    hK := hK
    hRm_nonneg := hRm_nonneg
    hVb := hVb
    hb0 := hb0
    hb1 := hb1
    h1b := h1b
    hRpos := hRpos
    hRρ := hRρ
    hRC2 := hRC2
    hρball := hρball
    hgs := hgs
    hsR := hsR
    hsρ := hsρ
    hsdiv := hsdiv
    hsmallBasis := hsmallBasis
    hsmallDir := hsmallDir
    hlaunch := hlaunch
    hKbound := hKbound
    hRm := hRm
    hγ := radialC1AtBall (I := I) g p hRC2 hb1
    hcard := hcard
    hpar := hpar
    hON := hON
    hFdiff := hFdiff
    hinit := hinit
    hmodelLe := hmodelLe
    hmodelGe := hmodelGe }

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in







theorem exists_metricBall_vol_two_local
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {c B Rlo Rup s : ℝ},
      0 ≤ B →
      0 < Rlo →
      0 < Rup →
      Rlo ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) Rlo,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) Rlo,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      (∀ w ∈ Metric.ball (0 : E) Rlo,
        c ≤ normalChartDensity (I := I) g p w) →
      s < Rup →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < Rup →
      Rup ≤ expMapC2Radius (I := I) g p →
      (letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
       MeasurableSet (Metric.ball p s)) →
      (∀ w ∈ Metric.ball (0 : E) Rup,
        ∀ i : Fin (Module.finrank ℝ E),
          Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
            (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
            (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal c *
          (ENNReal.ofReal (Rlo ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
            (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
              (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (Rup ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρlo, hρlo_pos, hlower⟩ := exists_metricBall_vol_ge_sc_local (I := I) g hEnorm p
  obtain ⟨ρup, hρup_pos, hupper⟩ := exists_metricBall_vol_scale_local (I := I) (M := M) g hEnorm p
  refine ⟨min ρlo ρup, lt_min hρlo_pos hρup_pos, ?_⟩
  intro c B Rlo Rup s hB hRlo_pos hRup_pos hRlo hρlo_ball hgs hdens
    hsRup hsρ hs_div_Rup hRup hmeas hJ
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hρlo_ball' : ∀ w ∈ Metric.ball (0 : E) Rlo,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρlo :=
    fun w hw => lt_of_lt_of_le (hρlo_ball w hw) (min_le_left _ _)
  have hsρup : s < ρup := lt_of_lt_of_le hsρ (min_le_right _ _)
  exact ⟨
    hlower hRlo_pos hRlo hρlo_ball' hgs hdens,
    hupper hB hRup_pos hsRup hsρup hs_div_Rup hRup hmeas hJ⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in






theorem exists_vol_two_same
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {c B R s : ℝ},
      0 ≤ B →
      0 < R →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      (∀ w ∈ Metric.ball (0 : E) R,
        c ≤ normalChartDensity (I := I) g p w) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
       MeasurableSet (Metric.ball p s)) →
      (∀ w ∈ Metric.ball (0 : E) R,
        ∀ i : Fin (Module.finrank ℝ E),
          Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
            (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
            (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal c *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
            (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
              (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρpos, htwo⟩ := exists_metricBall_vol_two_local (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρpos, ?_⟩
  intro c B R s hB hRpos hR hρball hgs hdens hsR hsρ hsdiv hmeas hJ
  exact htwo hB hRpos hRpos hR hρball hgs hdens hsR hsρ hsdiv hR hmeas hJ

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





theorem exists_vol_two_meas
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {c B R s : ℝ},
      0 ≤ B →
      0 < R →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      (∀ w ∈ Metric.ball (0 : E) R,
        c ≤ normalChartDensity (I := I) g p w) →
      s < R →
      s < ρ →
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R,
        ∀ i : Fin (Module.finrank ℝ E),
          Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
            (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
            (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal c *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
            (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
              (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρpos, htwo⟩ := exists_vol_two_same (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρpos, ?_⟩
  intro c B R s hB hRpos hR hρball hgs hdens hsR hsρ hsdiv hJ
  exact htwo hB hRpos hR hρball hgs hdens hsR hsρ hsdiv
    (metricBall_meas (I := I) (M := M) p s) hJ






omit [NeZero (Module.finrank ℝ E)] in
theorem metricBall_vol_ge [PseudoMetricSpace M]
    (g : SmoothRiemannianMetric I M) (p : M)
    {c R s : ℝ}
    (hball_target : Metric.ball (0 : E) R ⊆ (normalChartAt (I := I) g p).target)
    (hcoord_subset :
      (normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R ⊆ Metric.ball p s)
    (hdens : ∀ w ∈ Metric.ball (0 : E) R,
      c ≤ normalChartDensity (I := I) g p w) :
    ENNReal.ofReal c * (modelHaar (E := E)) (Metric.ball (0 : E) R) ≤
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) := by
  exact le_trans
    (coordBall_vol_ge (I := I) g p hball_target hdens)
    (MeasureTheory.measure_mono hcoord_subset)


omit [NeZero (Module.finrank ℝ E)] in
theorem metricBall_vol_ge_sc [PseudoMetricSpace M]
    (g : SmoothRiemannianMetric I M) (p : M)
    {c R s : ℝ} (hRpos : 0 < R)
    (hball_target : Metric.ball (0 : E) R ⊆ (normalChartAt (I := I) g p).target)
    (hcoord_subset :
      (normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R ⊆ Metric.ball p s)
    (hdens : ∀ w ∈ Metric.ball (0 : E) R,
      c ≤ normalChartDensity (I := I) g p w) :
    ENNReal.ofReal c *
        (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
          (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) := by
  simpa [modelHaar_ball (E := E) hRpos] using
    metricBall_vol_ge (I := I) g p hball_target hcoord_subset hdens



theorem metricBall_vol_ge_sc_c2 [PseudoMetricSpace M]
    (g : SmoothRiemannianMetric I M) (p : M)
    {c R s : ℝ} (hRpos : 0 < R)
    (hR : R ≤ expMapC2Radius (I := I) g p)
    (hcoord_subset :
      (normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R ⊆ Metric.ball p s)
    (hdens : ∀ w ∈ Metric.ball (0 : E) R,
      c ≤ normalChartDensity (I := I) g p w) :
    ENNReal.ofReal c *
        (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
          (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) :=
  metricBall_vol_ge_sc (I := I) g p hRpos
    (ball_tgt_of_radius (I := I) g p hR) hcoord_subset hdens

end BallUpper

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
