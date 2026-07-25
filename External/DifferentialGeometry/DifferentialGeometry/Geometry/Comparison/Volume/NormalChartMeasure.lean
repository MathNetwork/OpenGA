import DifferentialGeometry.Analysis.Integration.Measure.ParamEvaluation
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Exponential.JacobiVariation










noncomputable section

open Set Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section NormalChart

variable [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]








def normalChartDensity (g : SmoothRiemannianMetric I M) (p : M) : E → ℝ :=
  paramDensity (I := I) g (expMapDiffeo (I := I) g p)

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma normalChartDensity_apply
    (g : SmoothRiemannianMetric I M) (p : M) (w : E) :
    normalChartDensity (I := I) g p w =
      paramDensity (I := I) g (expMapDiffeo (I := I) g p) w := rfl



def normalGramMatrix (g : SmoothRiemannianMetric I M) (p : M) :
    E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  paramGramMatrix (I := I) g (expMapDiffeo (I := I) g p)

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma normalGram_apply
    (g : SmoothRiemannianMetric I M) (p : M) (w : E)
    (i j : Fin (Module.finrank ℝ E)) :
    normalGramMatrix (I := I) g p w i j =
      g.inner (expMapDiffeo (I := I) g p w)
        (mfderiv 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p) w ((chartModelBasis E) i))
        (mfderiv 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p) w ((chartModelBasis E) j)) :=
  rfl



omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma normalDensity_det
    (g : SmoothRiemannianMetric I M) (p : M) (w : E) :
    normalChartDensity (I := I) g p w =
      Real.sqrt (normalGramMatrix (I := I) g p w).det :=
  rfl





def radialJacobiField (g : SmoothRiemannianMetric I M) (p : M)
    (x w : E) (t : ℝ) :
    TangentSpace I
      ((expMap (I := I) g p (show TangentSpace I p from (t • x)) : M)) :=
  mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
    (expMap (I := I) g p
      (show TangentSpace I p from (t • (x + s • w))) : M)) 0 (1 : ℝ)


omit [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma radialJacobi_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) :
    radialJacobiField (I := I) g p x w 0 = 0 := by
  simpa [radialJacobiField] using
    DifferentialGeometry.Geometry.Riemannian.radial_jacobi_zero (I := I) g p x w


omit [SigmaCompactSpace M] in
theorem exists_radialJacobi_radius
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ t₀ ∈ Set.Ioo (0 : ℝ) 1,
      IsJacobiAt (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) t₀ := by
  simpa [radialJacobiField] using
    DifferentialGeometry.Geometry.Riemannian.exists_radial_jacobi_radius (I := I) g p

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_radialJacobi_zero_radius
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      IsJacobiAt (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 := by
  simpa [radialJacobiField] using
    DifferentialGeometry.Geometry.Riemannian.exists_jacobi_zero (I := I) g hEnorm p



omit [T2Space M] in
omit [SigmaCompactSpace M] in
theorem exists_radialJacobi_deriv_radius
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w := by
  simpa [radialJacobiField] using
    DifferentialGeometry.Geometry.Riemannian.exists_radial_jacobi_deriv_radius (I := I) g p



def radialJacobiGram (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1)
      (radialJacobiField (I := I) g p x ((chartModelBasis E) j) 1)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
@[simp] lemma radialJacobiGram_apply
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (i j : Fin (Module.finrank ℝ E)) :
    radialJacobiGram (I := I) g p x i j =
      g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) j) 1) :=
  rfl


omit [T2Space M] [SigmaCompactSpace M] in
lemma radialJacobi_one
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    radialJacobiField (I := I) g p x w 1 =
      mfderiv 𝓘(ℝ, E) I
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x w := by
  simpa [radialJacobiField] using
    DifferentialGeometry.Geometry.Riemannian.radial_jacobi_one (I := I) g p x w hx


omit [T2Space M] [SigmaCompactSpace M] in
lemma radialJacobi_one_smul
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (a : ℝ)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    radialJacobiField (I := I) g p x (a • w) 1 =
      a • radialJacobiField (I := I) g p x w 1 := by
  rw [radialJacobi_one (I := I) g p x (a • w) hx,
    radialJacobi_one (I := I) g p x w hx]
  exact (mfderiv 𝓘(ℝ, E) I
    (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x).map_smul a w



omit [T2Space M] [SigmaCompactSpace M] in
lemma radialJacobi_one_sum
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (c : Fin (Module.finrank ℝ E) → ℝ)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    radialJacobiField (I := I) g p x
        (∑ i, c i • (chartModelBasis E) i) 1 =
      ∑ i, c i • radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1 := by
  rw [radialJacobi_one (I := I) g p x (∑ i, c i • (chartModelBasis E) i) hx]
  set L :=
    mfderiv 𝓘(ℝ, E) I
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x
  change L (∑ i, c i • (chartModelBasis E) i) =
    ∑ i, c i • radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1
  rw [map_sum L]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [radialJacobi_one (I := I) g p x ((chartModelBasis E) i) hx]
  exact L.map_smul (c i) ((chartModelBasis E) i)



omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma expDiffeo_mfderiv
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hx : x ∈ (expMapDiffeo (I := I) g p).source) :
    mfderiv 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p) x =
      mfderiv 𝓘(ℝ, E) I
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x := by
  have hsrc : ∀ᶠ y in 𝓝 x, y ∈ (expMapDiffeo (I := I) g p).source :=
    (expMapDiffeo (I := I) g p).open_source.mem_nhds hx
  have hagree :
      (fun y : E => expMapDiffeo (I := I) g p y) =ᶠ[𝓝 x]
        (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) := by
    filter_upwards [hsrc] with y hy
    exact expMapDiffeo_apply_eq (I := I) g p hy
  exact hagree.mfderiv_eq




omit [T2Space M] [SigmaCompactSpace M] in
lemma normalGram_radial
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hxsrc : x ∈ (expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (i j : Fin (Module.finrank ℝ E)) :
    normalGramMatrix (I := I) g p x i j =
      g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) j) 1) := by
  rw [normalGram_apply]
  have hbase := expMapDiffeo_apply_eq (I := I) g p hxsrc
  have hderiv := expDiffeo_mfderiv (I := I) g p hxsrc
  have hi :
      mfderiv 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p) x ((chartModelBasis E) i) =
        mfderiv 𝓘(ℝ, E) I
          (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
          x ((chartModelBasis E) i) :=
    congrArg (fun L => L ((chartModelBasis E) i)) hderiv
  have hj :
      mfderiv 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p) x ((chartModelBasis E) j) =
        mfderiv 𝓘(ℝ, E) I
          (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
          x ((chartModelBasis E) j) :=
    congrArg (fun L => L ((chartModelBasis E) j)) hderiv
  rw [hi, hj, hbase]
  rw [← radialJacobi_one (I := I) g p x ((chartModelBasis E) i) hxrad]
  rw [← radialJacobi_one (I := I) g p x ((chartModelBasis E) j) hxrad]


omit [T2Space M] [SigmaCompactSpace M] in
lemma normalGram_radialMat
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hxsrc : x ∈ (expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    normalGramMatrix (I := I) g p x = radialJacobiGram (I := I) g p x := by
  ext i j
  exact normalGram_radial (I := I) g p hxsrc hxrad i j


omit [T2Space M] [SigmaCompactSpace M] in
lemma normalDensity_radial
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hxsrc : x ∈ (expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    normalChartDensity (I := I) g p x =
      Real.sqrt (radialJacobiGram (I := I) g p x).det := by
  rw [normalDensity_det, normalGram_radialMat (I := I) g p hxsrc hxrad]










omit [NeZero (Module.finrank ℝ E)] in
theorem normalChart_volume_eq
    (g : SmoothRiemannianMetric I M) (p : M)
    {A : Set M} (hA_meas : MeasurableSet A)
    (hA_source : A ⊆ (normalChartAt (I := I) g p).source) :
    riemannianVolumeMeasure (I := I) (M := M) g A =
      ∫⁻ w in (normalChartAt (I := I) g p) '' A,
        ENNReal.ofReal (normalChartDensity (I := I) g p w)
          ∂(modelHaar (E := E)) := by
  have hA_target : A ⊆ (expMapDiffeo (I := I) g p).target := by
    simpa [normalChartAt_source_eq (I := I) g p] using hA_source
  simpa [normalChartAt, normalChartDensity] using
    riemannianVolumeMeasure_param_target_eq (I := I) (M := M) g
      (expMapDiffeo (I := I) g p) hA_meas hA_target



theorem normalChart_volume_radial
    (g : SmoothRiemannianMetric I M) (p : M)
    {A : Set M} (hA_meas : MeasurableSet A)
    (hA_source : A ⊆ (normalChartAt (I := I) g p).source)
    (hA_rad : (normalChartAt (I := I) g p) '' A ⊆
      Metric.ball (0 : E) (expMapC2Radius (I := I) g p)) :
    riemannianVolumeMeasure (I := I) (M := M) g A =
      ∫⁻ w in (normalChartAt (I := I) g p) '' A,
        ENNReal.ofReal (Real.sqrt (radialJacobiGram (I := I) g p w).det)
          ∂(modelHaar (E := E)) := by
  have hA_target : A ⊆ (expMapDiffeo (I := I) g p).target := by
    simpa [normalChartAt_source_eq (I := I) g p] using hA_source
  have hB_meas : MeasurableSet ((normalChartAt (I := I) g p) '' A) := by
    simpa [normalChartAt] using
      measurableSet_symm_image_param (I := I) (M := M)
        (Ψ := expMapDiffeo (I := I) g p) hA_meas hA_target
  rw [normalChart_volume_eq (I := I) (M := M) g p hA_meas hA_source]
  refine MeasureTheory.setLIntegral_congr_fun hB_meas ?_
  intro w hw
  have hwsrc : w ∈ (expMapDiffeo (I := I) g p).source := by
    rcases hw with ⟨y, hyA, hyw⟩
    have hy_source : y ∈ (normalChartAt (I := I) g p).source := hA_source hyA
    have hw_target : normalChartAt (I := I) g p y ∈
        (normalChartAt (I := I) g p).target :=
      (normalChartAt (I := I) g p).map_source hy_source
    rw [hyw] at hw_target
    simpa [normalChartAt_target_eq (I := I) g p] using hw_target
  have hwrad : ‖w‖ < expMapC2Radius (I := I) g p := by
    have hwball : w ∈ Metric.ball (0 : E) (expMapC2Radius (I := I) g p) := hA_rad hw
    simpa [Metric.mem_ball, dist_eq_norm] using hwball
  simpa using
    congrArg ENNReal.ofReal (normalDensity_radial (I := I) g p hwsrc hwrad)

end NormalChart

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
