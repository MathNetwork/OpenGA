import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldContractionBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Operator.MetricSharpSmooth


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open TensorMultilinear
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def ricEndoRaisedFib (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => metricSharp (I := I) g x (ricciTensor (I := I) g x v).toLinearMap
      map_add' := fun v v' => by
        have h : (ricciTensor (I := I) g x (v + v')).toLinearMap =
            (ricciTensor (I := I) g x v).toLinearMap +
              (ricciTensor (I := I) g x v').toLinearMap := by
          ext w
          simp [map_add]
        rw [show metricSharp (I := I) g x (ricciTensor (I := I) g x (v + v')).toLinearMap =
            (metricFlatMap (I := I) g x).symm
              (ricciTensor (I := I) g x (v + v')).toLinearMap from rfl,
          h, map_add]
        rfl
      map_smul' := fun c v => by
        have h : (ricciTensor (I := I) g x (c • v)).toLinearMap =
            c • (ricciTensor (I := I) g x v).toLinearMap := by
          ext w
          simp [map_smul]
        rw [show metricSharp (I := I) g x (ricciTensor (I := I) g x (c • v)).toLinearMap =
            (metricFlatMap (I := I) g x).symm
              (ricciTensor (I := I) g x (c • v)).toLinearMap from rfl,
          h, map_smul]
        rfl }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma ricEndoRaisedFib_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    ricEndoRaisedFib (I := I) g x v =
      metricSharp (I := I) g x (ricciTensor (I := I) g x v).toLinearMap := by
  rw [ricEndoRaisedFib, LinearMap.coe_toContinuousLinearMap']
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma inner_ricEndoRaisedFib (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.inner x (ricEndoRaisedFib (I := I) g x v) w = ricciTensor (I := I) g x v w := by
  rw [ricEndoRaisedFib_apply]
  exact inner_metricSharp (I := I) g x (ricciTensor (I := I) g x v).toLinearMap w

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricEndoRaisedFib_contMDiff (g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (ricEndoRaisedFib (I := I) g x)) := by
  apply cotangentCov_clmSection_smooth_aux (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => ricEndoRaisedFib (I := I) g x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (ricciTensor (I := I) g b (Y b)).toLinearMap
          (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have hRic : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
          (ricciTensor (I := I) g b)) :=
      ricciTensor_contMDiff (I := I) g
    have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (chartBasisVec (I := I) α j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartBasisVec_contMDiffOn (I := I) α j
    have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b,
            ricciTensor (I := I) g b (Y b) (chartBasisVecFiber (I := I) α j b)⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (b := id) hRic.contMDiffOn Y.contMDiff.contMDiffOn hBasis
    have hbase_eq :
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) α
    rw [hbase_eq] at happ
    intro b hb
    have hpb := happ b hb
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
    exact hpb.2
  have hsmooth := metricSharp_contMDiff_total (I := I) g
    (cv := fun b : M => (ricciTensor (I := I) g b (Y b)).toLinearMap) hcv
  refine hsmooth.congr ?_
  intro x
  change TotalSpace.mk' E x
      (metricSharp (I := I) g x (ricciTensor (I := I) g x (Y x)).toLinearMap) =
    TotalSpace.mk' E x (ricEndoRaisedFib (I := I) g x (Y x))
  rw [ricEndoRaisedFib_apply]

set_option backward.isDefEq.respectTransparency false in

def ricSlotOpFib (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (s + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
          (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D).comp
            (ricEndoRaisedFib (I := I) g x))
      map_add' := fun D₁ D₂ => by
        rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.add_comp,
          map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
      map_smul' := fun c D => by
        rw [map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.smul_comp,
          map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
        rfl }

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma ricSlotOpFib_apply (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (D : Tensor0SSpace (s + 1) I x) :
    ricSlotOpFib (I := I) (M := M) g s x D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D).comp
          (ricEndoRaisedFib (I := I) g x)) := by
  rw [ricSlotOpFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma ricSlotOpFib_apply_eval (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (D : Tensor0SSpace (s + 1) I x) (v0 : E) (vs : Fin s → E) :
    Tensor0SSpace.toModel (ricSlotOpFib (I := I) (M := M) g s x D) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D
          (ricEndoRaisedFib (I := I) g x v0)) vs := by
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    (ricSlotOpFib (I := I) (M := M) g s x D) v0 vs]
  have hcurry : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      (ricSlotOpFib (I := I) (M := M) g s x D) =
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D).comp
        (ricEndoRaisedFib (I := I) g x) := by
    rw [ricSlotOpFib_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hcurry]
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricSlotOpFib_contMDiff (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel (s + 1) (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel (s + 1) (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace (s + 1) (s + 1) I z) x
        (ricSlotOpFib (I := I) (M := M) g s x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel (s + 1) ℝ E) (V₁ := fun x : M => Tensor0SSpace (s + 1) I x)
    (F₂ := Tensor0SModel (s + 1) ℝ E) (V₂ := fun x : M => Tensor0SSpace (s + 1) I x)
    (φ := fun x => ricSlotOpFib (I := I) (M := M) g s x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 1) I z) x
      (ricSlotOpFib (I := I) (M := M) g s x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 1) I z) x
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
          (ricEndoRaisedFib (I := I) g x)))) := by
    funext x
    rw [ricSlotOpFib_apply]
  rw [heq]
  have hcurriedY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x))) :=
    fun x => contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
      (fun y : M => Y y) x (Y.contMDiff x)
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
          (ricEndoRaisedFib (I := I) g x))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
      (φ := fun x => ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
        (ricEndoRaisedFib (I := I) g x))
    intro Z
    have heqZ : (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
          (ricEndoRaisedFib (I := I) g x)) (Z x))) =
        (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)
          (ricEndoRaisedFib (I := I) g x (Z x)))) := by
      funext x; rfl
    rw [heqZ]
    have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E
          (E := fun z : M => TangentSpace I z) x (ricEndoRaisedFib (I := I) g x (Z x))) :=
      ContMDiff.clm_bundle_apply (b := id) (ricEndoRaisedFib_contMDiff (I := I) g) Z.contMDiff
    exact ContMDiff.clm_bundle_apply (b := id) hcurriedY hinner
  exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
    (fun x : M => ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
      (ricEndoRaisedFib (I := I) g x)) hG

set_option backward.isDefEq.respectTransparency false in

def ricSlotOpField (g : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g (s + 1) (s + 1) where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (s + 1) (s + 1) I x from ricSlotOpFib (I := I) (M := M) g s x)
      contMDiff_toFun := ricSlotOpFib_contMDiff (I := I) (M := M) g s }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma ricSlotOpField_toSection (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    (ricSlotOpField (I := I) (M := M) g s).toSection x =
      (show TensorRSSpace (s + 1) (s + 1) I x from ricSlotOpFib (I := I) (M := M) g s x) := rfl

def ricTraceSection (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  operatorFieldApply (I := I) (M := M) g (s + 1) (s + 1)
    (ricSlotOpField (I := I) (M := M) g s) (covGrad (I := I) (M := M) g 0 s S)


omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma ricTraceSection_toSection (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (x : M) :
    (ricTraceSection (I := I) (M := M) g s S).toSection x =
      (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (ricSlotOpField (I := I) (M := M) g s).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  rw [ricTraceSection,
    appCc_toSection (I := I) (M := M) g (s + 1) (s + 1)
      (ricSlotOpField (I := I) (M := M) g s) (covGrad (I := I) (M := M) g 0 s S) x]

theorem exists_ricTraceSection_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((ricTraceSection (I := I) (M := M) g s S).toSection x) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  have hC : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensor g 0 s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((ricTraceSection (I := I) (M := M) g s S).toSection x) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
    intro s
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_uniform_riemannianFiberNormSq_appCc_le (I := I) (M := M) g (s + 1) (s + 1)
        (ricSlotOpField (I := I) (M := M) g s)
    refine ⟨C, hC_nn, fun S x => ?_⟩
    have h := hC (covGrad (I := I) (M := M) g 0 s S) x
    rwa [show (operatorFieldApply (I := I) (M := M) g (s + 1) (s + 1)
          (ricSlotOpField (I := I) (M := M) g s) (covGrad (I := I) (M := M) g 0 s S)) =
        ricTraceSection (I := I) (M := M) g s S from rfl] at h
  choose C hC_nn hC using hC
  refine ⟨fun s => Real.sqrt (C s), fun s => Real.sqrt_nonneg _, fun s S x => ?_⟩
  have hKsq : Real.sqrt (C s) ^ 2 = C s := Real.sq_sqrt (hC_nn s)
  rw [hKsq]
  have hfgS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hfS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  have h := hC s S x
  nlinarith [h, hfgS_nn, hfS_nn, hC_nn s, mul_nonneg (hC_nn s) hfgS_nn]


omit [NeZero (Module.finrank ℝ E)] in
theorem ricTraceSection_zero_apply (g : SmoothRiemannianMetric I M) (f : SmoothCcTensor g 0 0)
    (x : M) (v : E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 1) I x from
          (ricTraceSection (I := I) (M := M) g 0 f).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons v (fun i : Fin 0 => i.elim0)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 1) I x from
          (covGrad (I := I) (M := M) g 0 0 f).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons (ricEndoRaisedFib (I := I) g x v) (fun i : Fin 0 => i.elim0)) := by
  classical
  have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 1) I x from
        (ricTraceSection (I := I) (M := M) g 0 f).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      ricSlotOpFib (I := I) (M := M) g 0 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 1) I x from
          (covGrad (I := I) (M := M) g 0 0 f).toSection x)
          (unitZeroSec (I := I) (M := M) x)) := by
    rw [ricTraceSection_toSection, ricSlotOpField_toSection]
    rfl
  rw [hval]
  rw [ricSlotOpFib_apply_eval (I := I) (M := M) g 0 x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 1) I x from
      (covGrad (I := I) (M := M) g 0 0 f).toSection x)
      (unitZeroSec (I := I) (M := M) x)) v (fun i : Fin 0 => i.elim0)]
  rw [tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 1) I x from
      (covGrad (I := I) (M := M) g 0 0 f).toSection x)
      (unitZeroSec (I := I) (M := M) x)) (ricEndoRaisedFib (I := I) g x v)
    (fun i : Fin 0 => i.elim0)]

end Connection
end Integral
end DifferentialGeometry

end
