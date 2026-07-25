import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentCovDerivIdentification


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open TensorMultilinear (contMDiffAt_section_apply contMDiff_section_apply)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem g0FlatField_contMDiff (g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 1 ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace 1 I z) x
        (g0FlatCLM (I := I) g₀ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := Tensor0SModel 1 ℝ E) (V₂ := fun z : M => Tensor0SSpace 1 I z)
    (φ := fun x : M => g0FlatCLM (I := I) g₀ x)
  intro Z
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 1
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (g0FlatCLM (I := I) g₀ x (Z x) :
        Bundle.continuousMultilinearMap ℝ 1 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x (Z x) (Y (σ 0) x)) x₀ := by
    have h_total : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b, g₀.inner b (Z b) (Y (σ 0) b)⟩ :
          TotalSpace ℝ (Bundle.Trivial M ℝ))) x₀ :=
      (ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id)
        g₀.contMDiff.contMDiffOn Z.contMDiff.contMDiffOn
        (Y (σ 0)).contMDiff.contMDiffOn x₀ (mem_univ x₀)).contMDiffAt univ_mem
    rw [Bundle.contMDiffAt_totalSpace] at h_total
    exact h_total.2
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
    rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change (g0FlatCLM (I := I) g₀ x (Z x)) (fun j : Fin 1 => e₁.symmL ℝ x (b (σ j))) = _
  rw [show (fun j : Fin 1 => e₁.symmL ℝ x (b (σ j))) = (fun _ : Fin 1 => e₁.symmL ℝ x (b (σ 0))) from by
    funext j; fin_cases j; rfl]
  rw [hframe0]
  rw [g0FlatCLM_apply, dualToCotangent_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem sharpFlatEndoCcFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E →L[ℝ] Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E →L[ℝ] Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z →L[ℝ] Tensor0SSpace 1 I z) x
        ((g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun z : M => Tensor0SSpace 1 I z)
    (F₂ := Tensor0SModel 1 ℝ E) (V₂ := fun z : M => Tensor0SSpace 1 I z)
    (φ := fun x : M => (g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x))
  intro Y
  have hsharpY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (inverseMetricSharpFib (I := I) g₁ x (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (inverseMetricSharpField_contMDiff (I := I) g₁) Y.contMDiff
  have hflatsharpY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) x
        (g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x (Y x)))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (g0FlatField_contMDiff (I := I) g₀) hsharpY
  refine hflatsharpY.congr (fun x => ?_)
  rfl

def sharpFlatEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 1 where
  toSection :=
    { toFun := fun x : M => TensorRSSpace.ofCLM
        ((g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x))
      contMDiff_toFun := sharpFlatEndoCcFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma sharpFlatEndoCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpFlatEndoCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM
        ((g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x)) := rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SOne_apply_add' (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    om (fun _ : Fin 1 => a + b) = om (fun _ : Fin 1 => a) + om (fun _ : Fin 1 => b) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hb : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => b) = φ b := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hab : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a + b) = φ (a + b) := by rw [continuousMultilinearCurryFin1_apply]; rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ => a + b) = _
  rw [hab, ha, hb, map_add]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SOne_apply_smul' (x : M) (om : Tensor0SSpace 1 I x)
    (c : ℝ) (a : TangentSpace I x) :
    om (fun _ : Fin 1 => c • a) = c • om (fun _ : Fin 1 => a) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hca : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => c • a) = φ (c • a) := by rw [continuousMultilinearCurryFin1_apply]; rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ => c • a) = _
  rw [hca, ha, map_smul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SOne_apply_neg' (x : M) (om : Tensor0SSpace 1 I x)
    (a : TangentSpace I x) :
    om (fun _ : Fin 1 => -a) = -om (fun _ : Fin 1 => a) := by
  have h := tensor0SOne_apply_smul' (I := I) x om (-1) a
  simp only [neg_smul, one_smul] at h
  exact h

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SOne_apply_sub' (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    om (fun _ : Fin 1 => a - b) = om (fun _ : Fin 1 => a) - om (fun _ : Fin 1 => b) := by
  rw [show (fun _ : Fin 1 => a - b) = (fun _ : Fin 1 => a + (-b)) from by
    funext _; rw [sub_eq_add_neg]]
  rw [tensor0SOne_apply_add' (I := I) x om, tensor0SOne_apply_neg' (I := I) x om, sub_eq_add_neg]

def sharpFlatRaiseEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (inverseMetricSharpFib (I := I) g₀ x).comp (g0FlatCLM (I := I) g₁ x)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma sharpFlatRaiseEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    sharpFlatRaiseEndo (I := I) g₀ g₁ x v =
      inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x v) := rfl

@[irreducible] def raisedKoszulVec (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x) : TangentSpace I x :=
  sharpFlatRaiseEndo (I := I) g₀ g₁ x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma raisedKoszulVec_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x) :
    raisedKoszulVec (I := I) g₀ g₁ x a b =
      inverseMetricSharpFib (I := I) g₀ x
        (g0FlatCLM (I := I) g₁ x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b)) := by
  unfold raisedKoszulVec; rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
lemma raisedKoszulVec_continuous₂ (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Continuous (fun p : TangentSpace I x × TangentSpace I x =>
      raisedKoszulVec (I := I) g₀ g₁ x p.1 p.2) := by
  have hcd : Continuous (fun p : TangentSpace I x × TangentSpace I x =>
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x p.1 p.2) :=
    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).continuous₂
  have heq : (fun p : TangentSpace I x × TangentSpace I x =>
      raisedKoszulVec (I := I) g₀ g₁ x p.1 p.2) =
      (fun p : TangentSpace I x × TangentSpace I x =>
        sharpFlatRaiseEndo (I := I) g₀ g₁ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p.1 p.2)) := by
    funext p; rw [raisedKoszulVec_apply]; rfl
  rw [heq]
  exact (sharpFlatRaiseEndo (I := I) g₀ g₁ x).continuous.comp hcd

set_option maxHeartbeats 6400000 in
def raisedKoszulPairing (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun YZ => om (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ g₁ x (YZ 0) (YZ 1))
      map_update_add' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i Y Y'
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              raisedKoszulVec_apply, ContinuousLinearMap.add_apply, map_add]
            rw [tensor0SOne_apply_add' (I := I) x om]
      map_update_smul' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i c Y
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              raisedKoszulVec_apply, ContinuousLinearMap.smul_apply, map_smul]
            rw [tensor0SOne_apply_smul' (I := I) x om]
      cont := by
        have hpair : Continuous (fun YZ : Fin 2 → TangentSpace I x => (YZ 0, YZ 1)) :=
          (continuous_apply 0).prodMk (continuous_apply 1)
        have hbil : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
            raisedKoszulVec (I := I) g₀ g₁ x (YZ 0) (YZ 1)) :=
          (raisedKoszulVec_continuous₂ (I := I) g₀ g₁ x).comp hpair
        exact ((ContinuousMultilinearMap.coe_continuous
          (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)).comp
          (continuous_pi (fun _ => hbil))) } : Tensor0SSpace 2 I x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma raisedKoszulPairing_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    (raisedKoszulPairing (I := I) g₀ g₁ x om) YZ =
      om (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ g₁ x (YZ 0) (YZ 1)) := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
lemma raisedKoszulPairing_add (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om om' : Tensor0SSpace 1 I x) :
    raisedKoszulPairing (I := I) g₀ g₁ x (om + om') =
      raisedKoszulPairing (I := I) g₀ g₁ x om + raisedKoszulPairing (I := I) g₀ g₁ x om' := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.add_apply om om' _

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
lemma raisedKoszulPairing_smul (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (om : Tensor0SSpace 1 I x) :
    raisedKoszulPairing (I := I) g₀ g₁ x (c • om) =
      c • raisedKoszulPairing (I := I) g₀ g₁ x om := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.smul_apply om c _

def raisedKoszulFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TensorRSSpace 1 2 I x :=
  TensorRSSpace.ofCLM
    (LinearMap.toContinuousLinearMap
      { toFun := fun om => raisedKoszulPairing (I := I) g₀ g₁ x om
        map_add' := raisedKoszulPairing_add g₀ g₁ x
        map_smul' := raisedKoszulPairing_smul g₀ g₁ x })

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma raisedKoszulFib_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from raisedKoszulFib (I := I) g₀ g₁ x) om =
      raisedKoszulPairing (I := I) g₀ g₁ x om := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem sharpFlatRaiseEndo_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (sharpFlatRaiseEndo (I := I) g₀ g₁ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := E) (V₂ := fun z : M => TangentSpace I z)
    (φ := fun x : M => sharpFlatRaiseEndo (I := I) g₀ g₁ x)
  intro Y
  have hflatY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) x
        (g0FlatCLM (I := I) g₁ x (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (g0FlatField_contMDiff (I := I) g₁) Y.contMDiff
  have hsharpflatY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x (Y x)))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (inverseMetricSharpField_contMDiff (I := I) g₀) hflatY
  refine hsharpflatY.congr (fun x => ?_)
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem raisedKoszulFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) x (raisedKoszulFib (I := I) g₀ g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x : M => (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      raisedKoszulFib (I := I) g₀ g₁ x))
  intro om
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  have hsec : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (raisedKoszulPairing (I := I) g₀ g₁ x (om x))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (raisedKoszulPairing (I := I) g₀ g₁ x (om x) :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
    intro σ x₀
    set b := Module.finBasis ℝ E with hb
    set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
    have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
    obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
    have hvec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (raisedKoszulVec (I := I) g₀ g₁ x (Y (σ 0) x) (Y (σ 1) x))) := by
      have hcd : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun x : M => (⟨x, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y (σ 0) x) (Y (σ 1) x)⟩ :
            TotalSpace E (TangentSpace I))) :=
        PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ (Y (σ 0)).contMDiff (Y (σ 1)).contMDiff
      have hcomp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
            (sharpFlatRaiseEndo (I := I) g₀ g₁ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y (σ 0) x) (Y (σ 1) x)))) :=
        ContMDiff.clm_bundle_apply (b := id)
          (sharpFlatRaiseEndo_contMDiff (I := I) g₀ g₁) hcd
      refine hcomp.congr (fun x => ?_)
      rw [raisedKoszulVec_apply]
      rfl
    have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (om x)
          (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ g₁ x (Y (σ 0) x) (Y (σ 1) x))) x₀ :=
      TensorMultilinear.contMDiffAt_section_apply (n := 1) (x₀ := x₀)
        (fun x : M => om x) (om.contMDiff x₀)
        (fun _ : Fin 1 => fun x : M => raisedKoszulVec (I := I) g₀ g₁ x (Y (σ 0) x) (Y (σ 1) x))
        (fun _ => (hvec x₀))
    refine hscalar.congr_of_eventuallyEq ?_
    have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
    filter_upwards [h_base₁, hY] with x hx₁ hYx
    rw [continuousMultilinearMap_basis_repr]
    have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
      rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    have hframe1 : e₁.symmL ℝ x (b (σ 1)) = (Y (σ 1)) x := by
      rw [hYx (σ 1), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    change (raisedKoszulPairing (I := I) g₀ g₁ x (om x))
        (fun j : Fin 2 => e₁.symmL ℝ x (b (σ j))) = _
    rw [raisedKoszulPairing_apply]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rw [hframe0, hframe1]
    rfl
  refine hsec.congr ?_
  intro x
  rfl

def raisedKoszul (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M => raisedKoszulFib (I := I) g₀ g₁ x
      contMDiff_toFun := raisedKoszulFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma raisedKoszul_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (raisedKoszul (I := I) g₀ g₁).toSection x = raisedKoszulFib (I := I) g₀ g₁ x := rfl

def symmSCovGrad3 (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    SmoothCcTensor g₀ 0 3 :=
  covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma symmSCovGrad3_def (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    symmSCovGrad3 (I := I) (M := M) g₀ T =
      covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma connDiffPairing_eq_raisedKoszul_sharpFlat (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
      (g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om))
        (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ g₁ x (YZ 0) (YZ 1)) := by
  set D : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1) with hD
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₁ x om with hu
  have hLHS : om (fun _ : Fin 1 => D) = g₁.inner x u D := by
    rw [← cotangentToDual_apply (I := I) (x := x) om D]
    rw [show cotangentToDual (I := I) (x := x) om D
          = cotangentToDualLinear (I := I) (x := x) om D from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₁ x om D]
  rw [hLHS]
  set P : TangentSpace I x := raisedKoszulVec (I := I) g₀ g₁ x (YZ 0) (YZ 1) with hPdef
  rw [show (g0FlatCLM (I := I) g₀ x u) (fun _ : Fin 1 => P)
        = cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x u) P from
      (cotangentToDual_apply (I := I) (x := x) (g0FlatCLM (I := I) g₀ x u) P).symm]
  rw [cotangentToDual_g0FlatCLM (I := I) g₀ x u P]
  rw [g₀.symm x u P]
  have hPval : P = inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x D) := by
    rw [hPdef, raisedKoszulVec_apply]
  have hPinner : g₀.inner x P u = cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₁ x D) u := by
    rw [hPval, ← cotangentToDualLinear_apply (I := I) (x := x)]
    rw [inverseMetricSharpFib_inner (I := I) g₀ x (g0FlatCLM (I := I) g₁ x D) u]
  rw [hPinner, cotangentToDual_g0FlatCLM (I := I) g₁ x D u]
  rw [g₁.symm x D u, hu]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma connDiffVec_eq_invSharp_koszul
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x) =
      inverseMetricSharpFib (I := I) g₁ x
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) :=
  connDiff_eq_appCc_invGram_covGrad (I := I) (M := M) g₀ g₁ X Y x

omit [NeZero (Module.finrank ℝ E)] in
theorem connDiffInner_g1_eq_half_covGradSymmS
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (x : M) (a b c : TangentSpace I x) :
    g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b) c =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 3
            (covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)) x ![b, a, c]
          + unitModel (I := I) (M := M) g₀ 3
              (covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)) x ![a, b, c]
          - unitModel (I := I) (M := M) g₀ 3
              (covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)) x ![c, b, a]) := by
  have hbil : ∀ (b' : M) (u w : TangentSpace I b'),
      smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) g₀ T) b' u w =
        g₁.inner b' u w - g₀.inner b' u w :=
    symmS_hbil_of_realize (I := I) (M := M) g₀ g₁ T hg₁
  set af : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x a, smoothExtensionTangent_contMDiff (I := I) x a⟩ with haf
  set bf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x b, smoothExtensionTangent_contMDiff (I := I) x b⟩ with hbf
  set cf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x c, smoothExtensionTangent_contMDiff (I := I) x c⟩ with hcf
  have haa : af x = a := smoothExtensionTangent_eq (I := I) x a
  have hbb : bf x = b := smoothExtensionTangent_eq (I := I) x b
  have hcc : cf x = c := smoothExtensionTangent_eq (I := I) x c
  have h := koszulCovGradCovec_dual_apply_covGrad (I := I) (M := M) g₀ g₁
    (ccTensor02Symm (I := I) g₀ T) hbil bf af cf x
  rw [koszulCovGradCovec_dual_apply (I := I) (M := M) g₀ g₁ bf af x (cf x)] at h
  rw [haa, hbb, hcc] at h
  rw [h]
  rw [show unitModel (I := I) (M := M) g₀ 3
        (covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)) x ![b, a, c]
      = unitModel (I := I) (M := M) g₀ 3
          (covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)) x ![bf x, af x, cf x] from by
    rw [haa, hbb, hcc]]
  rw [show unitModel (I := I) (M := M) g₀ 3
        (covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)) x ![a, b, c]
      = unitModel (I := I) (M := M) g₀ 3
          (covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)) x ![af x, bf x, cf x] from by
    rw [haa, hbb, hcc]]
  rw [show unitModel (I := I) (M := M) g₀ 3
        (covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)) x ![c, b, a]
      = unitModel (I := I) (M := M) g₀ 3
          (covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)) x ![cf x, bf x, af x] from by
    rw [haa, hbb, hcc]]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem covDerivConnDiff_g1inner_eq_secondCovGrad_lowerArms
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (ζ : TangentSpace I x) :
    g₁.inner x
        (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x) ζ =
      ((cotangentCov (LeviCivita (I := I) g₀)).toFun
          (fun b : M => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)) ζ
        - g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))
            (inverseMetricSharpFib (I := I) g₁ x
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X
                ⟨smoothExtensionTangent (I := I) x ζ,
                  smoothExtensionTangent_contMDiff (I := I) x ζ⟩ x))
        - g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x)
              ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))) ζ
        - g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x)) ζ
        - g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (inverseMetricSharpFib (I := I) g₁ x
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)) (X x)) ζ := by
  rw [covDerivConnDiff_eq_invGramSharp_graded (I := I) (M := M) g₀ g₁ X Y Z x]
  rw [map_sub, map_sub, map_sub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sub_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x _ ζ, cotangentToDualLinear_apply,
    cotangentToDual_apply]
  rw [show (dualToCotangent (I := I)
        ((cotangentCov (LeviCivita (I := I) g₁)).toFun
          (fun b : M => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x))) (fun _ : Fin 1 => ζ)
      = ((cotangentCov (LeviCivita (I := I) g₁)).toFun
          (fun b : M => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)) ζ from by
    rw [← cotangentToDual_apply, cotangentToDual_dualToCotangent, ContinuousLinearMap.coe_coe]]
  rw [covDerivConnDiff_principal_align (I := I) (M := M) g₀ g₁ X Y Z x ζ]
  rw [show cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x ζ (X x))
      = g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x ζ (X x)) from by
    rw [show cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x ζ (X x))
        = cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x ζ (X x)) from rfl]
    exact koszulCovGradCovec_dual_apply (I := I) (M := M) g₀ g₁ Z Y x _]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x ζ (X x)
      = inverseMetricSharpFib (I := I) g₁ x
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X
            ⟨smoothExtensionTangent (I := I) x ζ,
              smoothExtensionTangent_contMDiff (I := I) x ζ⟩ x) from by
    have hζfx : (⟨smoothExtensionTangent (I := I) x ζ,
        smoothExtensionTangent_contMDiff (I := I) x ζ⟩
        : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x = ζ :=
      smoothExtensionTangent_eq (I := I) x ζ
    have h := connDiffVec_eq_invSharp_koszul (I := I) (M := M) g₀ g₁ X
      ⟨smoothExtensionTangent (I := I) x ζ,
        smoothExtensionTangent_contMDiff (I := I) x ζ⟩ x
    rw [hζfx] at h
    exact h]
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g₁ g₀ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2
        (raisedKoszul (I := I) g₀ g₁) (sharpFlatEndoCc (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connDiffSection_toSection, appCcRS_toSection, sharpFlatEndoCc_toSection,
    raisedKoszul_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  rw [ContinuousLinearMap.comp_apply]
  rw [connDiffFib_apply_eval]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        raisedKoszulFib (I := I) g₀ g₁ x)
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        TensorRSSpace.ofCLM
          ((g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x))) om)
      = raisedKoszulPairing (I := I) g₀ g₁ x
          ((g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x) om) from rfl]
  rw [raisedKoszulPairing_apply]
  rw [ContinuousLinearMap.comp_apply]
  exact connDiffPairing_eq_raisedKoszul_sharpFlat (I := I) g₀ g₁ x om YZ

def dualCotangentCLM (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] Tensor0SSpace 1 I x :=
  (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 1 x).symm.toContinuousLinearMap.comp
    (continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ).symm.toContinuousLinearMap

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma cotangentToCLM_apply_vec (x : M) (α : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    cotangentToCLM (I := I) α w = α (fun _ : Fin 1 => w) := by
  have h := cotangentToDual_apply (I := I) α w
  rw [show cotangentToDual (I := I) α w = cotangentToCLM (I := I) α w from rfl] at h
  exact h

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma cotangentToCLM_add (x : M) (om om' : Tensor0SSpace 1 I x) :
    cotangentToCLM (I := I) (om + om') =
      cotangentToCLM (I := I) om + cotangentToCLM (I := I) om' := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.add_apply, cotangentToCLM_apply_vec, cotangentToCLM_apply_vec,
    cotangentToCLM_apply_vec, ContinuousMultilinearMap.add_apply]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma cotangentToCLM_smul (x : M) (c : ℝ) (om : Tensor0SSpace 1 I x) :
    cotangentToCLM (I := I) (c • om) = c • cotangentToCLM (I := I) om := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.smul_apply, cotangentToCLM_apply_vec, cotangentToCLM_apply_vec,
    ContinuousMultilinearMap.smul_apply]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma cotangentToCLM_sub (x : M) (om om' : Tensor0SSpace 1 I x) :
    cotangentToCLM (I := I) (om - om') =
      cotangentToCLM (I := I) om - cotangentToCLM (I := I) om' := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.sub_apply, cotangentToCLM_apply_vec, cotangentToCLM_apply_vec,
    cotangentToCLM_apply_vec, ContinuousMultilinearMap.sub_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma dualCotangentCLM_eq (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) :
    dualCotangentCLM (I := I) (x := x) φ = dualToCotangent (I := I) (x := x) φ.toLinearMap := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply, cotangentToDual_apply,
    cotangentToDual_dualToCotangent]
  rw [dualCotangentCLM, ContinuousLinearMap.comp_apply]
  change (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 1 x).symm
      ((continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ).symm φ) (fun _ : Fin 1 => w) = _
  rw [tensor0SSpace_continuousLinearEquiv_symm_apply]
  rw [continuousMultilinearCurryFin1_symm_apply]
  rfl

def flatArmVecCLM (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M)
    (om : Tensor0SSpace 1 I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  if kind then
    -(PDE.DeTurck.connDiff (I := I) g₁ g₀ x (inverseMetricSharpFib (I := I) g₁ x om))
  else
    (inverseMetricSharpFib (I := I) g₁ x).comp
      ((dualCotangentCLM (I := I) (x := x)).comp
        (-((ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x) ℝ
              (cotangentToCLM (I := I) om)).comp
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip)))

def flatArmVec (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M)
    (om : Tensor0SSpace 1 I x) (v0 : TangentSpace I x) : TangentSpace I x :=
  if kind then
    - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (inverseMetricSharpFib (I := I) g₁ x om) v0
  else
    inverseMetricSharpFib (I := I) g₁ x
      (dualToCotangent (I := I)
        (-(cotangentToCLM (I := I) om).comp
            ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0)).toLinearMap)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma flatArmVecCLM_apply (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M)
    (om : Tensor0SSpace 1 I x) (v0 : TangentSpace I x) :
    flatArmVecCLM (I := I) g₀ g₁ kind x om v0 = flatArmVec (I := I) g₀ g₁ kind x om v0 := by
  cases kind with
  | true =>
      simp only [flatArmVecCLM, flatArmVec, if_true]
      rw [ContinuousLinearMap.neg_apply]
  | false =>
      simp only [flatArmVecCLM, flatArmVec, if_neg (by decide : ¬ (false = true))]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.compL_apply, dualCotangentCLM_eq]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma flatArmVec_add_om (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M)
    (om om' : Tensor0SSpace 1 I x) (v0 : TangentSpace I x) :
    flatArmVec (I := I) g₀ g₁ kind x (om + om') v0 =
      flatArmVec (I := I) g₀ g₁ kind x om v0 + flatArmVec (I := I) g₀ g₁ kind x om' v0 := by
  cases kind with
  | true =>
      simp only [flatArmVec, if_true, map_add, ContinuousLinearMap.add_apply, neg_add]
  | false =>
      simp only [flatArmVec, if_neg (by decide : ¬ (false = true)), ← dualCotangentCLM_eq]
      rw [cotangentToCLM_add]
      rw [show (-(cotangentToCLM (I := I) om + cotangentToCLM (I := I) om').comp
              ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0))
          = (-(cotangentToCLM (I := I) om).comp
              ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0))
            + (-(cotangentToCLM (I := I) om').comp
              ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0)) from by
        rw [ContinuousLinearMap.add_comp, neg_add]]
      rw [map_add, map_add]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma flatArmVec_smul_om (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M)
    (c : ℝ) (om : Tensor0SSpace 1 I x) (v0 : TangentSpace I x) :
    flatArmVec (I := I) g₀ g₁ kind x (c • om) v0 =
      c • flatArmVec (I := I) g₀ g₁ kind x om v0 := by
  cases kind with
  | true =>
      simp only [flatArmVec, if_true, map_smul, ContinuousLinearMap.smul_apply, smul_neg]
  | false =>
      simp only [flatArmVec, if_neg (by decide : ¬ (false = true)), ← dualCotangentCLM_eq]
      rw [cotangentToCLM_smul]
      rw [show (-(c • cotangentToCLM (I := I) om).comp
              ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0))
          = c • (-(cotangentToCLM (I := I) om).comp
              ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0)) from by
        rw [ContinuousLinearMap.smul_comp, smul_neg]]
      rw [map_smul, map_smul]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma flatArmVec_add_v0 (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M)
    (om : Tensor0SSpace 1 I x) (v0 v0' : TangentSpace I x) :
    flatArmVec (I := I) g₀ g₁ kind x om (v0 + v0') =
      flatArmVec (I := I) g₀ g₁ kind x om v0 + flatArmVec (I := I) g₀ g₁ kind x om v0' := by
  rw [← flatArmVecCLM_apply, ← flatArmVecCLM_apply, ← flatArmVecCLM_apply, map_add]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma flatArmVec_smul_v0 (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M)
    (c : ℝ) (om : Tensor0SSpace 1 I x) (v0 : TangentSpace I x) :
    flatArmVec (I := I) g₀ g₁ kind x om (c • v0) =
      c • flatArmVec (I := I) g₀ g₁ kind x om v0 := by
  rw [← flatArmVecCLM_apply, ← flatArmVecCLM_apply, map_smul]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
lemma flatArmVec_continuous₂ (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M)
    (om : Tensor0SSpace 1 I x) :
    Continuous (fun v0 : TangentSpace I x => flatArmVec (I := I) g₀ g₁ kind x om v0) := by
  have heq : (fun v0 : TangentSpace I x => flatArmVec (I := I) g₀ g₁ kind x om v0) =
      (fun v0 : TangentSpace I x => flatArmVecCLM (I := I) g₀ g₁ kind x om v0) := by
    funext v0; rw [flatArmVecCLM_apply]
  rw [heq]
  exact (flatArmVecCLM (I := I) g₀ g₁ kind x om).continuous

set_option maxHeartbeats 6400000 in
def flatArmPairing (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M)
    (om : Tensor0SSpace 1 I x) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun YZ => g₀.inner x (flatArmVec (I := I) g₀ g₁ kind x om (YZ 0)) (YZ 1)
      map_update_add' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i Y Y'
        fin_cases i <;>
          simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
            Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true]
        · rw [flatArmVec_add_v0, map_add, ContinuousLinearMap.add_apply]
        · rw [map_add]
      map_update_smul' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i c Y
        fin_cases i <;>
          simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
            Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true]
        · rw [flatArmVec_smul_v0, map_smul, ContinuousLinearMap.smul_apply]
        · rw [map_smul]
      cont := by
        have hpair : Continuous (fun YZ : Fin 2 → TangentSpace I x => (YZ 0, YZ 1)) :=
          (continuous_apply 0).prodMk (continuous_apply 1)
        have hvec : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
            flatArmVec (I := I) g₀ g₁ kind x om (YZ 0)) :=
          (flatArmVec_continuous₂ (I := I) g₀ g₁ kind x om).comp (continuous_apply 0)
        have hbil : Continuous (fun p : TangentSpace I x × TangentSpace I x =>
            g₀.inner x p.1 p.2) := (g₀.inner x).continuous₂
        exact hbil.comp (hvec.prodMk (continuous_apply 1)) } : Tensor0SSpace 2 I x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma flatArmPairing_apply (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    (flatArmPairing (I := I) g₀ g₁ kind x om) YZ =
      g₀.inner x (flatArmVec (I := I) g₀ g₁ kind x om (YZ 0)) (YZ 1) := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
lemma flatArmPairing_add (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M)
    (om om' : Tensor0SSpace 1 I x) :
    flatArmPairing (I := I) g₀ g₁ kind x (om + om') =
      flatArmPairing (I := I) g₀ g₁ kind x om + flatArmPairing (I := I) g₀ g₁ kind x om' := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  rw [show (flatArmPairing (I := I) g₀ g₁ kind x om + flatArmPairing (I := I) g₀ g₁ kind x om') YZ =
      flatArmPairing (I := I) g₀ g₁ kind x om YZ + flatArmPairing (I := I) g₀ g₁ kind x om' YZ from
    ContinuousMultilinearMap.add_apply _ _ _]
  rw [flatArmPairing_apply, flatArmPairing_apply, flatArmPairing_apply,
    flatArmVec_add_om, map_add, ContinuousLinearMap.add_apply]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
lemma flatArmPairing_smul (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M)
    (c : ℝ) (om : Tensor0SSpace 1 I x) :
    flatArmPairing (I := I) g₀ g₁ kind x (c • om) =
      c • flatArmPairing (I := I) g₀ g₁ kind x om := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  rw [show (c • flatArmPairing (I := I) g₀ g₁ kind x om) YZ =
      c • flatArmPairing (I := I) g₀ g₁ kind x om YZ from
    ContinuousMultilinearMap.smul_apply _ _ _]
  rw [flatArmPairing_apply, flatArmPairing_apply, flatArmVec_smul_om, map_smul,
    ContinuousLinearMap.smul_apply]

def flatArmFib (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M) :
    TensorRSSpace 1 2 I x :=
  TensorRSSpace.ofCLM
    (LinearMap.toContinuousLinearMap
      { toFun := fun om => flatArmPairing (I := I) g₀ g₁ kind x om
        map_add' := flatArmPairing_add g₀ g₁ kind x
        map_smul' := flatArmPairing_smul g₀ g₁ kind x })

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma flatArmFib_apply (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M)
    (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from flatArmFib (I := I) g₀ g₁ kind x) om =
      flatArmPairing (I := I) g₀ g₁ kind x om := rfl

def flatArmCovec (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (v0 : TangentSpace I x) : Tensor0SSpace 1 I x :=
  dualToCotangent (I := I)
    (-(cotangentToCLM (I := I) om).comp
        ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0)).toLinearMap

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma flatArmCovec_eval (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (v0 w : TangentSpace I x) :
    flatArmCovec (I := I) g₀ g₁ x om v0 (fun _ : Fin 1 => w) =
      - om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v0) := by
  rw [flatArmCovec, dualToCotangent_apply, ContinuousLinearMap.coe_neg, LinearMap.neg_apply,
    ContinuousLinearMap.coe_comp, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.flip_apply]
  rw [cotangentToCLM_apply_vec]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma flatArmCovec_section_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (om : ContMDiffSection I (Tensor0SModel 1 ℝ E) ∞ (fun x : M => Tensor0SSpace 1 I x))
    (V0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) x
        (flatArmCovec (I := I) g₀ g₁ x (om x) (V0 x))) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 1
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (flatArmCovec (I := I) g₀ g₁ x (om x) (V0 x) :
        Bundle.continuousMultilinearMap ℝ 1 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y (σ 0) x) (V0 x))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ (Y (σ 0)).contMDiff V0.contMDiff
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => - Tensor0SSpace.toModel (om x)
        (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y (σ 0) x) (V0 x))) x₀ := by
    have hsa : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (om x)
          (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y (σ 0) x) (V0 x))) x₀ :=
      TensorMultilinear.contMDiffAt_section_apply (n := 1) (x₀ := x₀)
        (fun x : M => om x) (om.contMDiff x₀)
        (fun _ : Fin 1 => fun x : M =>
          PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y (σ 0) x) (V0 x))
        (fun _ => (hconn x₀))
    exact hsa.neg
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
    rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change (flatArmCovec (I := I) g₀ g₁ x (om x) (V0 x)) (fun j : Fin 1 => e₁.symmL ℝ x (b (σ j))) = _
  rw [show (fun j : Fin 1 => e₁.symmL ℝ x (b (σ j))) = (fun _ : Fin 1 => e₁.symmL ℝ x (b (σ 0))) from by
    funext j; fin_cases j; rfl]
  rw [hframe0]
  rw [flatArmCovec_eval]
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma flatArmVec_section_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool)
    (om : ContMDiffSection I (Tensor0SModel 1 ℝ E) ∞ (fun x : M => Tensor0SSpace 1 I x))
    (V0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (flatArmVec (I := I) g₀ g₁ kind x (om x) (V0 x))) := by
  cases kind with
  | true =>
      have hsharp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
            (inverseMetricSharpFib (I := I) g₁ x (om x))) :=
        ContMDiff.clm_bundle_apply (b := id)
          (inverseMetricSharpField_contMDiff (I := I) g₁) om.contMDiff
      have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (inverseMetricSharpFib (I := I) g₁ x (om x)) (V0 x))) :=
        PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hsharp V0.contMDiff
      refine (hconn.neg_section).congr (fun x => ?_)
      simp only [flatArmVec, if_true]
      rfl
  | false =>
      have hcovec : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
          (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
            (E := fun z : M => Tensor0SSpace 1 I z) x
            (flatArmCovec (I := I) g₀ g₁ x (om x) (V0 x))) :=
        flatArmCovec_section_contMDiff (I := I) g₀ g₁ om V0
      have hsharp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
            (inverseMetricSharpFib (I := I) g₁ x
              (flatArmCovec (I := I) g₀ g₁ x (om x) (V0 x)))) :=
        ContMDiff.clm_bundle_apply (b := id)
          (inverseMetricSharpField_contMDiff (I := I) g₁) hcovec
      refine hsharp.congr (fun x => ?_)
      simp only [flatArmVec, if_neg (by decide : ¬ (false = true))]
      rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma flatArmScalar_section_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool)
    (om : ContMDiffSection I (Tensor0SModel 1 ℝ E) ∞ (fun x : M => Tensor0SSpace 1 I x))
    (V0 V1 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x (flatArmVec (I := I) g₀ g₁ kind x (om x) (V0 x)) (V1 x)) x₀ := by
  have hvec := flatArmVec_section_contMDiff (I := I) g₀ g₁ kind om V0
  have h_total : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M => (⟨b, g₀.inner b (flatArmVec (I := I) g₀ g₁ kind b (om b) (V0 b)) (V1 b)⟩ :
        TotalSpace ℝ (Bundle.Trivial M ℝ))) x₀ :=
    (ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id)
      g₀.contMDiff.contMDiffOn hvec.contMDiffOn V1.contMDiff.contMDiffOn x₀
      (mem_univ x₀)).contMDiffAt univ_mem
  rw [Bundle.contMDiffAt_totalSpace] at h_total
  exact h_total.2

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem flatArmFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) x (flatArmFib (I := I) g₀ g₁ kind x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x : M => (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      flatArmFib (I := I) g₀ g₁ kind x))
  intro om
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  have hsec : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (flatArmPairing (I := I) g₀ g₁ kind x (om x))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (flatArmPairing (I := I) g₀ g₁ kind x (om x) :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
    intro σ x₀
    set b := Module.finBasis ℝ E with hb
    set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
    have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
    obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
    have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => g₀.inner x
          (flatArmVec (I := I) g₀ g₁ kind x (om x) (Y (σ 0) x)) (Y (σ 1) x)) x₀ :=
      flatArmScalar_section_contMDiff (I := I) g₀ g₁ kind ⟨_, om.contMDiff⟩ (Y (σ 0)) (Y (σ 1)) x₀
    refine hscalar.congr_of_eventuallyEq ?_
    have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
    filter_upwards [h_base₁, hY] with x hx₁ hYx
    rw [continuousMultilinearMap_basis_repr]
    have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
      rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    have hframe1 : e₁.symmL ℝ x (b (σ 1)) = (Y (σ 1)) x := by
      rw [hYx (σ 1), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    change (flatArmPairing (I := I) g₀ g₁ kind x (om x))
        (fun j : Fin 2 => e₁.symmL ℝ x (b (σ j))) = _
    rw [flatArmPairing_apply]
    rw [hframe0, hframe1]
  refine hsec.congr ?_
  intro x
  rfl

def flatArmCc (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M => flatArmFib (I := I) g₀ g₁ kind x
      contMDiff_toFun := flatArmFib_contMDiff (I := I) g₀ g₁ kind }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma flatArmCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M) :
    (flatArmCc (I := I) g₀ g₁ kind).toSection x = flatArmFib (I := I) g₀ g₁ kind x := rfl

def omRecoverEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 1 where
  toSection :=
    { toFun := fun x : M => TensorRSSpace.ofCLM
        ((g0FlatCLM (I := I) g₁ x).comp (inverseMetricSharpFib (I := I) g₀ x))
      contMDiff_toFun := sharpFlatEndoCcFib_contMDiff (I := I) g₁ g₀ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma omRecoverEndoCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (omRecoverEndoCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM
        ((g0FlatCLM (I := I) g₁ x).comp (inverseMetricSharpFib (I := I) g₀ x)) := rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma omRecoverEndoCc_apply_covec (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (omRecoverEndoCc (I := I) g₀ g₁).toSection x) D =
      g0FlatCLM (I := I) g₁ x (inverseMetricSharpFib (I := I) g₀ x D) := by
  rw [omRecoverEndoCc_toSection]
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma sharpFlatEndoCc_toSection_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) D =
      g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x D) := by
  rw [sharpFlatEndoCc_toSection]
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma omRecoverEndoCc_comp_sharpFlatEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (omRecoverEndoCc (I := I) g₀ g₁).toSection x).comp
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) =
      ContinuousLinearMap.id ℝ (Tensor0SSpace 1 I x) := by
  apply ContinuousLinearMap.ext
  intro om
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [sharpFlatEndoCc_toSection_apply (I := I) g₀ g₁ x om]
  rw [omRecoverEndoCc_apply_covec (I := I) g₀ g₁ x
    (g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om))]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [g0FlatCLM_inverseMetricSharpFib (I := I) g₁ x om]

def flatArmCoeffCc (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) : SmoothCcTensor g₀ 1 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2
    (flatArmCc (I := I) g₀ g₁ kind) (omRecoverEndoCc (I := I) g₀ g₁)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma flatArmCoeffCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M) :
    (flatArmCoeffCc (I := I) g₀ g₁ kind).toSection x =
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          (flatArmCc (I := I) g₀ g₁ kind).toSection x).comp
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (omRecoverEndoCc (I := I) g₀ g₁).toSection x) := by
  rw [flatArmCoeffCc, appCcRS_toSection]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem flatArmCc_eq_appCcRS_flatArmCoeffCc (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) :
    flatArmCc (I := I) g₀ g₁ kind =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2
        (flatArmCoeffCc (I := I) g₀ g₁ kind) (sharpFlatEndoCc (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCcRS_toSection, flatArmCoeffCc_toSection]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (flatArmCc (I := I) g₀ g₁ kind).toSection x).comp
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
            (omRecoverEndoCc (I := I) g₀ g₁).toSection x))).comp
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (sharpFlatEndoCc (I := I) g₀ g₁).toSection x)
      = (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (flatArmCc (I := I) g₀ g₁ kind).toSection x).comp
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
              (omRecoverEndoCc (I := I) g₀ g₁).toSection x).comp
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
              (sharpFlatEndoCc (I := I) g₀ g₁).toSection x)) from
    (ContinuousLinearMap.comp_assoc _ _ _).symm]
  rw [omRecoverEndoCc_comp_sharpFlatEndoCc (I := I) g₀ g₁ x]
  rw [ContinuousLinearMap.comp_id]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem raisedKoszulVec_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    {σ τ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x : M =>
      TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x (σ x)))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x : M =>
      TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x (τ x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (raisedKoszulVec (I := I) g₀ g₁ x (σ x) (τ x))) := by
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (σ x) (τ x))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hσ hτ
  have hraise : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (sharpFlatRaiseEndo (I := I) g₀ g₁ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (σ x) (τ x)))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (sharpFlatRaiseEndo_contMDiff (I := I) g₀ g₁) hconn
  refine hraise.congr (fun x => ?_)
  rw [raisedKoszulVec_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma raisedKoszul_tensorCovDerivAt_homSplit
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) x (X x))
        (om x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
          (fun y : M => raisedKoszulPairing (I := I) g₀ g₁ y (om y)) x (X x) -
        raisedKoszulPairing (I := I) g₀ g₁ x
          (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
            (fun y : M => om y) x (X x)) := by
  have hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) y
        ((raisedKoszul (I := I) g₀ g₁).toSection y)) x :=
    (raisedKoszul (I := I) g₀ g₁).toSection.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hw : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E))
      (fun y : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) y (om y)) x :=
    om.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (X y)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) x (X x)]
  have hsplit := TensorRSNabla.tensorRSCovariantDerivative_apply_of_mdifferentiableAt
    (I := I) (M := M) 1 2 (LeviCivita (I := I) g₀)
    (fun y : M => (raisedKoszul (I := I) g₀ g₁).toSection y) (fun y : M => om y)
    (fun y : M => X y) hτ hw hV
  have hval : (fun y : M =>
        (show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 2 I y from
          (raisedKoszul (I := I) g₀ g₁).toSection y) (om y)) =
      (fun y : M => raisedKoszulPairing (I := I) g₀ g₁ y (om y)) := by
    funext y
    rw [raisedKoszul_toSection]
    rfl
  rw [hsplit, hval]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma tensorSectionMDiffAt_raisedKoszulPairing
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯) (x : M) :
    Integral.Connection.TensorSectionMDiffAt (I := I) 2
      (fun y : M => raisedKoszulPairing (I := I) g₀ g₁ y (om y)) x := by
  classical
  have hval : (fun y : M => raisedKoszulPairing (I := I) g₀ g₁ y (om y)) =
      (fun y : M => (show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 2 I y from
        (raisedKoszul (I := I) g₀ g₁).toSection y) (om y)) := by
    funext y
    rw [raisedKoszul_toSection]
    rfl
  rw [hval]
  unfold Integral.Connection.TensorSectionMDiffAt
  have hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) y
        ((raisedKoszul (I := I) g₀ g₁).toSection y)) x :=
    (raisedKoszul (I := I) g₀ g₁).toSection.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hw : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E))
      (fun y : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) y (om y)) x :=
    om.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
    (F₁ := Tensor0SModel 1 ℝ E) (F₂ := Tensor0SModel 2 ℝ E)
    (E₁ := fun y : M => Tensor0SSpace 1 I y)
    (E₂ := fun y : M => Tensor0SSpace 2 I y)
    (IM := I) (IB := I)
    (b := id)
    (ϕ := fun y : M => (show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 2 I y from
      (raisedKoszul (I := I) g₀ g₁).toSection y))
    (v := fun y : M => om y) hτ hw

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
theorem cotangentToCLMField_contMDiff
    (Dsec : ContMDiffSection I (Tensor0SModel 1 ℝ E) ∞ (fun x : M => Tensor0SSpace 1 I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun z : M => TangentSpace I z →L[ℝ] ℝ) b
        (cotangentToCLM (I := I) (Dsec b))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := ℝ) (V₂ := fun _ : M => ℝ)
    (φ := fun b : M => cotangentToCLM (I := I) (Dsec b))
  intro Z
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => Tensor0SSpace.toModel (Dsec b) (fun _ : Fin 1 => Z b)) :=
    TensorMultilinear.contMDiff_section_apply (n := 1)
      (fun b : M => Dsec b) Dsec.contMDiff
      (fun _ : Fin 1 => fun b : M => Z b) (fun _ => Z.contMDiff)
  have hmk : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) b
        (Tensor0SSpace.toModel (Dsec b) (fun _ : Fin 1 => Z b))) := by
    intro x
    exact (contMDiffAt_section (F := ℝ) (E := Bundle.Trivial M ℝ) x).mpr (hscalar x)
  refine hmk.congr (fun b => ?_)
  change (⟨b, Tensor0SSpace.toModel (Dsec b) (fun _ : Fin 1 => Z b)⟩ :
      TotalSpace ℝ (Bundle.Trivial M ℝ))
    = TotalSpace.mk' ℝ (E := fun _ : M => ℝ) b (cotangentToCLM (I := I) (Dsec b) (Z b))
  rw [cotangentToCLM_apply_vec]
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma sharpFlatEndoCc_apply_covec (g₀ g₁ : SmoothRiemannianMetric I M) (y : M)
    (D : Tensor0SSpace 1 I y) :
    (show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 1 I y from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection y) D =
      g0FlatCLM (I := I) g₀ y (inverseMetricSharpFib (I := I) g₁ y D) := by
  rw [sharpFlatEndoCc_toSection]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma cotangentToCLM_eq_metricFlat_g0Flat_sharp
    (g₀ g₁ : SmoothRiemannianMetric I M) (y : M) (D : Tensor0SSpace 1 I y) :
    cotangentToCLM (I := I)
        (g0FlatCLM (I := I) g₀ y (inverseMetricSharpFib (I := I) g₁ y D)) =
      Integral.Connection.metricFlat (I := I) g₀
        (fun b : M => inverseMetricSharpFib (I := I) g₁ b D) y := by
  apply ContinuousLinearMap.ext
  intro u
  rw [cotangentToCLM_apply_vec, ← cotangentToDual_apply,
    cotangentToDual_g0FlatCLM, Integral.Connection.metricFlat_apply]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensor0SDeriv_one_D_eq_dualToCotangent_cotangentCov
    (g₀ : SmoothRiemannianMetric I M)
    (Dsec : ContMDiffSection I (Tensor0SModel 1 ℝ E) ∞ (fun x : M => Tensor0SSpace 1 I x))
    (x : M) (v0 : TangentSpace I x) :
    Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
        (fun y : M => Dsec y) x v0 =
      dualToCotangent (I := I)
        ((cotangentCov (LeviCivita (I := I) g₀)).toFun
          (fun b : M => cotangentToCLM (I := I) (Dsec b)) x v0) := by
  classical
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro u
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x u
  have hDmd : Integral.Connection.TensorSectionMDiffAt (I := I) 1 (fun y : M => Dsec y) x :=
    (Dsec.contMDiff x).mdifferentiableAt (by norm_num)
  have hbridge := tensor0SCovariantDerivative_one_cotangentToCLM
    (I := I) g₀ (fun y : M => Dsec y) hDmd Y v0
  have hθmd : MDiffAtCotangent (I := I) (fun b : M => cotangentToCLM (I := I) (Dsec b)) x := by
    have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun z : M => TangentSpace I z →L[ℝ] ℝ) b
          (cotangentToCLM (I := I) (Dsec b))) :=
      cotangentToCLMField_contMDiff (I := I) Dsec
    exact (h1 x).mdifferentiableAt (by norm_num)
  have hYmd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hpair := cotangentCov_dualPairing (LeviCivita (I := I) g₀)
    (θ := fun b : M => cotangentToCLM (I := I) (Dsec b)) hθmd (Y := fun b : M => Y b) hYmd v0
  rw [show cotangentToDual (I := I)
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => Dsec y) x v0) u
      = cotangentToCLM (I := I)
          (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
            (fun y : M => Dsec y) x v0) u from rfl]
  rw [← hYx]
  rw [hbridge, hpair]
  simp only [add_sub_cancel_right, ContinuousLinearMap.coe_coe]

set_option maxHeartbeats 6400000 in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cotangentToCLM_tensorCovDerivAt_sharpFlatEndoCc_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 1 I x) (v0 w : TangentSpace I x) :
    cotangentToCLM (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          tensorCovDerivAt (I := I) (M := M) g₀ 1 1
            (sharpFlatEndoCc (I := I) g₀ g₁) x v0) D) w =
      g₀.inner x (flatArmVec (I := I) g₀ g₁ true x D v0) w
        + g₀.inner x (flatArmVec (I := I) g₀ g₁ false x D v0) w := by
  classical
  obtain ⟨Dsec, hDsecx⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E) (V := fun y : M => Tensor0SSpace 1 I y)
    (n := (⊤ : ℕ∞)) x D
  set τ := sharpFlatEndoCc (I := I) g₀ g₁ with hτ
  have hLeibniz := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) 1 1
    (LeviCivita (I := I) g₀) τ.toSection Dsec x v0
  have hτD : ∀ y : M, (show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 1 I y from τ.toSection y)
      (Dsec y) = g0FlatCLM (I := I) g₀ y (inverseMetricSharpFib (I := I) g₁ y (Dsec y)) :=
    fun y => sharpFlatEndoCc_apply_covec (I := I) g₀ g₁ y (Dsec y)
  have hmain :
      Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => (show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 1 I y from τ.toSection y)
            (Dsec y)) x v0 =
        Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => g0FlatCLM (I := I) g₀ y
            (inverseMetricSharpFib (I := I) g₁ y (Dsec y))) x v0 := by
    have hfun : (fun y : M => (show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 1 I y from τ.toSection y)
          (Dsec y)) =
        (fun y : M => g0FlatCLM (I := I) g₀ y
          (inverseMetricSharpFib (I := I) g₁ y (Dsec y))) := by
      funext y; exact hτD y
    rw [hfun]
  rw [hmain] at hLeibniz
  set X : Π b : M, TangentSpace I b :=
    fun b : M => inverseMetricSharpFib (I := I) g₁ b (Dsec b) with hX
  have hXmd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (X y)) x := by
    have hsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (X y)) :=
      ContMDiff.clm_bundle_apply (b := id)
        (inverseMetricSharpField_contMDiff (I := I) g₁) Dsec.contMDiff
    exact (hsm x).mdifferentiableAt (by norm_num)
  have hDcotmd : MDiffAtCotangent (I := I)
      (fun b : M => cotangentToCLM (I := I) (Dsec b)) x := by
    have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun z : M => TangentSpace I z →L[ℝ] ℝ) b
          (cotangentToCLM (I := I) (Dsec b))) :=
      cotangentToCLMField_contMDiff (I := I) Dsec
    exact (h1 x).mdifferentiableAt (by norm_num)
  have hflatpar :
      cotangentToCLM (I := I)
          (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
            (fun y : M => g0FlatCLM (I := I) g₀ y (X y)) x v0) w =
        g₀.inner x ((LeviCivita (I := I) g₀).toFun X x v0) w := by
    have hcot : (fun y : M => cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ y (X y))) =
        Integral.Connection.metricFlat (I := I) g₀ X := by
      funext y
      exact cotangentToCLM_eq_metricFlat_g0Flat_sharp (I := I) g₀ g₁ y (Dsec y)
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w
    have hg0flatmd : Integral.Connection.TensorSectionMDiffAt (I := I) 1
        (fun y : M => g0FlatCLM (I := I) g₀ y (X y)) x := by
      have h1 : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
            (E := fun z : M => Tensor0SSpace 1 I z) y
            (g0FlatCLM (I := I) g₀ y (X y))) :=
        ContMDiff.clm_bundle_apply (b := id) (g0FlatField_contMDiff (I := I) g₀)
          (ContMDiff.clm_bundle_apply (b := id)
            (inverseMetricSharpField_contMDiff (I := I) g₁) Dsec.contMDiff)
      exact (h1 x).mdifferentiableAt (by norm_num)
    have hbridge := tensor0SCovariantDerivative_one_cotangentToCLM
      (I := I) g₀ (fun y : M => g0FlatCLM (I := I) g₀ y (X y)) hg0flatmd Y v0
    have hYmd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (Y y)) x :=
      Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hθmd : MDiffAtCotangent (I := I)
        (fun b : M => cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ b (X b))) x := by
      rw [hcot]; exact Integral.Connection.metricFlat_mdiff (I := I) g₀ hXmd
    have hpair := cotangentCov_dualPairing (LeviCivita (I := I) g₀)
      (θ := fun b : M => cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ b (X b))) hθmd
      (Y := fun b : M => Y b) hYmd v0
    rw [← hYx, hbridge, hpair]
    rw [show (fun b : M => cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ b (X b)))
          = Integral.Connection.metricFlat (I := I) g₀ X from hcot]
    rw [cotangentCov_metricDuality (I := I) g₀ hXmd v0 (Y x)]
    rw [hYx]
    simp only [add_sub_cancel_right]
  have hsecondterm :
      cotangentToCLM (I := I)
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from τ.toSection x)
            (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
              Dsec x v0)) w =
        g₀.inner x (inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            ((cotangentCov (LeviCivita (I := I) g₀)).toFun
              (fun b : M => cotangentToCLM (I := I) (Dsec b)) x v0))) w := by
    rw [sharpFlatEndoCc_apply_covec (I := I) g₀ g₁ x
      (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀) Dsec x v0)]
    rw [tensor0SDeriv_one_D_eq_dualToCotangent_cotangentCov (I := I) g₀ Dsec x v0]
    rw [cotangentToCLM_apply_vec]
    rw [← cotangentToDual_g0FlatCLM (I := I) g₀ x
      (inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b : M => cotangentToCLM (I := I) (Dsec b)) x v0))) w]
    rw [cotangentToDual_apply]
  have hcross := Integral.Connection.covGrad_inverseMetricSharpFib_cross
    (I := I) g₀ g₁ (fun b : M => Dsec b) hXmd hDcotmd v0
  have hXval : X x = inverseMetricSharpFib (I := I) g₁ x (Dsec x) := rfl
  rw [show cotangentToCLM (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          tensorCovDerivAt (I := I) (M := M) g₀ 1 1 τ x v0) D) w
      = cotangentToCLM (I := I)
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
            TensorRSNabla.tensorRSCovariantDerivative I M 1 1 (LeviCivita (I := I) g₀)
              (fun y : M => τ.toSection y) x v0) D) w from by
    rw [tensorCovDerivAt_def]]
  rw [← hDsecx]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        TensorRSNabla.tensorRSCovariantDerivative I M 1 1 (LeviCivita (I := I) g₀)
          (fun y : M => τ.toSection y) x v0) (Dsec x))
      = Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => g0FlatCLM (I := I) g₀ y (inverseMetricSharpFib (I := I) g₁ y (Dsec y)))
          x v0
        - (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from τ.toSection x)
            (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
              Dsec x v0) from hLeibniz]
  rw [cotangentToCLM_sub, ContinuousLinearMap.sub_apply, hflatpar, hsecondterm]
  have hXfun : X = fun b : M => inverseMetricSharpFib (I := I) g₁ b (Dsec b) := rfl
  rw [show (LeviCivita (I := I) g₀).toFun X x v0
        = (LeviCivita (I := I) g₀).toFun
            (fun b : M => inverseMetricSharpFib (I := I) g₁ b (Dsec b)) x v0 from by
    rw [hXfun]]
  rw [hcross]
  rw [show (g₀.inner x)
        (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              ((cotangentCov (LeviCivita (I := I) g₀)).toFun
                (fun b : M => cotangentToCLM (I := I) (Dsec b)) x v0))
          - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (inverseMetricSharpFib (I := I) g₁ x (Dsec x)) v0
          + inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (-(cotangentToCLM (I := I) (Dsec x)).comp
                    ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0)).toLinearMap)) w
      = (g₀.inner x)
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                ((cotangentCov (LeviCivita (I := I) g₀)).toFun
                  (fun b : M => cotangentToCLM (I := I) (Dsec b)) x v0))) w
          - (g₀.inner x)
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (inverseMetricSharpFib (I := I) g₁ x (Dsec x)) v0) w
          + (g₀.inner x)
              (inverseMetricSharpFib (I := I) g₁ x
                (dualToCotangent (I := I)
                  (-(cotangentToCLM (I := I) (Dsec x)).comp
                      ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0)).toLinearMap)) w from by
    rw [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]]
  rw [hDsecx]
  rw [show flatArmVec (I := I) g₀ g₁ true x D v0
        = - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (inverseMetricSharpFib (I := I) g₁ x D) v0 from by
    simp only [flatArmVec, if_true]]
  rw [show flatArmVec (I := I) g₀ g₁ false x D v0
        = inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (-(cotangentToCLM (I := I) D).comp
                  ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0)).toLinearMap) from by
    simp only [flatArmVec, if_neg (by decide : ¬ (false = true))]]
  rw [show (g₀.inner x)
        (- PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (inverseMetricSharpFib (I := I) g₁ x D) v0) w
      = - (g₀.inner x)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (inverseMetricSharpFib (I := I) g₁ x D) v0) w from by
    rw [map_neg, ContinuousLinearMap.neg_apply]]
  ring

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_tensor0SOne_eq_cotangentToCLM (x : M)
    (α : Tensor0SSpace 1 I x) (w : Fin 1 → TangentSpace I x) :
    Tensor0SSpace.toModel α w = cotangentToCLM (I := I) α (w 0) := by
  rw [cotangentToCLM_apply_vec]
  congr 1
  funext i; fin_cases i; rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma raisedKoszulPairing_covariantDerivative02_eval
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
          (fun y : M => raisedKoszulPairing (I := I) g₀ g₁ y (om y)) x (X x))
        (Fin.cons (Y x) ![Z x]) =
      Integral.Connection.directionalDeriv (I := I)
          (fun b : M => om b (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ g₁ b (Y b) (Z b))) x (X x)
        - om x (fun _ : Fin 1 =>
            raisedKoszulVec (I := I) g₀ g₁ x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x))
        - om x (fun _ : Fin 1 =>
            raisedKoszulVec (I := I) g₀ g₁ x (Y x) ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)))
      := by
  classical
  set V : Π b : M, Tensor0SSpace 2 I b :=
    fun b => raisedKoszulPairing (I := I) g₀ g₁ b (om b) with hVdef
  have hV : Integral.Connection.TensorSectionMDiffAt (I := I) 2 V x :=
    tensorSectionMDiffAt_raisedKoszulPairing (I := I) g₀ g₁ om x
  set W₁ : Π b : M, Tensor0SSpace 1 I b :=
    fun b => Tensor0SNabla.curriedSection I M V b (Y b) with hW₁
  have hW₁_mdiff : Integral.Connection.TensorSectionMDiffAt (I := I) 1 W₁ x := by
    have hY' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
      Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    unfold Integral.Connection.TensorSectionMDiffAt
    have hCurried := Integral.Connection.mdifferentiableAt_curriedSection_of_section
      (I := I) (M := M) 1 V hV
    exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
      (F₁ := E) (F₂ := Tensor0SModel 1 ℝ E)
      (E₁ := fun b : M => TangentSpace I b)
      (E₂ := fun b : M => Tensor0SSpace 1 I b)
      (IM := I) (IB := I)
      (b := id) (ϕ := fun y : M => Tensor0SNabla.curriedSection I M V y)
      (v := fun y : M => Y y) hCurried hY'
  have hpeel1 := Integral.Connection.tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 1 V hV Y (X x) ![Z x]
  have hpeel2 := Integral.Connection.tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 W₁ hW₁_mdiff Z (X x) (fun i => Fin.elim0 i)
  have hbase : Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)
          (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (Z b)) x (X x))
        (fun i => Fin.elim0 i) =
      Integral.Connection.directionalDeriv (I := I)
        (fun b : M => om b (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ g₁ b (Y b) (Z b))) x (X x) := by
    rw [Integral.Connection.tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (Z b)) x (X x)]
    rw [Integral.Connection.directionalDeriv_eq]
    refine congrArg (fun f => (mfderiv I 𝓘(ℝ, ℝ) f x) (X x)) ?_
    funext b
    rw [Integral.Connection.scalarFn_eq_toModel_elim0 (I := I) (M := M)]
    show Tensor0SSpace.toModel
        (Tensor0SNabla.curriedSection I M W₁ b (Z b))
        (fun i => Fin.elim0 i) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := W₁)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
          (T := W₁ b) (v0 := Z b) (vs := (fun i => Fin.elim0 i))]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M V b (Y b))
        (Fin.cons (Z b) (fun i => Fin.elim0 i)) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := V)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
          (T := V b) (v0 := Y b) (vs := Fin.cons (Z b) (fun i => Fin.elim0 i))]
    simp only [hVdef]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rfl
  have hcorr2 : Tensor0SSpace.toModel (W₁ x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)) (fun i => Fin.elim0 i)) =
      om x (fun _ : Fin 1 =>
        raisedKoszulVec (I := I) g₀ g₁ x (Y x) ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)))
      := by
    have hW₁x : W₁ x = Tensor0SNabla.curriedSection I M V x (Y x) := rfl
    rw [hW₁x, Tensor0SNabla.curriedSection_apply]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V x) (v0 := Y x)
      (vs := Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))
        (fun i => Fin.elim0 i))]
    simp only [hVdef]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rfl
  have hcorr1 : Tensor0SSpace.toModel (V x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x))
          (Fin.cons (Z x) (fun i => Fin.elim0 i))) =
      om x (fun _ : Fin 1 =>
        raisedKoszulVec (I := I) g₀ g₁ x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x))
      := by
    simp only [hVdef]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rfl
  rw [hpeel1]
  rw [show (fun y : M => Tensor0SNabla.curriedSection I M V y (Y y)) = W₁ from rfl]
  rw [show (![Z x] : Fin 1 → E) = Fin.cons (Z x) (fun i => Fin.elim0 i) from by
    funext k; refine Fin.cases rfl (fun j => j.elim0) k]
  rw [hpeel2, hbase, hcorr2, hcorr1]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma raisedKoszulPairing_covariantDerivative01_eval
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    raisedKoszulPairing (I := I) g₀ g₁ x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => om y) x (X x))
        (Fin.cons (Y x) ![Z x]) =
      Integral.Connection.directionalDeriv (I := I)
          (fun b : M => om b (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ g₁ b (Y b) (Z b))) x (X x)
        - om x (fun _ : Fin 1 =>
            (LeviCivita (I := I) g₀).toFun
              (fun b => raisedKoszulVec (I := I) g₀ g₁ b (Y b) (Z b)) x (X x)) := by
  classical
  have hWYZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (raisedKoszulVec (I := I) g₀ g₁ b (Y b) (Z b))) :=
    raisedKoszulVec_contMDiff (I := I) g₀ g₁ Y.contMDiff Z.contMDiff
  set WYZ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b : M => raisedKoszulVec (I := I) g₀ g₁ b (Y b) (Z b)) hWYZ with hWYZdef
  have hom_mdiff : Integral.Connection.TensorSectionMDiffAt (I := I) 1 (fun y : M => om y) x :=
    om.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hpeel := Integral.Connection.tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 (fun y : M => om y) hom_mdiff WYZ (X x) (fun i => Fin.elim0 i)
  have hLHS : raisedKoszulPairing (I := I) g₀ g₁ x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => om y) x (X x))
        (Fin.cons (Y x) ![Z x]) =
      Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => om y) x (X x))
        (Fin.cons (WYZ x) (fun i => Fin.elim0 i)) := by
    rw [raisedKoszulPairing_apply]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    refine congrArg _ ?_
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [hWYZdef]
    rfl
  rw [hLHS, hpeel]
  have hbase : Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)
          (fun y : M => Tensor0SNabla.curriedSection I M (fun y : M => om y) y (WYZ y)) x (X x))
        (fun i => Fin.elim0 i) =
      Integral.Connection.directionalDeriv (I := I)
        (fun b : M => om b (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ g₁ b (Y b) (Z b))) x (X x) := by
    rw [Integral.Connection.tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun y : M => Tensor0SNabla.curriedSection I M (fun y : M => om y) y (WYZ y)) x (X x)]
    rw [Integral.Connection.directionalDeriv_eq]
    refine congrArg (fun f => (mfderiv I 𝓘(ℝ, ℝ) f x) (X x)) ?_
    funext b
    rw [Integral.Connection.scalarFn_eq_toModel_elim0 (I := I) (M := M)]
    show Tensor0SSpace.toModel
        (Tensor0SNabla.curriedSection I M (fun y : M => om y) b (WYZ b))
        (fun i => Fin.elim0 i) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := fun y : M => om y)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := om b) (v0 := WYZ b) (vs := (fun i => Fin.elim0 i))]
    refine congrArg _ ?_
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [hWYZdef]
    rfl
  have hcorr : Tensor0SSpace.toModel ((fun y : M => om y) x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => WYZ b) x (X x)) (fun i => Fin.elim0 i)) =
      om x (fun _ : Fin 1 =>
        (LeviCivita (I := I) g₀).toFun
          (fun b => raisedKoszulVec (I := I) g₀ g₁ b (Y b) (Z b)) x (X x)) := by
    change Tensor0SSpace.toModel (om x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => WYZ b) x (X x))
          (fun i => Fin.elim0 i)) = _
    refine congrArg _ ?_
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [hWYZdef]
    rfl
  rw [hbase, hcorr]

def covDerivRaisedKoszulVec (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  (LeviCivita (I := I) g₀).toFun (fun b => raisedKoszulVec (I := I) g₀ g₁ b (Y b) (Z b)) x (X x)
    - raisedKoszulVec (I := I) g₀ g₁ x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x)
    - raisedKoszulVec (I := I) g₀ g₁ x (Y x)
        ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))

omit [NeZero (Module.finrank ℝ E)] in
theorem raisedKoszul_covGrad_eq_covDerivRaisedKoszulVec
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x)
          (om x))
        (Fin.cons (X x) (Fin.cons (Y x) ![Z x])) =
      om x (fun _ : Fin 1 => covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x) := by
  classical
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) x
    (om x) (Fin.cons (X x) (Fin.cons (Y x) ![Z x]))]
  rw [show (Fin.cons (X x) (Fin.cons (Y x) ![Z x]) : Fin 3 → TangentSpace I x) 0 = X x from rfl]
  rw [show Matrix.vecTail (Fin.cons (X x) (Fin.cons (Y x) ![Z x]) : Fin 3 → TangentSpace I x)
        = Fin.cons (Y x) ![Z x] from by
      funext k; simp only [Matrix.vecTail, Function.comp]
      refine Fin.cases rfl (fun j => ?_) k
      refine Fin.cases rfl (fun j' => ?_) j
      exact j'.elim0]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      tensorCovDerivAt (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) x (X x)) (om x)
      = _ from raisedKoszul_tensorCovDerivAt_homSplit (I := I) g₀ g₁ om X x]
  rw [show Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
            (fun y : M => raisedKoszulPairing (I := I) g₀ g₁ y (om y)) x (X x) -
          raisedKoszulPairing (I := I) g₀ g₁ x
            (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
              (fun y : M => om y) x (X x)))
        (Fin.cons (Y x) ![Z x]) =
      Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
            (fun y : M => raisedKoszulPairing (I := I) g₀ g₁ y (om y)) x (X x))
          (Fin.cons (Y x) ![Z x])
        - Tensor0SSpace.toModel
            (raisedKoszulPairing (I := I) g₀ g₁ x
              (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
                (fun y : M => om y) x (X x)))
            (Fin.cons (Y x) ![Z x]) from by
      rw [Tensor0SSpace.toModel_sub]; rfl]
  rw [raisedKoszulPairing_covariantDerivative02_eval (I := I) g₀ g₁ om X Y Z x]
  rw [show Tensor0SSpace.toModel
        (raisedKoszulPairing (I := I) g₀ g₁ x
          (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
            (fun y : M => om y) x (X x)))
        (Fin.cons (Y x) ![Z x]) =
      raisedKoszulPairing (I := I) g₀ g₁ x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => om y) x (X x))
        (Fin.cons (Y x) ![Z x]) from rfl]
  rw [raisedKoszulPairing_covariantDerivative01_eval (I := I) g₀ g₁ om X Y Z x]
  have hvec : covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x =
      (LeviCivita (I := I) g₀).toFun (fun b => raisedKoszulVec (I := I) g₀ g₁ b (Y b) (Z b)) x (X x)
        - raisedKoszulVec (I := I) g₀ g₁ x
            ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x)
        - raisedKoszulVec (I := I) g₀ g₁ x (Y x)
            ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)) := rfl
  rw [show (fun _ : Fin 1 => covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x)
      = (fun _ : Fin 1 =>
          (LeviCivita (I := I) g₀).toFun (fun b => raisedKoszulVec (I := I) g₀ g₁ b (Y b) (Z b)) x (X x)
            - raisedKoszulVec (I := I) g₀ g₁ x
                ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x)
            - raisedKoszulVec (I := I) g₀ g₁ x (Y x)
                ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)))
      from by funext k; rw [hvec]]
  rw [tensor0SOne_apply_sub' (I := I) x (om x), tensor0SOne_apply_sub' (I := I) x (om x)]
  ring

set_option maxHeartbeats 6400000 in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_sharpFlatEndoCc_eq_arms (g₀ g₁ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 1 1 (sharpFlatEndoCc (I := I) g₀ g₁) =
      flatArmCc (I := I) g₀ g₁ true + flatArmCc (I := I) g₀ g₁ false := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 2 x
  intro D
  apply Tensor0SSpace.toModel_injective (I := I) (M := M)
  apply ContinuousMultilinearMap.ext
  intro v
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 1 1 (sharpFlatEndoCc (I := I) g₀ g₁) x D v]
  rw [toModel_tensor0SOne_eq_cotangentToCLM (I := I) x
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        tensorCovDerivAt (I := I) (M := M) g₀ 1 1 (sharpFlatEndoCc (I := I) g₀ g₁) x (v 0)) D)
      (Matrix.vecTail v)]
  rw [show (Matrix.vecTail v) 0 = v 1 from rfl]
  rw [cotangentToCLM_tensorCovDerivAt_sharpFlatEndoCc_eq (I := I) g₀ g₁ x D (v 0) (v 1)]
  have hRHS : Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          (flatArmCc (I := I) g₀ g₁ true + flatArmCc (I := I) g₀ g₁ false).toSection x) D) v
      = g₀.inner x (flatArmVec (I := I) g₀ g₁ true x D (v 0)) (v 1)
        + g₀.inner x (flatArmVec (I := I) g₀ g₁ false x D (v 0)) (v 1) := by
    rw [show ((flatArmCc (I := I) g₀ g₁ true + flatArmCc (I := I) g₀ g₁ false).toSection x)
          = (flatArmCc (I := I) g₀ g₁ true).toSection x
            + (flatArmCc (I := I) g₀ g₁ false).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          ((flatArmCc (I := I) g₀ g₁ true).toSection x
            + (flatArmCc (I := I) g₀ g₁ false).toSection x)) D
        = (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (flatArmCc (I := I) g₀ g₁ true).toSection x) D
          + (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (flatArmCc (I := I) g₀ g₁ false).toSection x) D from rfl]
    rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
    rw [flatArmCc_toSection, flatArmCc_toSection]
    rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          flatArmFib (I := I) g₀ g₁ true x) D = flatArmPairing (I := I) g₀ g₁ true x D from rfl]
    rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          flatArmFib (I := I) g₀ g₁ false x) D = flatArmPairing (I := I) g₀ g₁ false x D from rfl]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply,
      Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rfl
  rw [hRHS]

theorem riemannianFiberNormSq_iteratedCovGrad_connDiffSection_diagonalProductGrid_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      diagonalGridGrowthFactor (E := E) j *
        ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l
                  (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) := by
  rw [connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) g₀ g₁]
  exact riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le (I := I) (M := M) g₀ j 1 1 2
    (raisedKoszul (I := I) g₀ g₁) (sharpFlatEndoCc (I := I) g₀ g₁) x

theorem riemannianFiberNormSq_iteratedCovGrad_connDiffSection_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (j : ℕ) (x : M)
    (B S : ℕ → ℝ)
    (hKos : ∀ i ≤ j,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤ B i)
    (hSharp : ∀ l ≤ j,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤ S l)
    (hS0 : ∀ l, 0 ≤ S l) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      diagonalGridGrowthFactor (E := E) j *
        ∑ i ∈ Finset.range (j + 1), B i * ∑ l ∈ Finset.range (j + 1 - i), S l := by
  refine (riemannianFiberNormSq_iteratedCovGrad_connDiffSection_diagonalProductGrid_le (I := I) (M := M)
    g₀ g₁ j x).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) j)
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hile : i ≤ j := by simp only [Finset.mem_range] at hi; omega
  have hKi_nn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + i) x _
  have hinner : (∑ l ∈ Finset.range (j + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)) ≤
      ∑ l ∈ Finset.range (j + 1 - i), S l := by
    refine Finset.sum_le_sum (fun l hl => ?_)
    have hlj : l ≤ j := by simp only [Finset.mem_range] at hl; omega
    exact hSharp l hlj
  have hinnerS_nn : (0 : ℝ) ≤ ∑ l ∈ Finset.range (j + 1 - i), S l :=
    Finset.sum_nonneg (fun l _ => hS0 l)
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
      ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i), S l :=
        mul_le_mul_of_nonneg_left hinner hKi_nn
    _ ≤ B i * ∑ l ∈ Finset.range (j + 1 - i), S l :=
        mul_le_mul_of_nonneg_right (hKos i hile) hinnerS_nn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_smul (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_iteratedCovGrad_sharpFlatEndoCc_succ_le_arms
    (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (m + 1)) x
        ((iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
          (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((1 + 1) + m) x
            ((iteratedCovGrad (I := I) g₀ 1 2 m
              (flatArmCc (I := I) g₀ g₁ true)).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((1 + 1) + m) x
            ((iteratedCovGrad (I := I) g₀ 1 2 m
              (flatArmCc (I := I) g₀ g₁ false)).toSection x) := by
  rw [← rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 1 m
    (sharpFlatEndoCc (I := I) g₀ g₁) x]
  rw [covGrad_sharpFlatEndoCc_eq_arms (I := I) g₀ g₁]
  rw [iteratedCovGrad_add]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 ((1 + 1) + m) x _ _

private lemma diagonalGrid_power_closure (G Bc : ℝ) (hG : 0 ≤ G) (hB : 0 ≤ Bc)
    (j : ℕ) (r : ℝ) (hr : 1 ≤ r) (Q : ℕ → ℝ)
    (hQ_nn : ∀ i, 0 ≤ Q i)
    (hQ_le : ∀ i ≤ j, Q i ≤ Bc * r ^ (2 * (i + 1))) :
    G * ∑ i ∈ Finset.range (j + 1), Q i *
        ∑ l ∈ Finset.range (j + 1 - i), Q l ≤
      (G * (↑(j + 1) * Bc) ^ 2) * r ^ (2 * (j + 2)) := by
  have hBr_nn : ∀ k, 0 ≤ Bc * r ^ (2 * (k + 1)) := fun k => by positivity
  have hcell : ∀ i ∈ Finset.range (j + 1),
      Q i * ∑ l ∈ Finset.range (j + 1 - i), Q l ≤
        (↑(j + 1) * Bc ^ 2) * r ^ (2 * (j + 2)) := by
    intro i hi
    have hij : i ≤ j := by simp only [Finset.mem_range] at hi; omega
    have hQi : Q i ≤ Bc * r ^ (2 * (i + 1)) := hQ_le i hij
    have hQi_nn : 0 ≤ Q i := hQ_nn i
    have hinner : ∑ l ∈ Finset.range (j + 1 - i), Q l ≤
        ↑(j + 1) * (Bc * r ^ (2 * (j - i + 1))) := by
      have hterm : ∀ l ∈ Finset.range (j + 1 - i),
          Q l ≤ Bc * r ^ (2 * (j - i + 1)) := by
        intro l hl
        have hlj : l ≤ j - i := by simp only [Finset.mem_range] at hl; omega
        have hlj' : l ≤ j := by omega
        refine le_trans (hQ_le l hlj') ?_
        refine mul_le_mul_of_nonneg_left ?_ hB
        exact pow_le_pow_right₀ hr (by omega)
      refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
      rw [Finset.card_range, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (hBr_nn _)
      exact_mod_cast Nat.cast_le.mpr (by omega : j + 1 - i ≤ j + 1)
    have hinner_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - i), Q l :=
      Finset.sum_nonneg (fun l _ => hQ_nn l)
    calc Q i * ∑ l ∈ Finset.range (j + 1 - i), Q l
        ≤ (Bc * r ^ (2 * (i + 1))) * (↑(j + 1) * (Bc * r ^ (2 * (j - i + 1)))) :=
          mul_le_mul hQi hinner hinner_nn (hBr_nn _)
      _ = (↑(j + 1) * Bc ^ 2) * (r ^ (2 * (i + 1)) * r ^ (2 * (j - i + 1))) := by ring
      _ ≤ (↑(j + 1) * Bc ^ 2) * r ^ (2 * (j + 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← pow_add]
          exact pow_le_pow_right₀ hr (by omega)
  have hsum : ∑ i ∈ Finset.range (j + 1), Q i *
        ∑ l ∈ Finset.range (j + 1 - i), Q l ≤
      ↑(j + 1) * ((↑(j + 1) * Bc ^ 2) * r ^ (2 * (j + 2))) := by
    refine le_trans (Finset.sum_le_sum hcell) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc G * ∑ i ∈ Finset.range (j + 1), Q i *
          ∑ l ∈ Finset.range (j + 1 - i), Q l
      ≤ G * (↑(j + 1) * ((↑(j + 1) * Bc ^ 2) * r ^ (2 * (j + 2)))) :=
        mul_le_mul_of_nonneg_left hsum hG
    _ = (G * (↑(j + 1) * Bc) ^ 2) * r ^ (2 * (j + 2)) := by ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_iteratedCovGrad_two_symmS_le
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (x : M) :
    letI : Bundle.RiemannianBundle
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
    ‖((iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ T)).toSection x :
        Tensor0SBundle.TensorRSSpace 0 4 I x)‖ ≤
      ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
          Tensor0SBundle.TensorRSSpace 0 4 I x)‖ := by
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
  set Tsw : SmoothCcTensor g₀ 0 2 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap 0 1) T with hTsw_def
  have hiter_eq : iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ T) =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 2 2 T +
        iteratedCovGrad (I := I) g₀ 0 2 2 Tsw) := by
    rw [hTsw_def, smul_add]
    exact iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ T 2
  have htoSec : ((iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ T)).toSection x :
        Tensor0SBundle.TensorRSSpace 0 4 I x) =
      (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 2 2 Tsw).toSection x) := by
    rw [hiter_eq]
    rfl
  have hsw_norm : ‖((iteratedCovGrad (I := I) g₀ 0 2 2 Tsw).toSection x :
        Tensor0SBundle.TensorRSSpace 0 4 I x)‖ =
      ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
          Tensor0SBundle.TensorRSSpace 0 4 I x)‖ := by
    have hfib := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g₀ (s := 2) (Equiv.swap 0 1) T 2 x
    rw [← hTsw_def] at hfib
    rw [riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 4 x,
        riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 4 x] at hfib
    have hnn1 : (0 : ℝ) ≤ ‖((iteratedCovGrad (I := I) g₀ 0 2 2 Tsw).toSection x :
        Tensor0SBundle.TensorRSSpace 0 4 I x)‖ := norm_nonneg _
    have hnn2 : (0 : ℝ) ≤ ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
        Tensor0SBundle.TensorRSSpace 0 4 I x)‖ := norm_nonneg _
    nlinarith [hfib, hnn1, hnn2]
  rw [htoSec, norm_smul]
  have habs : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by
    rw [Real.norm_eq_abs]; norm_num
  rw [habs]
  have htri := norm_add_le
    ((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 4 I x)
    ((iteratedCovGrad (I := I) g₀ 0 2 2 Tsw).toSection x :
      Tensor0SBundle.TensorRSSpace 0 4 I x)
  rw [hsw_norm] at htri
  nlinarith [htri, norm_nonneg ((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
    Tensor0SBundle.TensorRSSpace 0 4 I x)]

omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivConnDiff_g1inner_eq_half_secondCovGrad_sub_connDiffSq
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (ζ : TangentSpace I x) :
    g₁.inner x
        (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x) ζ =
      (1 / 2 : ℝ) *
        ( unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ T)) x ![X x, Z x, Y x, ζ]
        + unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ T)) x ![X x, Y x, Z x, ζ]
        - unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ T)) x ![X x, ζ, Z x, Y x] )
      - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))
          (inverseMetricSharpFib (I := I) g₁ x
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X
              ⟨smoothExtensionTangent (I := I) x ζ,
                smoothExtensionTangent_contMDiff (I := I) x ζ⟩ x))
      - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (inverseMetricSharpFib (I := I) g₁ x
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)) (X x)) ζ := by
  rw [covDerivConnDiff_g1inner_eq_secondCovGrad_lowerArms (I := I) (M := M) g₀ g₁ X Y Z x ζ]
  have hbil := symmS_hbil_of_realize (I := I) (M := M) g₀ g₁ T hg₁
  have hTerm1 := koszulCovGradCovec_covDeriv_eq_secondCovGrad (I := I) (M := M) g₀ g₁
    (ccTensor02Symm (I := I) g₀ T) hbil X Y Z x ζ
  have e1 : ((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b : M => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)) ζ
      = (cotangentToDual (I := I) (x := x)
          (dualToCotangent (I := I)
            ((cotangentCov (LeviCivita (I := I) g₀)).toFun
              (fun b : M => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)))) ζ := by
    rw [cotangentToDual_dualToCotangent, ContinuousLinearMap.coe_coe]
  rw [e1, hTerm1]
  rw [connDiffInner_g1_eq_half_covGradSymmS (I := I) g₀ g₁ T hg₁ x
        (Y x) ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)) ζ]
  rw [connDiffInner_g1_eq_half_covGradSymmS (I := I) g₀ g₁ T hg₁ x
        ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x) ζ]
  ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
