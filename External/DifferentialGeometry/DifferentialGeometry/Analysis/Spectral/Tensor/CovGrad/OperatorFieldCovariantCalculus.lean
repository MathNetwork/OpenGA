import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldEvaluationLeibniz


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open TensorMultilinear
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
theorem riemannianFiberNormSq_comp_clm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (φ : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ W : TensorRSSpace 0 r I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (show TensorRSSpace 0 s I x from
          φ.comp (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W)) ≤
        Cφ * riemannianFiberNormSq (I := I) (M := M) g 0 r x W := by
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 r I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 r
  letI instTgt : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 s
  let appOp : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x :=
    LinearMap.toContinuousLinearMap
      { toFun := fun W => (show TensorRSSpace 0 s I x from
          φ.comp (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W))
        map_add' := fun W₁ W₂ => ContinuousLinearMap.comp_add φ _ _
        map_smul' := fun c W => ContinuousLinearMap.comp_smul φ c _ }
  obtain ⟨Cφ, hCφ_nn, hCφ⟩ :=
    riemannianFiberNormSq_clm_apply_le (I := I) (M := M) g r s x appOp
  refine ⟨Cφ, hCφ_nn, fun W => ?_⟩
  have happ : appOp W = (show TensorRSSpace 0 s I x from
      φ.comp (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W)) := rfl
  rw [← happ]
  exact hCφ W

set_option backward.isDefEq.respectTransparency false in

def appCcFib (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (x : M) :
    TensorRSSpace 0 s I x :=
  (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem appCcFib_contMDiff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x
        (appCcFib (I := I) (M := M) g r s Φ W x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 0 ℝ E) (V₁ := fun x : M => Tensor0SSpace 0 I x)
    (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
    (φ := fun x => appCcFib (I := I) (M := M) g r s Φ W x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
      (E := fun z : M => Tensor0SSpace s I z) x
      (appCcFib (I := I) (M := M) g r s Φ W x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
      (E := fun z : M => Tensor0SSpace s I z) x
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) (Y x)))) := by
    funext x; rfl
  rw [heq]
  have hWY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id) W.toSection.contMDiff Y.contMDiff
  exact ContMDiff.clm_bundle_apply (b := id) Φ.toSection.contMDiff hWY

set_option backward.isDefEq.respectTransparency false in

def operatorFieldApply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun x : M => appCcFib (I := I) (M := M) g r s Φ W x
      contMDiff_toFun := appCcFib_contMDiff (I := I) (M := M) g r s Φ W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
@[simp] lemma appCc_toSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (x : M) :
    (operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) := rfl

set_option backward.isDefEq.respectTransparency false in

def slotExtendPointwise (_g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) :
    Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (r + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
          (A.comp ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) D))
      map_add' := fun D₁ D₂ => by
        rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x),
          ContinuousLinearMap.comp_add, map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
      map_smul' := fun c D => by
        rw [map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x),
          ContinuousLinearMap.comp_smul, map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
        rfl }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
@[simp] lemma slotExtendFib_apply (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) (D : Tensor0SSpace (r + 1) I x) :
    slotExtendPointwise (I := I) (M := M) g r s x A D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (A.comp ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) D)) := by
  rw [slotExtendPointwise, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
lemma slotExtendFib_apply_eval (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) (D : Tensor0SSpace (r + 1) I x)
    (v0 : E) (vs : Fin s → E) :
    Tensor0SSpace.toModel (slotExtendPointwise (I := I) (M := M) g r s x A D) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        (A ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) D v0)) vs := by
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    (slotExtendPointwise (I := I) (M := M) g r s x A D) v0 vs]
  have hcurry : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      (slotExtendPointwise (I := I) (M := M) g r s x A D) =
      A.comp ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) D) := by
    rw [slotExtendFib_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hcurry]
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem contMDiff_uncurriedSection_of_contMDiff_homSection {n : ℕ}
    (G : ∀ b : M, TangentSpace I b →L[ℝ] Tensor0SSpace n I b)
    (hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel n ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (E →L[ℝ] Tensor0SModel n ℝ E)
          (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) b (G b))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (n + 1) ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel (n + 1) ℝ E)
          (E := fun y : M => Tensor0SSpace (n + 1) I y) b
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) n b).symm (G b))) := by
  letI : TopologicalSpace (TotalSpace (Tensor0SModel (n + 1) ℝ E)
      (fun y : M => Tensor0SSpace (n + 1) I y)) :=
    tensor0SBundle_topology (n + 1)
  intro x
  rw [Bundle.contMDiffAt_section (F := Tensor0SModel (n + 1) ℝ E)
    (E := fun y : M => Tensor0SSpace (n + 1) I y)]
  have hG_at := (Bundle.contMDiffAt_section (F := E →L[ℝ] Tensor0SModel n ℝ E)
    (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) x).mp (hG x)
  have huncurry :
      ContMDiff 𝓘(ℝ, E →L[ℝ] Tensor0SModel n ℝ E) 𝓘(ℝ, Tensor0SModel (n + 1) ℝ E)
        (∞ : WithTop ℕ∞)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ).symm :=
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ
      ).toContinuousLinearEquiv.symm.toContinuousLinearMap).contMDiff
  have hcomp := huncurry.contMDiffAt.comp x hG_at
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt (Tensor0SModel n ℝ E)
    (fun y : M => Tensor0SSpace n I y) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ _)] with b hb
  have hUcurry : curriedSection (I := I) (M := M)
      (fun y : M => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) n y).symm (G y)) b = G b := by
    rw [curriedSection]
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  have hfwd := trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
    (fun y : M => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) n y).symm (G y)) x b hb
  rw [hUcurry] at hfwd
  change (trivializationAt (Tensor0SModel (n + 1) ℝ E)
      (fun y : M => Tensor0SSpace (n + 1) I y) x
      ⟨b, (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) n b).symm (G b)⟩).2 =
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ).symm
      ((trivializationAt (E →L[ℝ] Tensor0SModel n ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) x ⟨b, G b⟩).2)
  rw [hfwd]
  exact (LinearIsometryEquiv.symm_apply_apply
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ) _).symm

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem slotExtendFib_contMDiff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel (r + 1) (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel (r + 1) (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace (r + 1) (s + 1) I z) x
        (slotExtendPointwise (I := I) (M := M) g r s x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel (r + 1) ℝ E) (V₁ := fun x : M => Tensor0SSpace (r + 1) I x)
    (F₂ := Tensor0SModel (s + 1) ℝ E) (V₂ := fun x : M => Tensor0SSpace (s + 1) I x)
    (φ := fun x => slotExtendPointwise (I := I) (M := M) g r s x
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x))
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 1) I z) x
      (slotExtendPointwise (I := I) (M := M) g r s x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x) (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 1) I z) x
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) (Y x))))) := by
    funext x
    rw [slotExtendFib_apply]
  rw [heq]
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) (Y x)))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
      (φ := fun x => (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) (Y x)))
    intro Z
    have heqZ : (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        (((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) (Y x))) (Z x))) =
        (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
          ((curriedSection (I := I) (M := M) (fun y : M => Y y) x) (Z x)))) := by
      funext x; rfl
    rw [heqZ]
    have hcurriedY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel r ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel r ℝ E)
          (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace r I z) x
          (curriedSection (I := I) (M := M) (fun y : M => Y y) x)) :=
      fun x => contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
        (fun y : M => Y y) x (Y.contMDiff x)
    have hinner : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
          (E := fun z : M => Tensor0SSpace r I z) x
          ((curriedSection (I := I) (M := M) (fun y : M => Y y) x) (Z x))) :=
      ContMDiff.clm_bundle_apply (b := id) hcurriedY Z.contMDiff
    exact ContMDiff.clm_bundle_apply (b := id) Φ.toSection.contMDiff hinner
  exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
    (fun x : M => (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) (Y x))) hG

set_option backward.isDefEq.respectTransparency false in

def slotExtend (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) : SmoothCcTensor g (r + 1) (s + 1) where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (r + 1) (s + 1) I x from
          slotExtendPointwise (I := I) (M := M) g r s x
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x))
      contMDiff_toFun := slotExtendFib_contMDiff (I := I) (M := M) g r s Φ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
@[simp] lemma slotExtend_toSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) :
    (slotExtend (I := I) (M := M) g r s Φ).toSection x =
      (show TensorRSSpace (r + 1) (s + 1) I x from
        slotExtendPointwise (I := I) (M := M) g r s x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)) := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem slotExtend_sub (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : SmoothCcTensor g r s) :
    slotExtend (I := I) (M := M) g r s (X - Y) =
      slotExtend (I := I) (M := M) g r s X - slotExtend (I := I) (M := M) g r s Y := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotExtend (I := I) (M := M) g r s X -
        slotExtend (I := I) (M := M) g r s Y).toSection x) =
      (slotExtend (I := I) (M := M) g r s X).toSection x -
        (slotExtend (I := I) (M := M) g r s Y).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_apply]
  rw [show ((slotExtend (I := I) (M := M) g r s (X - Y)).toSection x) D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (X - Y).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((slotExtend (I := I) (M := M) g r s X).toSection x) D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((slotExtend (I := I) (M := M) g r s Y).toSection x) D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Y.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((X - Y).toSection x) = X.toSection x - Y.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      X.toSection x - Y.toSection x).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) =
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) -
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Y.toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from by
    apply ContinuousLinearMap.ext
    intro w
    rfl]
  rw [map_sub]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem appCc_add_right (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W₁ W₂ : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s Φ (W₁ + W₂) =
      operatorFieldApply (I := I) (M := M) g r s Φ W₁ + operatorFieldApply (I := I) (M := M) g r s Φ W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((operatorFieldApply (I := I) (M := M) g r s Φ W₁ + operatorFieldApply (I := I) (M := M) g r s Φ W₂).toSection x) =
      (operatorFieldApply (I := I) (M := M) g r s Φ W₁).toSection x +
        (operatorFieldApply (I := I) (M := M) g r s Φ W₂).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((W₁ + W₂).toSection x : TensorRSSpace 0 r I x) = W₁.toSection x + W₂.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.comp_add]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem appCc_smul_right (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s Φ (c • W) =
      c • operatorFieldApply (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x) =
      c • (operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • W).toSection x : TensorRSSpace 0 r I x) = c • W.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.comp_smul]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem appCc_smul_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s (c • Φ) W =
      c • operatorFieldApply (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x) =
      c • (operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • Φ).toSection x : TensorRSSpace r s I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem appCc_add_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s (Φ₁ + Φ₂) W =
      operatorFieldApply (I := I) (M := M) g r s Φ₁ W + operatorFieldApply (I := I) (M := M) g r s Φ₂ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((operatorFieldApply (I := I) (M := M) g r s Φ₁ W + operatorFieldApply (I := I) (M := M) g r s Φ₂ W).toSection x) =
      (operatorFieldApply (I := I) (M := M) g r s Φ₁ W).toSection x +
        (operatorFieldApply (I := I) (M := M) g r s Φ₂ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((Φ₁ + Φ₂).toSection x : TensorRSSpace r s I x) = Φ₁.toSection x + Φ₂.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_comp]

set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivAt_appCc_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (x : M) (v : E) :
    (show TensorRSSpace 0 s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s (operatorFieldApply (I := I) (M := M) g r s Φ W) x v) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s Φ x v).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) +
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
            tensorCovDerivAt (I := I) (M := M) g 0 r W x v) := by
  apply ContinuousLinearMap.ext
  intro d
  obtain ⟨dSec, hdSec⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 0 ℝ E) (V := fun y : M => Tensor0SSpace 0 I y) (n := (⊤ : ℕ∞)) x d
  have hWd_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace r I y from W.toSection y) (dSec y))) :=
    ContMDiff.clm_bundle_apply (b := id) W.toSection.contMDiff dSec.contMDiff
  let Wd : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯ :=
    ⟨fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace r I y from W.toSection y) (dSec y),
      hWd_smooth⟩

  have hLHS :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g 0 s (operatorFieldApply (I := I) (M := M) g r s Φ W) x v) d =
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
            (fun y : M =>
              (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) (Wd y)) x v) -
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
              (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
                (fun y : M => dSec y) x v)) := by
    have hval : (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
            (operatorFieldApply (I := I) (M := M) g r s Φ W).toSection y) (dSec y)) =
        (fun y : M =>
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) (Wd y)) := by
      funext y
      rw [appCc_toSection (I := I) (M := M) g r s Φ W y]
      rfl
    rw [show d = dSec x from hdSec.symm,
      tensorCovDerivAt_def (I := I) (M := M) g 0 s (operatorFieldApply (I := I) (M := M) g r s Φ W) x v,
      tensorRSCovariantDerivative_apply (I := I) (M := M) 0 s (LeviCivita (I := I) g)
        (operatorFieldApply (I := I) (M := M) g r s Φ W).toSection dSec x v, hval,
      appCc_toSection (I := I) (M := M) g r s Φ W x, ContinuousLinearMap.comp_apply]

  have hT1 :
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s Φ x v)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) d) =
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
            (fun y : M =>
              (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) (Wd y)) x v) -
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
            (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
              (fun y : M => Wd y) x v) := by
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) d = Wd x from by
      rw [show d = dSec x from hdSec.symm]; rfl,
      tensorCovDerivAt_def (I := I) (M := M) g r s Φ x v,
      tensorRSCovariantDerivative_apply (I := I) (M := M) r s (LeviCivita (I := I) g)
        Φ.toSection Wd x v]

  have hT2 :
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
          tensorCovDerivAt (I := I) (M := M) g 0 r W x v) d) =
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
          (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
              (fun y : M => Wd y) x v) -
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
              (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
                (fun y : M => dSec y) x v)) := by
    rw [show d = dSec x from hdSec.symm,
      tensorCovDerivAt_def (I := I) (M := M) g 0 r W x v,
      tensorRSCovariantDerivative_apply (I := I) (M := M) 0 r (LeviCivita (I := I) g)
        W.toSection dSec x v]
    rw [map_sub (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)]
    rfl
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hLHS, hT1, hT2]
  abel

set_option backward.isDefEq.respectTransparency false in

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensor0S_curry_covGrad_appCc_eq (g : SmoothRiemannianMetric I M) (r : ℕ)
    (W : SmoothCcTensor g 0 r) (x : M) (d : Tensor0SSpace 0 I x) (v0 : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from
          (covGrad (I := I) (M := M) g 0 r W).toSection x) d) v0 =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
        tensorCovDerivAt (I := I) (M := M) g 0 r W x v0) d := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from
      (covGrad (I := I) (M := M) g 0 r W).toSection x) d) (v0 := v0) (vs := m)]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 r W x d (Fin.cons v0 m)]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons v0 m ∘ Fin.succ) = m from funext (fun j => by simp [Fin.cons_succ])]

set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_operatorFieldApply_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    covGrad (I := I) (M := M) g 0 s (operatorFieldApply (I := I) (M := M) g r s Φ W) =
      operatorFieldApply (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) W +
        operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1) (slotExtend (I := I) (M := M) g r s Φ)
          (covGrad (I := I) (M := M) g 0 r W) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((operatorFieldApply (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) W +
        operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1) (slotExtend (I := I) (M := M) g r s Φ)
          (covGrad (I := I) (M := M) g 0 r W)).toSection x) =
      (operatorFieldApply (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) W).toSection x +
        (operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1) (slotExtend (I := I) (M := M) g r s Φ)
          (covGrad (I := I) (M := M) g 0 r W)).toSection x from rfl]
  apply ContinuousLinearMap.ext
  intro d
  rw [ContinuousLinearMap.add_apply]
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  beta_reduce
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 s (operatorFieldApply (I := I) (M := M) g r s Φ W) x d v]

  rw [appCc_toSection (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) W x,
    ContinuousLinearMap.comp_apply,
    covGrad_toSection_apply_eval (I := I) (M := M) g r s Φ x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) d) v]

  have hT2val : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1) (slotExtend (I := I) (M := M) g r s Φ)
            (covGrad (I := I) (M := M) g 0 r W)).toSection x) d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
            tensorCovDerivAt (I := I) (M := M) g 0 r W x (v 0)) d))
        (Matrix.vecTail v) := by
    rw [appCc_toSection (I := I) (M := M) g (r + 1) (s + 1) (slotExtend (I := I) (M := M) g r s Φ)
        (covGrad (I := I) (M := M) g 0 r W) x, ContinuousLinearMap.comp_apply,
      slotExtend_toSection (I := I) (M := M) g r s Φ x]
    rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from (Fin.cons_self_tail v).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g r s x
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from
        (covGrad (I := I) (M := M) g 0 r W).toSection x) d) (v 0) (Matrix.vecTail v)]
    rw [tensor0S_curry_covGrad_appCc_eq (I := I) (M := M) g r W x d (v 0)]
    simp only [Fin.cons_zero, Matrix.vecTail]
    rw [show (Fin.cons (v 0) (v ∘ Fin.succ) ∘ Fin.succ) = v ∘ Fin.succ from
      funext (fun j => by simp [Fin.cons_succ])]
  rw [hT2val]

  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s (operatorFieldApply (I := I) (M := M) g r s Φ W) x (v 0)) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s Φ x (v 0)).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) +
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
            tensorCovDerivAt (I := I) (M := M) g 0 r W x (v 0)) from
    tensorCovDerivAt_appCc_eq (I := I) (M := M) g r s Φ W x (v 0)]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

end Connection
end Integral
end DifferentialGeometry

end
