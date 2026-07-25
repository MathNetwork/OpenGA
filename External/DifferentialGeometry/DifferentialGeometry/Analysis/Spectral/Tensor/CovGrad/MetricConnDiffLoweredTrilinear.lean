import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CorrFieldChristoffelCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.SlotSubstitutionFiberNormBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def domDomCongrFibRank (d : ℕ) (σ : Equiv.Perm (Fin d)) (x : M) :
    Tensor0SBundle.Tensor0SSpace d I x →L[ℝ] Tensor0SBundle.Tensor0SSpace d I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) d x).symm.toContinuousLinearMap.comp
    (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          σ).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) d x).toContinuousLinearMap)


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem domDomCongrFibRank_apply (d : ℕ) (σ : Equiv.Perm (Fin d)) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace d I x) :
    domDomCongrFibRank (I := I) d σ x D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [domDomCongrFibRank]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

noncomputable def modelProdCLM (p q : ℕ) :
    Tensor0SBundle.Tensor0SModel p ℝ E →L[ℝ]
      Tensor0SBundle.Tensor0SModel q ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel (p + q) ℝ E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A =>
        LinearMap.toContinuousLinearMap
          { toFun := fun B =>
              Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q A B
            map_add' := fun B B' => by
              apply ContinuousMultilinearMap.ext
              intro v
              rw [ContinuousMultilinearMap.add_apply,
                Bundle.continuousMultilinearMap.modelProduct_apply,
                Bundle.continuousMultilinearMap.modelProduct_apply,
                Bundle.continuousMultilinearMap.modelProduct_apply,
                ContinuousMultilinearMap.add_apply]
              ring
            map_smul' := fun c B => by
              apply ContinuousMultilinearMap.ext
              intro v
              rw [RingHom.id_apply, ContinuousMultilinearMap.smul_apply,
                Bundle.continuousMultilinearMap.modelProduct_apply,
                Bundle.continuousMultilinearMap.modelProduct_apply,
                ContinuousMultilinearMap.smul_apply]
              simp only [smul_eq_mul]
              ring }
      map_add' := fun A A' => by
        apply ContinuousLinearMap.ext
        intro B
        apply ContinuousMultilinearMap.ext
        intro v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply]
        rw [Bundle.continuousMultilinearMap.modelProduct_apply,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousMultilinearMap.add_apply]
        ring
      map_smul' := fun c A => by
        apply ContinuousLinearMap.ext
        intro B
        apply ContinuousMultilinearMap.ext
        intro v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          RingHom.id_apply, ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
        rw [Bundle.continuousMultilinearMap.modelProduct_apply,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousMultilinearMap.smul_apply]
        simp only [smul_eq_mul]
        ring }


omit [NeZero (Module.finrank ℝ E)] in
theorem modelProdCLM_apply (p q : ℕ)
    (A : Tensor0SBundle.Tensor0SModel p ℝ E) (B : Tensor0SBundle.Tensor0SModel q ℝ E) :
    modelProdCLM (E := E) p q A B =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q A B := by
  rw [modelProdCLM]
  rfl

noncomputable def tensor0SProdKappaFib {p q : ℕ} (x : M)
    (κ : Tensor0SBundle.Tensor0SSpace q I x) :
    Tensor0SBundle.Tensor0SSpace p I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (p + q) I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (p + q)
      x).symm.toContinuousLinearMap.comp
    (((modelProdCLM (E := E) p q).flip
        (Tensor0SBundle.Tensor0SSpace.toModel κ)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) p x).toContinuousLinearMap)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem tensor0SProdKappaFib_apply {p q : ℕ} (x : M)
    (κ : Tensor0SBundle.Tensor0SSpace q I x) (D : Tensor0SBundle.Tensor0SSpace p I x) :
    tensor0SProdKappaFib (I := I) x κ D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (Tensor0SBundle.Tensor0SSpace.toModel D) (Tensor0SBundle.Tensor0SSpace.toModel κ)) := by
  rw [tensor0SProdKappaFib]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.flip_apply]
  rw [modelProdCLM_apply]
  rfl

private noncomputable def trilinFormToModel (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] :
    (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) ≃ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 3 => F) ℝ :=
  ((ContinuousLinearEquiv.refl ℝ F).arrowCongr
      (bilinFormToModelₗᵢ F).toContinuousLinearEquiv).toLinearEquiv.trans
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => F) ℝ).symm.toLinearEquiv

private theorem trilinFormToModel_apply (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) (v : Fin 3 → F) :
    trilinFormToModel F B v = B (v 0) (v 1) (v 2) := by
  classical
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => F) ℝ).symm
      (((ContinuousLinearEquiv.refl ℝ F).arrowCongr
          (bilinFormToModelₗᵢ F).toContinuousLinearEquiv) B) v =
    B (v 0) (v 1) (v 2)
  rw [continuousMultilinearCurryLeftEquiv_symm_apply,
    ContinuousLinearEquiv.arrowCongr_apply]
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [show ((bilinFormToModelₗᵢ F) (B (v 0)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => F) ℝ)
      = bilinFormToModel F (B (v 0)) from rfl]
  rw [bilinFormToModel_apply]
  rfl

noncomputable def metricConnDiffLoweredTrilin (gm gA gB : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x)
      (TangentSpace I x →L[ℝ] ℝ) (gm.inner x)).comp
    (PDE.DeTurck.connDiff (I := I) gA gB x)


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem metricConnDiffLoweredTrilin_apply (gm gA gB : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    metricConnDiffLoweredTrilin (I := I) gm gA gB x a b c =
      gm.inner x (PDE.DeTurck.connDiff (I := I) gA gB x a b) c := by
  rw [metricConnDiffLoweredTrilin]
  rfl

noncomputable def metricConnDiffLoweredFib (gm gA gB : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x :=
  Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
    (trilinFormToModel (TangentSpace I x) (metricConnDiffLoweredTrilin (I := I) gm gA gB x))


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem metricConnDiffLoweredFib_toModel (gm gA gB : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 3 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) gm gA gB x) v =
      gm.inner x (PDE.DeTurck.connDiff (I := I) gA gB x (v 0) (v 1)) (v 2) := by
  rw [metricConnDiffLoweredFib, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  change (trilinFormToModel (TangentSpace I x))
      (metricConnDiffLoweredTrilin (I := I) gm gA gB x) v = _
  rw [trilinFormToModel_apply, metricConnDiffLoweredTrilin_apply]

noncomputable def ccBilinConnDiffLoweredTrilin (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x)
      (TangentSpace I x →L[ℝ] ℝ) (ccTensorBilinSymm (I := I) g₀ V x)).comp
    (PDE.DeTurck.connDiff (I := I) gA gB x)


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem ccBilinConnDiffLoweredTrilin_apply (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    ccBilinConnDiffLoweredTrilin (I := I) g₀ V gA gB x a b c =
      ccTensorBilinSymm (I := I) g₀ V x (PDE.DeTurck.connDiff (I := I) gA gB x a b) c := by
  rw [ccBilinConnDiffLoweredTrilin]
  rfl

noncomputable def ccBilinConnDiffLoweredFib (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x :=
  Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
    (trilinFormToModel (TangentSpace I x) (ccBilinConnDiffLoweredTrilin (I := I) g₀ V gA gB x))


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem ccBilinConnDiffLoweredFib_toModel (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 3 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (ccBilinConnDiffLoweredFib (I := I) g₀ V gA gB x) v =
      ccTensorBilinSymm (I := I) g₀ V x
        (PDE.DeTurck.connDiff (I := I) gA gB x (v 0) (v 1)) (v 2) := by
  rw [ccBilinConnDiffLoweredFib, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  change (trilinFormToModel (TangentSpace I x))
      (ccBilinConnDiffLoweredTrilin (I := I) g₀ V gA gB x) v = _
  rw [trilinFormToModel_apply, ccBilinConnDiffLoweredTrilin_apply]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem trilinKernel_section_contMDiff
    (K : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hK : ∀ (Y0 Y1 Y2 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x₀ : M),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x : M => K x (Y0 x) (Y1 x) (Y2 x)) x₀) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (trilinFormToModel (TangentSpace I x) (K x)))) := by
  classical
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x : M => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (trilinFormToModel (TangentSpace I x) (K x)) :
          Tensor0SBundle.Tensor0SSpace 3 I x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  refine (hK (Y (σ 0)) (Y (σ 1)) (Y (σ 2)) x₀).congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
    rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  have hframe1 : e₁.symmL ℝ x (b (σ 1)) = (Y (σ 1)) x := by
    rw [hYx (σ 1), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  have hframe2 : e₁.symmL ℝ x (b (σ 2)) = (Y (σ 2)) x := by
    rw [hYx (σ 2), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change (trilinFormToModel (TangentSpace I x) (K x))
      (fun j : Fin 3 => e₁.symmL ℝ x (b (σ j))) = _
  rw [trilinFormToModel_apply]
  rw [hframe0, hframe1, hframe2]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricConnDiffLoweredFib_contMDiff (gm gA gB : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x
        (metricConnDiffLoweredFib (I := I) gm gA gB x)) := by
  refine trilinKernel_section_contMDiff (I := I)
    (K := fun x => metricConnDiffLoweredTrilin (I := I) gm gA gB x) ?_
  intro Y0 Y1 Y2 x₀
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) gA gB x (Y0 x) (Y1 x))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) gA gB Y0.contMDiff Y1.contMDiff
  have hscalar : ContMDiff I 𝓘(ℝ) ∞
      (fun x : M => gm.inner x
        (PDE.DeTurck.connDiff (I := I) gA gB x (Y0 x) (Y1 x)) (Y2 x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) gm
      ⟨fun x => PDE.DeTurck.connDiff (I := I) gA gB x (Y0 x) (Y1 x), hconn⟩ Y2
  refine (hscalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [metricConnDiffLoweredTrilin_apply]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ccBilinConnDiffLoweredFib_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x
        (ccBilinConnDiffLoweredFib (I := I) g₀ V gA gB x)) := by
  refine trilinKernel_section_contMDiff (I := I)
    (K := fun x => ccBilinConnDiffLoweredTrilin (I := I) g₀ V gA gB x) ?_
  intro Y0 Y1 Y2 x₀
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) gA gB x (Y0 x) (Y1 x))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) gA gB Y0.contMDiff Y1.contMDiff
  have h_total : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun x : M => (⟨x, ccTensorBilinSymm (I := I) g₀ V x
        (PDE.DeTurck.connDiff (I := I) gA gB x (Y0 x) (Y1 x)) (Y2 x)⟩ :
          TotalSpace ℝ (Bundle.Trivial M ℝ))) x₀ :=
    (ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id)
      (ccTensorBilinSymm_contMDiff (I := I) g₀ V).contMDiffOn hconn.contMDiffOn
      Y2.contMDiff.contMDiffOn x₀ (mem_univ x₀)).contMDiffAt univ_mem
  rw [Bundle.contMDiffAt_totalSpace] at h_total
  refine (h_total.2).congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [ccBilinConnDiffLoweredTrilin_apply]
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
