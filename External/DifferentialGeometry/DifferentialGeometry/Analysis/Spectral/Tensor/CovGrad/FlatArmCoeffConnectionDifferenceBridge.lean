import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 6400000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section NormedConnectionDifferenceLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def connDiffLoweredCovec (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 3 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I x) ℝ from
    { toFun := fun m =>
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2)
      map_update_add' := by
        have h01 : (0 : Fin 3) ≠ 1 := by decide
        have h02 : (0 : Fin 3) ≠ 2 := by decide
        have h10 : (1 : Fin 3) ≠ 0 := by decide
        have h12 : (1 : Fin 3) ≠ 2 := by decide
        have h20 : (2 : Fin 3) ≠ 0 := by decide
        have h21 : (2 : Fin 3) ≠ 1 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h10, h12, h20, h21, not_false_eq_true,
            map_add, ContinuousLinearMap.add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 3) ≠ 1 := by decide
        have h02 : (0 : Fin 3) ≠ 2 := by decide
        have h10 : (1 : Fin 3) ≠ 0 := by decide
        have h12 : (1 : Fin 3) ≠ 2 := by decide
        have h20 : (2 : Fin 3) ≠ 0 := by decide
        have h21 : (2 : Fin 3) ≠ 1 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h10, h12, h20, h21, not_false_eq_true,
            map_smul, ContinuousLinearMap.smul_apply]
      cont := by
        have hconn : Continuous (fun m : Fin 3 → TangentSpace I x =>
            PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) :=
          ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).continuous.comp
            (continuous_apply 0)).clm_apply (continuous_apply 1)
        exact ((g₀.inner x).continuous.comp hconn).clm_apply (continuous_apply 2) }
    : Tensor0SSpace 3 I x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma connDiffLoweredCovec_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    connDiffLoweredCovec (I := I) g₀ g₁ x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma connDiffLoweredScalar_contMDiffAt (g₀ g₁ : SmoothRiemannianMetric I M)
    (V0 V1 V2 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (V0 x) (V1 x)) (V2 x)) x₀ := by
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (V0 x) (V1 x))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ V0.contMDiff V1.contMDiff
  have h_total : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M =>
        (⟨b, g₀.inner b (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (V0 b) (V1 b)) (V2 b)⟩ :
          TotalSpace ℝ (Bundle.Trivial M ℝ))) x₀ :=
    (ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id)
      g₀.contMDiff.contMDiffOn hconn.contMDiffOn V2.contMDiff.contMDiffOn x₀
      (mem_univ x₀)).contMDiffAt univ_mem
  rw [Bundle.contMDiffAt_totalSpace] at h_total
  exact h_total.2

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connDiffLoweredCovec_section_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SSpace 3 I z) x (connDiffLoweredCovec (I := I) g₀ g₁ x)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (connDiffLoweredCovec (I := I) g₀ g₁ x :
        Bundle.continuousMultilinearMap ℝ 3 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y (σ 0) x) (Y (σ 1) x)) (Y (σ 2) x)) x₀ :=
    connDiffLoweredScalar_contMDiffAt (I := I) g₀ g₁ (Y (σ 0)) (Y (σ 1)) (Y (σ 2)) x₀
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
  have hframe2 : e₁.symmL ℝ x (b (σ 2)) = (Y (σ 2)) x := by
    rw [hYx (σ 2), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      (e₁.symmL ℝ x (b (σ 0))) (e₁.symmL ℝ x (b (σ 1)))) (e₁.symmL ℝ x (b (σ 2))) = _
  rw [hframe0, hframe1, hframe2]

def connDiffLoweredField (g₀ g₁ : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => connDiffLoweredCovec (I := I) g₀ g₁ x,
    connDiffLoweredCovec_section_contMDiff (I := I) g₀ g₁⟩

def connDiffLoweredCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (connDiffLoweredField (I := I) g₀ g₁)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma connDiffLoweredCc_unitModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x =
      Tensor0SSpace.toModel (connDiffLoweredCovec (I := I) g₀ g₁ x) := by
  rw [unitModel]
  rw [show (connDiffLoweredCc (I := I) g₀ g₁).toSection x (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) g₀ g₁ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma connDiffLoweredCc_unitModel_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  rw [connDiffLoweredCc_unitModel]
  rfl

end NormedConnectionDifferenceLowering

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma interior_product_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem riemannianFiberNormSq_neg_value
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma connDiffSection_eq_cometricRaiseSlot0Field (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connDiffSection_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om YZ =
      g₀.inner x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := by
    rw [connDiffFib_apply_eval]
    rw [show om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from
      (cotangentToDual_apply (I := I) om _).symm]
    rw [show cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)), ← hu]
  have hRHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [interior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  rw [hLHS, hRHS]
  have hum : unitModel (I := I) (M := M) g₀ 3
      (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x
          ![u, YZ 0, YZ 1] from by
    rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
        ![YZ 0, YZ 1, u] from by
    funext i; fin_cases i <;> simp [finRotate_succ_apply]]
  rw [connDiffLoweredCc_unitModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [g₀.symm x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1))]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma flatArmCoeffCc_true_eq_cometricRaiseSlot0Field
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    flatArmCoeffCc (I := I) g₀ g₁ true =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1 (-connDiffLoweredCc (I := I) g₀ g₁) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [flatArmCoeffCc_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (-connDiffLoweredCc (I := I) g₀ g₁).toSection x) (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (flatArmCc (I := I) g₀ g₁ true).toSection x).comp
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
            (omRecoverEndoCc (I := I) g₀ g₁).toSection x))) om YZ =
      - g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u (YZ 0)) (YZ 1) := by
    rw [ContinuousLinearMap.comp_apply]
    rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (omRecoverEndoCc (I := I) g₀ g₁).toSection x) om =
        g0FlatCLM (I := I) g₁ x (inverseMetricSharpFib (I := I) g₀ x om) from by
      rw [omRecoverEndoCc_toSection]; rfl]
    rw [flatArmCc_toSection, flatArmFib_apply, flatArmPairing_apply]
    rw [show flatArmVec (I := I) g₀ g₁ true x
          (g0FlatCLM (I := I) g₁ x (inverseMetricSharpFib (I := I) g₀ x om)) (YZ 0) =
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (inverseMetricSharpFib (I := I) g₀ x om) (YZ 0) from by
      simp only [flatArmVec, if_true]
      rw [inverseMetricSharpFib_g0FlatCLM]]
    rw [map_neg, ContinuousLinearMap.neg_apply, ← hu]
  have hRHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [interior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  rw [hLHS, hRHS]
  have hum : unitModel (I := I) (M := M) g₀ 3 (-connDiffLoweredCc (I := I) g₀ g₁) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
        unitModel (I := I) (M := M) g₀ 3 (-connDiffLoweredCc (I := I) g₀ g₁) x ![u, YZ 0, YZ 1]
        from by rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
  rw [show unitModel (I := I) (M := M) g₀ 3 (-connDiffLoweredCc (I := I) g₀ g₁) x =
        - unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x from by
      simp only [unitModel]
      rw [SmoothCcTensor.toSection_neg, ContMDiffSection.coe_neg, Pi.neg_apply,
        ContinuousLinearMap.neg_apply, Tensor0SSpace.toModel_neg]]
  rw [ContinuousMultilinearMap.neg_apply, connDiffLoweredCc_unitModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_iteratedCovGrad_flatArmCoeffCc_true_eq_connDiffSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i
          (flatArmCoeffCc (I := I) g₀ g₁ true)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (flatArmCoeffCc (I := I) g₀ g₁ true)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (-connDiffLoweredCc (I := I) g₀ g₁))).toSection x) := by
        rw [flatArmCoeffCc_true_eq_cometricRaiseSlot0Field]
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 3 i
            (-connDiffLoweredCc (I := I) g₀ g₁)).toSection x) :=
        riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (-connDiffLoweredCc (I := I) g₀ g₁) i x
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 3 i (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) := by
        rw [iteratedCovGrad_neg]
        rw [show ((-(iteratedCovGrad (I := I) g₀ 0 3 i
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) =
            -((iteratedCovGrad (I := I) g₀ 0 3 i
              (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) from by
          rw [SmoothCcTensor.toSection_neg]; rfl]
        rw [riemannianFiberNormSq_neg_value]
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 3 i
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁) i x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (connDiffLoweredCc (I := I) g₀ g₁)))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (connDiffLoweredCc (I := I) g₀ g₁)) i x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀)).toSection x) := by
        rw [connDiffSection_eq_cometricRaiseSlot0Field]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
