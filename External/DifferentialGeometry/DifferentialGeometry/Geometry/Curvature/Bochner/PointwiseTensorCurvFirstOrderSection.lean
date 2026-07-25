import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorCurvFirstOrderBound
import DifferentialGeometry.Geometry.Connection.TensorNabla.FullHomCovariantCalculusRS
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Slot0CurryReconstruction
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma smoothOrthoFrame_parsevalExpand
    (g : SmoothRiemannianMetric I M) (x : M) (u : TangentSpace I x) :
    u = ∑ a : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x) u • (smoothOrthoFrame (I := I) g x a x) := by
  classical
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) g x a x with he_def
  have horth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (e k)).map_smul (c j) (e j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]; rfl
  set bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse_eq : ∀ i, bse i = e i := by
    intro i; rw [hbse_def]; exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i
  conv_lhs => rw [← bse.sum_repr u]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hbse_eq a]
  congr 1
  have hrepr : g.inner x (e a) u =
      ∑ b : Fin (Module.finrank ℝ E), bse.repr u b * g.inner x (e a) (e b) := by
    conv_lhs => rw [show u = ∑ b : Fin (Module.finrank ℝ E),
      bse.repr u b • bse b from (bse.sum_repr u).symm]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [(g.inner x (e a)).map_smul (bse.repr u b) (bse b), smul_eq_mul, hbse_eq b]
  rw [hrepr, Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, mul_one]
  · intro b _ hba; rw [horth a b, if_neg (fun h => hba h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SAsRS_add_loc {t : ℕ} (x : M) (C D : Tensor0SSpace t I x) :
    tensor0SToTensorRS (I := I) (M := M) x (C + D) =
      tensor0SToTensorRS (I := I) (M := M) x C + tensor0SToTensorRS (I := I) (M := M) x D := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 t x
  intro τ
  rw [tensor0SAsRS_apply (I := I) (M := M) x (C + D) τ]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SToTensorRS (I := I) (M := M) x C + tensor0SToTensorRS (I := I) (M := M) x D) τ =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SToTensorRS (I := I) (M := M) x C) τ +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
          tensor0SToTensorRS (I := I) (M := M) x D) τ from by
    rw [ContinuousLinearMap.add_apply]]
  rw [tensor0SAsRS_apply (I := I) (M := M) x C τ, tensor0SAsRS_apply (I := I) (M := M) x D τ,
    smul_add]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SAsRS_smul_loc {t : ℕ} (x : M) (c : ℝ) (C : Tensor0SSpace t I x) :
    tensor0SToTensorRS (I := I) (M := M) x (c • C) =
      c • tensor0SToTensorRS (I := I) (M := M) x C := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 t x
  intro τ
  rw [tensor0SAsRS_apply (I := I) (M := M) x (c • C) τ]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        c • tensor0SToTensorRS (I := I) (M := M) x C) τ =
      c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SToTensorRS (I := I) (M := M) x C) τ from by
    rw [ContinuousLinearMap.smul_apply]]
  rw [tensor0SAsRS_apply (I := I) (M := M) x C τ, smul_comm]

noncomputable def tensorSlotZeroEvalFib (x : M) (s : ℕ)
    (v : TangentSpace I x) :
    TensorRSSpace 0 (s + 1) I x →L[ℝ] TensorRSSpace 0 s I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  haveI : T2Space (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun Wx =>
        tensor0SToTensorRS (I := I) (M := M) x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Wx)
              (unitZeroSec (I := I) (M := M) x)) v)
      map_add' := fun W₁ W₂ => by
        have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₁ + W₂)
            (unitZeroSec (I := I) (M := M) x) =
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₁)
              (unitZeroSec (I := I) (M := M) x) +
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₂)
              (unitZeroSec (I := I) (M := M) x) := by
          rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₁ + W₂) =
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₁) +
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₂) from rfl,
            ContinuousLinearMap.add_apply]
        rw [hval, map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.add_apply,
          tensor0SAsRS_add_loc (I := I) (M := M) x]
      map_smul' := fun c W => by
        have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from c • W)
            (unitZeroSec (I := I) (M := M) x) =
            c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W)
              (unitZeroSec (I := I) (M := M) x) := by
          rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from c • W) =
              c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W) from rfl,
            ContinuousLinearMap.smul_apply]
        rw [hval, map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.smul_apply, tensor0SAsRS_smul_loc (I := I) (M := M) x]
        rfl }


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma slot0SliceFib_apply (x : M) (s : ℕ) (v : TangentSpace I x)
    (Wx : TensorRSSpace 0 (s + 1) I x) :
    tensorSlotZeroEvalFib (I := I) (M := M) x s v Wx =
      tensor0SToTensorRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Wx)
            (unitZeroSec (I := I) (M := M) x)) v) := by
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  haveI : T2Space (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  rw [tensorSlotZeroEvalFib, LinearMap.coe_toContinuousLinearMap']
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma slot0SliceFib_eq_covGradBundleEquiv_symm (x : M) (s : ℕ) (v : TangentSpace I x)
    (T : TensorRSSpace 0 (s + 1) I x) :
    tensorSlotZeroEvalFib (I := I) (M := M) x s v T =
      (show TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x from
        (covGradBundleEquiv (I := I) (M := M) 0 s x).symm T) v := by
  classical
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 s x
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [slot0SliceFib_apply]

  rw [tensor0SAsRS_apply (I := I) (M := M) x _ D]
  simp only [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T)
        (unitZeroSec (I := I) (M := M) x)) (v0 := v) (vs := m)]

  rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) 0 s x T v D m]

  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T) D =
      tensor00Scalar (I := I) (M := M) x D •
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T)
          (unitZeroSec (I := I) (M := M) x) from by
    conv_lhs => rw [tensor0S_zero_span' (I := I) (M := M) x D]
    rw [ContinuousLinearMap.map_smul]]
  simp only [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]

omit [NeZero (Module.finrank ℝ E)] in
lemma slot0SliceFib_covGrad_eq (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (x : M) (v : TangentSpace I x) :
    tensorSlotZeroEvalFib (I := I) (M := M) x s v ((covGrad (I := I) (M := M) g 0 s S).toSection x) =
      (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x v := by
  rw [slot0SliceFib_apply]
  rw [curry_covGrad_unit_eval_general (I := I) (M := M) g s S x v]
  exact tensor0SAsRS_unit_recover (I := I) (M := M) s x
    ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x v)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma slot0SliceFib_dir_add (x : M) (s : ℕ) (v v' : TangentSpace I x)
    (Wx : TensorRSSpace 0 (s + 1) I x) :
    tensorSlotZeroEvalFib (I := I) (M := M) x s (v + v') Wx =
      tensorSlotZeroEvalFib (I := I) (M := M) x s v Wx + tensorSlotZeroEvalFib (I := I) (M := M) x s v' Wx := by
  rw [slot0SliceFib_apply, slot0SliceFib_apply, slot0SliceFib_apply]
  rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Wx)
      (unitZeroSec (I := I) (M := M) x)))]
  rw [tensor0SAsRS_add_loc (I := I) (M := M) x]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma slot0SliceFib_dir_smul (x : M) (s : ℕ) (c : ℝ) (v : TangentSpace I x)
    (Wx : TensorRSSpace 0 (s + 1) I x) :
    tensorSlotZeroEvalFib (I := I) (M := M) x s (c • v) Wx =
      c • tensorSlotZeroEvalFib (I := I) (M := M) x s v Wx := by
  rw [slot0SliceFib_apply, slot0SliceFib_apply]
  rw [map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Wx)
      (unitZeroSec (I := I) (M := M) x)))]
  rw [tensor0SAsRS_smul_loc (I := I) (M := M) x]

noncomputable def curvatureGradContractionDirLM
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (Wx : TensorRSSpace 0 (s + 1) I x) :
    TangentSpace I x →ₗ[ℝ] TensorRSSpace 0 s I x where
  toFun w := ∑ i : Fin (Module.finrank ℝ E),
    ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
        (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) Wx) -
      tensorSlotZeroEvalFib (I := I) (M := M) x s
        (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx)
  map_add' w w' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_add (riemannOp (tensorCov (I := I) g 0 s) x (B i x)) w w',
      ContinuousLinearMap.add_apply, smul_add]
    rw [map_add (riemannOp (LeviCivita (I := I) g) x (B i x)) w w',
      ContinuousLinearMap.add_apply, slot0SliceFib_dir_add (I := I) (M := M) x s]
    abel
  map_smul' c w := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul (riemannOp (tensorCov (I := I) g 0 s) x (B i x)) c w,
      ContinuousLinearMap.smul_apply, smul_comm (2 : ℝ) c]
    rw [map_smul (riemannOp (LeviCivita (I := I) g) x (B i x)) c w,
      ContinuousLinearMap.smul_apply, slot0SliceFib_dir_smul (I := I) (M := M) x s]
    rw [smul_sub]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma gradArmDirLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (Wx : TensorRSSpace 0 (s + 1) I x) (w : TangentSpace I x) :
    curvatureGradContractionDirLM (I := I) (M := M) g s B x Wx w =
      ∑ i : Fin (Module.finrank ℝ E),
        ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
            (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) Wx) -
          tensorSlotZeroEvalFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx) := rfl

noncomputable def curvatureGradContractionDirCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (Wx : TensorRSSpace 0 (s + 1) I x) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (curvatureGradContractionDirLM (I := I) (M := M) g s B x Wx)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma gradArmDirCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (Wx : TensorRSSpace 0 (s + 1) I x) (w : TangentSpace I x) :
    curvatureGradContractionDirCLM (I := I) (M := M) g s B x Wx w =
      ∑ i : Fin (Module.finrank ℝ E),
        ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
            (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) Wx) -
          tensorSlotZeroEvalFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx) := by
  rw [curvatureGradContractionDirCLM, LinearMap.coe_toContinuousLinearMap']
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma gradArmDirCLM_value_add
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (W₁ W₂ : TensorRSSpace 0 (s + 1) I x) :
    curvatureGradContractionDirCLM (I := I) (M := M) g s B x (W₁ + W₂) =
      curvatureGradContractionDirCLM (I := I) (M := M) g s B x W₁ + curvatureGradContractionDirCLM (I := I) (M := M) g s B x W₂ := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.add_apply, gradArmDirCLM_apply, gradArmDirCLM_apply, gradArmDirCLM_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_add (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x)) W₁ W₂,
    map_add (riemannOp (tensorCov (I := I) g 0 s) x (B i x) w), smul_add,
    map_add (tensorSlotZeroEvalFib (I := I) (M := M) x s
      (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x))) W₁ W₂]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma gradArmDirCLM_value_smul
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (c : ℝ) (W : TensorRSSpace 0 (s + 1) I x) :
    curvatureGradContractionDirCLM (I := I) (M := M) g s B x (c • W) =
      c • curvatureGradContractionDirCLM (I := I) (M := M) g s B x W := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.smul_apply, gradArmDirCLM_apply, gradArmDirCLM_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x)) c W,
    map_smul (riemannOp (tensorCov (I := I) g 0 s) x (B i x) w),
    map_smul (tensorSlotZeroEvalFib (I := I) (M := M) x s
      (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x))) c W]
  rw [smul_sub, smul_comm (2 : ℝ) c]

noncomputable def curvatureGradContractionFib
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) :
    TensorRSSpace 0 (s + 1) I x →L[ℝ] TensorRSSpace 0 (s + 1) I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  haveI : T2Space (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun Wx =>
        covGradBundleEquiv (I := I) (M := M) 0 s x
          (curvatureGradContractionDirCLM (I := I) (M := M) g s B x Wx)
      map_add' := fun W₁ W₂ => by
        rw [gradArmDirCLM_value_add (I := I) (M := M) g s B x W₁ W₂, map_add]
      map_smul' := fun c W => by
        rw [gradArmDirCLM_value_smul (I := I) (M := M) g s B x c W, map_smul]
        rfl }


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma gradArmFib_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (Wx : TensorRSSpace 0 (s + 1) I x) :
    curvatureGradContractionFib (I := I) (M := M) g s B x Wx =
      covGradBundleEquiv (I := I) (M := M) 0 s x
        (curvatureGradContractionDirCLM (I := I) (M := M) g s B x Wx) := by
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  haveI : T2Space (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  rw [curvatureGradContractionFib, LinearMap.coe_toContinuousLinearMap']
  rfl

lemma gradArmFib_covGrad_slice_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    tensor0SToTensorRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            curvatureGradContractionFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x))
            (unitZeroSec (I := I) (M := M) x))
          (smoothOrthoFrame (I := I) g x a x)) =
      (2 : ℝ) • ∑ i : Fin (Module.finrank ℝ E),
          riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame (I := I) g x a)
            (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => S.toSection y)) x -
        ∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
            (riemannOp (LeviCivita (I := I) g) x (smoothOrthoFrame (I := I) g x i x)
              (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x i x)) := by
  classical
  set B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b :=
    fun i => smoothOrthoFrame (I := I) g x i with hB
  set Wx : TensorRSSpace 0 (s + 1) I x := (covGrad (I := I) (M := M) g 0 s S).toSection x with hWx

  rw [gradArmFib_apply (I := I) (M := M) g s B x Wx]
  rw [tensor0S_curry_covGradBundleEquiv_unit_genVal (I := I) (M := M) s x
    (curvatureGradContractionDirCLM (I := I) (M := M) g s B x Wx) (B a x)]
  rw [tensor0SAsRS_unit_recover (I := I) (M := M) s x
    (curvatureGradContractionDirCLM (I := I) (M := M) g s B x Wx (B a x))]
  rw [gradArmDirCLM_apply (I := I) (M := M) g s B x Wx (B a x)]

  rw [Finset.sum_sub_distrib, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)

    rw [hWx, slot0SliceFib_covGrad_eq (I := I) (M := M) g s S x (B i x)]
    rw [riemannSec_eq_riemannOp_tensorCov (I := I) g 0 s
      (smoothOrthoFrame_smooth (I := I) g x i) (smoothOrthoFrame_smooth (I := I) g x a)
      (covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g x i))]
    rfl
  · refine Finset.sum_congr rfl (fun i _ => ?_)

    rw [hWx, slot0SliceFib_covGrad_eq (I := I) (M := M) g s S x
      (riemannOp (LeviCivita (I := I) g) x (B i x) (B a x) (B i x))]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma slot0SliceFib_section_contMDiff
    (_g : SmoothRiemannianMetric I M) (s : ℕ)
    {Y : Π b : M, TensorRSSpace 0 (s + 1) I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) b (Y b)))
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (tensorSlotZeroEvalFib (I := I) (M := M) b s (V b) (Y b))) := by

  have heq : (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
      (E := fun z : M => TensorRSSpace 0 s I z) b
      (tensorSlotZeroEvalFib (I := I) (M := M) b s (V b) (Y b))) =
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        ((show TangentSpace I b →L[ℝ] TensorRSSpace 0 s I b from
          (covGradBundleEquiv (I := I) (M := M) 0 s b).symm (Y b)) (V b))) := by
    funext b
    rw [slot0SliceFib_eq_covGradBundleEquiv_symm (I := I) (M := M) b s (V b) (Y b)]
  rw [heq]

  have hHom : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace 0 s I z) b
        ((covGradBundleEquiv (I := I) (M := M) 0 s b).symm (Y b))) :=
    (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) 0 s).comp hY
  exact ContMDiff.clm_bundle_apply (b := fun b : M => b)
    (ϕ := fun b => (covGradBundleEquiv (I := I) (M := M) 0 s b).symm (Y b))
    (v := fun b => V b) hHom hV

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma gradArmDirCLM_homSection_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    {Y : Π b : M, TensorRSSpace 0 (s + 1) I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) b (Y b))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace 0 s I z) x
        (curvatureGradContractionDirCLM (I := I) (M := M) g s B x (Y x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := TensorRSModel 0 s ℝ E) (V₂ := fun z : M => TensorRSSpace 0 s I z)
    (φ := fun x => curvatureGradContractionDirCLM (I := I) (M := M) g s B x (Y x))
  intro Z

  have hval : (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
      (E := fun z : M => TensorRSSpace 0 s I z) x
      (curvatureGradContractionDirCLM (I := I) (M := M) g s B x (Y x) (Z x))) =
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x
        (∑ i : Fin (Module.finrank ℝ E),
          ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) (Z x)
              (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) (Y x)) -
            tensorSlotZeroEvalFib (I := I) (M := M) x s
              (riemannOp (LeviCivita (I := I) g) x (B i x) (Z x) (B i x)) (Y x)))) := by
    funext x
    rw [gradArmDirCLM_apply]
  rw [hval]

  refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)

  have hRarm : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x
        ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) (Z x)
          (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) (Y x)))) := by
    have hslice := slot0SliceFib_section_contMDiff (I := I) (M := M) g s hY (hB i)
    have hRsec : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
          (E := fun z : M => TensorRSSpace 0 s I z) x
          (riemannSec (tensorCov (I := I) g 0 s) (B i) Z
            (fun y : M => tensorSlotZeroEvalFib (I := I) (M := M) y s (B i y) (Y y)) x)) :=
      riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) (hB i) Z.contMDiff hslice
    have hpt : (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x
        ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) (Z x)
          (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) (Y x)))) =
        (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
          (E := fun z : M => TensorRSSpace 0 s I z) x
          ((2 : ℝ) • riemannSec (tensorCov (I := I) g 0 s) (B i) Z
            (fun y : M => tensorSlotZeroEvalFib (I := I) (M := M) y s (B i y) (Y y)) x)) := by
      funext x
      rw [riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 s) (hB i) Z.contMDiff hslice]
    rw [hpt]
    exact ContMDiff.smul_section (𝕜 := ℝ) (contMDiff_const (c := (2 : ℝ))) hRsec

  have hC5arm : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x
        (tensorSlotZeroEvalFib (I := I) (M := M) x s
          (riemannOp (LeviCivita (I := I) g) x (B i x) (Z x) (B i x)) (Y x))) := by

    have hdir : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun x : M => riemannOp (LeviCivita (I := I) g) x (B i x) (Z x) (B i x))) := by
      have hsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (T% (fun y : M => riemannSec (LeviCivita (I := I) g) (B i) Z (B i) y)) :=
        riemannSec_contMDiff (cov := LeviCivita (I := I) g) (hB i) Z.contMDiff (hB i)
      refine hsec.congr ?_
      intro x
      exact congrArg (TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x)
        (riemannOp_apply_smooth (cov := LeviCivita (I := I) g) (hB i) Z.contMDiff (hB i))
    exact slot0SliceFib_section_contMDiff (I := I) (M := M) g s hY hdir
  exact hRarm.sub_section hC5arm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma gradArmFib_frozen_section_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    {Y : Π b : M, TensorRSSpace 0 (s + 1) I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) b (Y b))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
        (curvatureGradContractionFib (I := I) (M := M) g s B x (Y x))) := by
  have heq : (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
      (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
      (curvatureGradContractionFib (I := I) (M := M) g s B x (Y x))) =
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
        (covGradBundleEquiv (I := I) (M := M) 0 s x
          (curvatureGradContractionDirCLM (I := I) (M := M) g s B x (Y x)))) := by
    funext x
    rw [gradArmFib_apply (I := I) (M := M) g s B x (Y x)]
  rw [heq]
  exact (covGradBundleEquiv_contMDiff_totalSpace (I := I) (M := M) 0 s).comp
    (gradArmDirCLM_homSection_contMDiff (I := I) (M := M) g s hB hY)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma frameSum_riemannOp_LeviCivita_eq_neg_ricEndoRaised
    (g : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (v : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E), riemannOp (LeviCivita (I := I) g) x (e i) v (e i) =
      - ricEndoRaisedFib (I := I) g x v := by
  classical
  apply SmoothRiemannianMetric.eq_of_inner_eq (I := I) g
  intro ζ
  rw [map_sum, ContinuousLinearMap.sum_apply, map_neg]

  have hflip : ∀ i : Fin (Module.finrank ℝ E),
      g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) v (e i)) ζ =
        - g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) v ζ) (e i) := by
    intro i
    have hskew := riemannOp_metric_skew (I := I) g x (e i) v (e i) ζ
    have hsymm : g.inner x (e i) (riemannOp (LeviCivita (I := I) g) x (e i) v ζ) =
        g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) v ζ) (e i) :=
      g.symm x _ _
    rw [hsymm] at hskew
    linarith [hskew]
  rw [Finset.sum_congr rfl (fun i _ => hflip i), Finset.sum_neg_distrib]

  rw [ContinuousLinearMap.neg_apply, inner_ricEndoRaisedFib (I := I) (M := M) g x v ζ,
    ricciTensor_eq_orthonormal_trace (I := I) g x v ζ e horth]

private noncomputable def curvatureGradContractionBilin
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (w : TangentSpace I x)
    (Wx : TensorRSSpace 0 (s + 1) I x) (m : Fin s → E) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI iFD : FiniteDimensional ℝ (TensorRSSpace 0 s I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x))
  haveI iT2 : T2Space (TensorRSSpace 0 s I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x))

  let evalCLM : TensorRSSpace 0 s I x →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun T => Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T)
            (unitZeroSec (I := I) (M := M) x)) m
        map_add' := fun T T' => by
          simp only [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T + T') =
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T) +
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T') from rfl,
            ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
            ContinuousMultilinearMap.add_apply]
        map_smul' := fun c T => by
          simp only [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from c • T) =
              c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T) from rfl,
            ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
            ContinuousMultilinearMap.smul_apply, RingHom.id_apply] }

  let sliceDirCLM : TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x :=
    LinearMap.toContinuousLinearMap
      { toFun := fun b => tensorSlotZeroEvalFib (I := I) (M := M) x s b Wx
        map_add' := fun b b' => slot0SliceFib_dir_add (I := I) (M := M) x s b b' Wx
        map_smul' := fun c b => slot0SliceFib_dir_smul (I := I) (M := M) x s c b Wx }
  LinearMap.toContinuousLinearMap
    { toFun := fun a => evalCLM.comp
        ((riemannOp (tensorCov (I := I) g 0 s) x a w).comp sliceDirCLM)
      map_add' := fun a a' => by
        apply ContinuousLinearMap.ext; intro b
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
          map_add (riemannOp (tensorCov (I := I) g 0 s) x) a a',
          ContinuousLinearMap.add_apply, map_add evalCLM]
      map_smul' := fun c a => by
        apply ContinuousLinearMap.ext; intro b
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
          RingHom.id_apply, map_smul (riemannOp (tensorCov (I := I) g 0 s) x) c a,
          ContinuousLinearMap.smul_apply, map_smul evalCLM] }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] private lemma rArmBilin_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (w : TangentSpace I x)
    (Wx : TensorRSSpace 0 (s + 1) I x) (m : Fin s → E) (a b : TangentSpace I x) :
    curvatureGradContractionBilin (I := I) (M := M) g s x w Wx m a b =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          riemannOp (tensorCov (I := I) g 0 s) x a w
            (tensorSlotZeroEvalFib (I := I) (M := M) x s b Wx))
          (unitZeroSec (I := I) (M := M) x)) m := by
  rw [curvatureGradContractionBilin]
  simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma gradArmDirCLM_summand_toModel
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (w : TangentSpace I x) (Wx : TensorRSSpace 0 (s + 1) I x) (m : Fin s → E)
    (i : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
              (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) Wx) -
            tensorSlotZeroEvalFib (I := I) (M := M) x s
              (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx)
          (unitZeroSec (I := I) (M := M) x)) m =
      (2 : ℝ) * curvatureGradContractionBilin (I := I) (M := M) g s x w Wx m (B i x) (B i x) -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            tensorSlotZeroEvalFib (I := I) (M := M) x s
              (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx)
            (unitZeroSec (I := I) (M := M) x)) m := by
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
            (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) Wx) -
          tensorSlotZeroEvalFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx) =
      (2 : ℝ) • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
            (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) Wx)) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorSlotZeroEvalFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx) from rfl]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply]
  rw [rArmBilin_apply (I := I) (M := M) g s x w Wx m (B i x) (B i x)]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_unit_finsum {ι : Type*} (s : ℕ) (x : M) (fs : Finset ι)
    (T : ι → TensorRSSpace 0 s I x) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from ∑ i ∈ fs, T i)
          (unitZeroSec (I := I) (M := M) x)) m =
      ∑ i ∈ fs, Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T i)
          (unitZeroSec (I := I) (M := M) x)) m := by
  classical
  induction fs using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            (0 : TensorRSSpace 0 s I x)) (unitZeroSec (I := I) (M := M) x) =
          (0 : Tensor0SSpace s I x) from ContinuousLinearMap.zero_apply _]
      rw [Tensor0SSpace.toModel_zero, ContinuousMultilinearMap.zero_apply]
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T a + ∑ i ∈ t, T i)
            (unitZeroSec (I := I) (M := M) x) =
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T a)
              (unitZeroSec (I := I) (M := M) x) +
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from ∑ i ∈ t, T i)
              (unitZeroSec (I := I) (M := M) x) from by
        rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T a + ∑ i ∈ t, T i) =
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T a) +
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from ∑ i ∈ t, T i) from rfl,
          ContinuousLinearMap.add_apply]]
      rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, ih]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gradArmDirCLM_frame_independent
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (B C : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hBorth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i x) (B j x) = if i = j then (1 : ℝ) else 0)
    (hCorth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (C i x) (C j x) = if i = j then (1 : ℝ) else 0)
    (Wx : TensorRSSpace 0 (s + 1) I x) :
    curvatureGradContractionDirCLM (I := I) (M := M) g s B x Wx =
      curvatureGradContractionDirCLM (I := I) (M := M) g s C x Wx := by
  classical
  apply ContinuousLinearMap.ext
  intro w
  rw [gradArmDirCLM_apply, gradArmDirCLM_apply]

  apply tensorRSSpace_ext (𝕜 := ℝ) 0 s x
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)

  have hredD : ∀ F : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b,
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            ∑ i : Fin (Module.finrank ℝ E),
              ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (F i x) w
                  (tensorSlotZeroEvalFib (I := I) (M := M) x s (F i x) Wx) -
                tensorSlotZeroEvalFib (I := I) (M := M) x s
                  (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx)) D) m =
        tensor00Scalar (I := I) (M := M) x D *
          ∑ i : Fin (Module.finrank ℝ E),
            Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
                (2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (F i x) w
                    (tensorSlotZeroEvalFib (I := I) (M := M) x s (F i x) Wx) -
                  tensorSlotZeroEvalFib (I := I) (M := M) x s
                    (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx)
                (unitZeroSec (I := I) (M := M) x)) m := by
    intro F
    set T : TensorRSSpace 0 s I x :=
      ∑ i : Fin (Module.finrank ℝ E),
        ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (F i x) w
            (tensorSlotZeroEvalFib (I := I) (M := M) x s (F i x) Wx) -
          tensorSlotZeroEvalFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx) with hT
    have hstep : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T) D) m =
        tensor00Scalar (I := I) (M := M) x D *
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T)
              (unitZeroSec (I := I) (M := M) x)) m := by
      conv_lhs => rw [tensor0S_zero_span' (I := I) (M := M) x D]
      rw [ContinuousLinearMap.map_smul]
      simp only [Tensor0SSpace.toModel_smul,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    rw [hstep, hT]
    apply congrArg (fun z : ℝ => tensor00Scalar (I := I) (M := M) x D * z)
    exact toModel_unit_finsum (I := I) (M := M) s x Finset.univ
      (fun i => (2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (F i x) w
            (tensorSlotZeroEvalFib (I := I) (M := M) x s (F i x) Wx) -
          tensorSlotZeroEvalFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx) m
  rw [hredD B, hredD C]
  apply congrArg (fun z : ℝ => tensor00Scalar (I := I) (M := M) x D * z)

  rw [Finset.sum_congr rfl (fun i _ =>
    gradArmDirCLM_summand_toModel (I := I) (M := M) g s x B w Wx m i),
    Finset.sum_congr rfl (fun i _ =>
    gradArmDirCLM_summand_toModel (I := I) (M := M) g s x C w Wx m i)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  apply congrArg₂ (fun a b : ℝ => a - b)
  · rw [← Finset.mul_sum, ← Finset.mul_sum]
    apply congrArg (fun z : ℝ => 2 * z)
    rw [orthonormal_basis_bilin_trace (I := I) g x (curvatureGradContractionBilin (I := I) (M := M) g s x w Wx m)
        (fun i => B i x) hBorth,
      orthonormal_basis_bilin_trace (I := I) g x (curvatureGradContractionBilin (I := I) (M := M) g s x w Wx m)
        (fun i => C i x) hCorth]
  · have hsliceSum : ∀ F : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b,
        (∑ i : Fin (Module.finrank ℝ E),
            Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
              tensorSlotZeroEvalFib (I := I) (M := M) x s
                (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx)
              (unitZeroSec (I := I) (M := M) x)) m) =
          Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            tensorSlotZeroEvalFib (I := I) (M := M) x s
              (∑ i : Fin (Module.finrank ℝ E),
                riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx)
            (unitZeroSec (I := I) (M := M) x)) m := by
      intro F

      let sliceLM : TangentSpace I x →ₗ[ℝ] TensorRSSpace 0 s I x :=
        { toFun := fun v => tensorSlotZeroEvalFib (I := I) (M := M) x s v Wx
          map_add' := fun v v' => slot0SliceFib_dir_add (I := I) (M := M) x s v v' Wx
          map_smul' := fun c v => slot0SliceFib_dir_smul (I := I) (M := M) x s c v Wx }
      have hdir : tensorSlotZeroEvalFib (I := I) (M := M) x s
            (∑ i : Fin (Module.finrank ℝ E),
              riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx =
          ∑ i : Fin (Module.finrank ℝ E),
            tensorSlotZeroEvalFib (I := I) (M := M) x s
              (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx :=
        map_sum sliceLM (fun i => riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x))
          Finset.univ
      rw [hdir]
      exact (toModel_unit_finsum (I := I) (M := M) s x Finset.univ
        (fun i => tensorSlotZeroEvalFib (I := I) (M := M) x s
          (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx) m).symm
    rw [hsliceSum B, hsliceSum C]
    rw [frameSum_riemannOp_LeviCivita_eq_neg_ricEndoRaised (I := I) (M := M) g x
        (fun i => B i x) hBorth w,
      frameSum_riemannOp_LeviCivita_eq_neg_ricEndoRaised (I := I) (M := M) g x
        (fun i => C i x) hCorth w]

omit [CompactSpace M] [I.Boundaryless] in
lemma gradArmFib_moving_section_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {Y : Π b : M, TensorRSSpace 0 (s + 1) I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) b (Y b))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
        (curvatureGradContractionFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x) x (Y x))) := by
  classical
  intro x₀

  have hfrozen : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
        (curvatureGradContractionFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x₀) x (Y x))) x₀ :=
    gradArmFib_frozen_section_contMDiff (I := I) (M := M) g s
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) hY x₀
  refine hfrozen.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy

  refine congrArg (TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
    (E := fun z : M => TensorRSSpace 0 (s + 1) I z) y) ?_
  rw [gradArmFib_apply, gradArmFib_apply,
    gradArmDirCLM_frame_independent (I := I) (M := M) g s y
      (fun i => smoothOrthoFrame (I := I) g y i) (fun i => smoothOrthoFrame (I := I) g x₀ i)
      (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g y i j)
      (fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hy i j) (Y y)]

noncomputable def curvatureGradContractionSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 (s + 1)) :
    SmoothCcTensor g 0 (s + 1) where
  toSection :=
    { toFun := fun x : M =>
        curvatureGradContractionFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x) x (W.toSection x)
      contMDiff_toFun :=
        gradArmFib_moving_section_contMDiff (I := I) (M := M) g s W.toSection.contMDiff_toFun }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
@[simp] lemma gradArmSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 (s + 1)) (x : M) :
    (curvatureGradContractionSection (I := I) (M := M) g s W).toSection x =
      curvatureGradContractionFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x) x (W.toSection x) := rfl

noncomputable def curvatureCommutatorRemainderSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  pointwiseTensorCurv (I := I) (M := M) g s S -
    curvatureGradContractionSection (I := I) (M := M) g s (covGrad (I := I) (M := M) g 0 s S)

lemma diffArmSection_slice_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    tensor0SToTensorRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (curvatureCommutatorRemainderSection (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x))
          (smoothOrthoFrame (I := I) g x a x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x := by
  classical

  have hsub : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (curvatureCommutatorRemainderSection (I := I) (M := M) g s S).toSection x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (curvatureGradContractionSection (I := I) (M := M) g s
            (covGrad (I := I) (M := M) g 0 s S)).toSection x) := by
    rw [curvatureCommutatorRemainderSection, SmoothCcTensor.toSection_sub]; rfl
  rw [hsub, ContinuousLinearMap.sub_apply, map_sub, ContinuousLinearMap.sub_apply,
    tensor0SAsRS_sub' (I := I) (M := M) s x]

  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (curvatureGradContractionSection (I := I) (M := M) g s
          (covGrad (I := I) (M := M) g 0 s S)).toSection x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        curvatureGradContractionFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x)) from rfl]
  rw [slot0_read_curv_eq_frameFree (I := I) (M := M) g s S
    (smoothOrthoFrame_smooth (I := I) g x a) x]
  rw [gradArmFib_covGrad_slice_eq (I := I) (M := M) g s S x a]
  abel

lemma diffArmSection_slice_toModel_value_local
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (a : Fin (Module.finrank ℝ E)) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensor0SToTensorRS (I := I) (M := M) x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                (curvatureCommutatorRemainderSection (I := I) (M := M) g s S).toSection x)
                (unitZeroSec (I := I) (M := M) x))
              (smoothOrthoFrame (I := I) g x a x)))
          (unitZeroSec (I := I) (M := M) x)) m =
      - ∑ k : Fin s,
          Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g s S x)
            (Function.update m k
              (∑ i : Fin (Module.finrank ℝ E),
                nablaBaseSlotCurv (I := I) g
                  (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                    (smoothOrthoFrame_smooth (I := I) g x i))
                  (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                    (smoothOrthoFrame_smooth (I := I) g x i))
                  (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
                    (smoothOrthoFrame_smooth (I := I) g x a)) x (m k))) := by
  classical
  set Ba : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
      (smoothOrthoFrame_smooth (I := I) g x a) with hBa
  set A : Π b : M, Tensor0SSpace s I b := unitEvalSection (I := I) (M := M) g s S with hA

  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor0SToTensorRS (I := I) (M := M) x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (curvatureCommutatorRemainderSection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x))
            (smoothOrthoFrame (I := I) g x a x))) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        ∑ i : Fin (Module.finrank ℝ E),
          nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x) from
    diffArmSection_slice_eq (I := I) (M := M) g s S x a]
  rw [toModel_unit_finsum (I := I) (M := M) s x Finset.univ
    (fun i => nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x) m]
  have hper : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) m =
      Tensor0SSpace.toModel
        (nablaTensor0SCurv (I := I) g s
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i)) Ba A x) m := by
    intro i
    exact nablaTensorCurvSec_tensorRSCov_unitEval (I := I) (M := M) g s
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i))
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i))
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
        (smoothOrthoFrame_smooth (I := I) g x a)) S.toSection x ▸ rfl
  rw [Finset.sum_congr rfl (fun i _ => hper i)]

  rw [frame_sum_nablaTensor0SCurv_diag_baseSlot_eval (I := I) g s Ba A
    (contMDiff_unitEvalSection (I := I) (M := M) g s S) x m]

set_option maxHeartbeats 6400000 in

lemma diffArmSection_value_local
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S₁ S₂ : SmoothCcTensor g 0 s) (x : M)
    (hx : S₁.toSection x = S₂.toSection x) :
    (curvatureCommutatorRemainderSection (I := I) (M := M) g s S₁).toSection x =
      (curvatureCommutatorRemainderSection (I := I) (M := M) g s S₂).toSection x := by
  classical

  apply tensorRSSpace_ext (𝕜 := ℝ) 0 (s + 1) x
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)

  have hredD : ∀ T : TensorRSSpace 0 (s + 1) I x,
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T) D) v =
        tensor00Scalar (I := I) (M := M) x D *
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T)
              (unitZeroSec (I := I) (M := M) x)) v := by
    intro T
    conv_lhs => rw [tensor0S_zero_span' (I := I) (M := M) x D]
    rw [ContinuousLinearMap.map_smul]
    simp only [Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [hredD, hredD]
  congr 1

  obtain ⟨w, m, hcons⟩ : ∃ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
      v = Fin.cons w m := ⟨v 0, Fin.tail v, (Fin.cons_self_tail v).symm⟩
  subst hcons
  rw [tensor0S_uncurry_cons_eval_orthonormal (I := I) g _
    (fun a => smoothOrthoFrame (I := I) g x a x)
    (fun u => smoothOrthoFrame_parsevalExpand (I := I) (M := M) g x u) w m,
    tensor0S_uncurry_cons_eval_orthonormal (I := I) g _
    (fun a => smoothOrthoFrame (I := I) g x a x)
    (fun u => smoothOrthoFrame_parsevalExpand (I := I) (M := M) g x u) w m]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1

  have hbridge : ∀ S : SmoothCcTensor g 0 s,
      Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (curvatureCommutatorRemainderSection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x))
            (smoothOrthoFrame (I := I) g x a x)) m =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            tensor0SToTensorRS (I := I) (M := M) x
              (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
                ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                  (curvatureCommutatorRemainderSection (I := I) (M := M) g s S).toSection x)
                  (unitZeroSec (I := I) (M := M) x))
                (smoothOrthoFrame (I := I) g x a x)))
            (unitZeroSec (I := I) (M := M) x)) m := by
    intro S
    rw [tensor0SAsRS_apply (I := I) (M := M) x _ (unitZeroSec (I := I) (M := M) x),
      tensor00Scalar_unitZeroSec' (I := I) (M := M) x, one_smul]
  rw [hbridge S₁, hbridge S₂]
  rw [diffArmSection_slice_toModel_value_local (I := I) (M := M) g s S₁ x a m,
    diffArmSection_slice_toModel_value_local (I := I) (M := M) g s S₂ x a m]
  rw [show unitEvalSection (I := I) (M := M) g s S₁ x =
      unitEvalSection (I := I) (M := M) g s S₂ x from by
    rw [unitEvalSection_apply, unitEvalSection_apply, hx]]

omit [I.Boundaryless] in
lemma gradArmSection_toSection_add
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W₁ W₂ : SmoothCcTensor g 0 (s + 1)) (x : M) :
    (curvatureGradContractionSection (I := I) (M := M) g s (W₁ + W₂)).toSection x =
      (curvatureGradContractionSection (I := I) (M := M) g s W₁).toSection x +
        (curvatureGradContractionSection (I := I) (M := M) g s W₂).toSection x := by
  rw [gradArmSection_toSection, gradArmSection_toSection, gradArmSection_toSection]
  rw [show (W₁ + W₂).toSection x = W₁.toSection x + W₂.toSection x from by
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]]
  rw [map_add]

omit [I.Boundaryless] in
lemma gradArmSection_toSection_smul
    (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ) (W : SmoothCcTensor g 0 (s + 1)) (x : M) :
    (curvatureGradContractionSection (I := I) (M := M) g s (c • W)).toSection x =
      c • (curvatureGradContractionSection (I := I) (M := M) g s W).toSection x := by
  rw [gradArmSection_toSection, gradArmSection_toSection]
  rw [show (c • W).toSection x = c • W.toSection x from by
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]]
  rw [map_smul]

omit [I.Boundaryless] in
lemma gradArmSection_value_local
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W₁ W₂ : SmoothCcTensor g 0 (s + 1)) (x : M)
    (hx : W₁.toSection x = W₂.toSection x) :
    (curvatureGradContractionSection (I := I) (M := M) g s W₁).toSection x =
      (curvatureGradContractionSection (I := I) (M := M) g s W₂).toSection x := by
  rw [gradArmSection_toSection, gradArmSection_toSection, hx]

omit [I.Boundaryless] in
theorem exists_gradArmSection_appFullSec (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ H_R : HomTensorRSField (E := E) (M := M) 0 (s + 1) (s + 1) I,
      ∀ W : SmoothCcTensor g 0 (s + 1),
        curvatureGradContractionSection (I := I) (M := M) g s W =
          homTensorRSFieldApply (I := I) (M := M) g 0 (s + 1) (s + 1) H_R W :=
  exists_value_local_appFullSec (I := I) (M := M) g 0 (s + 1) (s + 1)
    (fun W => curvatureGradContractionSection (I := I) (M := M) g s W)
    (fun W₁ W₂ x => gradArmSection_toSection_add (I := I) (M := M) g s W₁ W₂ x)
    (fun c W x => gradArmSection_toSection_smul (I := I) (M := M) g s c W x)
    (fun W₁ W₂ x hW => gradArmSection_value_local (I := I) (M := M) g s W₁ W₂ x hW)

lemma pointwiseTensorCurv_toSection_add
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S₁ S₂ : SmoothCcTensor g 0 s) (x : M) :
    (pointwiseTensorCurv (I := I) (M := M) g s (S₁ + S₂)).toSection x =
      (pointwiseTensorCurv (I := I) (M := M) g s S₁).toSection x +
        (pointwiseTensorCurv (I := I) (M := M) g s S₂).toSection x := by
  classical
  have hRoughGrad : rawTensorConnLapSmooth (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s (S₁ + S₂)) =
      rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S₁) +
        rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S₂) := by
    rw [covGrad_add (I := I) (M := M) g 0 s S₁ S₂]
    apply SmoothCcTensor.ext; apply ContMDiffSection.ext; intro y
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      rawTensorConnLapSmooth_toSection_apply, rawTensorConnLapSmooth_toSection_apply,
      rawTensorConnLapSmooth_toSection_apply]
    rw [show (fun z : M => (covGrad (I := I) (M := M) g 0 s S₁ +
          covGrad (I := I) (M := M) g 0 s S₂).toSection z) =
        (fun z : M => (covGrad (I := I) (M := M) g 0 s S₁).toSection z) +
          (fun z : M => (covGrad (I := I) (M := M) g 0 s S₂).toSection z) from by
      funext z; rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]]
    exact rawTensorConnLap_add (I := I) g 0 (s + 1)
      (fun z => ((covGrad (I := I) (M := M) g 0 s S₁).toSection.contMDiff z).mdifferentiableAt
        (by simp))
      (fun z => ((covGrad (I := I) (M := M) g 0 s S₂).toSection.contMDiff z).mdifferentiableAt
        (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S₁).toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S₂).toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp)) y
  have hGradRough : covGrad (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s (S₁ + S₂)) =
      covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S₁) +
        covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S₂) := by
    rw [← covGrad_add (I := I) (M := M) g 0 s]
    refine congrArg (covGrad (I := I) (M := M) g 0 s) ?_
    apply SmoothCcTensor.ext; apply ContMDiffSection.ext; intro y
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      rawTensorConnLapSmooth_toSection_apply, rawTensorConnLapSmooth_toSection_apply,
      rawTensorConnLapSmooth_toSection_apply]
    rw [show (fun z : M => (S₁ + S₂).toSection z) =
        (fun z : M => S₁.toSection z) + (fun z : M => S₂.toSection z) from by
      funext z; rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]]
    exact rawTensorConnLap_add (I := I) g 0 s
      (fun z => (S₁.toSection.contMDiff z).mdifferentiableAt (by simp))
      (fun z => (S₂.toSection.contMDiff z).mdifferentiableAt (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 s S₁.toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 s S₂.toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp)) y
  rw [pointwiseTensorCurv_toSection_eq_sub, pointwiseTensorCurv_toSection_eq_sub,
    pointwiseTensorCurv_toSection_eq_sub, hRoughGrad, hGradRough]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  abel

lemma pointwiseTensorCurv_toSection_smul
    (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ) (S : SmoothCcTensor g 0 s) (x : M) :
    (pointwiseTensorCurv (I := I) (M := M) g s (c • S)).toSection x =
      c • (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x := by
  classical
  have hRoughGrad : rawTensorConnLapSmooth (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s (c • S)) =
      c • rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) := by
    rw [covGrad_smul (I := I) (M := M) g 0 s c S]
    apply SmoothCcTensor.ext; apply ContMDiffSection.ext; intro y
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      rawTensorConnLapSmooth_toSection_apply, rawTensorConnLapSmooth_toSection_apply]
    rw [show (fun z : M => (c • covGrad (I := I) (M := M) g 0 s S).toSection z) =
        (fun z : M => c • (covGrad (I := I) (M := M) g 0 s S).toSection z) from by
      funext z; rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]]
    exact rawTensorConnLap_smul (I := I) g 0 (s + 1) c
      (fun z => ((covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff z).mdifferentiableAt
        (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp)) y
  have hGradRough : covGrad (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s (c • S)) =
      c • covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S) := by
    rw [← covGrad_smul (I := I) (M := M) g 0 s]
    refine congrArg (covGrad (I := I) (M := M) g 0 s) ?_
    apply SmoothCcTensor.ext; apply ContMDiffSection.ext; intro y
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      rawTensorConnLapSmooth_toSection_apply, rawTensorConnLapSmooth_toSection_apply]
    rw [show (fun z : M => (c • S).toSection z) =
        (fun z : M => c • S.toSection z) from by
      funext z; rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]]
    exact rawTensorConnLap_smul (I := I) g 0 s c
      (fun z => (S.toSection.contMDiff z).mdifferentiableAt (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp)) y
  rw [pointwiseTensorCurv_toSection_eq_sub, pointwiseTensorCurv_toSection_eq_sub,
    hRoughGrad, hGradRough]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply, smul_sub]

lemma diffArmSection_toSection_add
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S₁ S₂ : SmoothCcTensor g 0 s) (x : M) :
    (curvatureCommutatorRemainderSection (I := I) (M := M) g s (S₁ + S₂)).toSection x =
      (curvatureCommutatorRemainderSection (I := I) (M := M) g s S₁).toSection x +
        (curvatureCommutatorRemainderSection (I := I) (M := M) g s S₂).toSection x := by
  rw [curvatureCommutatorRemainderSection, curvatureCommutatorRemainderSection, curvatureCommutatorRemainderSection]
  rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, ContMDiffSection.coe_sub, ContMDiffSection.coe_sub,
    Pi.sub_apply, Pi.sub_apply, Pi.sub_apply]
  rw [pointwiseTensorCurv_toSection_add (I := I) (M := M) g s S₁ S₂]
  rw [covGrad_add (I := I) (M := M) g 0 s S₁ S₂,
    gradArmSection_toSection_add (I := I) (M := M) g s
      (covGrad (I := I) (M := M) g 0 s S₁) (covGrad (I := I) (M := M) g 0 s S₂) x]
  abel

lemma diffArmSection_toSection_smul
    (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ) (S : SmoothCcTensor g 0 s) (x : M) :
    (curvatureCommutatorRemainderSection (I := I) (M := M) g s (c • S)).toSection x =
      c • (curvatureCommutatorRemainderSection (I := I) (M := M) g s S).toSection x := by
  rw [curvatureCommutatorRemainderSection, curvatureCommutatorRemainderSection]
  rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, ContMDiffSection.coe_sub, Pi.sub_apply, Pi.sub_apply]
  rw [pointwiseTensorCurv_toSection_smul (I := I) (M := M) g s c S]
  rw [covGrad_smul (I := I) (M := M) g 0 s c S,
    gradArmSection_toSection_smul (I := I) (M := M) g s c
      (covGrad (I := I) (M := M) g 0 s S) x]
  rw [smul_sub]

theorem exists_diffArmSection_appFullSec (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ H_dR : HomTensorRSField (E := E) (M := M) 0 s (s + 1) I,
      ∀ S : SmoothCcTensor g 0 s,
        curvatureCommutatorRemainderSection (I := I) (M := M) g s S =
          homTensorRSFieldApply (I := I) (M := M) g 0 s (s + 1) H_dR S :=
  exists_value_local_appFullSec (I := I) (M := M) g 0 s (s + 1)
    (fun S => curvatureCommutatorRemainderSection (I := I) (M := M) g s S)
    (fun S₁ S₂ x => diffArmSection_toSection_add (I := I) (M := M) g s S₁ S₂ x)
    (fun c S x => diffArmSection_toSection_smul (I := I) (M := M) g s c S x)
    (fun S₁ S₂ x hS => diffArmSection_value_local (I := I) (M := M) g s S₁ S₂ x hS)

theorem exists_pointwiseTensorCurv_firstOrder_homField_section
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ (H_R : HomTensorRSField (E := E) (M := M) 0 (s + 1) (s + 1) I)
      (H_dR : HomTensorRSField (E := E) (M := M) 0 s (s + 1) I),
      ∀ S : SmoothCcTensor g 0 s,
        pointwiseTensorCurv (I := I) (M := M) g s S =
          homTensorRSFieldApply (I := I) (M := M) g 0 (s + 1) (s + 1) H_R
            (covGrad (I := I) (M := M) g 0 s S) +
          homTensorRSFieldApply (I := I) (M := M) g 0 s (s + 1) H_dR S := by
  obtain ⟨H_R, hH_R⟩ := exists_gradArmSection_appFullSec (I := I) (M := M) (E := E) g s
  obtain ⟨H_dR, hH_dR⟩ := exists_diffArmSection_appFullSec (I := I) (M := M) (E := E) g s
  refine ⟨H_R, H_dR, fun S => ?_⟩

  have hdecomp : pointwiseTensorCurv (I := I) (M := M) g s S =
      curvatureGradContractionSection (I := I) (M := M) g s (covGrad (I := I) (M := M) g 0 s S) +
        curvatureCommutatorRemainderSection (I := I) (M := M) g s S := by
    rw [curvatureCommutatorRemainderSection]
    abel
  rw [hdecomp, hH_R (covGrad (I := I) (M := M) g 0 s S), hH_dR S]

end Connection
end Integral
end DifferentialGeometry

end
