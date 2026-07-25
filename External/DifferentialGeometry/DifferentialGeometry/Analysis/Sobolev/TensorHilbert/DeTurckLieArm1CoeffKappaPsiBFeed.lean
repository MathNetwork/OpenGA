import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCovariantJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SymmAbsorbedCoeffInputReindexBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.FlatArmCoeffConnectionDifferenceBridge
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffPieceConnDiffFeed


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open TensorMultilinear
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam convexPerturbation
  convexPerturbation_gFibreOpBound realizedFam_inner_of_mem Icc_subset_realizedSmallSet)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (g0FlatCLM metricComparisonEndo
  gInvRaisedEndo_apply gInvRaisedEndo_eq_diff_add_id metricComparisonDiffEndo
  cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private def lieArm1LowFixField (g₀ g_bg : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => metricConnDiffLoweredFib (I := I) g₀ g₀ g_bg x,
    metricConnDiffLoweredFib_contMDiff (I := I) g₀ g₀ g_bg⟩

private def lieArm1LowFix (g₀ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (lieArm1LowFixField (I := I) (M := M) g₀ g_bg)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

private def lieArm1PbLowField (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (gA gB : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => ccBilinConnDiffLoweredFib (I := I) g₀ P gA gB x,
    ccBilinConnDiffLoweredFib_contMDiff (I := I) g₀ P gA gB⟩

private def lieArm1PbLow (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (gA gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (lieArm1PbLowField (I := I) (M := M) g₀ P gA gB)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma lieArm1_kappa_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg) x m =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g_bg g₁ x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) g₁ g_bg x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_connDiffLowered_unitModel_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
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
private lemma lieArm1_LowFix_unitModel_apply (g₀ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (lieArm1LowFix (I := I) (M := M) g₀ g_bg) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₀ g_bg x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lieArm1LowFix (I := I) (M := M) g₀ g_bg).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (lieArm1LowFixField (I := I) (M := M) g₀ g_bg x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnDiffLoweredFib_toModel (I := I) g₀ g₀ g_bg x m

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm1_PbLow_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (lieArm1PbLow (I := I) (M := M) g₀ P gA gB) x m =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) gA gB x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lieArm1PbLow (I := I) (M := M) g₀ P gA gB).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (lieArm1PbLowField (I := I) (M := M) g₀ P gA gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact ccBilinConnDiffLoweredFib_toModel (I := I) g₀ P gA gB x m

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm1_unitModel_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) (m : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s (A + B) x m =
      unitModel (I := I) (M := M) g₀ s A x m + unitModel (I := I) (M := M) g₀ s B x m := by
  rw [unitModel, unitModel, unitModel]
  rw [show ((A + B).toSection x) = A.toSection x + B.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      (A.toSection x + B.toSection x)) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm1_unitModel_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) (m : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s (A - B) x m =
      unitModel (I := I) (M := M) g₀ s A x m - unitModel (I := I) (M := M) g₀ s B x m := by
  rw [unitModel, unitModel, unitModel]
  rw [show ((A - B).toSection x) = A.toSection x - B.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      (A.toSection x - B.toSection x)) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) from rfl]
  rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_connDiff_self_zero (gA : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) gA gA x u v = 0 := by
  have h := PDE.DeTurck.connDiff_cocycle (I := I) gA gA gA x u v
  have h2 : PDE.DeTurck.connDiff (I := I) gA gA x u v +
      PDE.DeTurck.connDiff (I := I) gA gA x u v =
      PDE.DeTurck.connDiff (I := I) gA gA x u v + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h2

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
lemma lieArm1_connDiff_antisymm (gA gB : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) gA gB x u v =
      -PDE.DeTurck.connDiff (I := I) gB gA x u v := by
  have h := PDE.DeTurck.connDiff_cocycle (I := I) gB gA gA x u v
  rw [lieArm1_connDiff_self_zero (I := I) (M := M) gA x u v] at h
  exact eq_neg_of_add_eq_zero_left h.symm

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lieArm1_kappa_add_decomp (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg =
      -(connDiffLoweredCc (I := I) g₀ g₁ + lieArm1LowFix (I := I) (M := M) g₀ g_bg
        + lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀
        + lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg) := by
  set S : SmoothCcTensor g₀ 0 3 :=
    connDiffLoweredCc (I := I) g₀ g₁ + lieArm1LowFix (I := I) (M := M) g₀ g_bg
      + lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀
      + lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg with hS_def
  rw [show -S = S - (S + S) from by abel]
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [lieArm1_unitModel_sub (I := I) (M := M) g₀ 3 S (S + S) x m,
    lieArm1_unitModel_add (I := I) (M := M) g₀ 3 S S x m]
  have hSval : unitModel (I := I) (M := M) g₀ 3 S x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) +
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₀ g_bg x (m 0) (m 1)) (m 2) +
        ccTensorBilinSymm (I := I) g₀ P x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) +
        ccTensorBilinSymm (I := I) g₀ P x
          (PDE.DeTurck.connDiff (I := I) g₀ g_bg x (m 0) (m 1)) (m 2) := by
    rw [hS_def]
    rw [lieArm1_unitModel_add (I := I) (M := M) g₀ 3 _ _ x m,
      lieArm1_unitModel_add (I := I) (M := M) g₀ 3 _ _ x m,
      lieArm1_unitModel_add (I := I) (M := M) g₀ 3 _ _ x m]
    rw [lieArm1_connDiffLowered_unitModel_apply (I := I) (M := M) g₀ g₁ x m,
      lieArm1_LowFix_unitModel_apply (I := I) (M := M) g₀ g_bg x m,
      lieArm1_PbLow_unitModel_apply (I := I) (M := M) g₀ P g₁ g₀ x m,
      lieArm1_PbLow_unitModel_apply (I := I) (M := M) g₀ P g₀ g_bg x m]
  have hκval : unitModel (I := I) (M := M) g₀ 3
      (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg) x m =
      -(g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) +
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₀ g_bg x (m 0) (m 1)) (m 2) +
        ccTensorBilinSymm (I := I) g₀ P x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) +
        ccTensorBilinSymm (I := I) g₀ P x
          (PDE.DeTurck.connDiff (I := I) g₀ g_bg x (m 0) (m 1)) (m 2)) := by
    rw [lieArm1_kappa_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x m]
    rw [htie x (PDE.DeTurck.connDiff (I := I) g_bg g₁ x (m 0) (m 1)) (m 2)]
    have hbg1 : PDE.DeTurck.connDiff (I := I) g_bg g₁ x (m 0) (m 1) =
        -(PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1) +
          PDE.DeTurck.connDiff (I := I) g₀ g_bg x (m 0) (m 1)) := by
      rw [PDE.DeTurck.connDiff_cocycle (I := I) g₀ g_bg g₁ x (m 0) (m 1)]
      rw [lieArm1_connDiff_antisymm (I := I) (M := M) g_bg g₀ x (m 0) (m 1),
        lieArm1_connDiff_antisymm (I := I) (M := M) g₀ g₁ x (m 0) (m 1)]
      abel
    rw [hbg1]
    rw [map_neg (g₀.inner x), map_neg (ccTensorBilinSymm (I := I) g₀ P x)]
    rw [ContinuousLinearMap.neg_apply, ContinuousLinearMap.neg_apply]
    rw [map_add (g₀.inner x), map_add (ccTensorBilinSymm (I := I) g₀ P x)]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
    ring
  rw [hκval, hSval]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm1_interior_product_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
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

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_connDiffSection_eq_raise_lowered (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) := by
  apply SmoothCcTensor.ext
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
    rw [lieArm1_interior_product_toModel_eval (I := I) (M := M) (1 + 1) x
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
  rw [lieArm1_connDiffLowered_unitModel_apply (I := I) (M := M) g₀ g₁ x ![YZ 0, YZ 1, u]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [g₀.symm x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1))]

omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm1_rfns_icg_lowered_eq_connDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (connDiffLoweredCc (I := I) g₀ g₁)))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (connDiffLoweredCc (I := I) g₀ g₁)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
        rw [lieArm1_connDiffSection_eq_raise_lowered (I := I) (M := M) g₀ g₁]

omit [NeZero (Module.finrank ℝ E)] in
private theorem lieArm1_pbLow_raise_eq (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (Ψc : SmoothCcTensor g₀ 1 2)
    (hΨc : ∀ x : M, Ψc.toSection x = connDiffFib (I := I) gA gB x) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 Ψc
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (ccTensor02Symm (I := I) (M := M) g₀ P)) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricRaiseSlot0Field_toSection, appCcRS_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)) u := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [lieArm1_interior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
    have hum : unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)) x =
        Tensor0SSpace.toModel D := rfl
    rw [show Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
          unitModel (I := I) (M := M) g₀ 3
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)) x
            ![u, YZ 0, YZ 1] from by
      rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
    rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
          ![YZ 0, YZ 1, u] from by
      funext i; fin_cases i <;> simp [finRotate_succ_apply]]
    rw [lieArm1_PbLow_unitModel_apply (I := I) (M := M) g₀ P gA gB x ![YZ 0, YZ 1, u]]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  have hRHS : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψc.toSection x).comp
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x)) om YZ =
      ccTensorBilinSymm (I := I) g₀ P x u
        (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)) := by
    rw [ContinuousLinearMap.comp_apply]
    rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψc.toSection x) =
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          connDiffFib (I := I) gA gB x) from by rw [hΨc x]]
    rw [connDiffFib_apply_eval]
    set om' : Tensor0SSpace 1 I x :=
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x) om with hom'
    rw [show om' (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)) =
        Tensor0SSpace.toModel om'
          (fun _ : Fin 1 =>
            (show E from PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))) from rfl]
    rw [hom']
    rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x) om =
        cometricRaiseSlot0Fib (I := I) g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (ccTensor02Symm (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x)) om from by
      rw [cometricRaiseSlot0Field_toSection]]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
    rw [lieArm1_interior_product_toModel_eval (I := I) (M := M) 1 x
      (inverseMetricSharpFib (I := I) g₀ x om) _
      (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))]
    rw [← hu]
    rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (ccTensor02Symm (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x))
          (Fin.cons (show E from u)
            (fun k => (show E from PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)))) =
        unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ P) x
          ![u, PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)] from by
      rw [unitModel]; congr 1; funext k; fin_cases k <;> rfl]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ P) x u
      (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))]
    rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P x u
      (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))]
  rw [hLHS, hRHS]
  exact (ccTensorBilinSymm_symm (I := I) g₀ P x u
    (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))).symm

omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm1_rfns_icg_pbLow_eq (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (Ψc : SmoothCcTensor g₀ 1 2)
    (hΨc : ∀ x : M, Ψc.toSection x = connDiffFib (I := I) gA gB x) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 Ψc
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (ccTensor02Symm (I := I) (M := M) g₀ P)))).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (lieArm1PbLow (I := I) (M := M) g₀ P gA gB))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (lieArm1PbLow (I := I) (M := M) g₀ P gA gB) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 Ψc
              (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
                (ccTensor02Symm (I := I) (M := M) g₀ P)))).toSection x) := by
        rw [lieArm1_pbLow_raise_eq (I := I) (M := M) g₀ P gA gB Ψc hΨc]

private theorem lieArm1_twoArm_1121_fn (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C2 : ℕ → ℝ, (∀ k, 0 ≤ C2 k) ∧ ∀ k, k ≤ a →
      ∀ (S : SmoothCcTensor g₀ 1 2) (T : SmoothCcTensor g₀ 1 1)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C2 k * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 2 n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 1 l T‖ ^ 2) := by
  have h2A : ∀ k : ℕ, k ≤ a → ∃ c : ℝ, 0 ≤ c ∧
      ∀ (S : SmoothCcTensor g₀ 1 2) (T : SmoothCcTensor g₀ 1 1)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            c * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 2 n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 1 l T‖ ^ 2) := by
    intro k _
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 1 1 2 1 k
    exact ⟨C, hC_nn, fun S T ΛS ΛT h1 h2 h3 h4 => hC S T ΛS ΛT h1 h2 h3 h4⟩
  obtain ⟨C2, hC2_nn, hC2⟩ := exists_fn_of_forall_exists_bounded a _ h2A
  exact ⟨C2, hC2_nn, hC2⟩

omit [NeZero (Module.finrank ℝ E)] in
private theorem lieArm1_WB_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    {δ₀ : ℝ} (P : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hPball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) :
    (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * max δ₀ 0 ^ 2) ∧
    (∀ l : ℕ, l ≤ a →
      ‖iteratedCovGrad (I := I) g₀ 1 1 l
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ P))‖ ^ 2 ≤ R ^ 2) := by
  constructor
  · intro x
    have h0 := riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
      (ccTensor02Symm (I := I) (M := M) g₀ P) 0 x
    simp only [iteratedCovGrad_zero] at h0
    rw [h0]
    refine le_trans (lieArm1_rfns_symmS_zero_le (I := I) (M := M) g₀ P hδ0 hδ x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hδmax : δ ≤ max δ₀ 0 := le_trans hδ_le (le_max_left _ _)
    exact pow_le_pow_left₀ hδ0 hδmax 2
  · intro l hl
    rw [lieArm1_normSq_icg_raise_eq (I := I) (M := M) g₀ 0 (ccTensor02Symm (I := I) (M := M) g₀ P) l]
    refine le_trans (lieArm1_normSq_icg_symmS_le (I := I) (M := M) g₀ P l) ?_
    have h1 := hPball l (by omega)
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2

omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm1_normSq_icg_lowered_eq (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)‖ ^ 2 := by
  rw [lieArm1_normSq_eq_integral, lieArm1_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact lieArm1_rfns_icg_lowered_eq_connDiff (I := I) (M := M) g₀ g₁ n x

omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm1_normSq_icg_pbLow_eq (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (Ψc : SmoothCcTensor g₀ 1 2)
    (hΨc : ∀ x : M, Ψc.toSection x = connDiffFib (I := I) gA gB x) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (lieArm1PbLow (I := I) (M := M) g₀ P gA gB)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 1 2 n
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 Ψc
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P)))‖ ^ 2 := by
  rw [lieArm1_normSq_eq_integral, lieArm1_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact lieArm1_rfns_icg_pbLow_eq (I := I) (M := M) g₀ P gA gB Ψc hΨc n x

omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm1_rfns_icg_raiseDomDom_eq (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (κ' : SmoothCcTensor g₀ 0 3) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
            (domDomCongrSection (I := I) g₀ σ κ'))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n κ').toSection x) := by
  rw [riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
    (domDomCongrSection (I := I) g₀ σ κ') n x]
  exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    σ κ' n x

omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm1_normSq_icg_raiseDomDom_eq (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (κ' : SmoothCcTensor g₀ 0 3) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 2 n
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ σ κ'))‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 0 3 n κ'‖ ^ 2 := by
  rw [lieArm1_normSq_eq_integral, lieArm1_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact lieArm1_rfns_icg_raiseDomDom_eq (I := I) (M := M) g₀ σ κ' n x

private theorem lieArm1_appCc12_normSq_le (g₀ : SmoothRiemannianMetric I M)
    (Φ : SmoothCcTensor g₀ 1 2) (W : SmoothCcTensor g₀ 1 1) (q : ℕ)
    (C2q ΛΦ ΛW FΦq FWq : ℝ) (hC2q : 0 ≤ C2q) (hΛΦ : 0 ≤ ΛΦ) (hΛW : 0 ≤ ΛW)
    (hΦ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (Φ.toSection x) ≤ ΛΦ)
    (hW0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (W.toSection x) ≤ ΛW)
    (hFΦ : ∑ n ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 1 2 n Φ‖ ^ 2 ≤ FΦq)
    (hFW : ∑ l ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 1 1 l W‖ ^ 2 ≤ FWq)
    (htwo : ∀ (S : SmoothCcTensor g₀ 1 2) (T : SmoothCcTensor g₀ 1 1)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 n S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 n S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C2q * (ΛT ^ 2 * ∑ n ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 2 n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 1 l T‖ ^ 2)) :
    ‖iteratedCovGrad (I := I) g₀ 1 2 q (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 Φ W)‖ ^ 2 ≤
      diagonalGridGrowthFactor (E := E) q * (C2q * (ΛW * FΦq + ΛΦ * FWq)) := by
  have hΦ0' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (Φ.toSection x) ≤
      (Real.sqrt ΛΦ) ^ 2 := by
    intro x
    rw [Real.sq_sqrt hΛΦ]
    exact hΦ0 x
  have hW0' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (W.toSection x) ≤
      (Real.sqrt ΛW) ^ 2 := by
    intro x
    rw [Real.sq_sqrt hΛW]
    exact hW0 x
  obtain ⟨hgi, hgb⟩ := htwo Φ W (Real.sqrt ΛΦ) (Real.sqrt ΛW)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hΦ0' hW0'
  have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (2 + q)
    (iteratedCovGrad (I := I) g₀ 1 2 q (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 Φ W))
    (fun x => diagonalGridGrowthFactor (E := E) q *
      ∑ n ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 2 n Φ).toSection x)
          * ∑ l ∈ Finset.range (q + 1 - n),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l W).toSection x))
    (hgi.const_mul (diagonalGridGrowthFactor (E := E) q))
    (fun x => riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ q 1 1 2 Φ W x)
  refine le_trans hkey ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) q)
  refine le_trans hgb ?_
  refine mul_le_mul_of_nonneg_left ?_ hC2q
  rw [Real.sq_sqrt hΛΦ, Real.sq_sqrt hΛW]
  have e1 := mul_le_mul_of_nonneg_left hFΦ hΛW
  have e2 := mul_le_mul_of_nonneg_left hFW hΛΦ
  linarith [e1, e2]

private theorem lieArm1_kappa_feed (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
    lieArm1_connDiff_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λlow, hΛlow_nn, hΛlow⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 3
      (lieArm1LowFix (I := I) (M := M) g₀ g_bg)
  obtain ⟨Λfx, hΛfx_nn, hΛfx⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 2
      (lieArm1FixCd (I := I) (M := M) g₀ g_bg)
  obtain ⟨C2b, hC2b_nn, hC2b⟩ := lieArm1_twoArm_1121_fn (I := I) (M := M) g₀ a
  set nQ : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * max δ₀ 0 ^ 2 with hnQ_def
  have hnQ_nn : 0 ≤ nQ := by rw [hnQ_def]; positivity
  set FB : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieArm1LowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2
    with hFB_def
  have hFB_nn : ∀ i, 0 ≤ FB i := fun i => Finset.sum_nonneg fun q _ => sq_nonneg _
  set Ffx : ℕ → ℝ := fun q => ∑ l ∈ Finset.range (q + 1),
    ‖iteratedCovGrad (I := I) g₀ 1 2 l (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2
    with hFfx_def
  have hFfx_nn : ∀ q, 0 ≤ Ffx q := fun q => Finset.sum_nonneg fun l _ => sq_nonneg _
  set FC : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    diagonalGridGrowthFactor (E := E) q * (C2b q * (nQ * Fcd q + Λcd * (((q : ℝ) + 1) * R ^ 2)))
    with hFC_def
  have hFC_nn : ∀ i, 0 ≤ FC i := by
    intro i
    refine Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hnQ_nn (hFcd_nn q))
        (mul_nonneg hΛcd_nn (by positivity))))
  set FD : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    diagonalGridGrowthFactor (E := E) q * (C2b q * (nQ * Ffx q + Λfx * (((q : ℝ) + 1) * R ^ 2)))
    with hFD_def
  have hFD_nn : ∀ i, 0 ≤ FD i := by
    intro i
    refine Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hnQ_nn (hFfx_nn q))
        (mul_nonneg hΛfx_nn (by positivity))))
  refine ⟨8 * Λcd + 8 * Λlow + 4 * (Λcd * nQ) + 2 * (Λfx * nQ),
    fun i => 8 * Fcd i + 8 * FB i + 4 * FC i + 2 * FD i,
    by
      have e1 := mul_nonneg hΛcd_nn hnQ_nn
      have e2 := mul_nonneg hΛfx_nn hnQ_nn
      linarith [hΛcd_nn, hΛlow_nn, e1, e2],
    fun i => by
      have := hFcd_nn i
      have := hFB_nn i
      have := hFC_nn i
      have := hFD_nn i
      linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hWB0, hWBL2⟩ :=
    lieArm1_WB_feed (I := I) (M := M) g₀ a P hδ_le hδ0 hδ hPball
  obtain ⟨hcd0, hcdL2⟩ := hcd g₁ P htie hδ_le hδ0 hδ hPball
  have hκeq := lieArm1_kappa_add_decomp (I := I) (M := M) g₀ g₁ g_bg P htie
  have hΨcC : ∀ x : M, (connDiffSection (I := I) g₁ g₀).toSection x =
      connDiffFib (I := I) g₁ g₀ x := fun x => rfl
  have hΨcD : ∀ x : M, (lieArm1FixCd (I := I) (M := M) g₀ g_bg).toSection x =
      connDiffFib (I := I) g₀ g_bg x := fun x => rfl
  have hWBsum : ∀ q : ℕ, q ≤ a →
      ∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 1 l
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P))‖ ^ 2 ≤ ((q : ℝ) + 1) * R ^ 2 := by
    intro q hq
    refine le_trans (Finset.sum_le_sum fun l hl =>
      hWBL2 l (le_trans (by have := Finset.mem_range.mp hl; omega : l ≤ q) hq)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    exact le_refl _
  refine ⟨?_, ?_⟩
  · intro x
    have hsec : (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg).toSection x =
        -((connDiffLoweredCc (I := I) g₀ g₁ + lieArm1LowFix (I := I) (M := M) g₀ g_bg
          + lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀
          + lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg).toSection x) := by
      rw [hκeq, SmoothCcTensor.toSection_neg]
      rfl
    rw [hsec, lieArm1_rfns_neg (I := I) (M := M) g₀ 0 3 x]
    have h1 := lieArm1_rfns_toSection_add_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁ + lieArm1LowFix (I := I) (M := M) g₀ g_bg
        + lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀)
      (lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg) x
    have h2 := lieArm1_rfns_toSection_add_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁ + lieArm1LowFix (I := I) (M := M) g₀ g_bg)
      (lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀) x
    have h3 := lieArm1_rfns_toSection_add_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁) (lieArm1LowFix (I := I) (M := M) g₀ g_bg) x
    have hA0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((connDiffLoweredCc (I := I) g₀ g₁).toSection x) ≤ Λcd := by
      have h := lieArm1_rfns_icg_lowered_eq_connDiff (I := I) (M := M) g₀ g₁ 0 x
      simp only [iteratedCovGrad_zero] at h
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((connDiffLoweredCc (I := I) g₀ g₁).toSection x)
          = riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
              ((connDiffSection (I := I) g₁ g₀).toSection x) := h
        _ ≤ Λcd := hcd0 x
    have hB0 := hΛlow x
    have hC0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀).toSection x) ≤ Λcd * nQ := by
      have h := lieArm1_rfns_icg_pbLow_eq (I := I) (M := M) g₀ P g₁ g₀
        (connDiffSection (I := I) g₁ g₀) hΨcC 0 x
      simp only [iteratedCovGrad_zero] at h
      have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
            ((ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 (connDiffSection (I := I) g₁ g₀)
              (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
                (ccTensor02Symm (I := I) (M := M) g₀ P))).toSection x) := h
      rw [h2, appCcRS_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
        (show TensorRSSpace 1 2 I x from (connDiffSection (I := I) g₁ g₀).toSection x)
        (show TensorRSSpace 1 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x)) ?_
      exact mul_le_mul (hcd0 x) (hWB0 x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) hΛcd_nn
    have hD0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg).toSection x) ≤ Λfx * nQ := by
      have h := lieArm1_rfns_icg_pbLow_eq (I := I) (M := M) g₀ P g₀ g_bg
        (lieArm1FixCd (I := I) (M := M) g₀ g_bg) hΨcD 0 x
      simp only [iteratedCovGrad_zero] at h
      have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
            ((ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 (lieArm1FixCd (I := I) (M := M) g₀ g_bg)
              (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
                (ccTensor02Symm (I := I) (M := M) g₀ P))).toSection x) := h
      rw [h2, appCcRS_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
        (show TensorRSSpace 1 2 I x from
          (lieArm1FixCd (I := I) (M := M) g₀ g_bg).toSection x)
        (show TensorRSSpace 1 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x)) ?_
      exact mul_le_mul (hΛfx x) (hWB0 x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) hΛfx_nn
    linarith [h1, h2, h3, hA0, hB0, hC0, hD0]
  · intro i hi
    have hstep : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
        8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
          8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieArm1LowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2 +
          4 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2 := by
      intro q _
      have hnorm : ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 =
          ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (connDiffLoweredCc (I := I) g₀ g₁ + lieArm1LowFix (I := I) (M := M) g₀ g_bg
              + lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀
              + lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2 := by
        rw [hκeq, iteratedCovGrad_neg, norm_neg]
      rw [hnorm]
      have k1 := lieArm1_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
        (connDiffLoweredCc (I := I) g₀ g₁ + lieArm1LowFix (I := I) (M := M) g₀ g_bg
          + lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀)
        (lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg)
      have k2 := lieArm1_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
        (connDiffLoweredCc (I := I) g₀ g₁ + lieArm1LowFix (I := I) (M := M) g₀ g_bg)
        (lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀)
      have k3 := lieArm1_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
        (connDiffLoweredCc (I := I) g₀ g₁) (lieArm1LowFix (I := I) (M := M) g₀ g_bg)
      linarith [k1, k2, k3]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    have hsplit : ∑ q ∈ Finset.range (i + 1),
        (8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
          8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieArm1LowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2 +
          4 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2) =
        8 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
          8 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lieArm1LowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2 +
          4 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
          2 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsplit]
    have hBsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lieArm1LowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2 ≤ FB i := le_rfl
    have hAsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 ≤ Fcd i := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun q _ =>
        lieArm1_normSq_icg_lowered_eq (I := I) (M := M) g₀ g₁ q)) ?_
      exact hcdL2 i hi
    have hCsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lieArm1PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 ≤ FC i := by
      rw [hFC_def]
      refine Finset.sum_le_sum fun q hq => ?_
      have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
      rw [lieArm1_normSq_icg_pbLow_eq (I := I) (M := M) g₀ P g₁ g₀
        (connDiffSection (I := I) g₁ g₀) hΨcC q]
      exact lieArm1_appCc12_normSq_le (I := I) (M := M) g₀ (connDiffSection (I := I) g₁ g₀)
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (ccTensor02Symm (I := I) (M := M) g₀ P)) q
        (C2b q) Λcd nQ (Fcd q) (((q : ℝ) + 1) * R ^ 2)
        (hC2b_nn q) hΛcd_nn hnQ_nn hcd0 hWB0 (hcdL2 q hq_le) (hWBsum q hq_le)
        (hC2b q hq_le)
    have hDsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lieArm1PbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2 ≤ FD i := by
      rw [hFD_def]
      refine Finset.sum_le_sum fun q hq => ?_
      have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
      rw [lieArm1_normSq_icg_pbLow_eq (I := I) (M := M) g₀ P g₀ g_bg
        (lieArm1FixCd (I := I) (M := M) g₀ g_bg) hΨcD q]
      refine lieArm1_appCc12_normSq_le (I := I) (M := M) g₀
        (lieArm1FixCd (I := I) (M := M) g₀ g_bg)
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (ccTensor02Symm (I := I) (M := M) g₀ P)) q
        (C2b q) Λfx nQ (Ffx q) (((q : ℝ) + 1) * R ^ 2)
        (hC2b_nn q) hΛfx_nn hnQ_nn hΛfx hWB0 le_rfl (hWBsum q hq_le)
        (hC2b q hq_le)
    linarith [hAsum, hCsum, hDsum, hBsum]

theorem lieArm1_psiB_feed (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
            ((lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 q
              (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λκ, Fκ, hΛκ_nn, hFκ_nn, hκ⟩ :=
    lieArm1_kappa_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λsf, Fsf, hΛsf_nn, hFsf_nn, hsf⟩ :=
    lieArm1_sharpFlat_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨C2b, hC2b_nn, hC2b⟩ := lieArm1_twoArm_1121_fn (I := I) (M := M) g₀ a
  refine ⟨Λκ * Λsf,
    fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2b q * (Λsf * Fκ q + Λκ * Fsf q)),
    mul_nonneg hΛκ_nn hΛsf_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hΛsf_nn (hFκ_nn q))
        (mul_nonneg hΛκ_nn (hFsf_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hκ0, hκL2⟩ := hκ g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hsf0, hsfL2⟩ := hsf g₁ P htie hδ_le hδ0 hδ hPball
  have hdef : lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
            (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))
        (sharpFlatEndoCc (I := I) g₀ g₁) := rfl
  have hA0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
      ((cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
          (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg))).toSection x) ≤ Λκ := by
    intro x
    have h := lieArm1_rfns_icg_raiseDomDom_eq (I := I) (M := M) g₀ lieArm1RhoSlot0
      (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg) 0 x
    simp only [iteratedCovGrad_zero] at h
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
            (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
              (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg))).toSection x)
        = riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg).toSection x) := h
      _ ≤ Λκ := hκ0 x
  have hAL2 : ∀ q : ℕ, q ≤ a →
      ∑ n ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 n
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
            (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
              (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))‖ ^ 2 ≤ Fκ q := by
    intro q hq
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ =>
      lieArm1_normSq_icg_raiseDomDom_eq (I := I) (M := M) g₀ lieArm1RhoSlot0
        (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg) n)) ?_
    exact hκL2 q hq
  refine ⟨?_, ?_⟩
  · intro x
    rw [hdef, appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
      (show TensorRSSpace 1 2 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
            (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg))).toSection x)
      (show TensorRSSpace 1 1 I x from (sharpFlatEndoCc (I := I) g₀ g₁).toSection x)) ?_
    exact mul_le_mul (hA0 x) (hsf0 x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) hΛκ_nn
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
    rw [hdef]
    exact lieArm1_appCc12_normSq_le (I := I) (M := M) g₀
      (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
          (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))
      (sharpFlatEndoCc (I := I) g₀ g₁) q
      (C2b q) Λκ Λsf (Fκ q) (Fsf q)
      (hC2b_nn q) hΛκ_nn hΛsf_nn hA0 hsf0 (hAL2 q hq_le) (hsfL2 q hq_le)
      (hC2b q hq_le)

end DifferentialGeometry.Integral.Connection

end
