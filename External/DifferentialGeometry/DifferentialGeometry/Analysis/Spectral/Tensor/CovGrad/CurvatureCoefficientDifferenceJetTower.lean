import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerCurvDiffGridWindow
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerRiemannLoweredDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerRiemannMixedBiContraction
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerPairTraceRepresentation
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerPerOrderTameEnvelope
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCovariantJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulParallelRaiseJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.Tuple.NatAntidiagonal


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (metricCauchySchwarzBound ccTensorBilinSymm smoothCcTensorBilinForm ccTensorBilin_apply ccTensorModel ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section TopSeparatedTransportMirrors

set_option backward.isDefEq.respectTransparency false

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tsCastRankCc_db_refl (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a : ℕ} (h : a = a)
    (W : SmoothCcTensor g₀ r a) : castCcTensorRank g₀ r h W = W := rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tsCovGrad_castRankCc_db (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W : SmoothCcTensor g₀ r a) :
    covGrad (I := I) (M := M) g₀ r b (castCcTensorRank g₀ r h W) =
      castCcTensorRank g₀ r (by omega : a + 1 = b + 1)
        (covGrad (I := I) (M := M) g₀ r a W) := by
  subst h; rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tsCastRankCc_db_trans (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b c : ℕ}
    (h₁ : a = b) (h₂ : b = c) (W : SmoothCcTensor g₀ r a) :
    castCcTensorRank g₀ r h₂ (castCcTensorRank g₀ r h₁ W) =
      castCcTensorRank g₀ r (h₁.trans h₂) W := by
  subst h₁; subst h₂; rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tsCastRankCc_db_sub (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W W' : SmoothCcTensor g₀ r a) :
    castCcTensorRank g₀ r h (W - W') = castCcTensorRank g₀ r h W - castCcTensorRank g₀ r h W' := by
  subst h; rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tsCastRankCc_db_add (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W W' : SmoothCcTensor g₀ r a) :
    castCcTensorRank g₀ r h (W + W') = castCcTensorRank g₀ r h W + castCcTensorRank g₀ r h W' := by
  subst h; rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma tsExists_iteratedCovGrad_domDomCongrSection (g₀ : SmoothRiemannianMetric I M)
    {s : ℕ} (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) (i : ℕ) :
    ∃ σ' : Equiv.Perm (Fin (s + i)),
      iteratedCovGrad (I := I) g₀ 0 s i (domDomCongrSection (I := I) g₀ σ S) =
        domDomCongrSection (I := I) g₀ σ' (iteratedCovGrad (I := I) g₀ 0 s i S) := by
  obtain ⟨σ', hσ'⟩ := exists_iteratedCovGrad_unit_toModel_domDomCongr (I := I) (M := M)
    g₀ s σ S (domDomCongrSection (I := I) g₀ σ S)
    (fun y => domDomCongrSection_unitModel (I := I) g₀ σ S y) i
  refine ⟨σ', ?_⟩
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  rw [hσ' x, domDomCongrSection_unitModel]

omit [NeZero (Module.finrank ℝ E)] in
private lemma tsExists_covGrad_domDomCongrSection (g₀ : SmoothRiemannianMetric I M)
    {s : ℕ} (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) :
    ∃ σ' : Equiv.Perm (Fin (s + 1)),
      covGrad (I := I) (M := M) g₀ 0 s (domDomCongrSection (I := I) g₀ σ S) =
        domDomCongrSection (I := I) g₀ σ' (covGrad (I := I) (M := M) g₀ 0 s S) := by
  obtain ⟨σ', hσ'⟩ := tsExists_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ σ S 1
  rw [show iteratedCovGrad (I := I) g₀ 0 s 1 (domDomCongrSection (I := I) g₀ σ S) =
      covGrad (I := I) (M := M) g₀ 0 s (domDomCongrSection (I := I) g₀ σ S) from by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]; rfl] at hσ'
  rw [show iteratedCovGrad (I := I) g₀ 0 s 1 S =
      covGrad (I := I) (M := M) g₀ 0 s S from by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]; rfl] at hσ'
  exact ⟨σ', hσ'⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tsDomDomCongrSection_refl (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (S : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ (Equiv.refl (Fin s)) S = S := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  rw [domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tsDomDomCongrSection_comp (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ τ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ τ (domDomCongrSection (I := I) g₀ σ S) =
      domDomCongrSection (I := I) g₀ (σ.trans τ) S := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.domDomCongr_apply, Equiv.trans_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tsDomDomCongrSection_sub (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S S' : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ σ (S - S') =
      domDomCongrSection (I := I) g₀ σ S - domDomCongrSection (I := I) g₀ σ S' := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  have hsub : ∀ (A B : SmoothCcTensor g₀ 0 s) (y : M),
      unitModel (I := I) (M := M) g₀ s (A - B) y =
        unitModel (I := I) (M := M) g₀ s A y - unitModel (I := I) (M := M) g₀ s B y := by
    intro A B y
    simp only [unitModel]
    rw [show ((A - B).toSection y) = A.toSection y - B.toSection y from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub]
  rw [hsub, domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel, hsub S S' x]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.domDomCongr_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tsDomDomCongrSection_add (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S S' : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ σ (S + S') =
      domDomCongrSection (I := I) g₀ σ S + domDomCongrSection (I := I) g₀ σ S' := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  have hadd : ∀ (A B : SmoothCcTensor g₀ 0 s) (y : M),
      unitModel (I := I) (M := M) g₀ s (A + B) y =
        unitModel (I := I) (M := M) g₀ s A y + unitModel (I := I) (M := M) g₀ s B y := by
    intro A B y
    simp only [unitModel]
    rw [show ((A + B).toSection y) = A.toSection y + B.toSection y from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]
  rw [hadd, domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel, hadd S S' x]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.domDomCongr_apply]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tsIteratedCovGrad_covGrad_eq_cast (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor g₀ r s) (i : ℕ) :
    iteratedCovGrad (I := I) g₀ r (s + 1) i (covGrad (I := I) (M := M) g₀ r s W) =
      castCcTensorRank g₀ r (by omega : s + (i + 1) = (s + 1) + i)
        (iteratedCovGrad (I := I) g₀ r s (i + 1) W) := by
  induction i with
  | zero =>
      rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]
      rfl
  | succ i ih =>
      rw [iteratedCovGrad_succ, ih]
      rw [tsCovGrad_castRankCc_db (I := I) (M := M) g₀ r
        (by omega : s + (i + 1) = (s + 1) + i)]
      rw [show iteratedCovGrad (I := I) g₀ r s (i + 1 + 1) W =
          covGrad (I := I) (M := M) g₀ r (s + (i + 1))
            (iteratedCovGrad (I := I) g₀ r s (i + 1) W) from by
        rw [iteratedCovGrad_succ]]

omit [NeZero (Module.finrank ℝ E)] in
private lemma tsExists_iteratedCovGrad_rsDomDomCongrSection (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (σ : Equiv.Perm (Fin s)) (Z : SmoothCcTensor g₀ r s) (i : ℕ) :
    ∃ σ' : Equiv.Perm (Fin (s + i)),
      ∀ x : M,
        ((iteratedCovGrad (I := I) g₀ r s i
            (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z)).toSection x :
          Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + i) I x) =
        tensorRS_domDomCongr (I := I) (M := M) σ'
          ((iteratedCovGrad (I := I) g₀ r s i Z).toSection x) := by
  induction i with
  | zero =>
      refine ⟨σ, fun x => ?_⟩
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
      rfl
  | succ i ih =>
      obtain ⟨σ', hσ'⟩ := ih
      refine ⟨Equiv.Perm.decomposeFin.symm (0, σ'), fun x => ?_⟩
      rw [iteratedCovGrad_succ, iteratedCovGrad_succ]
      apply ContinuousLinearMap.ext
      intro d
      apply Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro v
      have hL := covGrad_rs_toModel_domDomCongr (I := I) (M := M) g₀ r (s + i) σ'
        (iteratedCovGrad (I := I) g₀ r s i Z)
        (iteratedCovGrad (I := I) g₀ r s i
          (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z))
        (fun y d' => by
          rw [hσ' y]
          exact toModel_rsDomDomCongr_apply (I := I) (M := M) σ' _ d') x d v
      refine hL.trans ?_
      exact (congrArg (fun f => f v) (toModel_rsDomDomCongr_apply (I := I) (M := M)
        (Equiv.Perm.decomposeFin.symm (0, σ'))
        ((covGrad (I := I) (M := M) g₀ r (s + i)
          (iteratedCovGrad (I := I) g₀ r s i Z)).toSection x) d)).symm

section TsMetricLowering

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

private def tsMetricCovec (g₀ : SmoothRiemannianMetric I M) (x : M) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun m => g₀.inner x (m 0) (m 1)
      map_update_add' := by
        have h01 : (0 : Fin 2) ≠ 1 := by decide
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h10, not_false_eq_true, map_add,
            ContinuousLinearMap.add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 2) ≠ 1 := by decide
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h10, not_false_eq_true, map_smul,
            ContinuousLinearMap.smul_apply]
      cont := ((g₀.inner x).continuous.comp (continuous_apply 0)).clm_apply
        (continuous_apply 1) }
    : Tensor0SSpace 2 I x)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] private lemma tsMetricCovec_apply (g₀ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 2 → TangentSpace I x) :
    tsMetricCovec (I := I) g₀ x m = g₀.inner x (m 0) (m 1) := rfl

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tsMetricCovec_section_contMDiff (g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x (tsMetricCovec (I := I) g₀ x)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (tsMetricCovec (I := I) g₀ x :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x (Y (σ 0) x) (Y (σ 1) x)) x₀ :=
    (contMDiff_g_inner_of_smooth_sections (I := I) g₀ (Y (σ 0)) (Y (σ 1))).contMDiffAt
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframeEq : ∀ k : Fin 2, e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
    intro k
    rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change g₀.inner x (e₁.symmL ℝ x (b (σ 0))) (e₁.symmL ℝ x (b (σ 1))) = _
  rw [hframeEq 0, hframeEq 1]

private def tsMetricField (g₀ : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  ⟨fun x => tsMetricCovec (I := I) g₀ x, tsMetricCovec_section_contMDiff (I := I) g₀⟩

private def tsMetricCc (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (tsMetricField (I := I) g₀)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tsMetricCc_unitModel (g₀ : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 2 (tsMetricCc (I := I) (M := M) g₀) x =
      Tensor0SSpace.toModel (tsMetricCovec (I := I) g₀ x) := by
  rw [unitModel]
  rw [show (tsMetricCc (I := I) (M := M) g₀).toSection x
        (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (tsMetricField (I := I) g₀ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tsToModel_om_single (x : M) (om : Tensor0SSpace 1 I x)
    (m : Fin 1 → TangentSpace I x) :
    Tensor0SSpace.toModel om (fun k => (m k : E)) =
      cotangentToDual (I := I) (x := x) om (m 0) := by
  rw [show (fun k : Fin 1 => (m k : E)) = (fun _ : Fin 1 => (m 0 : E)) from by
    funext k; fin_cases k; rfl]
  rw [cotangentToDual_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tsMetricCovec_curry_eq_flat (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (tsMetricCovec (I := I) g₀ x) v =
      g0FlatCLM (I := I) g₀ x v := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
    (T := tsMetricCovec (I := I) g₀ x) (v0 := v) (vs := fun k => w k)
  rw [show (Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x)
          (tsMetricCovec (I := I) g₀ x) v)) w =
      Tensor0SSpace.toModel (tsMetricCovec (I := I) g₀ x)
        (Fin.cons v (fun k => w k)) from h1]
  rw [tsToModel_om_single (I := I) (M := M) x (g0FlatCLM (I := I) g₀ x v) w]
  rw [cotangentToDual_g0FlatCLM]
  rfl

private noncomputable def tsLoweredSlot0 (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g₀ 1 (s + 1)) : SmoothCcTensor g₀ 0 (s + 2) :=
  operatorFieldApply (I := I) (M := M) g₀ 2 (s + 2)
    (slotExtend (I := I) (M := M) g₀ 1 (s + 1) Z) (tsMetricCc (I := I) (M := M) g₀)

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tsMetricCc_toSection_unit (g₀ : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (tsMetricCc (I := I) (M := M) g₀).toSection x)
      (unitTensor (I := I) (M := M) x) = tsMetricCovec (I := I) g₀ x := by
  apply Tensor0SSpace.toModel_injective
  have h := tsMetricCc_unitModel (I := I) (M := M) g₀ x
  rw [unitModel] at h
  exact h

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tsLoweredSlot0_unitModel_apply (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g₀ 1 (s + 1)) (x : M) (m : Fin (s + 2) → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ (s + 2) (tsLoweredSlot0 (I := I) (M := M) g₀ s Z) x m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Z.toSection x)
          (g0FlatCLM (I := I) g₀ x (m 0)))
        (Matrix.vecTail m) := by
  classical
  rw [unitModel]
  rw [show ((tsLoweredSlot0 (I := I) (M := M) g₀ s Z).toSection x
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (slotExtend (I := I) (M := M) g₀ 1 (s + 1) Z).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (tsMetricCc (I := I) (M := M) g₀).toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [tsMetricCc_toSection_unit (I := I) (M := M) g₀ x]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (slotExtend (I := I) (M := M) g₀ 1 (s + 1) Z).toSection x)
        (tsMetricCovec (I := I) g₀ x)) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Z.toSection x).comp
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x)
            (tsMetricCovec (I := I) g₀ x))) from rfl]
  rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from by
    funext k
    refine Fin.cases rfl (fun j => rfl) k]
  have hkey := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := s + 1)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Z.toSection x).comp
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (tsMetricCovec (I := I) g₀ x))))
    (v0 := m 0) (vs := Matrix.vecTail (Fin.cons (m 0) (Matrix.vecTail m)))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey
  rw [show (Fin.cons (m 0) (Matrix.vecTail (Fin.cons (m 0) (Matrix.vecTail m)))
        : Fin (s + 2) → TangentSpace I x) =
      Fin.cons (m 0) (Matrix.vecTail m) from by
    funext k
    refine Fin.cases rfl (fun j => rfl) k] at hkey
  rw [← hkey]
  rw [ContinuousLinearMap.comp_apply]
  rw [tsMetricCovec_curry_eq_flat (I := I) (M := M) g₀ x (m 0)]
  rw [show (Matrix.vecTail (Fin.cons (m 0) (Matrix.vecTail m))
        : Fin (s + 1) → TangentSpace I x) = Matrix.vecTail m from by
    funext k
    rfl]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tsInteriorProduct_toModel_eval (s : ℕ) (x : M) (vv : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x vv D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from vv) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x vv D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from vv)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tsLoweredSlot0_cometricRaise (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g₀ 0 (s + 2)) :
    tsLoweredSlot0 (I := I) (M := M) g₀ s
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W) = W := by
  classical
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [tsLoweredSlot0_unitModel_apply (I := I) (M := M) g₀ s
    (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W) x m]
  rw [cometricRaiseSlot0Field_toSection (I := I) (M := M) g₀ s W x]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
      (unitTensor (I := I) (M := M) x))
    (g0FlatCLM (I := I) g₀ x (m 0))]
  rw [tsInteriorProduct_toModel_eval (I := I) (M := M) (s + 1) x
    (inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₀ x (m 0)))
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
      (unitTensor (I := I) (M := M) x)) (Matrix.vecTail m)]
  rw [inverseMetricSharpFib_g0FlatCLM]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  refine Fin.cases rfl (fun j => rfl) k

omit [NeZero (Module.finrank ℝ E)] in
private lemma tsExists_iteratedCovGrad_cometricRaiseSlot0Field (g₀ : SmoothRiemannianMetric I M)
    (s : ℕ) (W : SmoothCcTensor g₀ 0 (s + 2)) (i : ℕ) :
    ∃ σ : Equiv.Perm (Fin ((s + i) + 2)),
      iteratedCovGrad (I := I) g₀ 1 (s + 1) i
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W) =
        castCcTensorRank g₀ 1 (by omega : (s + i) + 1 = (s + 1) + i)
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ (s + i)
            (domDomCongrSection (I := I) g₀ σ
              (castCcTensorRank g₀ 0 (by omega : (s + 2) + i = (s + i) + 2)
                (iteratedCovGrad (I := I) g₀ 0 (s + 2) i W)))) := by
  induction i with
  | zero =>
      refine ⟨Equiv.refl _, ?_⟩
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
      rw [show (castCcTensorRank g₀ 0 (by omega : (s + 2) + 0 = (s + 0) + 2) W) = W from rfl]
      rw [tsDomDomCongrSection_refl (I := I) (M := M) g₀ W]
      rfl
  | succ i ih =>
      obtain ⟨σ, hσ⟩ := ih
      obtain ⟨σ', hσ'⟩ := tsExists_covGrad_domDomCongrSection (I := I) (M := M) g₀ σ
        (castCcTensorRank g₀ 0 (by omega : (s + 2) + i = (s + i) + 2)
          (iteratedCovGrad (I := I) g₀ 0 (s + 2) i W))
      refine ⟨σ'.trans (Equiv.swap (0 : Fin ((s + i) + 2 + 1)) 1), ?_⟩
      rw [iteratedCovGrad_succ, hσ]
      rw [tsCovGrad_castRankCc_db (I := I) (M := M) g₀ 1
        (by omega : (s + i) + 1 = (s + 1) + i)]
      rw [covGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ (s + i)]
      rw [hσ']
      rw [tsDomDomCongrSection_comp (I := I) (M := M) g₀ σ'
        (Equiv.swap (0 : Fin ((s + i) + 2 + 1)) 1)]
      rw [tsCovGrad_castRankCc_db (I := I) (M := M) g₀ 0
        (by omega : (s + 2) + i = (s + i) + 2)]
      rw [← iteratedCovGrad_succ]
      rfl

end TsMetricLowering

section TsHeadTransport

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tsRfns_order_congr (g : SmoothRiemannianMetric I M)
    (r s : ℕ) {n n' : ℕ} (h : n = n') (S : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + n) x
        ((iteratedCovGrad (I := I) g r s n S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + n') x
        ((iteratedCovGrad (I := I) g r s n' S).toSection x) := by
  subst h; rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma tsRfns_domDomCongrSection_zero (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x
        ((domDomCongrSection (I := I) g₀ σ S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (S.toSection x) := by
  have h := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M)
    g₀ σ S 0 x
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tsRfns_castRankCc_db_zero (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W : SmoothCcTensor g₀ r a) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r b x
        ((castCcTensorRank g₀ r h W).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r a x (W.toSection x) := by
  subst h; rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma tsSlotExtend_sub (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (X X' : SmoothCcTensor g₀ r s) :
    slotExtend (I := I) (M := M) g₀ r s (X - X') =
      slotExtend (I := I) (M := M) g₀ r s X - slotExtend (I := I) (M := M) g₀ r s X' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((slotExtend (I := I) (M := M) g₀ r s X -
        slotExtend (I := I) (M := M) g₀ r s X').toSection x) =
      (slotExtend (I := I) (M := M) g₀ r s X).toSection x -
        (slotExtend (I := I) (M := M) g₀ r s X').toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [slotExtend_toSection, slotExtend_toSection, slotExtend_toSection]
  have e0 : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from (X - X').toSection x) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x) -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X'.toSection x) := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (show TensorRSSpace (r + 1) (s + 1) I x from
          slotExtendPointwise (I := I) (M := M) g₀ r s x
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x)) -
        (show TensorRSSpace (r + 1) (s + 1) I x from
          slotExtendPointwise (I := I) (M := M) g₀ r s x
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X'.toSection x))) D) =
      (show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        slotExtendPointwise (I := I) (M := M) g₀ r s x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x)) D -
      (show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        slotExtendPointwise (I := I) (M := M) g₀ r s x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X'.toSection x)) D from rfl]
  rw [show ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        slotExtendPointwise (I := I) (M := M) g₀ r s x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from (X - X').toSection x)) D) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from (X - X').toSection x).comp
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) D)) from rfl]
  rw [e0, ContinuousLinearMap.sub_comp, map_sub]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma tsAppCc_sub_left (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ Φ' : SmoothCcTensor g₀ r s) (W : SmoothCcTensor g₀ 0 r) :
    operatorFieldApply (I := I) (M := M) g₀ r s (Φ - Φ') W =
      operatorFieldApply (I := I) (M := M) g₀ r s Φ W - operatorFieldApply (I := I) (M := M) g₀ r s Φ' W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((operatorFieldApply (I := I) (M := M) g₀ r s Φ W -
        operatorFieldApply (I := I) (M := M) g₀ r s Φ' W).toSection x) =
      (operatorFieldApply (I := I) (M := M) g₀ r s Φ W).toSection x -
        (operatorFieldApply (I := I) (M := M) g₀ r s Φ' W).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from (Φ - Φ').toSection x)) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x) -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ'.toSection x) from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_comp]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tsRsDomDomCongr_sub {r s : ℕ} {x : M} (σ : Equiv.Perm (Fin s))
    (T T' : TensorRSSpace r s I x) :
    tensorRS_domDomCongr (I := I) (M := M) σ (T - T') =
      tensorRS_domDomCongr (I := I) (M := M) σ T - tensorRS_domDomCongr (I := I) (M := M) σ T' := by
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hL := congrArg (fun f => f v)
    (toModel_rsDomDomCongr_apply (I := I) (M := M) σ (T - T') d)
  refine hL.trans ?_
  have e1 : ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T - T') d) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T') d := rfl
  have e2 : ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorRS_domDomCongr (I := I) (M := M) σ T - tensorRS_domDomCongr (I := I) (M := M) σ T') d) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorRS_domDomCongr (I := I) (M := M) σ T) d -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorRS_domDomCongr (I := I) (M := M) σ T') d := rfl
  have h1 : Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorRS_domDomCongr (I := I) (M := M) σ T) d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d)
        (fun k => v (σ k)) := by
    have := congrArg (fun f => f v) (toModel_rsDomDomCongr_apply (I := I) (M := M) σ T d)
    refine this.trans ?_
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
  have h2 : Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorRS_domDomCongr (I := I) (M := M) σ T') d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T') d)
        (fun k => v (σ k)) := by
    have := congrArg (fun f => f v) (toModel_rsDomDomCongr_apply (I := I) (M := M) σ T' d)
    refine this.trans ?_
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
  calc ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T - T') d)) v
      = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T - T') d)
          (fun k => v (σ k)) := by
        simp only [ContinuousMultilinearMap.domDomCongr_apply]
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d -
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T') d)
          (fun k => v (σ k)) := by rw [e1]
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d)
          (fun k => v (σ k)) -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T') d)
          (fun k => v (σ k)) := by
        rw [Tensor0SSpace.toModel_sub]
        simp only [ContinuousMultilinearMap.sub_apply]
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            tensorRS_domDomCongr (I := I) (M := M) σ T) d) v -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            tensorRS_domDomCongr (I := I) (M := M) σ T') d) v := by rw [h1, h2]
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            tensorRS_domDomCongr (I := I) (M := M) σ T -
              tensorRS_domDomCongr (I := I) (M := M) σ T') d) v := by
        rw [e2, Tensor0SSpace.toModel_sub]
        simp only [ContinuousMultilinearMap.sub_apply]

private lemma tsExists_loweredPair_headTransport (g₀ : SmoothRiemannianMetric I M)
    (σ₀ : Equiv.Perm (Fin (2 + 2)))
    (Y : SmoothCcTensor g₀ 1 (2 + 1)) (i : ℕ) (HY : SmoothCcTensor g₀ 1 ((2 + 1) + i)) :
    ∃ Hd : SmoothCcTensor g₀ 0 ((2 + 2) + i), ∀ x : M,
      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x (Hd.toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x (HY.toSection x)) ∧
      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) i
              (domDomCongrSection (I := I) g₀ σ₀
                (tsLoweredSlot0 (I := I) (M := M) g₀ 2 Y)) - Hd).toSection x) ≤
        2 * ((Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x)) +
        2 * ((i : ℝ) * diagonalGridGrowthFactor (E := E) i *
            ∑ k ∈ Finset.range i,
              ((Module.finrank ℝ E : ℝ) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
                  ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
                  (tsMetricCc (I := I) (M := M) g₀)).toSection x))) := by
  classical
  obtain ⟨σ₂, hσ₂⟩ := exists_iteratedCovGrad_slotExtend_rsDomDomCongr (I := I) (M := M)
    g₀ 1 (2 + 1) Y i
  obtain ⟨σ₁, hσ₁⟩ := tsExists_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    σ₀ (tsLoweredSlot0 (I := I) (M := M) g₀ 2 Y) i
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  set gW : SmoothCcTensor g₀ 0 2 := tsMetricCc (I := I) (M := M) g₀ with hgW_def
  set TransHead : SmoothCcTensor g₀ (1 + 1) (((2 + 1) + 1) + i) :=
    rsDomDomCongrSection (I := I) (M := M) g₀ (1 + 1) (((2 + 1) + 1) + i) σ₂
      (castCcTensorRank g₀ (1 + 1) (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
        (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) HY)) with hTransHead_def
  refine ⟨domDomCongrSection (I := I) g₀ σ₁
    (operatorFieldApply (I := I) (M := M) g₀ 2 ((2 + 2) + i) TransHead gW), fun x => ?_⟩
  have hgW_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (gW.toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x _
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hTransHead_rfns : ∀ (V : SmoothCcTensor g₀ 1 ((2 + 1) + i)),
      riemannianFiberNormSq (I := I) (M := M) g₀ (1 + 1) (((2 + 1) + 1) + i) x
        ((rsDomDomCongrSection (I := I) (M := M) g₀ (1 + 1) (((2 + 1) + 1) + i) σ₂
          (castCcTensorRank g₀ (1 + 1) (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
            (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) V))).toSection x) =
      n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x (V.toSection x) := by
    intro V
    rw [rsDomDomCongrSection_toSection]
    rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ (1 + 1)
      (((2 + 1) + 1) + i) x σ₂ _]
    rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ (1 + 1)
      (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
      (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) V) x]
    rw [rfns_slotExtend_eq (I := I) (M := M) g₀ 1 ((2 + 1) + i) V x]
  constructor
  · rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σ₁ _ x]
    rw [appCc_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 2
      ((2 + 2) + i) x
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace ((2 + 2) + i) I x from
        TransHead.toSection x)
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from gW.toSection x)) ?_
    rw [hTransHead_def, hTransHead_rfns HY]
    exact le_of_eq (by ring)
  · have hcorner := iteratedCovGrad_appCc_eq_coeffCorner_add_lower (I := I) (M := M) g₀ 2
      (2 + 2) (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) gW i
    have hlow : tsLoweredSlot0 (I := I) (M := M) g₀ 2 Y =
        operatorFieldApply (I := I) (M := M) g₀ 2 (2 + 2)
          (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) gW := rfl
    have hsplit : iteratedCovGrad (I := I) g₀ 0 (2 + 2) i
          (domDomCongrSection (I := I) g₀ σ₀
            (tsLoweredSlot0 (I := I) (M := M) g₀ 2 Y)) -
          domDomCongrSection (I := I) g₀ σ₁
            (operatorFieldApply (I := I) (M := M) g₀ 2 ((2 + 2) + i) TransHead gW) =
        domDomCongrSection (I := I) g₀ σ₁
          (operatorFieldApply (I := I) (M := M) g₀ 2 ((2 + 2) + i)
              (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
                (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW +
            ∑ k ∈ Finset.range i,
              ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
                (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)) := by
      rw [hσ₁, hlow, hcorner]
      rw [← tsDomDomCongrSection_sub (I := I) (M := M) g₀ σ₁]
      refine congrArg (fun Z => domDomCongrSection (I := I) g₀ σ₁ Z) ?_
      rw [tsAppCc_sub_left (I := I) (M := M) g₀ 2 ((2 + 2) + i) _ TransHead gW]
      rw [add_sub_right_comm]
    rw [hsplit]
    rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σ₁ _ x]
    rw [show (((operatorFieldApply (I := I) (M := M) g₀ 2 ((2 + 2) + i)
          (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW +
        ∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
            (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x)) =
        (operatorFieldApply (I := I) (M := M) g₀ 2 ((2 + 2) + i)
          (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW).toSection x +
        (∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
            (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 ((2 + 2) + i) x _ _) ?_
    have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
        ((operatorFieldApply (I := I) (M := M) g₀ 2 ((2 + 2) + i)
          (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW).toSection x) ≤
        n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (gW.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x) := by
      rw [appCc_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 2
        ((2 + 2) + i) x _ _) ?_
      have hD : riemannianFiberNormSq (I := I) (M := M) g₀ 2 ((2 + 2) + i) x
          ((iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead).toSection x) =
          n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x) := by
        rw [show ((iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead).toSection x) =
            (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y)).toSection x -
              TransHead.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [hσ₂ x]
        rw [hTransHead_def, rsDomDomCongrSection_toSection]
        rw [← tsRsDomDomCongr_sub (I := I) (M := M) σ₂]
        rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ (1 + 1)
          (((2 + 1) + 1) + i) x σ₂ _]
        rw [show ((castCcTensorRank g₀ (1 + 1)
              (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
              (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i)
                (iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y))).toSection x -
            (castCcTensorRank g₀ (1 + 1)
              (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
              (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) HY)).toSection x) =
            ((castCcTensorRank g₀ (1 + 1)
              (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
              (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i)
                  (iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y) -
                slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) HY)).toSection x) from by
          rw [tsCastRankCc_db_sub, SmoothCcTensor.toSection_sub]; rfl]
        rw [← tsSlotExtend_sub (I := I) (M := M) g₀ 1 ((2 + 1) + i)]
        rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ (1 + 1)
          (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i) _ x]
        rw [rfns_slotExtend_eq (I := I) (M := M) g₀ 1 ((2 + 1) + i) _ x]
      rw [hD]
      have hgWx := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x (gW.toSection x)
      have hYd := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
        ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x)
      exact le_of_eq (by ring)
    have tsCorrTerm_le : ∀ k ∈ Finset.range i,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
            (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x) ≤
        diagonalGridGrowthFactor (E := E) i *
          ((n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
              ((2 + 1) + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x)) := by
      intro k hk
      have hk_le : k + 1 ≤ i := by
        rw [Finset.mem_range] at hk; omega
      rw [appCcRS_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0
        (2 + (k + 1)) ((2 + 2) + i) x _ _) ?_
      have hΨ : riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (k + 1)) ((2 + 2) + i) x
          ((appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1)).toSection x) ≤
          diagonalGridGrowthFactor (E := E) i *
            (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
              ((2 + 1) + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) := by
        have hw := rfns_iteratedCovGrad_appCcLeibnizPsi_window_le (I := I) (M := M) g₀ 2
          (2 + 2) (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1) 0 hk_le x
        rw [iteratedCovGrad_zero] at hw
        rw [tsRfns_order_congr (I := I) (M := M) g₀ 2 (2 + 2)
          (show (i - (k + 1)) + 0 = i - (k + 1) from by omega)
          (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) x] at hw
        refine le_trans hw ?_
        exact mul_le_mul_of_nonneg_left
          (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 (2 + 1)
            Y (i - (k + 1)) x)
          (appCcGdiag_nonneg (E := E) i)
      refine le_trans (mul_le_mul_of_nonneg_right hΨ
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (k + 1)) x _)) ?_
      exact le_of_eq (by ring)
    have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
        ((∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
            (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x) ≤
        (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
          ∑ k ∈ Finset.range i,
            (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x) := by
      rw [SmoothCcTensor.toSection_sum_apply]
      refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g₀ 0
        ((2 + 2) + i) x (Finset.range i) _) ?_
      rw [Finset.card_range]
      calc ((i : ℕ) : ℝ) * ∑ k ∈ Finset.range i,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
              ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
                (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x)
          ≤ ((i : ℕ) : ℝ) * ∑ k ∈ Finset.range i,
              diagonalGridGrowthFactor (E := E) i *
                ((n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
                    ((2 + 1) + (i - (k + 1))) x
                    ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x)) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k hk => ?_))
              (Nat.cast_nonneg i)
            exact tsCorrTerm_le k hk
        _ = (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
              ∑ k ∈ Finset.range i,
                (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
                  ((2 + 1) + (i - (k + 1))) x
                  ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun k _ => by ring)
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
            ((operatorFieldApply (I := I) (M := M) g₀ 2 ((2 + 2) + i)
              (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
                (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
            ((∑ k ∈ Finset.range i,
              ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
                (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x)
        ≤ 2 * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (gW.toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
                ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x)) +
            2 * ((i : ℝ) * diagonalGridGrowthFactor (E := E) i *
              ∑ k ∈ Finset.range i,
                (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
                  ((2 + 1) + (i - (k + 1))) x
                  ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x)) := by
          have h2 : (0 : ℝ) ≤ 2 := by norm_num
          exact add_le_add (mul_le_mul_of_nonneg_left hA h2)
            (mul_le_mul_of_nonneg_left hB h2)
      _ = _ := by rw [hgW_def, hn_def]

end TsHeadTransport

section TsCarrierSplit

set_option backward.isDefEq.respectTransparency false

omit [NeZero (Module.finrank ℝ E)] in
private lemma tsConnDiff_carrier_split (g₀ g₁ : SmoothRiemannianMetric I M) (j : ℕ) :
    iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j)
          (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
          (sharpFlatEndoCc (I := I) g₀ g₁) +
        ∑ k ∈ Finset.range j,
          ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
            (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) (sharpFlatEndoCc (I := I) g₀ g₁)) := by
  rw [connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀ g₁]
  rw [iteratedCovGrad_appCcRS_eq (I := I) (M := M) g₀ 1 1 2
    (raisedKoszul (I := I) g₀ g₁) (sharpFlatEndoCc (I := I) g₀ g₁) j]
  rw [Finset.sum_range_succ' (fun k =>
    ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + k) (2 + j)
      (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j k)
      (iteratedCovGrad (I := I) g₀ 1 1 k (sharpFlatEndoCc (I := I) g₀ g₁))) j]
  have hf0 : ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + 0) (2 + j)
      (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j 0)
      (iteratedCovGrad (I := I) g₀ 1 1 0 (sharpFlatEndoCc (I := I) g₀ g₁)) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j)
        (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
        (sharpFlatEndoCc (I := I) g₀ g₁) :=
    congrArg (fun Z : SmoothCcTensor g₀ 1 (2 + j) =>
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j) Z (sharpFlatEndoCc (I := I) g₀ g₁))
      (appCcLeibnizPsi_zero_right_eq (I := I) (M := M) g₀ 1 2
        (raisedKoszul (I := I) g₀ g₁) j)
  rw [hf0]
  exact add_comm _ _

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma tsRfns_rsDomDomCongrSection_zero (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (σ : Equiv.Perm (Fin s)) (Z : SmoothCcTensor g₀ r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x
        ((rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r s x (Z.toSection x) := by
  rw [rsDomDomCongrSection_toSection]
  exact riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ r s x σ _

private lemma tsRfns_iteratedCovGrad_rsDomDomCongrSection_eq
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (σ : Equiv.Perm (Fin s))
    (Z : SmoothCcTensor g₀ r s) (m : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r (s + m) x
        ((iteratedCovGrad (I := I) g₀ r s m
          (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + m) x
        ((iteratedCovGrad (I := I) g₀ r s m Z).toSection x) :=
  riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ r s σ Z
    (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z)
    (fun y d => by
      rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) m x

end TsCarrierSplit

end TopSeparatedTransportMirrors

section TopSeparatedRungRLD

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

private lemma tsTgridSum_le_boundedWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    {W₀ K W : ℕ} (hK : W₀ ≤ K + 1) (hW : W₀ ≤ W) :
    ∑ k ∈ Finset.range W₀, Combinatorics.antidiagonalTupleGrid b k ≤
      Combinatorics.boundedFactorGridWindow b K W := by
  calc ∑ k ∈ Finset.range W₀, Combinatorics.antidiagonalTupleGrid b k
      = ∑ k ∈ Finset.range W₀, Combinatorics.boundedFactorGrid b K k :=
        Finset.sum_congr rfl (fun k hk =>
          Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
            (by rw [Finset.mem_range] at hk; omega))
    _ ≤ Combinatorics.boundedFactorGridWindow b K W := by
        rw [Combinatorics.boundedFactorGridWindow]
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr hW) ?_
        intro k _ _
        exact Combinatorics.boundedFactorGrid_nonneg b hb K k

private lemma tsResSum_le_boundedWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    ∑ k ∈ Finset.range j, b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1) ≤
      (j : ℝ) * Combinatorics.boundedFactorGridWindow b j (j + 2) := by
  calc ∑ k ∈ Finset.range j, b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)
      ≤ ∑ _k ∈ Finset.range j, Combinatorics.boundedFactorGridWindow b j (j + 2) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        rw [Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
          (show k + 1 ≤ j from by omega)]
        refine le_trans (Combinatorics.single_factor_mul_boundedFactorGrid_le b hb
          (k + 1) (j - k) (by omega) (by omega)) ?_
        rw [show (k + 1) + (j - k) = j + 1 from by omega]
        exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)
    _ = (j : ℝ) * Combinatorics.boundedFactorGridWindow b j (j + 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tsRfns_sub_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (P Q : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (P - Q) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x P +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x Q := by
  have h1 := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x P (-Q)
  have h2 := rfns_neg_pt (I := I) (M := M) g r s x Q
  rw [h2] at h1
  rw [sub_eq_add_neg]
  exact h1

private theorem tsExists_quad_jets (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) :
    ∃ KQ : ℕ → ℝ, (∀ m, 0 ≤ KQ m) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (m : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
            ((iteratedCovGrad (I := I) g₀ 1 3 m
              (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
          KQ m * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (m + 1) (m + 3) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := exists_rfns_iteratedCovGrad_connDiffSection_tgrid
    (I := I) (M := M) g₀ hδ₀
  refine ⟨fun m => diagonalGridGrowthFactor (E := E) m *
      ∑ a ∈ Finset.range (m + 1),
        ((Module.finrank ℝ E : ℝ) * CA a) *
          ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
            Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2)),
    fun m => mul_nonneg (appCcGdiag_nonneg (E := E) m)
      (Finset.sum_nonneg (fun a _ => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (hCA_nn a))
        (mul_nonneg (Finset.sum_nonneg (fun l _ => hCA_nn l))
          (Combinatorics.windowPairCellCount_nonneg _ _)))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound m x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (m + 1) (m + 3) with hWfin_def
  have hWfin_nn : 0 ≤ Wfin := Combinatorics.boundedFactorGridWindow_nonneg b hb (m + 1) (m + 3)
  have hquad : quadraticConnDiffCc (I := I) (M := M) g₀ g₁ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 3
        (armSlotEndoPassZeroCc (I := I) (M := M) g₀
          (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))
        (connDiffSection (I := I) g₁ g₀) := rfl
  rw [hquad]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ m 1 2 3
    (armSlotEndoPassZeroCc (I := I) (M := M) g₀
      (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))
    (connDiffSection (I := I) g₁ g₀) x) ?_
  have hterm : ∀ a ∈ Finset.range (m + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + a) x
          ((iteratedCovGrad (I := I) g₀ 2 3 a
            (armSlotEndoPassZeroCc (I := I) (M := M) g₀
              (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
        (∑ l ∈ Finset.range (m + 1 - a),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l
              (connDiffSection (I := I) g₁ g₀)).toSection x)) ≤
      (((Module.finrank ℝ E : ℝ) * CA a) *
        ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
          Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2))) * Wfin := by
    intro a ha
    rw [Finset.mem_range] at ha
    have hΦ : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + a) x
        ((iteratedCovGrad (I := I) g₀ 2 3 a
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) ≤
        ((Module.finrank ℝ E : ℝ) * CA a) *
          Combinatorics.boundedFactorGridWindow b (m + 1) (a + 2) := by
      refine le_trans (rfns_iteratedCovGrad_armSlotPass_connDiffArm_le (I := I) (M := M)
        g₀ g₁ a x) ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine le_trans (hCA g₁ T htie hδ_le hδ0 hbound a x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCA_nn a)
      exact tsTgridSum_le_boundedWindow b hb (by omega) (by omega)
    have hW : (∑ l ∈ Finset.range (m + 1 - a),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connDiffSection (I := I) g₁ g₀)).toSection x)) ≤
        (∑ l ∈ Finset.range (m + 1 - a), CA l) *
          Combinatorics.boundedFactorGridWindow b (m + 1) ((m - a) + 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun l hl => ?_)
      rw [Finset.mem_range] at hl
      refine le_trans (hCA g₁ T htie hδ_le hδ0 hbound l x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCA_nn l)
      exact tsTgridSum_le_boundedWindow b hb (by omega) (by omega)
    have hpair : Combinatorics.boundedFactorGridWindow b (m + 1) (a + 2) *
        Combinatorics.boundedFactorGridWindow b (m + 1) ((m - a) + 2) ≤
        Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2) * Wfin := by
      refine le_trans (Combinatorics.boundedFactorGridWindow_mul_le b hb (m + 1)
        (a + 2) ((m - a) + 2) (by omega) (by omega)) ?_
      refine mul_le_mul_of_nonneg_left ?_ (Combinatorics.windowPairCellCount_nonneg _ _)
      rw [hWfin_def]
      refine Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) ?_
      omega
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + a) x
            ((iteratedCovGrad (I := I) g₀ 2 3 a
              (armSlotEndoPassZeroCc (I := I) (M := M) g₀
                (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
          (∑ l ∈ Finset.range (m + 1 - a),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 2 l
                (connDiffSection (I := I) g₁ g₀)).toSection x))
        ≤ (((Module.finrank ℝ E : ℝ) * CA a) *
            Combinatorics.boundedFactorGridWindow b (m + 1) (a + 2)) *
          ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
            Combinatorics.boundedFactorGridWindow b (m + 1) ((m - a) + 2)) := by
          refine mul_le_mul hΦ hW (Finset.sum_nonneg (fun l _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + l) x _)) ?_
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn a))
            (Combinatorics.boundedFactorGridWindow_nonneg b hb _ _)
      _ = (((Module.finrank ℝ E : ℝ) * CA a) * (∑ l ∈ Finset.range (m + 1 - a), CA l)) *
            (Combinatorics.boundedFactorGridWindow b (m + 1) (a + 2) *
              Combinatorics.boundedFactorGridWindow b (m + 1) ((m - a) + 2)) := by ring
      _ ≤ (((Module.finrank ℝ E : ℝ) * CA a) * (∑ l ∈ Finset.range (m + 1 - a), CA l)) *
            (Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2) * Wfin) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn a))
            (Finset.sum_nonneg (fun l _ => hCA_nn l))
      _ = (((Module.finrank ℝ E : ℝ) * CA a) *
            ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
              Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2))) * Wfin := by ring
  change diagonalGridGrowthFactor (E := E) m *
      (∑ a ∈ Finset.range (m + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + a) x
            ((iteratedCovGrad (I := I) g₀ 2 3 a
              (armSlotEndoPassZeroCc (I := I) (M := M) g₀
                (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
          ∑ l ∈ Finset.range (m + 1 - a),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 2 l
                (connDiffSection (I := I) g₁ g₀)).toSection x)) ≤
    (diagonalGridGrowthFactor (E := E) m *
      ∑ a ∈ Finset.range (m + 1),
        ((Module.finrank ℝ E : ℝ) * CA a) *
          ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
            Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2))) * Wfin
  rw [mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) m)
  exact Finset.sum_le_sum hterm

private theorem tsExists_palatiniPair_jets (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) :
    ∃ KP : ℕ → ℝ, (∀ m, 0 ≤ KP m) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (m : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
            ((iteratedCovGrad (I := I) g₀ 1 3 m
              (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
                  (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
                    quadraticConnDiffCc (I := I) (M := M) g₀ g₁) -
                rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
                  (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
                    quadraticConnDiffCc (I := I) (M := M) g₀ g₁))).toSection x) ≤
          KP m * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (m + 2) (m + 3) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := exists_rfns_iteratedCovGrad_connDiffSection_tgrid
    (I := I) (M := M) g₀ hδ₀
  obtain ⟨KQ, hKQ_nn, hKQ⟩ := tsExists_quad_jets (I := I) (M := M) g₀ hδ₀
  refine ⟨fun m => 8 * (CA (m + 1) + KQ m),
    fun m => by have := hCA_nn (m + 1); have := hKQ_nn m; linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound m x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set A : SmoothCcTensor g₀ 1 3 :=
    covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
      quadraticConnDiffCc (I := I) (M := M) g₀ g₁ with hA_def
  set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (m + 2) (m + 3) with hWfin_def
  have hWfin_nn : 0 ≤ Wfin :=
    Combinatorics.boundedFactorGridWindow_nonneg b hb (m + 2) (m + 3)
  have hAjets : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
      ((iteratedCovGrad (I := I) g₀ 1 3 m A).toSection x) ≤
      (2 * CA (m + 1) + 2 * KQ m) * Wfin := by
    rw [hA_def, iteratedCovGrad_add]
    rw [show ((iteratedCovGrad (I := I) g₀ 1 3 m
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)) +
        iteratedCovGrad (I := I) g₀ 1 3 m
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) =
        (iteratedCovGrad (I := I) g₀ 1 3 m
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x +
        (iteratedCovGrad (I := I) g₀ 1 3 m
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (3 + m) x _ _) ?_
    have hcd : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 1 3 m
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x) ≤
        CA (m + 1) * Wfin := by
      rw [tsIteratedCovGrad_covGrad_eq_cast (I := I) (M := M) g₀ 1 2
        (connDiffSection (I := I) g₁ g₀) m]
      rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 1
        (by omega : 2 + (m + 1) = (2 + 1) + m)
        (iteratedCovGrad (I := I) g₀ 1 2 (m + 1) (connDiffSection (I := I) g₁ g₀)) x]
      refine le_trans (hCA g₁ T htie hδ_le hδ0 hbound (m + 1) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCA_nn (m + 1))
      exact tsTgridSum_le_boundedWindow b hb (by omega) (by omega)
    have hq : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 1 3 m
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
        KQ m * Wfin := by
      refine le_trans (hKQ g₁ T htie hδ_le hδ0 hbound m x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKQ_nn m)
      rw [hWfin_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb (by omega) (le_refl _)
    nlinarith [hcd, hq]
  rw [show ((iteratedCovGrad (I := I) g₀ 1 3 m
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) A -
          rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A)).toSection x) =
      (iteratedCovGrad (I := I) g₀ 1 3 m
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3
          (Equiv.swap (1 : Fin 3) 2) A)).toSection x -
      (iteratedCovGrad (I := I) g₀ 1 3 m
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A)).toSection x from by
    rw [iteratedCovGrad_sub, SmoothCcTensor.toSection_sub]; rfl]
  refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 1 (3 + m) x _ _) ?_
  rw [tsRfns_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 1 3
    (Equiv.swap (1 : Fin 3) 2) A m x]
  rw [tsRfns_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 1 3
    (finRotate 3) A m x]
  nlinarith [hAjets]

theorem riemannianFiberNormSq_iteratedCovGrad_riemannLoweredBackgroundDifference_topSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ),
        ∃ Hd : SmoothCcTensor g₀ 0 (4 + i),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (Hd.toSection x) ≤
              Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
                ((iteratedCovGrad (I := I) g₀ 0 4 i
                    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) -
                  Hd).toSection x) ≤
              Kc i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3)) := by
  classical
  obtain ⟨Kt0, hKt0_nn, Kc0, hKc0_nn, hbot⟩ :=
    rfns_iteratedCovGrad_connDiffSection_topSeparated_le (I := I) (M := M) g₀ hδ₀
  obtain ⟨KP, hKP_nn, hKP⟩ := tsExists_palatiniPair_jets (I := I) (M := M) g₀ hδ₀
  obtain ⟨KQ, hKQ_nn, hKQ⟩ := tsExists_quad_jets (I := I) (M := M) g₀ hδ₀
  obtain ⟨cg, hcg_nn, hcg⟩ := exists_iteratedCovGrad_fiberNormSq_bound (I := I) (M := M) g₀ 0 2
    (tsMetricCc (I := I) (M := M) g₀)
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  refine ⟨n * cg 0 * (4 * Kt0),
    mul_nonneg (mul_nonneg hn_nn (hcg_nn 0)) (mul_nonneg (by norm_num) hKt0_nn), ?_⟩
  refine ⟨fun i => 2 * (n * cg 0 *
      (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) + 2 * KQ i))) +
      2 * ((i : ℝ) * diagonalGridGrowthFactor (E := E) i *
        ∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1)),
    fun i => by
      have h1 : (0 : ℝ) ≤ Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ) :=
        mul_nonneg (hKc0_nn (i + 1)) (Nat.cast_nonneg _)
      have h2 : (0 : ℝ) ≤ KQ i := hKQ_nn i
      have h3 : (0 : ℝ) ≤ ∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1) :=
        Finset.sum_nonneg (fun k _ => mul_nonneg (mul_nonneg hn_nn (hKP_nn _)) (hcg_nn _))
      have h4 : (0 : ℝ) ≤ (i : ℝ) * diagonalGridGrowthFactor (E := E) i :=
        mul_nonneg (Nat.cast_nonneg _) (appCcGdiag_nonneg (E := E) i)
      have h5 : (0 : ℝ) ≤ n * cg 0 := mul_nonneg hn_nn (hcg_nn 0)
      nlinarith [mul_nonneg h4 h3, mul_nonneg h5 (by linarith : (0:ℝ) ≤ 4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) + 2 * KQ i))], ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i
  have hpal := riemannLoweredBackgroundDifference_palatini_repr (I := I) (M := M) g₀ g₁
  set A : SmoothCcTensor g₀ 1 3 :=
    covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
      quadraticConnDiffCc (I := I) (M := M) g₀ g₁ with hA_def
  set PA : SmoothCcTensor g₀ 1 3 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) A -
      rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A with hPA_def
  have hswap : tsLoweredSlot0 (I := I) (M := M) g₀ 2 PA =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) := by
    rw [← hpal]
    exact tsLoweredSlot0_cometricRaise (I := I) (M := M) g₀ 2 _
  have hCD4 : riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (tsLoweredSlot0 (I := I) (M := M) g₀ 2 PA) := by
    rw [hswap, tsDomDomCongrSection_comp, Equiv.swap_swap, tsDomDomCongrSection_refl]
  set HeadCore : SmoothCcTensor g₀ 1 (2 + (i + 1)) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + (i + 1))
      (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (raisedKoszul (I := I) g₀ g₁))
      (sharpFlatEndoCc (I := I) g₀ g₁) with hHeadCore_def
  set HA : SmoothCcTensor g₀ 1 (3 + i) :=
    castCcTensorRank g₀ 1 (by omega : 2 + (i + 1) = 3 + i) HeadCore with hHA_def
  obtain ⟨τ₁, hτ₁⟩ := tsExists_iteratedCovGrad_rsDomDomCongrSection (I := I) (M := M)
    g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) A i
  obtain ⟨τ₂, hτ₂⟩ := tsExists_iteratedCovGrad_rsDomDomCongrSection (I := I) (M := M)
    g₀ 1 3 (finRotate 3) A i
  set HPA : SmoothCcTensor g₀ 1 (3 + i) :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA -
      rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA with hHPA_def
  obtain ⟨Hd, hHd⟩ := tsExists_loweredPair_headTransport (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 4) 1) PA i HPA
  refine ⟨Hd, ?_, ?_⟩
  · intro x
    have h1 := (hHd x).1
    have hHPA_rfns : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        (HPA.toSection x) ≤
        4 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
          (HeadCore.toSection x) := by
      rw [hHPA_def]
      rw [show ((rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA -
            rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA).toSection x) =
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA).toSection x -
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 1 (3 + i) x _ _) ?_
      rw [tsRfns_rsDomDomCongrSection_zero (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA x,
        tsRfns_rsDomDomCongrSection_zero (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA x]
      rw [hHA_def, tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 1
        (by omega : 2 + (i + 1) = 3 + i) HeadCore x]
      linarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
        (HeadCore.toSection x)]
    have hHC := (hbot g₁ T htie hδ_le hδ0 hbound (i + 1) x).1
    rw [tsRfns_order_congr (I := I) (M := M) g₀ 0 2
      (show (i + 1) + 1 = i + 2 from by omega) T x] at hHC
    have hgW := hcg 0 x
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 0 (tsMetricCc (I := I) (M := M) g₀)) =
        tsMetricCc (I := I) (M := M) g₀ from iteratedCovGrad_zero (I := I) g₀ 0 2 _] at hgW
    have hb_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)
    have hHC_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
      (HeadCore.toSection x)
    have hgW_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x
      ((tsMetricCc (I := I) (M := M) g₀).toSection x)
    have hHPA_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (3 + i) x
      (HPA.toSection x)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (Hd.toSection x)
        ≤ n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x (HPA.toSection x) := h1
      _ ≤ n * cg 0 *
          (4 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
          have hstep1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
              (HPA.toSection x) ≤
              4 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by
            refine le_trans hHPA_rfns ?_
            linarith [hHC]
          have hng : 0 ≤ n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((tsMetricCc (I := I) (M := M) g₀).toSection x) :=
            mul_nonneg hn_nn hgW_nn
          calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
                ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x (HPA.toSection x)
              ≤ n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
                  ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
                (4 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) :=
                mul_le_mul_of_nonneg_left hstep1 hng
            _ ≤ n * cg 0 *
                (4 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
                refine mul_le_mul_of_nonneg_right ?_ ?_
                · exact mul_le_mul_of_nonneg_left hgW hn_nn
                · exact mul_nonneg (by norm_num) (mul_nonneg hKt0_nn hb_nn)
      _ = n * cg 0 * (4 * Kt0) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  · intro x
    have h2 := (hHd x).2
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
    have hb : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hWfin_def
    have hWfin_nn : 0 ≤ Wfin :=
      Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i + 3)
    rw [show (iteratedCovGrad (I := I) g₀ 0 4 i
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) =
        iteratedCovGrad (I := I) g₀ 0 4 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (tsLoweredSlot0 (I := I) (M := M) g₀ 2 PA)) from by rw [← hCD4]]
    refine le_trans h2 ?_
    have hAdiff : iteratedCovGrad (I := I) g₀ 1 3 i A - HA =
        castCcTensorRank g₀ 1 (by omega : 2 + (i + 1) = 3 + i)
          (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
            HeadCore) +
        iteratedCovGrad (I := I) g₀ 1 3 i (quadraticConnDiffCc (I := I) (M := M) g₀ g₁) := by
      rw [hA_def, iteratedCovGrad_add]
      rw [show (iteratedCovGrad (I := I) g₀ 1 3 i
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))) =
          castCcTensorRank g₀ 1 (by omega : 2 + (i + 1) = 3 + i)
            (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀))
          from tsIteratedCovGrad_covGrad_eq_cast (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I) g₁ g₀) i]
      rw [hHA_def]
      rw [tsCastRankCc_db_sub (I := I) (M := M) g₀ 1
        (by omega : 2 + (i + 1) = 3 + i)]
      exact add_sub_right_comm _ _ _
    have hdiff_pt : ((iteratedCovGrad (I := I) g₀ 1 3 i PA - HPA).toSection x :
        Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (3 + i) I x) =
        tensorRS_domDomCongr (I := I) (M := M) τ₁
            ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) -
          tensorRS_domDomCongr (I := I) (M := M) τ₂
            ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) := by
      rw [show ((iteratedCovGrad (I := I) g₀ 1 3 i PA - HPA).toSection x) =
          (iteratedCovGrad (I := I) g₀ 1 3 i PA).toSection x - HPA.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [hPA_def, iteratedCovGrad_sub]
      rw [show ((iteratedCovGrad (I := I) g₀ 1 3 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) A) -
          iteratedCovGrad (I := I) g₀ 1 3 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A)).toSection x) =
          (iteratedCovGrad (I := I) g₀ 1 3 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3
              (Equiv.swap (1 : Fin 3) 2) A)).toSection x -
          (iteratedCovGrad (I := I) g₀ 1 3 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A)).toSection x
          from by rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [hτ₁ x, hτ₂ x]
      rw [hHPA_def]
      rw [show ((rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA -
            rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA).toSection x) =
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA).toSection x -
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [rsDomDomCongrSection_toSection, rsDomDomCongrSection_toSection]
      rw [show ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) =
          (iteratedCovGrad (I := I) g₀ 1 3 i A).toSection x - HA.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [tsRsDomDomCongr_sub (I := I) (M := M) τ₁, tsRsDomDomCongr_sub (I := I) (M := M) τ₂]
      abel
    have hPAHPA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i PA - HPA).toSection x) ≤
        4 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) := by
      rw [hdiff_pt]
      refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 1 (3 + i) x _ _) ?_
      rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ 1 (3 + i) x τ₁ _,
        riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ 1 (3 + i) x τ₂ _]
      linarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x)]
    have hAHA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) ≤
        2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin + 2 * KQ i * Wfin := by
      rw [hAdiff]
      rw [show ((castCcTensorRank g₀ 1 (by omega : 2 + (i + 1) = 3 + i)
            (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
              HeadCore) +
          iteratedCovGrad (I := I) g₀ 1 3 i
            (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) =
          (castCcTensorRank g₀ 1 (by omega : 2 + (i + 1) = 3 + i)
            (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
              HeadCore)).toSection x +
          (iteratedCovGrad (I := I) g₀ 1 3 i
            (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (3 + i) x _ _) ?_
      rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 1
        (by omega : 2 + (i + 1) = 3 + i) _ x]
      have hres := (hbot g₁ T htie hδ_le hδ0 hbound (i + 1) x).2
      rw [hHeadCore_def]
      have hresW : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
            ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + (i + 1))
              (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (raisedKoszul (I := I) g₀ g₁))
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          Kc0 (i + 1) * (((i + 1 : ℕ) : ℝ) * Wfin) := by
        refine le_trans hres ?_
        refine mul_le_mul_of_nonneg_left ?_ (hKc0_nn (i + 1))
        refine le_trans (tsResSum_le_boundedWindow b hb (i + 1)) ?_
        rw [show (i + 1) + 2 = i + 3 from by omega]
      have hqW := hKQ g₁ T htie hδ_le hδ0 hbound i x
      nlinarith [hresW, hqW, hWfin_nn, hKc0_nn (i + 1), hKQ_nn i]
    have hcorr : ∀ k ∈ Finset.range i,
        (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
          ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) PA).toSection x)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
            (tsMetricCc (I := I) (M := M) g₀)).toSection x) ≤
        ((n * KP (i - (k + 1))) * cg (k + 1)) * Wfin := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hPAj : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + (i - (k + 1))) x
          ((iteratedCovGrad (I := I) g₀ 1 3 (i - (k + 1)) PA).toSection x) ≤
          KP (i - (k + 1)) * Wfin := by
        rw [hPA_def, hA_def]
        refine le_trans (hKP g₁ T htie hδ_le hδ0 hbound (i - (k + 1)) x) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hKP_nn (i - (k + 1)))
        rw [hWfin_def]
        exact Combinatorics.boundedFactorGridWindow_mono b hb (by omega) (by omega)
      have hgj := hcg (k + 1) x
      have hPAj_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1
        (3 + (i - (k + 1))) x
        ((iteratedCovGrad (I := I) g₀ 1 3 (i - (k + 1)) PA).toSection x)
      have hgj_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
          (tsMetricCc (I := I) (M := M) g₀)).toSection x)
      calc (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) PA).toSection x)) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
              (tsMetricCc (I := I) (M := M) g₀)).toSection x)
          ≤ (n * (KP (i - (k + 1)) * Wfin)) * cg (k + 1) := by
            refine mul_le_mul ?_ hgj hgj_nn ?_
            · exact mul_le_mul_of_nonneg_left hPAj hn_nn
            · exact mul_nonneg hn_nn (mul_nonneg (hKP_nn _) hWfin_nn)
        _ = ((n * KP (i - (k + 1))) * cg (k + 1)) * Wfin := by ring
    have hterm2 : (∑ k ∈ Finset.range i,
        (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
          ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) PA).toSection x)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
            (tsMetricCc (I := I) (M := M) g₀)).toSection x)) ≤
        (∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1)) * Wfin := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hcorr
    have hterm1 : n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x) ≤
        n * cg 0 * (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin +
          2 * KQ i * Wfin)) := by
      have hgW := hcg 0 x
      rw [show (iteratedCovGrad (I := I) g₀ 0 2 0 (tsMetricCc (I := I) (M := M) g₀)) =
          tsMetricCc (I := I) (M := M) g₀ from iteratedCovGrad_zero (I := I) g₀ 0 2 _] at hgW
      have hd_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x) ≤
          4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin + 2 * KQ i * Wfin) := by
        refine le_trans hPAHPA ?_
        nlinarith [hAHA, riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x)]
      have hgW_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x
        ((tsMetricCc (I := I) (M := M) g₀).toSection x)
      have hd_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
        ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x)
      calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x)
          ≤ n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
            (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin + 2 * KQ i * Wfin)) :=
            mul_le_mul_of_nonneg_left hd_le (mul_nonneg hn_nn hgW_nn)
        _ ≤ n * cg 0 * (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin +
            2 * KQ i * Wfin)) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hgW hn_nn) ?_
            have h1 : (0 : ℝ) ≤ 2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin :=
              mul_nonneg (mul_nonneg (by norm_num)
                (mul_nonneg (hKc0_nn _) (Nat.cast_nonneg _))) hWfin_nn
            have h2 : (0 : ℝ) ≤ 2 * KQ i * Wfin :=
              mul_nonneg (mul_nonneg (by norm_num) (hKQ_nn i)) hWfin_nn
            linarith
    calc 2 * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x)) +
        2 * ((i : ℝ) * diagonalGridGrowthFactor (E := E) i *
          ∑ k ∈ Finset.range i,
            (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) PA).toSection x)) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
                (tsMetricCc (I := I) (M := M) g₀)).toSection x))
        ≤ 2 * (n * cg 0 * (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin +
            2 * KQ i * Wfin))) +
          2 * ((i : ℝ) * diagonalGridGrowthFactor (E := E) i *
            ((∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1)) * Wfin)) := by
          refine add_le_add (mul_le_mul_of_nonneg_left hterm1 (by norm_num)) ?_
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left hterm2
            (mul_nonneg (Nat.cast_nonneg _) (appCcGdiag_nonneg (E := E) i))
      _ = (2 * (n * cg 0 *
            (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) + 2 * KQ i))) +
          2 * ((i : ℝ) * diagonalGridGrowthFactor (E := E) i *
            ∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1))) * Wfin := by
          ring

end TopSeparatedRungRLD

section TopSeparatedRungSlotInsert

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma tsCometricRaise_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (W W' : SmoothCcTensor g₀ 0 (s + 2)) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ s (W - W') =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ s W -
        cometricRaiseSlot0Field (I := I) (M := M) g₀ s W' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((cometricRaiseSlot0Field (I := I) (M := M) g₀ s W -
        cometricRaiseSlot0Field (I := I) (M := M) g₀ s W').toSection x) =
      (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W).toSection x -
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W').toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [cometricRaiseSlot0Field_toSection, cometricRaiseSlot0Field_toSection,
    cometricRaiseSlot0Field_toSection]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (W - W').toSection x) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
          (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W'.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [show ((W - W').toSection x) = W.toSection x - W'.toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rfl]
  apply ContinuousLinearMap.ext
  intro om
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (show TensorRSSpace 1 (s + 1) I x from
          cometricRaiseSlot0Fib g₀ s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
              (unitTensor (I := I) (M := M) x))) -
        (show TensorRSSpace 1 (s + 1) I x from
          cometricRaiseSlot0Fib g₀ s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W'.toSection x)
              (unitTensor (I := I) (M := M) x)))) om) =
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        cometricRaiseSlot0Fib g₀ s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
            (unitTensor (I := I) (M := M) x))) om -
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        cometricRaiseSlot0Fib g₀ s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W'.toSection x)
            (unitTensor (I := I) (M := M) x))) om from rfl]
  rw [cometricRaiseSlot0Fib_clm_apply, cometricRaiseSlot0Fib_clm_apply,
    cometricRaiseSlot0Fib_clm_apply]
  set DW : Tensor0SSpace (s + 2) I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hDW_def
  set DW' : Tensor0SSpace (s + 2) I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W'.toSection x)
      (unitTensor (I := I) (M := M) x) with hDW'_def
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  calc Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om) (DW - DW')) w
      = Tensor0SSpace.toModel (DW - DW')
          (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
            (fun k => (show E from w k))) :=
        tsInteriorProduct_toModel_eval (I := I) (M := M) (s + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om) (DW - DW') w
    _ = Tensor0SSpace.toModel DW
          (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
            (fun k => (show E from w k))) -
        Tensor0SSpace.toModel DW'
          (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
            (fun k => (show E from w k))) := by
        rw [Tensor0SSpace.toModel_sub]
        simp only [ContinuousMultilinearMap.sub_apply]
    _ = Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) DW) w -
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) DW') w := by
        rw [tsInteriorProduct_toModel_eval (I := I) (M := M) (s + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om) DW w]
        rw [tsInteriorProduct_toModel_eval (I := I) (M := M) (s + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om) DW' w]
    _ = Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) DW -
          Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) DW') w := by
        rw [Tensor0SSpace.toModel_sub]
        simp only [ContinuousMultilinearMap.sub_apply]

omit [NeZero (Module.finrank ℝ E)] in
private lemma tsRfns_cometricRaise_eq (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g₀ 0 (s + 2)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (s + 1) x
        ((cometricRaiseSlot0Field (I := I) (M := M) g₀ s W).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 2) x (W.toSection x) := by
  have h := riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ s W 0 x
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] in
private lemma tsAppCcRS_coeffCorner_split (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c) (W : SmoothCcTensor g₀ a b) (j : ℕ) :
    iteratedCovGrad (I := I) g₀ a c j (ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ W) =
      ccOperatorFieldComp (I := I) (M := M) g₀ a b (c + j)
          (iteratedCovGrad (I := I) g₀ b c j Φ) W +
        ∑ k ∈ Finset.range j,
          ccOperatorFieldComp (I := I) (M := M) g₀ a (b + (k + 1)) (c + j)
            (appCcLeibnizPsi (I := I) (M := M) g₀ b c Φ j (k + 1))
            (iteratedCovGrad (I := I) g₀ a b (k + 1) W) := by
  rw [iteratedCovGrad_appCcRS_eq (I := I) (M := M) g₀ a b c Φ W j]
  rw [Finset.sum_range_succ' (fun k =>
    ccOperatorFieldComp (I := I) (M := M) g₀ a (b + k) (c + j)
      (appCcLeibnizPsi (I := I) (M := M) g₀ b c Φ j k)
      (iteratedCovGrad (I := I) g₀ a b k W)) j]
  have hf0 : ccOperatorFieldComp (I := I) (M := M) g₀ a (b + 0) (c + j)
      (appCcLeibnizPsi (I := I) (M := M) g₀ b c Φ j 0)
      (iteratedCovGrad (I := I) g₀ a b 0 W) =
      ccOperatorFieldComp (I := I) (M := M) g₀ a b (c + j)
        (iteratedCovGrad (I := I) g₀ b c j Φ) W :=
    congrArg (fun Z : SmoothCcTensor g₀ b (c + j) =>
      ccOperatorFieldComp (I := I) (M := M) g₀ a b (c + j) Z W)
      (appCcLeibnizPsi_zero_right_eq (I := I) (M := M) g₀ b c Φ j)
  rw [hf0]
  exact add_comm _ _

omit [BoundarylessManifold I M] in
private lemma tsParallel_argCorner_head_le (g₀ : SmoothRiemannianMetric I M) (p a b : ℕ)
    (Φ : SmoothCcTensor g₀ a b) (i : ℕ) (HX : SmoothCcTensor g₀ p (a + i)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ p (b + i) x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ p (a + i) (b + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i i) HX).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ a b x (Φ.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ p (a + i) x (HX.toSection x) :=
  rfns_appCcRS_appCcLeibnizPsi_diag_le (I := I) (M := M) g₀ p a b Φ i HX x

private lemma tsParallel_argCorner_residual_le (g₀ : SmoothRiemannianMetric I M) (p a b : ℕ)
    (Φ : SmoothCcTensor g₀ a b)
    (hΦ : covGrad (I := I) (M := M) g₀ a b Φ = 0)
    (X : SmoothCcTensor g₀ p a) (i : ℕ) (HX : SmoothCcTensor g₀ p (a + i)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ p (b + i) x
        ((iteratedCovGrad (I := I) g₀ p b i (ccOperatorFieldComp (I := I) (M := M) g₀ p a b Φ X) -
          ccOperatorFieldComp (I := I) (M := M) g₀ p (a + i) (b + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i i) HX).toSection x) ≤
      2 * (riemannianFiberNormSq (I := I) (M := M) g₀ a b x (Φ.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ p (a + i) x
          ((iteratedCovGrad (I := I) g₀ p a i X - HX).toSection x)) := by
  have hsplit : iteratedCovGrad (I := I) g₀ p b i
        (ccOperatorFieldComp (I := I) (M := M) g₀ p a b Φ X) -
        ccOperatorFieldComp (I := I) (M := M) g₀ p (a + i) (b + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i i) HX =
      ccOperatorFieldComp (I := I) (M := M) g₀ p (a + i) (b + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i i)
          (iteratedCovGrad (I := I) g₀ p a i X - HX) +
        ∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ p (a + k) (b + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i k)
            (iteratedCovGrad (I := I) g₀ p a k X) := by
    rw [iteratedCovGrad_appCcRS_eq_argCorner_add_lower (I := I) (M := M) g₀ p a b Φ X i]
    rw [appCcRS_sub_right_cc (I := I) (M := M) g₀ p (a + i) (b + i)
      (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i i)
      (iteratedCovGrad (I := I) g₀ p a i X) HX]
    exact add_sub_right_comm _ _ _
  rw [hsplit]
  rw [show (((ccOperatorFieldComp (I := I) (M := M) g₀ p (a + i) (b + i)
        (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i i)
        (iteratedCovGrad (I := I) g₀ p a i X - HX) +
      ∑ k ∈ Finset.range i,
        ccOperatorFieldComp (I := I) (M := M) g₀ p (a + k) (b + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i k)
          (iteratedCovGrad (I := I) g₀ p a k X)).toSection x)) =
      (ccOperatorFieldComp (I := I) (M := M) g₀ p (a + i) (b + i)
        (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i i)
        (iteratedCovGrad (I := I) g₀ p a i X - HX)).toSection x +
      (∑ k ∈ Finset.range i,
        ccOperatorFieldComp (I := I) (M := M) g₀ p (a + k) (b + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i k)
          (iteratedCovGrad (I := I) g₀ p a k X)).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ p (b + i) x _ _) ?_
  have hcorr : riemannianFiberNormSq (I := I) (M := M) g₀ p (b + i) x
      ((∑ k ∈ Finset.range i,
        ccOperatorFieldComp (I := I) (M := M) g₀ p (a + k) (b + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i k)
          (iteratedCovGrad (I := I) g₀ p a k X)).toSection x) ≤ 0 := by
    refine le_trans (rfns_appCcRS_argLower_le (I := I) (M := M) g₀ p a b Φ X i x) ?_
    have hzero : ∀ k ∈ Finset.range i,
        riemannianFiberNormSq (I := I) (M := M) g₀ a (b + (i - k)) x
            ((iteratedCovGrad (I := I) g₀ a b (i - k) Φ).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ p (a + k) x
            ((iteratedCovGrad (I := I) g₀ p a k X).toSection x) = 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show i - k = (i - k - 1) + 1 from by omega]
      rw [iteratedCovGrad_zero_of_covGrad_zero (I := I) (M := M) g₀ a b Φ hΦ (i - k - 1)]
      rw [SmoothCcTensor.toSection_zero]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
      rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ a (b + ((i - k - 1) + 1)) x]
      ring
    rw [Finset.sum_congr rfl hzero, Finset.sum_const, smul_zero, mul_zero]
  have hhead := le_trans
    (rfns_appCcRS_appCcLeibnizPsi_diag_le (I := I) (M := M) g₀ p a b Φ i
      (iteratedCovGrad (I := I) g₀ p a i X - HX) x) (le_refl _)
  linarith [hhead, hcorr]

theorem rfns_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_topSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ),
        ∃ Hd : SmoothCcTensor g₀ 1 (1 + i),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x (Hd.toSection x) ≤
              Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
                ((iteratedCovGrad (I := I) g₀ 1 1 i
                    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                      (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)) -
                  Hd).toSection x) ≤
              Kc i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3)) := by
  classical
  obtain ⟨KtA, hKtA_nn, KcA, hKcA_nn, hA⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannLoweredBackgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨S, hS_nn, hS⟩ :=
    exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨CDel, hCDel_nn, hCDel⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciMixedSharpBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cPhi, hcPhi_nn, hcPhi⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
  obtain ⟨cB, hcB_nn, hcB⟩ := exists_iteratedCovGrad_fiberNormSq_bound (I := I) (M := M) g₀ 1 1
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (ricciEndomorphismField (I := I) (M := M) g₀))
  obtain ⟨cId, hcId_nn, hcId⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 1 1
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₀))
  refine ⟨cPhi * KtA * S 0,
    mul_nonneg (mul_nonneg hcPhi_nn hKtA_nn) (hS_nn 0), ?_⟩
  refine ⟨fun i => 4 * (cPhi * (KcA i) * S 0) +
      4 * ((i : ℝ) * ∑ k ∈ Finset.range i,
        diagonalGridGrowthFactor (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
          Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) +
      4 * (diagonalGridGrowthFactor (E := E) i * ∑ a' ∈ Finset.range (i + 1),
        cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l))),
    fun i => by
      have h1 : (0 : ℝ) ≤ cPhi * (KcA i) * S 0 :=
        mul_nonneg (mul_nonneg hcPhi_nn (hKcA_nn i)) (hS_nn 0)
      have h2 : (0 : ℝ) ≤ (i : ℝ) * ∑ k ∈ Finset.range i,
          diagonalGridGrowthFactor (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
            Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2) :=
        mul_nonneg (Nat.cast_nonneg i) (Finset.sum_nonneg fun k _ =>
          mul_nonneg (mul_nonneg (mul_nonneg (appCcGdiag_nonneg (E := E) i)
            (hCDel_nn _)) (hS_nn _)) (Combinatorics.windowPairCellCount_nonneg _ _))
      have h3 : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) i * ∑ a' ∈ Finset.range (i + 1),
          cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l)) :=
        mul_nonneg (appCcGdiag_nonneg (E := E) i) (Finset.sum_nonneg fun a' _ =>
          mul_nonneg (hcB_nn a') (Finset.sum_nonneg fun l _ => by
            have := hS_nn 0; have := hS_nn l; linarith))
      linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i
  obtain ⟨HdA, hHdA_head, hHdA_res⟩ := hA g₁ T htie hδ_le hδ0 hbound i
  set dTr : SmoothCcTensor g₀ 4 2 := cometricDoubleTraceField (I := I) g₀ 2 with hdTr_def
  set RLD : SmoothCcTensor g₀ 0 4 :=
    riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ with hRLD_def
  set Z : SmoothCcTensor g₀ 0 2 := ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 2 dTr RLD with hZ_def
  set ZS : SmoothCcTensor g₀ 0 2 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) Z with hZS_def
  set sF : SmoothCcTensor g₀ 1 1 := sharpFlatEndoCc (I := I) g₀ g₁ with hsF_def
  set B0f : SmoothCcTensor g₀ 1 1 :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (ricciEndomorphismField (I := I) (M := M) g₀)
    with hB0f_def
  set Dg : SmoothCcTensor g₀ 1 1 :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁)
    with hDg_def
  set InsId : SmoothCcTensor g₀ 1 1 :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₀)
    with hInsId_def
  set Delta : SmoothCcTensor g₀ 1 1 :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (ricciEndomorphismField (I := I) (M := M) g₀)
    with hDelta_def
  have hdTr_par : covGrad (I := I) (M := M) g₀ 4 2 dTr = 0 :=
    cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2
  have hsF_split : sF = Dg + InsId := by
    rw [hsF_def, hDg_def, hInsId_def,
      sharpFlatEndoCc_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁,
      fullRaisedEndoField_diff_split (I := I) (M := M) g₀ g₁,
      slotInsertEndoCc_add_endo (I := I) (M := M) g₀ 0]
  have hDg_eq : Dg = sF - InsId := eq_sub_of_add_eq hsF_split.symm
  have hBmix : endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
      (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) = Delta + B0f := by
    rw [hDelta_def, hB0f_def]; abel
  have hDeltaDg : ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta Dg =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta sF -
        ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta InsId := by
    rw [hDg_eq]
    exact appCcRS_sub_right_cc (I := I) (M := M) g₀ 1 1 1 Delta sF InsId
  have hInsRet : ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta InsId = Delta := by
    rw [hInsId_def]
    exact appCcRS_slotInsert_id_eq (I := I) (M := M) g₀ 0 1 Delta
  have hXsplit : endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta sF +
        ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 B0f Dg := by
    calc endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)
        = (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricciEndomorphismField (I := I) (M := M) g₀)) +
          ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)) :=
          slotInsertEndoCc_zero_ricEndoBackgroundDifference_telescope (I := I) (M := M) g₀ g₁
      _ = Delta + ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 (Delta + B0f) Dg := by
          rw [← hDelta_def, ← hDg_def, hBmix]
      _ = Delta + (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta Dg +
            ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 B0f Dg) := by
          rw [appCcRS_add_left_local (I := I) (M := M) g₀ 1 1 1 Delta B0f Dg]
      _ = Delta + ((ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta sF - Delta) +
            ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 B0f Dg) := by
          rw [hDeltaDg, hInsRet]
      _ = ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta sF +
            ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 B0f Dg := by abel
  have hΔrepr := slotInsert_ricMixedSharp_sub_ricEndoRaised_eq_raise_doubleTrace
    (I := I) (M := M) g₀ g₁
  obtain ⟨σs, hσs⟩ := tsExists_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) Z i
  obtain ⟨σr, hσr⟩ := tsExists_iteratedCovGrad_cometricRaiseSlot0Field (I := I) (M := M)
    g₀ 0 ZS i
  set HdZ : SmoothCcTensor g₀ 0 (2 + i) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + i) (2 + i)
      (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2 dTr i i) HdA with hHdZ_def
  set HdD : SmoothCcTensor g₀ 1 (1 + i) :=
    castCcTensorRank g₀ 1 (by omega : (0 + i) + 1 = (0 + 1) + i)
      (cometricRaiseSlot0Field (I := I) (M := M) g₀ (0 + i)
        (domDomCongrSection (I := I) g₀ σr
          (castCcTensorRank g₀ 0 (by omega : (0 + 2) + i = (0 + i) + 2)
            (domDomCongrSection (I := I) g₀ σs HdZ)))) with hHdD_def
  refine ⟨ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (1 + i) HdD sF, ?_, ?_⟩
  · intro x
    have hHdD_rfns : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        (HdD.toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x (HdZ.toSection x) := by
      rw [hHdD_def]
      rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 1
        (by omega : (0 + i) + 1 = (0 + 1) + i) _ x]
      rw [tsRfns_cometricRaise_eq (I := I) (M := M) g₀ (0 + i) _ x]
      rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σr _ x]
      rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 0
        (by omega : (0 + 2) + i = (0 + i) + 2) _ x]
      rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σs _ x]
    rw [appCcRS_toSection (I := I) (M := M) g₀ 1 1 (1 + i) HdD sF x]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 (1 + i) x
      _ _) ?_
    have hHdZ_le : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        (HdZ.toSection x) ≤
        cPhi * (KtA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by
      rw [hHdZ_def]
      refine le_trans (tsParallel_argCorner_head_le (I := I) (M := M) g₀ 0 4 2 dTr i HdA x) ?_
      exact mul_le_mul (hcPhi x) (hHdA_head x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x _) hcPhi_nn
    have hsF0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (sF.toSection x) ≤ S 0 := by
      have h := hS g₁ T htie hδ_le hδ0 hbound 0 x
      rw [iteratedCovGrad_zero] at h
      rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
      exact h
    have hb_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)
    have hHdD_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + i) x
      (HdD.toSection x)
    have hsF_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x (sF.toSection x)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x (HdD.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (sF.toSection x)
        ≤ (cPhi * (KtA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) * S 0 := by
          refine mul_le_mul ?_ hsF0 hsF_nn ?_
          · rw [hHdD_rfns]; exact hHdZ_le
          · exact mul_nonneg hcPhi_nn (mul_nonneg hKtA_nn hb_nn)
      _ = cPhi * KtA * S 0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  · intro x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
    have hb : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hWfin_def
    have hWfin_nn : 0 ≤ Wfin :=
      Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i + 3)
    have hWfin_one : 1 ≤ Wfin :=
      Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
    have hNdDiff : iteratedCovGrad (I := I) g₀ 1 1 i Delta - HdD =
        castCcTensorRank g₀ 1 (by omega : (0 + i) + 1 = (0 + 1) + i)
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ (0 + i)
            (domDomCongrSection (I := I) g₀ σr
              (castCcTensorRank g₀ 0 (by omega : (0 + 2) + i = (0 + i) + 2)
                (domDomCongrSection (I := I) g₀ σs
                  (iteratedCovGrad (I := I) g₀ 0 2 i Z - HdZ))))) := by
      have hNdDelta : iteratedCovGrad (I := I) g₀ 1 1 i Delta =
          castCcTensorRank g₀ 1 (by omega : (0 + i) + 1 = (0 + 1) + i)
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ (0 + i)
              (domDomCongrSection (I := I) g₀ σr
                (castCcTensorRank g₀ 0 (by omega : (0 + 2) + i = (0 + i) + 2)
                  (domDomCongrSection (I := I) g₀ σs
                    (iteratedCovGrad (I := I) g₀ 0 2 i Z))))) := by
        calc iteratedCovGrad (I := I) g₀ 1 1 i Delta
            = iteratedCovGrad (I := I) g₀ 1 (0 + 1) i
                (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 ZS) := by
              rw [hDelta_def, hΔrepr, hZS_def, hZ_def, hdTr_def, hRLD_def]
          _ = castCcTensorRank g₀ 1 (by omega : (0 + i) + 1 = (0 + 1) + i)
                (cometricRaiseSlot0Field (I := I) (M := M) g₀ (0 + i)
                  (domDomCongrSection (I := I) g₀ σr
                    (castCcTensorRank g₀ 0 (by omega : (0 + 2) + i = (0 + i) + 2)
                      (iteratedCovGrad (I := I) g₀ 0 (0 + 2) i ZS)))) := hσr
          _ = _ := by
              rw [show (iteratedCovGrad (I := I) g₀ 0 (0 + 2) i ZS) =
                  domDomCongrSection (I := I) g₀ σs
                    (iteratedCovGrad (I := I) g₀ 0 2 i Z) from by
                rw [← hσs, hZS_def]]
      rw [hNdDelta, hHdD_def]
      rw [← tsCastRankCc_db_sub (I := I) (M := M) g₀ 1
        (by omega : (0 + i) + 1 = (0 + 1) + i)]
      rw [← tsCometricRaise_sub (I := I) (M := M) g₀ (0 + i)]
      rw [← tsDomDomCongrSection_sub (I := I) (M := M) g₀ σr]
      rw [← tsCastRankCc_db_sub (I := I) (M := M) g₀ 0
        (by omega : (0 + 2) + i = (0 + i) + 2)]
      rw [← tsDomDomCongrSection_sub (I := I) (M := M) g₀ σs]
    have hΔres : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i Delta - HdD).toSection x) ≤
        2 * (cPhi * (KcA i * Wfin)) := by
      rw [hNdDiff]
      rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 1
        (by omega : (0 + i) + 1 = (0 + 1) + i) _ x]
      rw [tsRfns_cometricRaise_eq (I := I) (M := M) g₀ (0 + i) _ x]
      rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σr _ x]
      rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 0
        (by omega : (0 + 2) + i = (0 + i) + 2) _ x]
      rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σs _ x]
      rw [hHdZ_def, hZ_def]
      refine le_trans (tsParallel_argCorner_residual_le (I := I) (M := M) g₀ 0 4 2 dTr
        hdTr_par RLD i HdA x) ?_
      have hres := hHdA_res x
      have hd_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i RLD - HdA).toSection x)
      have hKcW_nn : 0 ≤ KcA i * Wfin := mul_nonneg (hKcA_nn i) hWfin_nn
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine mul_le_mul (hcPhi x) ?_ hd_nn hcPhi_nn
      exact hres
    set P1t := ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (1 + i)
        (iteratedCovGrad (I := I) g₀ 1 1 i Delta - HdD) sF with hP1t_def
    set P2t := ∑ k ∈ Finset.range i,
        ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (k + 1)) (1 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1))
          (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF) with hP2t_def
    set P3t := iteratedCovGrad (I := I) g₀ 1 1 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 B0f Dg) with hP3t_def
    have hsplit : iteratedCovGrad (I := I) g₀ 1 1 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)) -
          ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (1 + i) HdD sF =
        P1t + (P2t + P3t) := by
      rw [hP1t_def, hP2t_def, hP3t_def, hXsplit]
      rw [iteratedCovGrad_add (I := I) g₀ 1 1 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta sF)
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 B0f Dg)]
      rw [tsAppCcRS_coeffCorner_split (I := I) (M := M) g₀ 1 1 1 Delta sF i]
      rw [appCcRS_sub_left_local (I := I) (M := M) g₀ 1 1 (1 + i)
        (iteratedCovGrad (I := I) g₀ 1 1 i Delta) HdD sF]
      abel
    rw [hsplit]
    rw [show ((P1t + (P2t + P3t)).toSection x) =
        P1t.toSection x + (P2t + P3t).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + i) x _ _) ?_
    rw [show ((P2t + P3t).toSection x) = P2t.toSection x + P3t.toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    have hP1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        (P1t.toSection x) ≤ 2 * (cPhi * (KcA i)) * S 0 * Wfin := by
      rw [hP1t_def]
      rw [appCcRS_toSection (I := I) (M := M) g₀ 1 1 (1 + i)
        (iteratedCovGrad (I := I) g₀ 1 1 i Delta - HdD) sF x]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1
        (1 + i) x _ _) ?_
      have hsF0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (sF.toSection x) ≤
          S 0 := by
        have h := hS g₁ T htie hδ_le hδ0 hbound 0 x
        rw [iteratedCovGrad_zero] at h
        rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
        exact h
      have hsF_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x
        (sF.toSection x)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i Delta - HdD).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (sF.toSection x)
          ≤ (2 * (cPhi * (KcA i * Wfin))) * S 0 := by
            refine mul_le_mul hΔres hsF0 hsF_nn ?_
            exact mul_nonneg (by norm_num)
              (mul_nonneg hcPhi_nn (mul_nonneg (hKcA_nn i) hWfin_nn))
        _ = 2 * (cPhi * (KcA i)) * S 0 * Wfin := by ring
    have hP2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        (P2t.toSection x) ≤
        ((i : ℝ) * ∑ k ∈ Finset.range i,
          diagonalGridGrowthFactor (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
            Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin := by
      rw [hP2t_def]
      rw [SmoothCcTensor.toSection_sum_apply]
      refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g₀ 1
        (1 + i) x (Finset.range i) _) ?_
      rw [Finset.card_range]
      have hterm : ∀ k ∈ Finset.range i,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (k + 1)) (1 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1))
              (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF)).toSection x) ≤
          (diagonalGridGrowthFactor (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
            Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin := by
        intro k hk
        rw [Finset.mem_range] at hk
        rw [appCcRS_toSection (I := I) (M := M) g₀ 1 (1 + (k + 1)) (1 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1))
          (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF) x]
        refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1
          (1 + (k + 1)) (1 + i) x _ _) ?_
        have hPsi : riemannianFiberNormSq (I := I) (M := M) g₀ (1 + (k + 1)) (1 + i) x
            ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1)).toSection x) ≤
            diagonalGridGrowthFactor (E := E) i *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (i - (k + 1))) x
                ((iteratedCovGrad (I := I) g₀ 1 1 (i - (k + 1)) Delta).toSection x) := by
          have hw := rfns_iteratedCovGrad_appCcLeibnizPsi_window_le (I := I) (M := M) g₀ 1 1
            Delta i (k + 1) 0 (by omega) x
          rw [iteratedCovGrad_zero] at hw
          rw [tsRfns_order_congr (I := I) (M := M) g₀ 1 1
            (show (i - (k + 1)) + 0 = i - (k + 1) from by omega) Delta x] at hw
          exact hw
        have hDeltaJets : riemannianFiberNormSq (I := I) (M := M) g₀ 1
            (1 + (i - (k + 1))) x
            ((iteratedCovGrad (I := I) g₀ 1 1 (i - (k + 1)) Delta).toSection x) ≤
            CDel (i - (k + 1)) *
              Combinatorics.boundedFactorGridWindow b (i + 1) ((i - (k + 1)) + 3) := by
          refine le_trans (hCDel g₁ T htie hδ_le hδ0 hbound (i - (k + 1)) x) ?_
          refine mul_le_mul_of_nonneg_left ?_ (hCDel_nn (i - (k + 1)))
          exact tsTgridSum_le_boundedWindow b hb (by omega) (by omega)
        have hsFjet : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (k + 1)) x
            ((iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF).toSection x) ≤
            S (k + 1) * Combinatorics.boundedFactorGridWindow b (i + 1) (k + 2) := by
          refine le_trans (hS g₁ T htie hδ_le hδ0 hbound (k + 1) x) ?_
          refine mul_le_mul_of_nonneg_left ?_ (hS_nn (k + 1))
          rw [Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
            (show k + 1 ≤ i + 1 from by omega)]
          exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)
        have hpair : Combinatorics.boundedFactorGridWindow b (i + 1) ((i - (k + 1)) + 3) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (k + 2) ≤
            Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2) * Wfin := by
          refine le_trans (Combinatorics.boundedFactorGridWindow_mul_le b hb (i + 1)
            ((i - (k + 1)) + 3) (k + 2) (by omega) (by omega)) ?_
          refine mul_le_mul_of_nonneg_left ?_
            (Combinatorics.windowPairCellCount_nonneg _ _)
          rw [hWfin_def]
          refine Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) ?_
          omega
        calc riemannianFiberNormSq (I := I) (M := M) g₀ (1 + (k + 1)) (1 + i) x
              ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF).toSection x)
            ≤ (diagonalGridGrowthFactor (E := E) i *
                (CDel (i - (k + 1)) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) ((i - (k + 1)) + 3))) *
              (S (k + 1) * Combinatorics.boundedFactorGridWindow b (i + 1) (k + 2)) := by
              refine mul_le_mul ?_ hsFjet
                (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + (k + 1)) x _) ?_
              · refine le_trans hPsi ?_
                exact mul_le_mul_of_nonneg_left hDeltaJets (appCcGdiag_nonneg (E := E) i)
              · exact mul_nonneg (appCcGdiag_nonneg (E := E) i)
                  (mul_nonneg (hCDel_nn _)
                    (Combinatorics.boundedFactorGridWindow_nonneg b hb _ _))
          _ = (diagonalGridGrowthFactor (E := E) i * CDel (i - (k + 1)) * S (k + 1)) *
              (Combinatorics.boundedFactorGridWindow b (i + 1) ((i - (k + 1)) + 3) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (k + 2)) := by ring
          _ ≤ (diagonalGridGrowthFactor (E := E) i * CDel (i - (k + 1)) * S (k + 1)) *
              (Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2) * Wfin) := by
              refine mul_le_mul_of_nonneg_left hpair ?_
              exact mul_nonneg (mul_nonneg (appCcGdiag_nonneg (E := E) i)
                (hCDel_nn _)) (hS_nn _)
          _ = (diagonalGridGrowthFactor (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
              Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin := by
              ring
      calc ((i : ℕ) : ℝ) * ∑ k ∈ Finset.range i,
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
              ((ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (k + 1)) (1 + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1))
                (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF)).toSection x)
          ≤ ((i : ℕ) : ℝ) * ∑ k ∈ Finset.range i,
              (diagonalGridGrowthFactor (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
                Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Nat.cast_nonneg i)
        _ = ((i : ℝ) * ∑ k ∈ Finset.range i,
              diagonalGridGrowthFactor (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
                Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin := by
            rw [← Finset.sum_mul]
            ring
    have hP3 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        (P3t.toSection x) ≤
        (diagonalGridGrowthFactor (E := E) i * ∑ a' ∈ Finset.range (i + 1),
          cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l))) * Wfin := by
      rw [hP3t_def]
      refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
        (I := I) (M := M) g₀ i 1 1 1 B0f Dg x) ?_
      have hDjet : ∀ l : ℕ, l ≤ i →
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l Dg).toSection x) ≤
          (2 * S 0 + 2 * cId + S l) * Wfin := by
        intro l hl
        match l with
        | 0 =>
          rw [iteratedCovGrad_zero]
          have hDx : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (Dg.toSection x) ≤
              2 * S 0 + 2 * cId := by
            rw [hDg_eq]
            rw [show ((sF - InsId).toSection x) = sF.toSection x - InsId.toSection x from by
              rw [SmoothCcTensor.toSection_sub]; rfl]
            refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 1 1 x _ _) ?_
            have hsF0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
                (sF.toSection x) ≤ S 0 := by
              have h := hS g₁ T htie hδ_le hδ0 hbound 0 x
              rw [iteratedCovGrad_zero] at h
              rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
              exact h
            have hIdx := hcId x
            rw [hInsId_def] at *
            linarith
          calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (Dg.toSection x)
              ≤ 2 * S 0 + 2 * cId := hDx
            _ = (2 * S 0 + 2 * cId) * 1 := by ring
            _ ≤ (2 * S 0 + 2 * cId + S 0) * Wfin := by
                refine mul_le_mul ?_ hWfin_one (by norm_num) ?_
                · have := hS_nn 0; linarith
                · have := hS_nn 0; have := hcId_nn; linarith
        | (l' + 1) =>
          have hNdD : iteratedCovGrad (I := I) g₀ 1 1 (l' + 1) Dg =
              iteratedCovGrad (I := I) g₀ 1 1 (l' + 1) sF := by
            rw [hDg_eq, iteratedCovGrad_sub (I := I) g₀ 1 1 (l' + 1) sF InsId]
            rw [hInsId_def,
              iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero (I := I) (M := M) g₀ l']
            rw [sub_zero]
          rw [hNdD]
          refine le_trans (hS g₁ T htie hδ_le hδ0 hbound (l' + 1) x) ?_
          have hgrid : Combinatorics.antidiagonalTupleGrid b (l' + 1) ≤ Wfin := by
            rw [Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
              (show l' + 1 ≤ i + 1 from by omega)]
            rw [hWfin_def]
            exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)
          calc S (l' + 1) * Combinatorics.antidiagonalTupleGrid b (l' + 1)
              ≤ S (l' + 1) * Wfin := mul_le_mul_of_nonneg_left hgrid (hS_nn (l' + 1))
            _ ≤ (2 * S 0 + 2 * cId + S (l' + 1)) * Wfin := by
                refine mul_le_mul_of_nonneg_right ?_ hWfin_nn
                have := hS_nn 0
                linarith [hcId_nn]
      have hterm : ∀ a' ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + a') x
              ((iteratedCovGrad (I := I) g₀ 1 1 a' B0f).toSection x) *
            (∑ l ∈ Finset.range (i + 1 - a'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l Dg).toSection x)) ≤
          (cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l))) * Wfin := by
        intro a' ha'
        rw [Finset.mem_range] at ha'
        have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + a') x
            ((iteratedCovGrad (I := I) g₀ 1 1 a' B0f).toSection x) ≤ cB a' := by
          have h := hcB a' x
          rw [hB0f_def]
          exact h
        have hDsum : (∑ l ∈ Finset.range (i + 1 - a'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 1 l Dg).toSection x)) ≤
            (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l)) * Wfin := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum (fun l hl => ?_)
          rw [Finset.mem_range] at hl
          exact hDjet l (by omega)
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + a') x
              ((iteratedCovGrad (I := I) g₀ 1 1 a' B0f).toSection x) *
            (∑ l ∈ Finset.range (i + 1 - a'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l Dg).toSection x))
            ≤ cB a' * ((∑ l ∈ Finset.range (i + 1 - a'),
                (2 * S 0 + 2 * cId + S l)) * Wfin) := by
              refine mul_le_mul hB hDsum ?_ (hcB_nn a')
              exact Finset.sum_nonneg (fun l _ =>
                riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x _)
          _ = (cB a' * (∑ l ∈ Finset.range (i + 1 - a'),
                (2 * S 0 + 2 * cId + S l))) * Wfin := by ring
      calc diagonalGridGrowthFactor (E := E) i *
            ∑ a' ∈ Finset.range (i + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + a') x
                  ((iteratedCovGrad (I := I) g₀ 1 1 a' B0f).toSection x) *
                ∑ l ∈ Finset.range (i + 1 - a'),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                    ((iteratedCovGrad (I := I) g₀ 1 1 l Dg).toSection x)
          ≤ diagonalGridGrowthFactor (E := E) i *
            ∑ a' ∈ Finset.range (i + 1),
              (cB a' * (∑ l ∈ Finset.range (i + 1 - a'),
                (2 * S 0 + 2 * cId + S l))) * Wfin :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
              (appCcGdiag_nonneg (E := E) i)
        _ = (diagonalGridGrowthFactor (E := E) i * ∑ a' ∈ Finset.range (i + 1),
              cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l))) *
            Wfin := by
            rw [← Finset.sum_mul]
            ring
    have hP23 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        (P2t.toSection x + P3t.toSection x) ≤
        2 * (((i : ℝ) * ∑ k ∈ Finset.range i,
            diagonalGridGrowthFactor (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
              Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin) +
        2 * ((diagonalGridGrowthFactor (E := E) i * ∑ a' ∈ Finset.range (i + 1),
            cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l))) * Wfin) := by
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + i) x _ _) ?_
      exact add_le_add (mul_le_mul_of_nonneg_left hP2 (by norm_num))
        (mul_le_mul_of_nonneg_left hP3 (by norm_num))
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x (P1t.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          (P2t.toSection x + P3t.toSection x)
        ≤ 2 * (2 * (cPhi * (KcA i)) * S 0 * Wfin) +
          2 * (2 * (((i : ℝ) * ∑ k ∈ Finset.range i,
              diagonalGridGrowthFactor (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
                Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin) +
            2 * ((diagonalGridGrowthFactor (E := E) i * ∑ a' ∈ Finset.range (i + 1),
              cB a' * (∑ l ∈ Finset.range (i + 1 - a'),
                (2 * S 0 + 2 * cId + S l))) * Wfin)) :=
          add_le_add (mul_le_mul_of_nonneg_left hP1 (by norm_num))
            (mul_le_mul_of_nonneg_left hP23 (by norm_num))
      _ = (4 * (cPhi * (KcA i) * S 0) +
          4 * ((i : ℝ) * ∑ k ∈ Finset.range i,
            diagonalGridGrowthFactor (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
              Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) +
          4 * (diagonalGridGrowthFactor (E := E) i * ∑ a' ∈ Finset.range (i + 1),
            cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l)))) *
          Wfin := by ring

end TopSeparatedRungSlotInsert

section TopSeparatedRungLoweringSplit

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

theorem rfns_iteratedCovGrad_riemannG1LoweringDifference_topSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ),
        ∃ Hd : SmoothCcTensor g₀ 0 (4 + i),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (Hd.toSection x) ≤
              Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
                ((iteratedCovGrad (I := I) g₀ 0 4 i
                    (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                      riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) -
                  Hd).toSection x) ≤
              Kc i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3)) := by
  classical
  obtain ⟨KtA, hKtA_nn, KcA, hKcA_nn, hA⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannLoweredBackgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cfix, hcfix_nn, hcfix⟩ := exists_iteratedCovGrad_fiberNormSq_bound (I := I) (M := M) g₀ 0 4
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  refine ⟨n ^ 5 * KtA, mul_nonneg (pow_nonneg hn_nn 5) hKtA_nn, ?_⟩
  refine ⟨fun i => 2 * (n ^ 5 * (2 * KcA i + 2 * cfix i)) +
      2 * ((i : ℝ) * diagonalGridGrowthFactor (E := E) i *
        ∑ k ∈ Finset.range i, 2 * n ^ 3 * (CA k + cfix k)),
    fun i => by
      have h1 : (0 : ℝ) ≤ n ^ 5 * (2 * KcA i + 2 * cfix i) :=
        mul_nonneg (pow_nonneg hn_nn 5) (by have := hKcA_nn i; have := hcfix_nn i; linarith)
      have h2 : (0 : ℝ) ≤ (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
          ∑ k ∈ Finset.range i, 2 * n ^ 3 * (CA k + cfix k) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg i) (appCcGdiag_nonneg (E := E) i))
          (Finset.sum_nonneg fun k _ => mul_nonneg
            (mul_nonneg (by norm_num) (pow_nonneg hn_nn 3))
            (by have := hCA_nn k; have := hcfix_nn k; linarith))
      linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i
  obtain ⟨HdA, hHdA_head, hHdA_res⟩ := hA g₁ T htie hδ_le hδ0 hbound i
  set Dress : SmoothCcTensor g₀ 4 4 :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
      (perturbationSharpEndoField (I := I) (M := M) g₀ T) with hDress_def
  set RLCmix : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁
    with hRLCmix_def
  set RLCfix : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀
    with hRLCfix_def
  set RLD : SmoothCcTensor g₀ 0 4 :=
    riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ with hRLD_def
  have hmix_split : RLCmix = RLD + RLCfix := by
    rw [hRLD_def, riemannLoweredBackgroundDifference, ← hRLCmix_def, ← hRLCfix_def]
    abel
  set WS : SmoothCcTensor g₀ 0 4 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1) RLCmix with hWS_def
  set Ybig : SmoothCcTensor g₀ 0 4 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 4 Dress WS with hYbig_def
  have hrepr : riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
      riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1) Ybig := by
    rw [hYbig_def, hWS_def, hRLCmix_def, hDress_def]
    exact riemannG1LoweringDifference_slotInsert_repr (I := I) (M := M) g₀ g₁ T htie
  obtain ⟨σo, hσo⟩ := tsExists_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 4) 1) Ybig i
  obtain ⟨σw, hσw⟩ := tsExists_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 4) 1) RLCmix i
  set Hd0 : SmoothCcTensor g₀ 0 (4 + i) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
      (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
      (domDomCongrSection (I := I) g₀ σw HdA) with hHd0_def
  have hDress0 : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 4 y (Dress.toSection y) ≤ n ^ 5 := by
    intro y
    have h1 := rfns_iteratedCovGrad_slotInsert3_perturbationSharp_le (I := I) (M := M)
      g₀ T 0 y
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h1
    have h2 := rfns_symmS_zero_le_of_ball (I := I) (M := M) g₀ T hδ0 hbound y
    have hδ1 : δ ^ 2 ≤ 1 := by nlinarith [hδ0, lt_of_le_of_lt hδ_le hδ₀]
    have h3 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
        ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection y) ≤ n ^ 2 := by
      refine le_trans h2 ?_
      calc n ^ 2 * δ ^ 2 ≤ n ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hδ1 (pow_nonneg hn_nn 2)
        _ = n ^ 2 := by ring
    rw [hDress_def]
    refine le_trans h1 ?_
    calc n ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
          ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection y)
        ≤ n ^ 3 * n ^ 2 := mul_le_mul_of_nonneg_left h3 (pow_nonneg hn_nn 3)
      _ = n ^ 5 := by ring
  refine ⟨domDomCongrSection (I := I) g₀ σo Hd0, ?_, ?_⟩
  · intro x
    rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σo Hd0 x]
    rw [hHd0_def]
    refine le_trans (rfns_appCcRS_appCcLeibnizPsi_diag_le (I := I) (M := M) g₀ 0 4 4
      Dress i (domDomCongrSection (I := I) g₀ σw HdA) x) ?_
    rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σw HdA x]
    have hb_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 4 x (Dress.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (HdA.toSection x)
        ≤ n ^ 5 * (KtA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by
          refine mul_le_mul (hDress0 x) (hHdA_head x) ?_ (pow_nonneg hn_nn 5)
          exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x _
      _ = n ^ 5 * KtA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  · intro x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
    have hb : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hWfin_def
    have hWfin_nn : 0 ≤ Wfin :=
      Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i + 3)
    have hWfin_one : 1 ≤ Wfin :=
      Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
    have hdiff : iteratedCovGrad (I := I) g₀ 0 4 i
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
            riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) -
          domDomCongrSection (I := I) g₀ σo Hd0 =
        domDomCongrSection (I := I) g₀ σo
          (iteratedCovGrad (I := I) g₀ 0 4 i Ybig - Hd0) := by
      rw [hrepr, hσo]
      rw [tsDomDomCongrSection_sub (I := I) (M := M) g₀ σo]
    rw [hdiff]
    rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σo _ x]
    have hWSsplit : iteratedCovGrad (I := I) g₀ 0 4 i WS -
        domDomCongrSection (I := I) g₀ σw HdA =
        domDomCongrSection (I := I) g₀ σw
          ((iteratedCovGrad (I := I) g₀ 0 4 i RLD - HdA) +
            iteratedCovGrad (I := I) g₀ 0 4 i RLCfix) := by
      rw [hWS_def, hσw]
      rw [← tsDomDomCongrSection_sub (I := I) (M := M) g₀ σw]
      rw [show iteratedCovGrad (I := I) g₀ 0 4 i RLCmix =
          iteratedCovGrad (I := I) g₀ 0 4 i RLD +
            iteratedCovGrad (I := I) g₀ 0 4 i RLCfix from by
        rw [← iteratedCovGrad_add (I := I) g₀ 0 4 i RLD RLCfix, ← hmix_split]]
      rw [add_sub_right_comm]
    have hfirst : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
          (iteratedCovGrad (I := I) g₀ 0 4 i WS -
            domDomCongrSection (I := I) g₀ σw HdA)).toSection x) ≤
        n ^ 5 * ((2 * KcA i + 2 * cfix i) * Wfin) := by
      refine le_trans (rfns_appCcRS_appCcLeibnizPsi_diag_le (I := I) (M := M) g₀ 0 4 4
        Dress i _ x) ?_
      have hinner : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i WS -
            domDomCongrSection (I := I) g₀ σw HdA).toSection x) ≤
          (2 * KcA i + 2 * cfix i) * Wfin := by
        rw [hWSsplit]
        rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σw _ x]
        rw [show (((iteratedCovGrad (I := I) g₀ 0 4 i RLD - HdA) +
              iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) =
            (iteratedCovGrad (I := I) g₀ 0 4 i RLD - HdA).toSection x +
              (iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x from by
          rw [SmoothCcTensor.toSection_add]; rfl]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + i)
          x _ _) ?_
        have h1 := hHdA_res x
        have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) ≤
            cfix i * Wfin := by
          have h2a : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) ≤ cfix i := by
            rw [hRLCfix_def]
            exact hcfix i x
          calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
                ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x)
              ≤ cfix i := h2a
            _ = cfix i * 1 := by ring
            _ ≤ cfix i * Wfin := mul_le_mul_of_nonneg_left hWfin_one (hcfix_nn i)
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i RLD - HdA).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x)
            ≤ 2 * (KcA i * Wfin) + 2 * (cfix i * Wfin) := by
              refine add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
                (mul_le_mul_of_nonneg_left h2 (by norm_num))
          _ = (2 * KcA i + 2 * cfix i) * Wfin := by ring
      refine mul_le_mul (hDress0 x) hinner
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x _)
        (pow_nonneg hn_nn 5)
    have hcorr : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + k) (4 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i k)
            (iteratedCovGrad (I := I) g₀ 0 4 k WS)).toSection x) ≤
        (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
          ∑ k ∈ Finset.range i, (2 * n ^ 3 * (CA k + cfix k)) * Wfin := by
      refine le_trans (rfns_appCcRS_argLower_le (I := I) (M := M) g₀ 0 4 4 Dress WS i x) ?_
      rw [mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg i)
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
      refine Finset.sum_le_sum (fun k hk => ?_)
      rw [Finset.mem_range] at hk
      have hDjet : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + (i - k)) x
          ((iteratedCovGrad (I := I) g₀ 4 4 (i - k) Dress).toSection x) ≤
          n ^ 3 * b (i - k) := by
        rw [hDress_def]
        refine le_trans (rfns_iteratedCovGrad_slotInsert3_perturbationSharp_le
          (I := I) (M := M) g₀ T (i - k) x) ?_
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hn_nn 3)
        exact rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ T (i - k) x
      have hWjet : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
          ((iteratedCovGrad (I := I) g₀ 0 4 k WS).toSection x) ≤
          2 * (CA k * (∑ k' ∈ Finset.range (k + 3),
            Combinatorics.antidiagonalTupleGrid b k')) + 2 * cfix k := by
        rw [hWS_def]
        rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M)
          g₀ (Equiv.swap (0 : Fin 4) 1) RLCmix k x]
        rw [show iteratedCovGrad (I := I) g₀ 0 4 k RLCmix =
            iteratedCovGrad (I := I) g₀ 0 4 k RLD +
              iteratedCovGrad (I := I) g₀ 0 4 k RLCfix from by
          rw [← iteratedCovGrad_add (I := I) g₀ 0 4 k RLD RLCfix, ← hmix_split]]
        rw [show ((iteratedCovGrad (I := I) g₀ 0 4 k RLD +
              iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x) =
            (iteratedCovGrad (I := I) g₀ 0 4 k RLD).toSection x +
              (iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x from by
          rw [SmoothCcTensor.toSection_add]; rfl]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + k)
          x _ _) ?_
        have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
            ((iteratedCovGrad (I := I) g₀ 0 4 k RLD).toSection x) ≤
            CA k * (∑ k' ∈ Finset.range (k + 3),
              Combinatorics.antidiagonalTupleGrid b k') := by
          have h := hCA g₁ T htie hδ_le hδ0 hbound k x
          rw [hRLD_def]
          exact h
        have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
            ((iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x) ≤ cfix k := by
          rw [hRLCfix_def]; exact hcfix k x
        exact add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
          (mul_le_mul_of_nonneg_left h2 (by norm_num))
      have hbW : b (i - k) * (∑ k' ∈ Finset.range (k + 3),
          Combinatorics.antidiagonalTupleGrid b k') ≤ Wfin := by
        refine le_trans (mul_le_mul_of_nonneg_left
          (tsTgridSum_le_boundedWindow b hb (show k + 3 ≤ (i + 1) + 1 from by omega)
            (le_refl (k + 3))) (hb (i - k))) ?_
        refine le_trans (Combinatorics.single_factor_mul_boundedFactorGridWindow_le b hb
          (show 1 ≤ i - k from by omega) (show i - k ≤ i + 1 from by omega)) ?_
        rw [hWfin_def]
        refine Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) ?_
        omega
      have hbAlone : b (i - k) ≤ Wfin := by
        have h1 := Combinatorics.single_factor_mul_boundedFactorGrid_le b hb 0 (i - k)
          (show 1 ≤ i - k from by omega) (show i - k ≤ i + 1 from by omega)
        rw [Combinatorics.boundedFactorGrid_zero, mul_one] at h1
        refine le_trans h1 ?_
        rw [show 0 + (i - k) = i - k from by omega, hWfin_def]
        exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + (i - k)) x
            ((iteratedCovGrad (I := I) g₀ 4 4 (i - k) Dress).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
            ((iteratedCovGrad (I := I) g₀ 0 4 k WS).toSection x)
          ≤ (n ^ 3 * b (i - k)) *
            (2 * (CA k * (∑ k' ∈ Finset.range (k + 3),
              Combinatorics.antidiagonalTupleGrid b k')) + 2 * cfix k) := by
            refine mul_le_mul hDjet hWjet ?_ ?_
            · exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + k) x _
            · exact mul_nonneg (pow_nonneg hn_nn 3) (hb (i - k))
        _ = 2 * n ^ 3 * CA k *
              (b (i - k) * (∑ k' ∈ Finset.range (k + 3),
                Combinatorics.antidiagonalTupleGrid b k')) +
            2 * n ^ 3 * cfix k * b (i - k) := by ring
        _ ≤ 2 * n ^ 3 * CA k * Wfin + 2 * n ^ 3 * cfix k * Wfin := by
            refine add_le_add ?_ ?_
            · refine mul_le_mul_of_nonneg_left hbW ?_
              exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hn_nn 3)) (hCA_nn k)
            · refine mul_le_mul_of_nonneg_left hbAlone ?_
              exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hn_nn 3))
                (hcfix_nn k)
        _ = (2 * n ^ 3 * (CA k + cfix k)) * Wfin := by ring
    have hsplitY : iteratedCovGrad (I := I) g₀ 0 4 i Ybig - Hd0 =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
            (iteratedCovGrad (I := I) g₀ 0 4 i WS -
              domDomCongrSection (I := I) g₀ σw HdA) +
          ∑ k ∈ Finset.range i,
            ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + k) (4 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i k)
              (iteratedCovGrad (I := I) g₀ 0 4 k WS) := by
      rw [hYbig_def]
      rw [iteratedCovGrad_appCcRS_eq_argCorner_add_lower (I := I) (M := M) g₀ 0 4 4
        Dress WS i]
      rw [hHd0_def]
      rw [appCcRS_sub_right_cc (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
        (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
        (iteratedCovGrad (I := I) g₀ 0 4 i WS)
        (domDomCongrSection (I := I) g₀ σw HdA)]
      exact add_sub_right_comm _ _ _
    rw [hsplitY]
    rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
          (iteratedCovGrad (I := I) g₀ 0 4 i WS -
            domDomCongrSection (I := I) g₀ σw HdA) +
        ∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + k) (4 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i k)
            (iteratedCovGrad (I := I) g₀ 0 4 k WS)).toSection x) =
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
          (iteratedCovGrad (I := I) g₀ 0 4 i WS -
            domDomCongrSection (I := I) g₀ σw HdA)).toSection x +
        (∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + k) (4 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i k)
            (iteratedCovGrad (I := I) g₀ 0 4 k WS)).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + i) x _ _) ?_
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
            (iteratedCovGrad (I := I) g₀ 0 4 i WS -
              domDomCongrSection (I := I) g₀ σw HdA)).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((∑ k ∈ Finset.range i,
            ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + k) (4 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i k)
              (iteratedCovGrad (I := I) g₀ 0 4 k WS)).toSection x)
        ≤ 2 * (n ^ 5 * ((2 * KcA i + 2 * cfix i) * Wfin)) +
          2 * ((i : ℝ) * diagonalGridGrowthFactor (E := E) i *
            ∑ k ∈ Finset.range i, (2 * n ^ 3 * (CA k + cfix k)) * Wfin) :=
        add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num))
          (mul_le_mul_of_nonneg_left hcorr (by norm_num))
      _ = (2 * (n ^ 5 * (2 * KcA i + 2 * cfix i)) +
          2 * ((i : ℝ) * diagonalGridGrowthFactor (E := E) i *
            ∑ k ∈ Finset.range i, 2 * n ^ 3 * (CA k + cfix k))) * Wfin := by
          rw [← Finset.sum_mul]
          ring

end TopSeparatedRungLoweringSplit

section TopSeparatedRungCurvCoeff

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma tsSlotInsertEndoCc_succ_eq_reindex_slotExtend
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1) Λ =
      reindexCoeffGen (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
        (rsDomDomCongrSection (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
          (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
          (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)))
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1) Λ).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (reindexCoeffGen (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
          (rsDomDomCongrSection (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
            (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)))
          (Equiv.swap (0 : Fin (s + 1 + 1)) 1)).toSection x) D) m
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval]
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply, rsDomDomCongrSection_toSection,
    toModel_rsDomDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply, slotExtend_toSection]
  rw [show (fun k : Fin (s + 1 + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) k)) =
      Fin.cons (m 1) (fun j : Fin (s + 1) =>
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ j))) from by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [Fin.cons_zero, Equiv.swap_apply_left]
    · simp only [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval]
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval,
    TensorMultilinear.tensor0S_curry_apply_eval,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  have hswap_succ0 : (Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (0 : Fin (s + 1))) = 0 := by
    rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl, Equiv.swap_apply_right]
  rw [hswap_succ0]
  congr 1
  funext k
  refine Fin.cases ?_ (fun k₁ => ?_) k
  · rw [Equiv.swap_apply_left,
      show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl, Fin.cons_succ,
      Function.update_self, Function.update_self]
  · refine Fin.cases ?_ (fun k₂ => ?_) k₁
    · have h10 : (1 : Fin (s + 1 + 1)) ≠ 0 := by
        rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
        exact Fin.succ_ne_zero _
      rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl,
        Function.update_of_ne h10, Equiv.swap_apply_right, Fin.cons_zero]
    · have hne0 : (Fin.succ (Fin.succ k₂) : Fin (s + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
      have hne1 : (Fin.succ (Fin.succ k₂) : Fin (s + 1 + 1)) ≠ 1 := by
        rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
        exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
      rw [Function.update_of_ne hne0, Equiv.swap_apply_of_ne_of_ne hne0 hne1, Fin.cons_succ,
        Function.update_of_ne (Fin.succ_ne_zero k₂)]
      change m (Fin.succ (Fin.succ k₂)) =
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (Fin.succ k₂)))
      rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma tsReindexCoeffGen_sub (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R₁ R₂ : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) :
    reindexCoeffGen (I := I) (M := M) g₀ r s (R₁ - R₂) σ' =
      reindexCoeffGen (I := I) (M := M) g₀ r s R₁ σ' -
        reindexCoeffGen (I := I) (M := M) g₀ r s R₂ σ' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((reindexCoeffGen (I := I) (M := M) g₀ r s R₁ σ' -
        reindexCoeffGen (I := I) (M := M) g₀ r s R₂ σ').toSection x) =
      (reindexCoeffGen (I := I) (M := M) g₀ r s R₁ σ').toSection x -
        (reindexCoeffGen (I := I) (M := M) g₀ r s R₂ σ').toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [reindexCoeffGen_toSection, reindexCoeffGen_toSection, reindexCoeffGen_toSection]
  rw [show ((R₁ - R₂).toSection x) = R₁.toSection x - R₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [reindexCoeffFibGen, reindexCoeffFibGen, reindexCoeffFibGen]
  exact ContinuousLinearMap.sub_comp _ _ _

omit [NeZero (Module.finrank ℝ E)] in
private lemma tsRfns_reindexCoeffGen_zero (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x
        ((reindexCoeffGen (I := I) (M := M) g₀ r s R σ').toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r s x (R.toSection x) := by
  have h := riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ r s R σ' 0 x
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
  exact h

private lemma tsExists_slotExtend_headTransport (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (V : SmoothCcTensor g₀ r s) (i : ℕ) (HV : SmoothCcTensor g₀ r (s + i)) :
    ∃ HW : SmoothCcTensor g₀ (r + 1) ((s + 1) + i),
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) x
            (HW.toSection x) ≤
          (Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x (HV.toSection x)) ∧
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
                (slotExtend (I := I) (M := M) g₀ r s V) - HW).toSection x) ≤
          (Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
              ((iteratedCovGrad (I := I) g₀ r s i V - HV).toSection x)) := by
  obtain ⟨σa, hσa⟩ := exists_iteratedCovGrad_slotExtend_rsDomDomCongr (I := I) (M := M)
    g₀ r s V i
  refine ⟨rsDomDomCongrSection (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) σa
    (castCcTensorRank g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
      (slotExtend (I := I) (M := M) g₀ r (s + i) HV)), ?_, ?_⟩
  · intro x
    rw [tsRfns_rsDomDomCongrSection_zero (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) σa _ x]
    rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ (r + 1)
      (by omega : (s + i) + 1 = (s + 1) + i) _ x]
    rw [rfns_slotExtend_eq (I := I) (M := M) g₀ r (s + i) HV x]
  · intro x
    have hpt : ((iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
          (slotExtend (I := I) (M := M) g₀ r s V) -
        rsDomDomCongrSection (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) σa
          (castCcTensorRank g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g₀ r (s + i) HV))).toSection x) =
        tensorRS_domDomCongr (I := I) (M := M) σa
          ((castCcTensorRank g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g₀ r (s + i)
              (iteratedCovGrad (I := I) g₀ r s i V - HV))).toSection x) := by
      rw [show ((iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
            (slotExtend (I := I) (M := M) g₀ r s V) -
          rsDomDomCongrSection (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) σa
            (castCcTensorRank g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
              (slotExtend (I := I) (M := M) g₀ r (s + i) HV))).toSection x) =
          (iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
            (slotExtend (I := I) (M := M) g₀ r s V)).toSection x -
          (rsDomDomCongrSection (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) σa
            (castCcTensorRank g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
              (slotExtend (I := I) (M := M) g₀ r (s + i) HV))).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [hσa x, rsDomDomCongrSection_toSection]
      rw [← tsRsDomDomCongr_sub (I := I) (M := M) σa]
      rw [show ((castCcTensorRank g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g₀ r (s + i)
              (iteratedCovGrad (I := I) g₀ r s i V))).toSection x -
          (castCcTensorRank g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g₀ r (s + i) HV)).toSection x) =
          ((castCcTensorRank g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g₀ r (s + i)
                (iteratedCovGrad (I := I) g₀ r s i V) -
              slotExtend (I := I) (M := M) g₀ r (s + i) HV)).toSection x) from by
        rw [tsCastRankCc_db_sub, SmoothCcTensor.toSection_sub]; rfl]
      rw [← tsSlotExtend_sub (I := I) (M := M) g₀ r (s + i)]
    rw [hpt]
    rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ (r + 1)
      ((s + 1) + i) x σa _]
    rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ (r + 1)
      (by omega : (s + i) + 1 = (s + 1) + i) _ x]
    rw [rfns_slotExtend_eq (I := I) (M := M) g₀ r (s + i) _ x]

private lemma tsExists_rsDDC_headTransport (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (V : SmoothCcTensor g₀ r s) (i : ℕ)
    (HV : SmoothCcTensor g₀ r (s + i)) :
    ∃ HW : SmoothCcTensor g₀ r (s + i),
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x (HW.toSection x) ≤
          riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x (HV.toSection x)) ∧
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
            ((iteratedCovGrad (I := I) g₀ r s i
                (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ V) - HW).toSection x) ≤
          riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
            ((iteratedCovGrad (I := I) g₀ r s i V - HV).toSection x)) := by
  obtain ⟨σ', hσ'⟩ := tsExists_iteratedCovGrad_rsDomDomCongrSection (I := I) (M := M)
    g₀ r s σ V i
  refine ⟨rsDomDomCongrSection (I := I) (M := M) g₀ r (s + i) σ' HV, ?_, ?_⟩
  · intro x
    rw [tsRfns_rsDomDomCongrSection_zero (I := I) (M := M) g₀ r (s + i) σ' HV x]
  · intro x
    have hpt : ((iteratedCovGrad (I := I) g₀ r s i
          (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ V) -
        rsDomDomCongrSection (I := I) (M := M) g₀ r (s + i) σ' HV).toSection x) =
        tensorRS_domDomCongr (I := I) (M := M) σ'
          ((iteratedCovGrad (I := I) g₀ r s i V - HV).toSection x) := by
      rw [show ((iteratedCovGrad (I := I) g₀ r s i
            (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ V) -
          rsDomDomCongrSection (I := I) (M := M) g₀ r (s + i) σ' HV).toSection x) =
          (iteratedCovGrad (I := I) g₀ r s i
            (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ V)).toSection x -
          (rsDomDomCongrSection (I := I) (M := M) g₀ r (s + i) σ' HV).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [hσ' x, rsDomDomCongrSection_toSection]
      rw [← tsRsDomDomCongr_sub (I := I) (M := M) σ']
      rw [show ((iteratedCovGrad (I := I) g₀ r s i V).toSection x - HV.toSection x) =
          ((iteratedCovGrad (I := I) g₀ r s i V - HV).toSection x) from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [hpt]
    rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ r (s + i) x σ' _]

theorem rfns_iteratedCovGrad_ricciArmOrder0CurvCoeff_backgroundDifference_topSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ),
        ∃ Hd : SmoothCcTensor g₀ 2 (2 + i),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (Hd.toSection x) ≤
              Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
                ((iteratedCovGrad (I := I) g₀ 2 2 i
                    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) -
                  Hd).toSection x) ≤
              Kc i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3)) := by
  classical
  obtain ⟨KtB, hKtB_nn, KcB, hKcB_nn, hB⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  refine ⟨4 * (n * KtB), by positivity, ?_⟩
  refine ⟨fun i => 4 * (n * KcB i),
    fun i => by have := hKcB_nn i; positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i
  obtain ⟨HdB, hB_head, hB_res⟩ := hB g₁ T htie hδ_le hδ0 hbound i
  set Lam := ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ with hLam_def
  set X : SmoothCcTensor g₀ 1 1 := endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 Lam with hX_def
  set V : SmoothCcTensor g₀ 2 2 := endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 Lam with hV_def
  have hVrepr : V =
      reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotExtend (I := I) (M := M) g₀ 1 1 X))
        (Equiv.swap (0 : Fin 2) 1) := by
    rw [hV_def, hX_def]
    exact tsSlotInsertEndoCc_succ_eq_reindex_slotExtend (I := I) (M := M) g₀ 0 Lam
  obtain ⟨HdX1, hX1_head, hX1_res⟩ := tsExists_slotExtend_headTransport (I := I) (M := M)
    g₀ 1 1 X i HdB
  obtain ⟨HdX2, hX2_head, hX2_res⟩ := tsExists_rsDDC_headTransport (I := I) (M := M)
    g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) (slotExtend (I := I) (M := M) g₀ 1 1 X) i HdX1
  set HdV : SmoothCcTensor g₀ 2 (2 + i) :=
    reindexCoeffGen (I := I) (M := M) g₀ 2 (2 + i) HdX2 (Equiv.swap (0 : Fin 2) 1)
    with hHdV_def
  have hHdV_head : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdV.toSection x) ≤
        n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x (HdB.toSection x) := by
    intro x
    rw [hHdV_def, tsRfns_reindexCoeffGen_zero (I := I) (M := M) g₀ 2 (2 + i) HdX2 _ x]
    exact le_trans (hX2_head x) (hX1_head x)
  have hHdV_res : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i V - HdV).toSection x) ≤
        n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i X - HdB).toSection x) := by
    intro x
    have hVd : iteratedCovGrad (I := I) g₀ 2 2 i V - HdV =
        reindexCoeffGen (I := I) (M := M) g₀ 2 (2 + i)
          (iteratedCovGrad (I := I) g₀ 2 2 i
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotExtend (I := I) (M := M) g₀ 1 1 X)) - HdX2)
          (Equiv.swap (0 : Fin 2) 1) := by
      rw [hVrepr, hHdV_def]
      rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M) g₀ 2 2 _ _ i]
      rw [tsReindexCoeffGen_sub (I := I) (M := M) g₀ 2 (2 + i)]
    rw [hVd]
    rw [tsRfns_reindexCoeffGen_zero (I := I) (M := M) g₀ 2 (2 + i) _ _ x]
    exact le_trans (hX2_res x) (hX1_res x)
  obtain ⟨HdV2i, h2i_head, h2i_res⟩ := tsExists_rsDDC_headTransport (I := I) (M := M)
    g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) V i HdV
  set HdV2 : SmoothCcTensor g₀ 2 (2 + i) :=
    reindexCoeffGen (I := I) (M := M) g₀ 2 (2 + i) HdV2i (Equiv.swap (0 : Fin 2) 1)
    with hHdV2_def
  set V2 : SmoothCcTensor g₀ 2 2 :=
    reindexCoeffGen (I := I) (M := M) g₀ 2 2
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) V)
      (Equiv.swap (0 : Fin 2) 1) with hV2_def
  have hHdV2_head : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdV2.toSection x) ≤
        n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x (HdB.toSection x) := by
    intro x
    rw [hHdV2_def, tsRfns_reindexCoeffGen_zero (I := I) (M := M) g₀ 2 (2 + i) HdV2i _ x]
    exact le_trans (h2i_head x) (hHdV_head x)
  have hHdV2_res : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2).toSection x) ≤
        n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i X - HdB).toSection x) := by
    intro x
    have hV2d : iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2 =
        reindexCoeffGen (I := I) (M := M) g₀ 2 (2 + i)
          (iteratedCovGrad (I := I) g₀ 2 2 i
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) V) -
            HdV2i)
          (Equiv.swap (0 : Fin 2) 1) := by
      rw [hV2_def, hHdV2_def]
      rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M) g₀ 2 2 _ _ i]
      rw [tsReindexCoeffGen_sub (I := I) (M := M) g₀ 2 (2 + i)]
    rw [hV2d]
    rw [tsRfns_reindexCoeffGen_zero (I := I) (M := M) g₀ 2 (2 + i) _ _ x]
    exact le_trans (h2i_res x) (hHdV_res x)
  refine ⟨HdV + HdV2, ?_, ?_⟩
  · intro x
    rw [show ((HdV + HdV2).toSection x) = HdV.toSection x + HdV2.toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
    have h1 := le_trans (hHdV_head x) (mul_le_mul_of_nonneg_left (hB_head x) hn_nn)
    have h2 := le_trans (hHdV2_head x) (mul_le_mul_of_nonneg_left (hB_head x) hn_nn)
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdV.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdV2.toSection x)
        ≤ 2 * (n * (KtB * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) +
          2 * (n * (KtB * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
            (mul_le_mul_of_nonneg_left h2 (by norm_num))
      _ = 4 * (n * KtB) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  · intro x
    have hdecomp := ricciArmOrder0CurvCoeff_backgroundDifference_decomp (I := I) (M := M)
      g₀ g₁
    have hsplit : iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) -
          (HdV + HdV2) =
        (iteratedCovGrad (I := I) g₀ 2 2 i V - HdV) +
          (iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2) := by
      rw [show (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) = V + V2 from by
        rw [hV_def, hV2_def, hLam_def]
        exact hdecomp]
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i V V2]
      abel
    rw [hsplit]
    rw [show (((iteratedCovGrad (I := I) g₀ 2 2 i V - HdV) +
          (iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2)).toSection x) =
        (iteratedCovGrad (I := I) g₀ 2 2 i V - HdV).toSection x +
          (iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
    have h1 := le_trans (hHdV_res x) (mul_le_mul_of_nonneg_left (hB_res x) hn_nn)
    have h2 := le_trans (hHdV2_res x) (mul_le_mul_of_nonneg_left (hB_res x) hn_nn)
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i V - HdV).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2).toSection x)
        ≤ 2 * (n * (KcB i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3))) +
          2 * (n * (KcB i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3))) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
            (mul_le_mul_of_nonneg_left h2 (by norm_num))
      _ = 4 * (n * KcB i) * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3) := by
          ring

end TopSeparatedRungCurvCoeff

section TopSeparatedRungRiemannCoeff

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

theorem rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_topSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ),
        ∃ Hd : SmoothCcTensor g₀ 2 (2 + i),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (Hd.toSection x) ≤
              Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
                ((iteratedCovGrad (I := I) g₀ 2 2 i
                    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
                  Hd).toSection x) ≤
              Kc i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3)) := by
  classical
  obtain ⟨KtA, hKtA_nn, KcA, hKcA_nn, hA⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannLoweredBackgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨KtA', hKtA'_nn, KcA', hKcA'_nn, hA'⟩ :=
    rfns_iteratedCovGrad_riemannG1LoweringDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨C1, hC1_nn, hC1⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannLoweredCcFirstArgDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CD, hCD_nn, hCD⟩ := exists_fiberNormSq_iteratedCovGrad_pairTraceOp_diff_grid
    (I := I) (M := M) g₀ hδ₀
  obtain ⟨cfix, hcfix_nn, hcfix⟩ := exists_iteratedCovGrad_fiberNormSq_bound (I := I) (M := M) g₀ 0 4
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)
  obtain ⟨cP, hcP_nn, hcP⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  refine ⟨8 * (n * n) * (CD 0 + cP) * (2 * KtA' + 2 * KtA),
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hn_nn hn_nn))
      (add_nonneg (hCD_nn 0) hcP_nn)) (by linarith [hKtA'_nn, hKtA_nn]), ?_⟩
  refine ⟨fun i => 4 * (2 * (2 * (CD 0 * (n * n) *
        (4 * KcA' i + 4 * KcA i + 2 * cfix i)) +
      2 * ((i : ℝ) * diagonalGridGrowthFactor (E := E) i *
        ∑ k ∈ Finset.range i, CD (i - k) * (n * n) *
          ((2 * C1 k + 4 * CA k) *
              Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k))) +
      2 * (2 * (cP * (n * n)) * (2 * KcA' i + 2 * KcA i))),
    fun i => by
      have hp1 : (0 : ℝ) ≤ CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i) :=
        mul_nonneg (mul_nonneg (hCD_nn 0) (mul_nonneg hn_nn hn_nn))
          (by have := hKcA'_nn i; have := hKcA_nn i; have := hcfix_nn i; linarith)
      have hp2 : (0 : ℝ) ≤ (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
          ∑ k ∈ Finset.range i, CD (i - k) * (n * n) *
            ((2 * C1 k + 4 * CA k) *
                Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg i) (appCcGdiag_nonneg (E := E) i))
          (Finset.sum_nonneg fun k _ => mul_nonneg
            (mul_nonneg (hCD_nn _) (mul_nonneg hn_nn hn_nn))
            (add_nonneg
              (mul_nonneg (by have := hC1_nn k; have := hCA_nn k; linarith)
                (Combinatorics.windowPairCellCount_nonneg _ _))
              (by have := hcfix_nn k; linarith)))
      have hp3 : (0 : ℝ) ≤ 2 * (cP * (n * n)) * (2 * KcA' i + 2 * KcA i) :=
        mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hcP_nn (mul_nonneg hn_nn hn_nn)))
          (by have := hKcA'_nn i; have := hKcA_nn i; linarith)
      linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i
  obtain ⟨HdA, hHdA_head, hHdA_res⟩ := hA g₁ T htie hδ_le hδ0 hbound i
  obtain ⟨HdA', hHdA'_head, hHdA'_res⟩ := hA' g₁ T htie hδ_le hδ0 hbound i
  set RLC11 : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁
    with hRLC11_def
  set RLC01 : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁
    with hRLC01_def
  set RLCfix : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀
    with hRLCfix_def
  set Vd : SmoothCcTensor g₀ 0 4 := RLC11 - RLCfix with hVd_def
  set phiDt : SmoothCcTensor g₀ 6 2 := pairTraceOp (I := I) (M := M) g₀ g₀ with hphiDt_def
  set Dpt : SmoothCcTensor g₀ 6 2 :=
    pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀ with hDpt_def
  have hphiDt_par : covGrad (I := I) (M := M) g₀ 6 2 phiDt = 0 := by
    rw [hphiDt_def, pairTraceOp_self_eq (I := I) (M := M) g₀]
    exact phiDtPair_covGrad_zero (I := I) (M := M) g₀
  have hIter2 : ∀ Z : SmoothCcTensor g₀ 0 4,
      slotExtendIter (I := I) (M := M) g₀ 0 4 2 Z =
        slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 Z) :=
    fun Z => rfl
  set WBig : SmoothCcTensor g₀ 2 6 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
      (slotExtend (I := I) (M := M) g₀ 1 5
        (slotExtend (I := I) (M := M) g₀ 0 4 RLC11)) with hWBig_def
  set WVd : SmoothCcTensor g₀ 2 6 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
      (slotExtend (I := I) (M := M) g₀ 1 5
        (slotExtend (I := I) (M := M) g₀ 0 4 Vd)) with hWVd_def
  have hWfix_sub : rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
        (slotExtend (I := I) (M := M) g₀ 1 5
          (slotExtend (I := I) (M := M) g₀ 0 4 RLCfix)) =
      WBig - WVd := by
    rw [hWBig_def, hWVd_def, hVd_def]
    rw [tsSlotExtend_sub (I := I) (M := M) g₀ 0 4 RLC11 RLCfix]
    rw [tsSlotExtend_sub (I := I) (M := M) g₀ 1 5]
    rw [rsDomDomCongrSection_sub_cc (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm]
    abel
  have hRiemD : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig +
        (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 phiDt WVd := by
    have hL1 := riemannCoeff_eq_pairTrace (I := I) (M := M) g₀ g₁
    have hL0 := riemannCoeff_eq_pairTrace (I := I) (M := M) g₀ g₀
    rw [hIter2 (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)] at hL1
    rw [hIter2 (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)] at hL0
    rw [hL1, hL0]
    rw [show (pairTraceOp (I := I) (M := M) g₀ g₁) = Dpt + phiDt from by
      rw [hDpt_def, hphiDt_def]; abel]
    rw [appCcRS_add_left_local (I := I) (M := M) g₀ 2 6 2 Dpt phiDt]
    rw [← hWBig_def, ← hRLCfix_def, hWfix_sub]
    rw [appCcRS_sub_right_cc (I := I) (M := M) g₀ 2 6 2 phiDt WBig WVd]
    rw [smul_add, smul_sub]
    abel
  obtain ⟨HW1c, h1c_head, h1c_res⟩ := tsExists_slotExtend_headTransport (I := I) (M := M)
    g₀ 0 4 RLC11 i (HdA' + HdA)
  obtain ⟨HW2c, h2c_head, h2c_res⟩ := tsExists_slotExtend_headTransport (I := I) (M := M)
    g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 RLC11) i HW1c
  obtain ⟨HW11, h11_head, h11_res⟩ := tsExists_rsDDC_headTransport (I := I) (M := M)
    g₀ 2 6 pairTraceKernelSlotPerm
    (slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 RLC11))
    i HW2c
  obtain ⟨HW1d, h1d_head, h1d_res⟩ := tsExists_slotExtend_headTransport (I := I) (M := M)
    g₀ 0 4 Vd i (HdA' + HdA)
  obtain ⟨HW2d, h2d_head, h2d_res⟩ := tsExists_slotExtend_headTransport (I := I) (M := M)
    g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 Vd) i HW1d
  obtain ⟨HWd, hWd_head, hWd_res⟩ := tsExists_rsDDC_headTransport (I := I) (M := M)
    g₀ 2 6 pairTraceKernelSlotPerm
    (slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 Vd))
    i HW2d
  set HdT1 : SmoothCcTensor g₀ 2 (2 + i) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
      (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i) HW11 with hHdT1_def
  set HdT2 : SmoothCcTensor g₀ 2 (2 + i) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
      (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 phiDt i i) HWd with hHdT2_def
  have hHVc_head : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x ((HdA' + HdA).toSection x) ≤
        (2 * KtA' + 2 * KtA) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by
    intro x
    rw [show ((HdA' + HdA).toSection x) = HdA'.toSection x + HdA.toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + i) x _ _) ?_
    have h1 := hHdA'_head x
    have h2 := hHdA_head x
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (HdA'.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (HdA.toSection x)
        ≤ 2 * (KtA' * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) +
          2 * (KtA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
            (mul_le_mul_of_nonneg_left h2 (by norm_num))
      _ = (2 * KtA' + 2 * KtA) * riemannianFiberNormSq (I := I) (M := M) g₀ 0
            (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  refine ⟨(2 : ℝ) • (HdT1 + HdT2), ?_, ?_⟩
  · intro x
    rw [show (((2 : ℝ) • (HdT1 + HdT2)).toSection x) =
        (2 : ℝ) • ((HdT1 + HdT2).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [rfns_smul_pt (I := I) (M := M) g₀ 2 (2 + i) x 2 _]
    rw [show ((HdT1 + HdT2).toSection x) = HdT1.toSection x + HdT2.toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    have hb_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)
    have hHVchain : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
        (HW11.toSection x) ≤
        (n * n) * ((2 * KtA' + 2 * KtA) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by
      refine le_trans (h11_head x) ?_
      refine le_trans (h2c_head x) ?_
      calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x (HW1c.toSection x)
          ≤ n * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((HdA' + HdA).toSection x)) :=
            mul_le_mul_of_nonneg_left (h1c_head x) hn_nn
        _ ≤ n * (n * ((2 * KtA' + 2 * KtA) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
            refine mul_le_mul_of_nonneg_left ?_ hn_nn
            exact mul_le_mul_of_nonneg_left (hHVc_head x) hn_nn
        _ = (n * n) * ((2 * KtA' + 2 * KtA) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by ring
    have hHWdchain : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
        (HWd.toSection x) ≤
        (n * n) * ((2 * KtA' + 2 * KtA) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by
      refine le_trans (hWd_head x) ?_
      refine le_trans (h2d_head x) ?_
      calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x (HW1d.toSection x)
          ≤ n * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((HdA' + HdA).toSection x)) :=
            mul_le_mul_of_nonneg_left (h1d_head x) hn_nn
        _ ≤ n * (n * ((2 * KtA' + 2 * KtA) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
            refine mul_le_mul_of_nonneg_left ?_ hn_nn
            exact mul_le_mul_of_nonneg_left (hHVc_head x) hn_nn
        _ = (n * n) * ((2 * KtA' + 2 * KtA) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by ring
    have hDpt0 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x (Dpt.toSection x) ≤
        CD 0 := by
      have h := hCD g₁ T htie hδ_le hδ0 hbound 0 x
      rw [iteratedCovGrad_zero] at h
      rw [Finset.sum_range_one, Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
      rw [hDpt_def]
      exact h
    have hT1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        (HdT1.toSection x) ≤
        CD 0 * ((n * n) * ((2 * KtA' + 2 * KtA) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
      rw [hHdT1_def]
      refine le_trans (rfns_appCcRS_appCcLeibnizPsi_diag_le (I := I) (M := M) g₀ 2 6 2
        Dpt i HW11 x) ?_
      refine mul_le_mul hDpt0 hHVchain
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x _) (hCD_nn 0)
    have hT2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        (HdT2.toSection x) ≤
        cP * ((n * n) * ((2 * KtA' + 2 * KtA) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
      rw [hHdT2_def]
      refine le_trans (rfns_appCcRS_appCcLeibnizPsi_diag_le (I := I) (M := M) g₀ 2 6 2
        phiDt i HWd x) ?_
      refine mul_le_mul ?_ hHWdchain
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x _) hcP_nn
      rw [hphiDt_def]
      exact hcP x
    calc (2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          (HdT1.toSection x + HdT2.toSection x)
        ≤ (2 : ℝ) ^ 2 * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            (HdT1.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdT2.toSection x)) :=
          mul_le_mul_of_nonneg_left
            (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
            (by norm_num)
      _ ≤ (2 : ℝ) ^ 2 * (2 * (CD 0 * ((n * n) * ((2 * KtA' + 2 * KtA) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)))) +
          2 * (cP * ((n * n) * ((2 * KtA' + 2 * KtA) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact add_le_add (mul_le_mul_of_nonneg_left hT1 (by norm_num))
            (mul_le_mul_of_nonneg_left hT2 (by norm_num))
      _ = 8 * (n * n) * (CD 0 + cP) * (2 * KtA' + 2 * KtA) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  · intro x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
    have hb : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hWfin_def
    have hWfin_nn : 0 ≤ Wfin :=
      Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i + 3)
    have hWfin_one : 1 ≤ Wfin :=
      Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
    have hVd_res : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)).toSection x) ≤
        (2 * KcA' i + 2 * KcA i) * Wfin := by
      have hVd_split : iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA) =
          (iteratedCovGrad (I := I) g₀ 0 4 i (RLC11 - RLC01) - HdA') +
            (iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) - HdA) := by
        rw [show (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) =
            RLC01 - RLCfix from by
          rw [riemannLoweredBackgroundDifference, hRLC01_def, hRLCfix_def]]
        rw [show Vd = (RLC11 - RLC01) + (RLC01 - RLCfix) from by rw [hVd_def]; abel]
        rw [iteratedCovGrad_add (I := I) g₀ 0 4 i (RLC11 - RLC01) (RLC01 - RLCfix)]
        abel
      rw [hVd_split]
      rw [show (((iteratedCovGrad (I := I) g₀ 0 4 i (RLC11 - RLC01) - HdA') +
            (iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) -
              HdA)).toSection x) =
          (iteratedCovGrad (I := I) g₀ 0 4 i (RLC11 - RLC01) - HdA').toSection x +
            (iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) -
              HdA).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + i) x _ _) ?_
      have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i (RLC11 - RLC01) - HdA').toSection x) ≤
          KcA' i * Wfin := by
        have h := hHdA'_res x
        rw [hRLC11_def, hRLC01_def]
        exact h
      have h2 := hHdA_res x
      calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i (RLC11 - RLC01) - HdA').toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) -
              HdA).toSection x)
          ≤ 2 * (KcA' i * Wfin) + 2 * (KcA i * Wfin) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
              (mul_le_mul_of_nonneg_left h2 (by norm_num))
        _ = (2 * KcA' i + 2 * KcA i) * Wfin := by ring
    have hRLC11_res : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i RLC11 - (HdA' + HdA)).toSection x) ≤
        (4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin := by
      have hsplit : iteratedCovGrad (I := I) g₀ 0 4 i RLC11 - (HdA' + HdA) =
          (iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)) +
            iteratedCovGrad (I := I) g₀ 0 4 i RLCfix := by
        rw [show RLC11 = Vd + RLCfix from by rw [hVd_def]; abel]
        rw [iteratedCovGrad_add (I := I) g₀ 0 4 i Vd RLCfix]
        abel
      rw [hsplit]
      rw [show (((iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)) +
            iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) =
          (iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)).toSection x +
            (iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + i) x _ _) ?_
      have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) ≤ cfix i * Wfin := by
        have h2a : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) ≤ cfix i := by
          rw [hRLCfix_def]
          exact hcfix i x
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x)
            ≤ cfix i := h2a
          _ = cfix i * 1 := by ring
          _ ≤ cfix i * Wfin := mul_le_mul_of_nonneg_left hWfin_one (hcfix_nn i)
      calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x)
          ≤ 2 * ((2 * KcA' i + 2 * KcA i) * Wfin) + 2 * (cfix i * Wfin) :=
            add_le_add (mul_le_mul_of_nonneg_left hVd_res (by norm_num))
              (mul_le_mul_of_nonneg_left h2 (by norm_num))
        _ = (4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin := by ring
    have hT2res : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2).toSection x) ≤
        2 * (cP * ((n * n) * ((2 * KcA' i + 2 * KcA i) * Wfin))) := by
      rw [hHdT2_def]
      refine le_trans (tsParallel_argCorner_residual_le (I := I) (M := M) g₀ 2 6 2
        phiDt hphiDt_par WVd i HWd x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have hchain : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 6 i WVd - HWd).toSection x) ≤
          (n * n) * ((2 * KcA' i + 2 * KcA i) * Wfin) := by
        have hs1 := hWd_res x
        rw [← hWVd_def] at hs1
        refine le_trans hs1 ?_
        refine le_trans (h2d_res x) ?_
        calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 5 i
                (slotExtend (I := I) (M := M) g₀ 0 4 Vd) - HW1d).toSection x)
            ≤ n * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
                ((iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)).toSection x)) :=
              mul_le_mul_of_nonneg_left (h1d_res x) hn_nn
          _ ≤ n * (n * ((2 * KcA' i + 2 * KcA i) * Wfin)) := by
              refine mul_le_mul_of_nonneg_left ?_ hn_nn
              exact mul_le_mul_of_nonneg_left hVd_res hn_nn
          _ = (n * n) * ((2 * KcA' i + 2 * KcA i) * Wfin) := by ring
      have hp0 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x (phiDt.toSection x) ≤
          cP := by
        rw [hphiDt_def]; exact hcP x
      refine mul_le_mul hp0 hchain
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x _) hcP_nn
    have hT1res : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1).toSection x) ≤
        2 * (CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i)) * Wfin +
        2 * ((i : ℝ) * diagonalGridGrowthFactor (E := E) i *
          ∑ k ∈ Finset.range i, (CD (i - k) * (n * n) *
            ((2 * C1 k + 4 * CA k) *
                Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k)) *
            Wfin) := by
      have hsplitT1 : iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1 =
          ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11) +
            ∑ k ∈ Finset.range i,
              ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i k)
                (iteratedCovGrad (I := I) g₀ 2 6 k WBig) := by
        rw [iteratedCovGrad_appCcRS_eq_argCorner_add_lower (I := I) (M := M) g₀ 2 6 2
          Dpt WBig i]
        rw [hHdT1_def]
        rw [appCcRS_sub_right_cc (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
          (iteratedCovGrad (I := I) g₀ 2 6 i WBig) HW11]
        exact add_sub_right_comm _ _ _
      rw [hsplitT1]
      rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
            (iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11) +
          ∑ k ∈ Finset.range i,
            ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i k)
              (iteratedCovGrad (I := I) g₀ 2 6 k WBig)).toSection x) =
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
            (iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11)).toSection x +
          (∑ k ∈ Finset.range i,
            ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i k)
              (iteratedCovGrad (I := I) g₀ 2 6 k WBig)).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
      have hDpt0 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x (Dpt.toSection x) ≤
          CD 0 := by
        have h := hCD g₁ T htie hδ_le hδ0 hbound 0 x
        rw [iteratedCovGrad_zero] at h
        rw [Finset.sum_range_one, Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
        rw [hDpt_def]
        exact h
      have hpiece1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
            (iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11)).toSection x) ≤
          CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin := by
        refine le_trans (rfns_appCcRS_appCcLeibnizPsi_diag_le (I := I) (M := M) g₀ 2 6 2
          Dpt i _ x) ?_
        have hchain : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11).toSection x) ≤
            (n * n) * ((4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin) := by
          have hs1 := h11_res x
          rw [← hWBig_def] at hs1
          refine le_trans hs1 ?_
          refine le_trans (h2c_res x) ?_
          calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x
                ((iteratedCovGrad (I := I) g₀ 1 5 i
                  (slotExtend (I := I) (M := M) g₀ 0 4 RLC11) - HW1c).toSection x)
              ≤ n * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 i RLC11 -
                    (HdA' + HdA)).toSection x)) :=
                mul_le_mul_of_nonneg_left (h1c_res x) hn_nn
            _ ≤ n * (n * ((4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin)) := by
                refine mul_le_mul_of_nonneg_left ?_ hn_nn
                exact mul_le_mul_of_nonneg_left hRLC11_res hn_nn
            _ = (n * n) * ((4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin) := by ring
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x (Dpt.toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
                ((iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11).toSection x)
            ≤ CD 0 * ((n * n) * ((4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin)) := by
              refine mul_le_mul hDpt0 hchain
                (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x _)
                (hCD_nn 0)
          _ = CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin := by ring
      have hpiece2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((∑ k ∈ Finset.range i,
            ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i k)
              (iteratedCovGrad (I := I) g₀ 2 6 k WBig)).toSection x) ≤
          (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
            ∑ k ∈ Finset.range i, (CD (i - k) * (n * n) *
              ((2 * C1 k + 4 * CA k) *
                  Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k)) *
              Wfin := by
        refine le_trans (rfns_appCcRS_argLower_le (I := I) (M := M) g₀ 2 6 2 Dpt WBig i x) ?_
        rw [mul_assoc, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg i)
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        have hDptjet : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + (i - k)) x
            ((iteratedCovGrad (I := I) g₀ 6 2 (i - k) Dpt).toSection x) ≤
            CD (i - k) * (∑ l ∈ Finset.range ((i - k) + 1),
              Combinatorics.antidiagonalTupleGrid b l) := by
          have h := hCD g₁ T htie hδ_le hδ0 hbound (i - k) x
          rw [hDpt_def]
          exact h
        have hWjet : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + k) x
            ((iteratedCovGrad (I := I) g₀ 2 6 k WBig).toSection x) ≤
            (n * n) * ((2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
              Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k) := by
          rw [hWBig_def]
          rw [tsRfns_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6
            pairTraceKernelSlotPerm _ k x]
          refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
            (slotExtend (I := I) (M := M) g₀ 0 4 RLC11) k x) ?_
          have hinner : riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((4 + 1) + k) x
              ((iteratedCovGrad (I := I) g₀ 1 (4 + 1) k
                (slotExtend (I := I) (M := M) g₀ 0 4 RLC11)).toSection x) ≤
              n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                ((iteratedCovGrad (I := I) g₀ 0 4 k RLC11).toSection x) :=
            rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4 RLC11 k x
          have hRLC11jet : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
              ((iteratedCovGrad (I := I) g₀ 0 4 k RLC11).toSection x) ≤
              (2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
                Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k := by
            have hsplit11 : iteratedCovGrad (I := I) g₀ 0 4 k RLC11 =
                iteratedCovGrad (I := I) g₀ 0 4 k (RLC11 - RLC01) +
                  (iteratedCovGrad (I := I) g₀ 0 4 k
                    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) +
                    iteratedCovGrad (I := I) g₀ 0 4 k RLCfix) := by
              rw [← iteratedCovGrad_add (I := I) g₀ 0 4 k
                (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) RLCfix]
              rw [← iteratedCovGrad_add (I := I) g₀ 0 4 k (RLC11 - RLC01) _]
              refine congrArg (fun Z => iteratedCovGrad (I := I) g₀ 0 4 k Z) ?_
              rw [show (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) =
                  RLC01 - RLCfix from by
                rw [riemannLoweredBackgroundDifference, hRLC01_def, hRLCfix_def]]
              abel
            rw [hsplit11]
            rw [show ((iteratedCovGrad (I := I) g₀ 0 4 k (RLC11 - RLC01) +
                  (iteratedCovGrad (I := I) g₀ 0 4 k
                    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) +
                    iteratedCovGrad (I := I) g₀ 0 4 k RLCfix)).toSection x) =
                (iteratedCovGrad (I := I) g₀ 0 4 k (RLC11 - RLC01)).toSection x +
                  ((iteratedCovGrad (I := I) g₀ 0 4 k
                    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x +
                    (iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x) from by
              rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_add]; rfl]
            refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + k)
              x _ _) ?_
            have hd1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                ((iteratedCovGrad (I := I) g₀ 0 4 k (RLC11 - RLC01)).toSection x) ≤
                C1 k * (∑ k' ∈ Finset.range (k + 3),
                  Combinatorics.antidiagonalTupleGrid b k') := by
              have h := hC1 g₁ T htie hδ_le hδ0 hbound k x
              rw [hRLC11_def, hRLC01_def]
              exact h
            have hd23 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                ((iteratedCovGrad (I := I) g₀ 0 4 k
                    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x +
                  (iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x) ≤
                2 * (CA k * (∑ k' ∈ Finset.range (k + 3),
                  Combinatorics.antidiagonalTupleGrid b k')) + 2 * cfix k := by
              refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0
                (4 + k) x _ _) ?_
              have hd2 := hCA g₁ T htie hδ_le hδ0 hbound k x
              have hd3 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x) ≤ cfix k := by
                rw [hRLCfix_def]; exact hcfix k x
              exact add_le_add (mul_le_mul_of_nonneg_left hd2 (by norm_num))
                (mul_le_mul_of_nonneg_left hd3 (by norm_num))
            calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 k (RLC11 - RLC01)).toSection x) +
                2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 k
                      (riemannLoweredBackgroundDifference (I := I) (M := M)
                        g₀ g₁)).toSection x +
                    (iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x)
                ≤ 2 * (C1 k * (∑ k' ∈ Finset.range (k + 3),
                    Combinatorics.antidiagonalTupleGrid b k')) +
                  2 * (2 * (CA k * (∑ k' ∈ Finset.range (k + 3),
                    Combinatorics.antidiagonalTupleGrid b k')) + 2 * cfix k) :=
                  add_le_add (mul_le_mul_of_nonneg_left hd1 (by norm_num))
                    (mul_le_mul_of_nonneg_left hd23 (by norm_num))
              _ = (2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
                    Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k := by ring
          calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((4 + 1) + k) x
                ((iteratedCovGrad (I := I) g₀ 1 (4 + 1) k
                  (slotExtend (I := I) (M := M) g₀ 0 4 RLC11)).toSection x)
              ≤ n * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 k RLC11).toSection x)) :=
                mul_le_mul_of_nonneg_left hinner hn_nn
            _ ≤ n * (n * ((2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
                  Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k)) := by
                refine mul_le_mul_of_nonneg_left ?_ hn_nn
                exact mul_le_mul_of_nonneg_left hRLC11jet hn_nn
            _ = (n * n) * ((2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
                  Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k) := by ring
        have hDptW : (∑ l ∈ Finset.range ((i - k) + 1),
            Combinatorics.antidiagonalTupleGrid b l) ≤
            Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1) :=
          tsTgridSum_le_boundedWindow b hb (by omega) (le_refl _)
        have htgW : (∑ k' ∈ Finset.range (k + 3),
            Combinatorics.antidiagonalTupleGrid b k') ≤
            Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3) :=
          tsTgridSum_le_boundedWindow b hb (by omega) (le_refl _)
        have hWpair : Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3) ≤
            Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) * Wfin := by
          refine le_trans (Combinatorics.boundedFactorGridWindow_mul_le b hb (i + 1)
            ((i - k) + 1) (k + 3) (by omega) (by omega)) ?_
          refine mul_le_mul_of_nonneg_left ?_
            (Combinatorics.windowPairCellCount_nonneg _ _)
          rw [hWfin_def]
          refine Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) ?_
          omega
        have hDptWfin : Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1) ≤
            Wfin := by
          rw [hWfin_def]
          exact Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) (by omega)
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + (i - k)) x
              ((iteratedCovGrad (I := I) g₀ 6 2 (i - k) Dpt).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + k) x
              ((iteratedCovGrad (I := I) g₀ 2 6 k WBig).toSection x)
            ≤ (CD (i - k) * (∑ l ∈ Finset.range ((i - k) + 1),
                Combinatorics.antidiagonalTupleGrid b l)) *
              ((n * n) * ((2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
                Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k)) := by
              refine mul_le_mul hDptjet hWjet
                (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + k) x _) ?_
              exact mul_nonneg (hCD_nn _) (Finset.sum_nonneg fun l _ =>
                Combinatorics.antidiagonalTupleGrid_nonneg b hb l)
          _ ≤ (CD (i - k) * Combinatorics.boundedFactorGridWindow b (i + 1)
                ((i - k) + 1)) *
              ((n * n) * ((2 * C1 k + 4 * CA k) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3) + 4 * cfix k)) := by
              refine mul_le_mul ?_ ?_ ?_ ?_
              · exact mul_le_mul_of_nonneg_left hDptW (hCD_nn _)
              · refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hn_nn hn_nn)
                refine add_le_add ?_ (le_refl _)
                refine mul_le_mul_of_nonneg_left htgW ?_
                have := hC1_nn k; have := hCA_nn k; linarith
              · refine mul_nonneg (mul_nonneg hn_nn hn_nn) ?_
                refine add_nonneg ?_ ?_
                · refine mul_nonneg ?_ (Finset.sum_nonneg fun k' _ =>
                    Combinatorics.antidiagonalTupleGrid_nonneg b hb k')
                  have := hC1_nn k; have := hCA_nn k; linarith
                · have := hcfix_nn k; linarith
              · exact mul_nonneg (hCD_nn _)
                  (Combinatorics.boundedFactorGridWindow_nonneg b hb _ _)
          _ = CD (i - k) * (n * n) * (2 * C1 k + 4 * CA k) *
                (Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3)) +
              CD (i - k) * (n * n) * (4 * cfix k) *
                Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1) := by ring
          _ ≤ CD (i - k) * (n * n) * (2 * C1 k + 4 * CA k) *
                (Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) * Wfin) +
              CD (i - k) * (n * n) * (4 * cfix k) * Wfin := by
              refine add_le_add ?_ ?_
              · refine mul_le_mul_of_nonneg_left hWpair ?_
                refine mul_nonneg (mul_nonneg (hCD_nn _) (mul_nonneg hn_nn hn_nn)) ?_
                have := hC1_nn k; have := hCA_nn k; linarith
              · refine mul_le_mul_of_nonneg_left hDptWfin ?_
                refine mul_nonneg (mul_nonneg (hCD_nn _) (mul_nonneg hn_nn hn_nn)) ?_
                have := hcfix_nn k; linarith
          _ = (CD (i - k) * (n * n) *
              ((2 * C1 k + 4 * CA k) *
                  Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k)) *
              Wfin := by ring
      calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11)).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((∑ k ∈ Finset.range i,
              ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i k)
                (iteratedCovGrad (I := I) g₀ 2 6 k WBig)).toSection x)
          ≤ 2 * (CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin) +
            2 * ((i : ℝ) * diagonalGridGrowthFactor (E := E) i *
              ∑ k ∈ Finset.range i, (CD (i - k) * (n * n) *
                ((2 * C1 k + 4 * CA k) *
                    Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) +
                  4 * cfix k)) * Wfin) :=
          add_le_add (mul_le_mul_of_nonneg_left hpiece1 (by norm_num))
            (mul_le_mul_of_nonneg_left hpiece2 (by norm_num))
      _ = 2 * (CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i)) * Wfin +
          2 * ((i : ℝ) * diagonalGridGrowthFactor (E := E) i *
            ∑ k ∈ Finset.range i, (CD (i - k) * (n * n) *
              ((2 * C1 k + 4 * CA k) *
                  Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k)) *
              Wfin) := by ring
    have hsmul_diff : iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
          (2 : ℝ) • (HdT1 + HdT2) =
        (2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1) +
          (iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2)) := by
      rw [hRiemD]
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _]
      rw [iteratedCovGrad_smul_pt (I := I) (M := M) g₀ 2 2 i 2 _]
      rw [iteratedCovGrad_smul_pt (I := I) (M := M) g₀ 2 2 i 2 _]
      simp only [smul_add, smul_sub]
      abel
    rw [hsmul_diff]
    rw [show (((2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1) +
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2))).toSection x) =
        (2 : ℝ) • (((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1) +
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2)).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [rfns_smul_pt (I := I) (M := M) g₀ 2 (2 + i) x 2 _]
    rw [show ((((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1) +
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2)).toSection x)) =
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1).toSection x) +
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2).toSection x) from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    calc (2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          (((iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1).toSection x) +
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2).toSection x))
        ≤ (2 : ℝ) ^ 2 * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2).toSection x)) :=
          mul_le_mul_of_nonneg_left
            (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
            (by norm_num)
      _ ≤ (2 : ℝ) ^ 2 * (2 * (2 * (CD 0 * (n * n) *
              (4 * KcA' i + 4 * KcA i + 2 * cfix i)) * Wfin +
            2 * ((i : ℝ) * diagonalGridGrowthFactor (E := E) i *
              ∑ k ∈ Finset.range i, (CD (i - k) * (n * n) *
                ((2 * C1 k + 4 * CA k) *
                    Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) +
                  4 * cfix k)) * Wfin)) +
          2 * (2 * (cP * ((n * n) * ((2 * KcA' i + 2 * KcA i) * Wfin))))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact add_le_add (mul_le_mul_of_nonneg_left hT1res (by norm_num))
            (mul_le_mul_of_nonneg_left hT2res (by norm_num))
      _ = (4 * (2 * (2 * (CD 0 * (n * n) *
              (4 * KcA' i + 4 * KcA i + 2 * cfix i)) +
            2 * ((i : ℝ) * diagonalGridGrowthFactor (E := E) i *
              ∑ k ∈ Finset.range i, CD (i - k) * (n * n) *
                ((2 * C1 k + 4 * CA k) *
                    Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) +
                  4 * cfix k))) +
          2 * (2 * (cP * (n * n)) * (2 * KcA' i + 2 * KcA i)))) * Wfin := by
          rw [← Finset.sum_mul]
          ring

end TopSeparatedRungRiemannCoeff

section TopSeparatedResidualIntegrator

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

theorem boundedFactorGridWindow_integral_ballUniform_tameWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGridWindow
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Kt, hKt_nn, hKt⟩ := antidiagonalTupleGrid_integral_ballUniform_tameWindow
    (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => (∑ k ∈ Finset.range (i + 3), Kt k) * (1 + R ^ 2),
    fun i => mul_nonneg (Finset.sum_nonneg fun k _ => hKt_nn k) (by positivity), ?_⟩
  intro P hPball i hia
  set b : M → ℕ → ℝ := fun x l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb : ∀ (x : M) (l : ℕ), 0 ≤ b x l :=
    fun x l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hcont : ∀ l : ℕ, Continuous (fun x => b x l) := by
    intro l
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 l P)
    refine hc.congr (fun x => ?_)
    change tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x)
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 l P) x]
  have hWcont : Continuous (fun x =>
      Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3)) := by
    simp only [Combinatorics.boundedFactorGridWindow, Combinatorics.boundedFactorGrid]
    refine continuous_finset_sum _ (fun k _ => ?_)
    refine continuous_finset_sum _ (fun n _ => ?_)
    refine continuous_finset_sum _ (fun e _ => ?_)
    exact continuous_finset_prod _ (fun m _ => hcont (e m))
  have hint : MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    hWcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint, ?_⟩
  have hint_k : ∀ k : ℕ, MeasureTheory.Integrable
      (fun x => Combinatorics.antidiagonalTupleGrid (b x) k)
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun k => (hKt P hPball k).1
  have hint2_k : ∀ k : ℕ,
      (∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        Kt k * (1 + ∑ j ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
    fun k => (hKt P hPball k).2
  have hmaj_int : MeasureTheory.Integrable
      (fun x => ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid (b x) k)
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    MeasureTheory.integrable_finset_sum _ (fun k _ => hint_k k)
  have hmono : ∀ x : M,
      Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3) ≤
        ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid (b x) k := by
    intro x
    rw [Combinatorics.boundedFactorGridWindow]
    exact Finset.sum_le_sum (fun k _ =>
      Combinatorics.boundedFactorGrid_le_antidiagonalTupleGrid (b x) (hb x) (i + 1) k)
  refine le_trans (MeasureTheory.integral_mono hint hmaj_int hmono) ?_
  rw [MeasureTheory.integral_finset_sum _ (fun k _ => hint_k k)]
  have hterm : ∀ k ∈ Finset.range (i + 3),
      (∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        Kt k * (1 + R ^ 2) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    intro k hk
    rw [Finset.mem_range] at hk
    refine le_trans (hint2_k k) ?_
    have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    by_cases hk2 : k ≤ i + 1
    · have hsub : (∑ j ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤
          ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (by omega)) ?_
        intro j _ _
        exact sq_nonneg _
      have h1 : Kt k * (1 + ∑ j ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤
          Kt k * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (hKt_nn k)
      refine le_trans h1 ?_
      nlinarith [hKt_nn k, sq_nonneg R, hsum_nn,
        mul_nonneg (hKt_nn k) (add_nonneg (by norm_num : (0:ℝ) ≤ 1) hsum_nn)]
    · have hk_eq : k = i + 2 := by omega
      subst hk_eq
      have hsplit : (∑ j ∈ Finset.range ((i + 2) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) =
          (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 :=
        Finset.sum_range_succ _ (i + 2)

      have htop : ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 ≤ R ^ 2 := by
        have h := hPball (i + 2) (by omega)
        nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)]
      rw [hsplit]
      nlinarith [hKt_nn (i + 2), hsum_nn, sq_nonneg R,
        mul_nonneg (hKt_nn (i + 2)) hsum_nn,
        mul_nonneg (mul_nonneg (hKt_nn (i + 2)) (sq_nonneg R)) hsum_nn]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]

section NormedBoundedFactorIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem productTerm_integral_tame_le_ordS
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (u : SmoothCcTensor g₀ 0 s)
    {R : ℝ} (hR : 0 ≤ R)
    (i : ℕ) (hi1 : 1 ≤ i)
    {Λ : ℝ} (hΛ_nn : 0 ≤ Λ)
    (hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (u.toSection x) ≤ Λ ^ 2)
    (hNi : ‖iteratedCovGrad (I := I) g₀ 0 s i u‖ ≤ R)
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hGNP : ∀ j : ℕ, 0 < j → j < i →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
              ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x)) ^ ((i : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
        C * Λ ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)))
    (n : ℕ) (hn_le : n ≤ i) (e : Fin n → ℕ) (he : ∑ m, e m = i) :
    MeasureTheory.Integrable
        (fun x => ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (i : ℝ) * (max Λ (max C 1)) ^ (7 * i) * R ^ 2 := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hi_pos : 0 < i := hi1
  have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi_pos
  have hiR_ne : (i : ℝ) ≠ 0 := ne_of_gt hiR_pos
  have hnn : ∀ (j : ℕ) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
        ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x) :=
    fun j x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + j) x _
  have hcont : ∀ j : ℕ, Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
      ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x)) := by
    intro j
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 s j u)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (s + j) x
        ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 s j u) x]
  have hint : ∀ j : ℕ, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
        ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x)) μ := by
    intro j
    rw [hμ]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (s + j)
      (iteratedCovGrad (I := I) g₀ 0 s j u)
  have hint_rpow : ∀ (j : ℕ) (p : ℝ), 0 ≤ p → MeasureTheory.Integrable
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
        ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x)) ^ p) μ := by
    intro j p hp
    have hcp : Continuous (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
        ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x)) ^ p) :=
      (hcont j).rpow_const (fun x => Or.inr hp)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_prod : MeasureTheory.Integrable
      (fun x => ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) μ := by
    have hcp : Continuous (fun x => ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) :=
      continuous_finset_prod Finset.univ (fun m _ => hcont (e m))
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint_prod, ?_⟩
  set Mbar : ℝ := max Λ (max C 1) with hMbar
  have hMbar1 : (1 : ℝ) ≤ Mbar := le_trans (le_max_right C 1) (le_max_right Λ _)
  have hMbar_nn : 0 ≤ Mbar := le_trans zero_le_one hMbar1
  have hΛ_le : Λ ≤ Mbar := le_max_left _ _
  have hC_le : C ≤ Mbar := le_trans (le_max_left C 1) (le_max_right Λ _)
  set Sset : Finset (Fin n) := Finset.univ.filter (fun m => 0 < e m) with hSset
  set Zset : Finset (Fin n) := Finset.univ.filter (fun m => ¬ (0 < e m)) with hZset
  have hsplit : ∀ x : M,
      (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) =
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) *
          (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) := by
    intro x
    rw [hSset, hZset]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 0 < e m)
      (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x))).symm
  have hZbound : ∀ x : M,
      (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ≤ Λ ^ (2 * Zset.card) := by
    intro x
    calc (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x))
        ≤ ∏ _m ∈ Zset, Λ ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hnn (e m) x)
          intro m hm
          have hem0 : e m = 0 := by have := (Finset.mem_filter.mp hm).2; omega
          rw [hem0]; exact hΛsup x
      _ = Λ ^ (2 * Zset.card) := by rw [Finset.prod_const, ← pow_mul]
  have hZsum0 : ∑ m ∈ Zset, e m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have := (Finset.mem_filter.mp hm).2; omega
  have hSsum : ∑ m ∈ Sset, e m = i := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => 0 < e m) e
    rw [← hSset, ← hZset, hZsum0, add_zero, he] at h
    exact h
  have hScard_pos : 1 ≤ Sset.card := by
    rcases Nat.eq_zero_or_pos Sset.card with h0 | hp
    · exfalso
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hSsum
      omega
    · exact hp
  rcases Nat.lt_or_ge Sset.card 2 with hScard_lt2 | hScard_ge2
  · have hScard1 : Sset.card = 1 := by omega
    obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hScard1
    have hem₀ : e m₀ = i := by
      have hss : ∑ m ∈ Sset, e m = e m₀ := by rw [hm₀, Finset.sum_singleton]
      rw [hss] at hSsum; exact hSsum
    have hSprod : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
            ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) := by
      intro x; rw [hm₀, Finset.prod_singleton, hem₀]
    have hpt : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ≤
          Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
            ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) := by
      intro x
      rw [hsplit x, hSprod x]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
              ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x))
          ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
              ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x)) * Λ ^ (2 * Zset.card) :=
            mul_le_mul_of_nonneg_left (hZbound x) (hnn i x)
        _ = Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
              ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) := mul_comm _ _
    have hintFi : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
        ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) ∂μ) ≤ R ^ 2 := by
      have heq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
          ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) ∂μ) =
          ‖iteratedCovGrad (I := I) g₀ 0 s i u‖ ^ 2 := by
        rw [SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 s i u), hμ]
        exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i)
          ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection)).symm
      rw [heq]
      nlinarith [hNi, norm_nonneg (iteratedCovGrad (I := I) g₀ 0 s i u), hR]
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
            ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) ∂μ :=
          MeasureTheory.integral_mono hint_prod ((hint i).const_mul _) hpt
      _ = Λ ^ (2 * Zset.card) * ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
            ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * R ^ 2 := mul_le_mul_of_nonneg_left hintFi hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (7 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _)
              (pow_le_pow_right₀ hMbar1 (by omega))
          have e4 : Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (7 * i) * R ^ 2 :=
            mul_le_mul_of_nonneg_right e1 (sq_nonneg R)
          have e5 : Mbar ^ (7 * i) * R ^ 2 ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
            have h1i : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            have hMR : 0 ≤ Mbar ^ (7 * i) * R ^ 2 :=
              mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R)
            calc Mbar ^ (7 * i) * R ^ 2 = 1 * (Mbar ^ (7 * i) * R ^ 2) := by ring
              _ ≤ (i : ℝ) * (Mbar ^ (7 * i) * R ^ 2) := mul_le_mul_of_nonneg_right h1i hMR
              _ = (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by ring
          exact le_trans e4 e5
  · have hem_lt : ∀ m ∈ Sset, e m < i := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hadd : e m + ∑ m' ∈ Sset.erase m, e m' = ∑ m' ∈ Sset, e m' :=
        Finset.add_sum_erase Sset e hm
      rw [hSsum] at hadd
      have herase_ne : (Sset.erase m).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hm]; omega
      obtain ⟨m', hm'⟩ := herase_ne
      have hm'S : m' ∈ Sset := Finset.mem_of_mem_erase hm'
      have hm'pos : 1 ≤ e m' := (Finset.mem_filter.mp hm'S).2
      have hle : e m' ≤ ∑ m'' ∈ Sset.erase m, e m'' :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) hm'
      omega
    have hAMGM : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ≤
          ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      have hz_nn : ∀ m ∈ Sset, 0 ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        fun m _ => Real.rpow_nonneg (hnn (e m) x) _
      have hAM := Real.geom_mean_le_arith_mean_weighted Sset (fun m => (e m : ℝ) / i)
        (fun m => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
        hw_nn hw_sum hz_nn
      have hLHS : (∏ m ∈ Sset, ((riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
            ^ ((e m : ℝ) / i)) =
          ∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x) := by
        apply Finset.prod_congr rfl
        intro m hm
        have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
        have hemR_ne : (e m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
        rw [← Real.rpow_mul (hnn (e m) x)]
        rw [show ((i : ℝ) / (e m : ℝ)) * ((e m : ℝ) / i) = 1 by field_simp]
        rw [Real.rpow_one]
      rw [hLHS] at hAM
      exact hAM
    have hfactor : ∀ m ∈ Sset,
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
          Mbar ^ (5 * i) * R ^ 2 := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hem_lt_i : e m < i := hem_lt m hm
      have hemR_pos : (0 : ℝ) < (e m : ℝ) := by exact_mod_cast hmpos
      have hemR_ne : (e m : ℝ) ≠ 0 := ne_of_gt hemR_pos
      have hgn := hGNP (e m) hmpos hem_lt_i
      set Ival : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ
        with hIval
      have hIval_nn : 0 ≤ Ival := by
        rw [hIval]; exact integral_nonneg (fun x => Real.rpow_nonneg (hnn (e m) x) _)
      have hθ_nn : 0 ≤ (e m : ℝ) / i := by positivity
      have hθ_le1 : (e m : ℝ) / i ≤ 1 := by
        rw [div_le_one hiR_pos]; exact_mod_cast Nat.le_of_lt hem_lt_i
      have hexp1_nn : 0 ≤ 2 * (1 - (e m : ℝ) / i) := by nlinarith
      have hexp1_le : 2 * (1 - (e m : ℝ) / i) ≤ 2 := by nlinarith
      have hΛpow : Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 : ℕ) := by
        calc Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 * (1 - (e m : ℝ) / i)) :=
              Real.rpow_le_rpow hΛ_nn hΛ_le hexp1_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp1_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbase_le : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (3 : ℕ) := by
        have h1 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) :=
          mul_le_mul hC_le hΛpow (Real.rpow_nonneg hΛ_nn _) hMbar_nn
        calc C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) := h1
          _ = Mbar ^ (3 : ℕ) := by ring
      have hbase_nn : 0 ≤ C * Λ ^ (2 * (1 - (e m : ℝ) / i)) :=
        mul_nonneg hC_nn (Real.rpow_nonneg hΛ_nn _)
      have hIval_eq : Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := by
        rw [← Real.rpow_mul hIval_nn]
        rw [show ((e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 1 by field_simp]
        rw [Real.rpow_one]
      have hM3_one : (1 : ℝ) ≤ Mbar ^ (3 : ℕ) :=
        le_trans hMbar1 (le_self_pow₀ hMbar1 (by norm_num))
      have hidiv : (i : ℝ) / (e m : ℝ) ≤ (i : ℝ) :=
        div_le_self hiR_pos.le (by exact_mod_cast hmpos)
      have hsplit_pow : (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i))
            ^ ((i : ℝ) / (e m : ℝ)) =
          (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) *
            (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Real.mul_rpow hbase_nn (Real.rpow_nonneg hR _)
      have hRcollapse : (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) = R ^ (2 : ℕ) := by
        rw [← Real.rpow_mul hR]
        rw [show (2 * (e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 2 by field_simp]
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbasepow : (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) ≤
          Mbar ^ (5 * i) := by
        calc (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ))
            ≤ (Mbar ^ (3 : ℕ)) ^ ((i : ℝ) / (e m : ℝ)) :=
              Real.rpow_le_rpow hbase_nn hbase_le (by positivity)
          _ ≤ (Mbar ^ (3 : ℕ)) ^ ((i : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hM3_one hidiv
          _ = (Mbar ^ (3 : ℕ)) ^ (i : ℕ) := by rw [Real.rpow_natCast]
          _ = Mbar ^ (3 * i) := by rw [← pow_mul]
          _ ≤ Mbar ^ (5 * i) := pow_le_pow_right₀ hMbar1 (by omega)
      calc Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hIval_eq
        _ ≤ (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i))
              ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hIval_nn _) hgn (by positivity)
        _ = (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) *
              (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hsplit_pow
        _ = (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) * R ^ (2 : ℕ) := by
            rw [hRcollapse]
        _ ≤ Mbar ^ (5 * i) * R ^ 2 := mul_le_mul_of_nonneg_right hbasepow (sq_nonneg R)
    have hSsum_factor : ∑ m ∈ Sset, ((e m : ℝ) / i) *
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
        Mbar ^ (5 * i) * R ^ 2 := by
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      calc ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ)
          ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) * (Mbar ^ (5 * i) * R ^ 2) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul_of_nonneg_left (hfactor m hm) (hw_nn m hm)
        _ = (∑ m ∈ Sset, (e m : ℝ) / i) * (Mbar ^ (5 * i) * R ^ 2) := by rw [Finset.sum_mul]
        _ = Mbar ^ (5 * i) * R ^ 2 := by rw [hw_sum, one_mul]
    have hpt2 : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ≤
          Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      rw [hsplit x]
      have hZnn : 0 ≤ ∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x) :=
        Finset.prod_nonneg (fun m _ => hnn (e m) x)
      have hsum_nn : 0 ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hnn (e m) x) _))
      calc (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x))
          ≤ (∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) *
              Λ ^ (2 * Zset.card) :=
            mul_le_mul (hAMGM x) (hZbound x) hZnn hsum_nn
        _ = Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
            mul_comm _ _
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) μ := by
      apply MeasureTheory.integrable_finset_sum
      intro m _
      exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hint_eq : (∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) =
        ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) := by
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m _; rw [MeasureTheory.integral_const_mul]
      · intro m _
        exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_mono hint_prod (hsum_int.const_mul _) hpt2
      _ = Λ ^ (2 * Zset.card) * ∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2) := by
          rw [hint_eq]
          exact mul_le_mul_of_nonneg_left hSsum_factor hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _) (pow_le_pow_right₀ hMbar1 (by omega))
          have e3 : Mbar ^ (2 * i) * Mbar ^ (5 * i) = Mbar ^ (7 * i) := by
            rw [← pow_add]; congr 1; ring
          have e4 : Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2) ≤
              Mbar ^ (2 * i) * (Mbar ^ (5 * i) * R ^ 2) :=
            mul_le_mul_of_nonneg_right e1
              (mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R))
          have e5 : Mbar ^ (7 * i) * R ^ 2 ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
            have h1i : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            have hMR : 0 ≤ Mbar ^ (7 * i) * R ^ 2 :=
              mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R)
            calc Mbar ^ (7 * i) * R ^ 2 = 1 * (Mbar ^ (7 * i) * R ^ 2) := by ring
              _ ≤ (i : ℝ) * (Mbar ^ (7 * i) * R ^ 2) := mul_le_mul_of_nonneg_right h1i hMR
              _ = (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by ring
          calc Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2)
              ≤ Mbar ^ (2 * i) * (Mbar ^ (5 * i) * R ^ 2) := e4
            _ = Mbar ^ (7 * i) * R ^ 2 := by rw [← mul_assoc, e3]
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := e5

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem cappedTopLayerCell_integral_le
    (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    {Lam : ℝ} (hLam_nn : 0 ≤ Lam)
    (hΛsup_low : ∀ (m : ℕ), m ≤ 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2)
    (Cgn : ℕ → ℝ) (hCgn_nn : ∀ k, 0 ≤ Cgn k)
    (hGNv : ∀ (i₀ : ℕ), 1 ≤ i₀ → ∀ (j : ℕ), 0 < j → j < i₀ →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + j) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) j
                (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x)) ^ ((i₀ : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i₀ : ℝ)) ≤
        Cgn i₀ * Lam ^ (2 * (1 - (j : ℝ) / (i₀ : ℝ))) *
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ (2 * (j : ℝ) / (i₀ : ℝ)))
    (i n : ℕ) (e : Fin n → ℕ) (hn : n ≤ i + 2)
    (he_sum : ∑ m, e m = i + 2) (he_cap : ∀ m, e m ≤ i + 1)
    (MBv : ℝ) (hMBv1 : 1 ≤ MBv) (hMBv_Lam : Lam ≤ MBv)
    (hMBv_vol : ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal ≤ MBv)
    (hMBv_Cgn : ∀ k, k ≤ i → Cgn k ≤ MBv) :
    (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      (((i : ℝ) + 2) * MBv ^ (9 * (i + 2))) *
        (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hMBv_nn : 0 ≤ MBv := le_trans zero_le_one hMBv1
  have hLam2_nn : 0 ≤ Lam ^ 2 := sq_nonneg _
  set Wsum : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hWsum
  have hWsum1 : 1 ≤ Wsum := by
    rw [hWsum]
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j P‖))
    linarith
  have hWsum_nn : 0 ≤ Wsum := le_trans zero_le_one hWsum1
  set F : M → ℝ := fun x => ∏ m : Fin n,
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) with hF
  have hfac_nn : ∀ (m : Fin n) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
    fun m x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e m) x _
  have hfac_cont : ∀ m : Fin n, Continuous (fun x =>
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
    intro m
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 (e m) P)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 (e m) P) x]
  have hF_int : MeasureTheory.Integrable F μ := by
    have hcp : Continuous F := by
      rw [hF]; exact continuous_finset_prod _ (fun m _ => hfac_cont m)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set high : Finset (Fin n) := Finset.univ.filter (fun m => 3 ≤ e m) with hhigh
  set low : Finset (Fin n) := Finset.univ.filter (fun m => ¬ 3 ≤ e m) with hlow
  have hmem_high : ∀ m : Fin n, m ∈ high ↔ 3 ≤ e m := fun m => by
    rw [hhigh, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ m, h⟩⟩
  have hmem_low : ∀ m : Fin n, m ∈ low ↔ ¬ 3 ≤ e m := fun m => by
    rw [hlow, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ m, h⟩⟩
  have hlowbnd : ∀ (x : M),
      (∏ m ∈ low, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤ Lam ^ (2 * low.card) := by
    intro x
    calc (∏ m ∈ low, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        ≤ ∏ _m ∈ low, Lam ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hfac_nn m x)
          intro m hm
          have hem : e m ≤ 2 := by
            have := (hmem_low m).mp hm; omega
          exact hΛsup_low (e m) hem x
      _ = Lam ^ (2 * low.card) := by rw [Finset.prod_const, ← pow_mul, Nat.mul_comm]
  by_cases hne : high.Nonempty
  · have hcard_pos : 0 < high.card := Finset.Nonempty.card_pos hne
    set i₀ : ℕ := ∑ m ∈ high, (e m - 2) with hi₀
    have hge3 : ∀ m ∈ high, 3 ≤ e m := fun m hm => (hmem_high m).mp hm
    have hn'_le : high.card ≤ i₀ := by
      rw [hi₀, Finset.card_eq_sum_ones]
      apply Finset.sum_le_sum
      intro m hm; have := hge3 m hm; omega
    have hi₀_ge1 : 1 ≤ i₀ := le_trans hcard_pos hn'_le
    have heq_sum : (∑ m ∈ high, e m) = i₀ + 2 * high.card := by
      have h1 : (∑ m ∈ high, e m) = ∑ m ∈ high, ((e m - 2) + 2) :=
        Finset.sum_congr rfl (fun m hm => by have := hge3 m hm; omega)
      rw [h1, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← hi₀,
        Nat.mul_comm]
    have hsum_high_le : (∑ m ∈ high, e m) ≤ i + 2 := by
      calc (∑ m ∈ high, e m) ≤ ∑ m : Fin n, e m :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = i + 2 := he_sum
    have hi₀_bound : 2 + i₀ ≤ i + 1 := by
      rcases Nat.lt_or_ge high.card 2 with h1 | h2
      · have hcard1 : high.card = 1 := by omega
        obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hcard1
        have hsingle : (∑ m ∈ high, e m) = e m₀ := by rw [hm₀, Finset.sum_singleton]
        have hcap0 : e m₀ ≤ i + 1 := he_cap m₀
        omega
      · omega
    set ι : Fin high.card → {m // m ∈ high} := fun m' => (Finset.equivFin high).symm m' with hι
    set e' : Fin high.card → ℕ := fun m' => e ((ι m' : Fin n)) - 2 with he'
    have hge3' : ∀ m' : Fin high.card, 3 ≤ e ((ι m' : Fin n)) :=
      fun m' => hge3 _ (ι m').2
    have he'_sum : (∑ m', e' m') = i₀ := by
      rw [hi₀, ← Finset.sum_coe_sort high (fun m => e m - 2)]
      exact Equiv.sum_comp (Finset.equivFin high).symm (fun m : {m // m ∈ high} => e ↑m - 2)
    have hcongr_local : ∀ (x : M) (n₁ n₂ : ℕ), n₁ = n₂ →
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + n₁) x
          ((iteratedCovGrad (I := I) g₀ 0 2 n₁ P).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + n₂) x
          ((iteratedCovGrad (I := I) g₀ 0 2 n₂ P).toSection x) := by
      intro x n₁ n₂ h; subst h; rfl
    have hcellprod : ∀ x : M,
        (∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        ∏ m' : Fin high.card,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + e' m') x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) (e' m')
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x) := by
      intro x
      rw [← Finset.prod_coe_sort high (fun m =>
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)),
        ← Equiv.prod_comp (Finset.equivFin high).symm
          (fun m : {m // m ∈ high} =>
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e ↑m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e ↑m) P).toSection x))]
      refine Finset.prod_congr rfl (fun m' _ => ?_)
      symm
      rw [riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 2 (e' m') P x]
      exact hcongr_local x (2 + e' m') (e ((ι m' : Fin n))) (by
        have := hge3' m'; simp only [he']; omega)
    have hΛsup_v2 : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
          ((iteratedCovGrad (I := I) g₀ 0 2 2 P).toSection x) ≤ Lam ^ 2 :=
      hΛsup_low 2 (le_refl 2)
    have htmpl := productTerm_integral_tame_le_ordS (I := I) (M := M) g₀ (2 + 2)
      (iteratedCovGrad (I := I) g₀ 0 2 2 P)
      (norm_nonneg (iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
        (iteratedCovGrad (I := I) g₀ 0 2 2 P)))
      i₀ hi₀_ge1 hLam_nn hΛsup_v2 (le_refl _) (hCgn_nn i₀) (hGNv i₀ hi₀_ge1)
      high.card hn'_le e' he'_sum
    have hhigh_int : MeasureTheory.Integrable
        (fun x => ∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) μ := by
      have hcp : Continuous (fun x => ∏ m ∈ high,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) :=
        continuous_finset_prod _ (fun m _ => hfac_cont m)
      exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hnorm_int : ∀ (s' : ℕ) (w : Integral.L2.SmoothCcTensor g₀ 0 s'),
        (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s' x (w.toSection x) ∂μ) = ‖w‖ ^ 2 := by
      intro s' w
      rw [SmoothCcTensor.norm_def w, hμ]
      exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 s'
        (w.toSection)).symm
    have hhigh_le : (∫ x, ∏ m ∈ high,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ) ≤
        (i₀ : ℝ) * (max Lam (max (Cgn i₀) 1)) ^ (7 * i₀) *
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2 := by
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcellprod)]
      exact htmpl.2
    have hRsq_le : ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
        (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2 ≤ Wsum := by
      have e1 : ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
          (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i₀) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x) ∂μ :=
        (hnorm_int ((2 + 2) + i₀) (iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
          (iteratedCovGrad (I := I) g₀ 0 2 2 P))).symm
      have e2 : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i₀) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x) ∂μ) =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + i₀)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (2 + i₀) P).toSection x) ∂μ := by
        apply MeasureTheory.integral_congr_ae
        refine Filter.Eventually.of_forall (fun x => ?_)
        exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 2 i₀ P x
      have e3 : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + i₀)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (2 + i₀) P).toSection x) ∂μ) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (2 + i₀) P‖ ^ 2 :=
        hnorm_int (2 + (2 + i₀)) (iteratedCovGrad (I := I) g₀ 0 2 (2 + i₀) P)
      have hmem : 2 + i₀ ∈ Finset.range (i + 2) := Finset.mem_range.mpr (by omega)
      have hle_sum : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 + i₀) P‖ ^ 2 ≤
          ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
        Finset.single_le_sum
          (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
          (fun j _ => sq_nonneg _) hmem
      rw [e1, e2, e3, hWsum]; linarith
    have hRsq_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
        (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2 := sq_nonneg _
    have hmax_nn : 0 ≤ max Lam (max (Cgn i₀) 1) :=
      le_trans hLam_nn (le_max_left _ _)
    have hmax1 : (1 : ℝ) ≤ max Lam (max (Cgn i₀) 1) :=
      le_trans (le_max_right (Cgn i₀) 1) (le_max_right Lam _)
    have hmax_le : max Lam (max (Cgn i₀) 1) ≤ MBv := by
      apply max_le hMBv_Lam
      apply max_le (hMBv_Cgn i₀ (by omega)) hMBv1
    have hlowcard_le : low.card ≤ i + 2 :=
      le_trans (Finset.card_filter_le _ _) (le_trans (by simp) hn)
    have hLampow_nn : 0 ≤ Lam ^ (2 * low.card) := pow_nonneg hLam_nn _
    have hsplit : ∀ x : M, F x =
        (∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
        (∏ m ∈ low, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
      intro x
      rw [hF, hhigh, hlow]
      exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 3 ≤ e m)
        (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))).symm
    have hFbnd : ∀ x : M, F x ≤ Lam ^ (2 * low.card) *
        (∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
      intro x
      rw [hsplit x]
      have hhnn : 0 ≤ ∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
        Finset.prod_nonneg (fun m _ => hfac_nn m x)
      calc (∏ m ∈ high, _) * (∏ m ∈ low, _)
          ≤ (∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) * Lam ^ (2 * low.card) :=
            mul_le_mul_of_nonneg_left (hlowbnd x) hhnn
        _ = Lam ^ (2 * low.card) * (∏ m ∈ high, _) := by ring
    have hfinal : (∫ x, F x ∂μ) ≤ Lam ^ (2 * low.card) *
        ((i₀ : ℝ) * (max Lam (max (Cgn i₀) 1)) ^ (7 * i₀) *
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2) := by
      calc (∫ x, F x ∂μ)
          ≤ ∫ x, Lam ^ (2 * low.card) *
              (∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ∂μ :=
            MeasureTheory.integral_mono hF_int (hhigh_int.const_mul _) hFbnd
        _ = Lam ^ (2 * low.card) * ∫ x, ∏ m ∈ high,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ :=
            MeasureTheory.integral_const_mul _ _
        _ ≤ Lam ^ (2 * low.card) *
              ((i₀ : ℝ) * (max Lam (max (Cgn i₀) 1)) ^ (7 * i₀) *
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
                  (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hhigh_le hLampow_nn
    refine le_trans hfinal ?_
    have hLL : Lam ^ (2 * low.card) ≤ MBv ^ (2 * (i + 2)) :=
      le_trans (pow_le_pow_left₀ hLam_nn hMBv_Lam _)
        (pow_le_pow_right₀ hMBv1 (by omega))
    have hMM : (max Lam (max (Cgn i₀) 1)) ^ (7 * i₀) ≤ MBv ^ (7 * (i + 2)) :=
      le_trans (pow_le_pow_left₀ hmax_nn hmax_le _)
        (pow_le_pow_right₀ hMBv1 (by omega))
    have hi₀R : (i₀ : ℝ) ≤ (i : ℝ) + 2 := by
      have : i₀ ≤ i + 2 := by omega
      exact_mod_cast le_trans this (by norm_num)
    have hpowsum : MBv ^ (2 * (i + 2)) * MBv ^ (7 * (i + 2)) = MBv ^ (9 * (i + 2)) := by
      rw [← pow_add]; congr 1; ring
    calc Lam ^ (2 * low.card) *
          ((i₀ : ℝ) * (max Lam (max (Cgn i₀) 1)) ^ (7 * i₀) *
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2)
        ≤ MBv ^ (2 * (i + 2)) *
            (((i : ℝ) + 2) * MBv ^ (7 * (i + 2)) * Wsum) := by
          apply mul_le_mul hLL _ (by positivity) (by positivity)
          apply mul_le_mul (mul_le_mul hi₀R hMM (by positivity) (by positivity)) hRsq_le
            hRsq_nn (by positivity)
      _ = ((i : ℝ) + 2) * (MBv ^ (2 * (i + 2)) * MBv ^ (7 * (i + 2))) * Wsum := by ring
      _ = ((i : ℝ) + 2) * MBv ^ (9 * (i + 2)) * Wsum := by rw [hpowsum]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hallow : ∀ m : Fin n, e m ≤ 2 := by
      intro m
      by_contra h
      have hm3 : 3 ≤ e m := by omega
      have hmem : m ∈ high := (hmem_high m).mpr hm3
      rw [hne] at hmem
      exact absurd hmem (by simp)
    have hFbnd : ∀ x : M, F x ≤ Lam ^ (2 * n) := by
      intro x
      rw [hF]
      calc (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ ∏ _m : Fin n, Lam ^ 2 := by
            apply Finset.prod_le_prod (fun m _ => hfac_nn m x)
            intro m _; exact hΛsup_low (e m) (hallow m) x
        _ = Lam ^ (2 * n) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ← pow_mul, Nat.mul_comm]
    have hvol_int : (∫ x, F x ∂μ) ≤ Lam ^ (2 * n) *
        ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal := by
      calc (∫ x, F x ∂μ)
          ≤ ∫ _x, Lam ^ (2 * n) ∂μ :=
            MeasureTheory.integral_mono hF_int (MeasureTheory.integrable_const _) hFbnd
        _ = Lam ^ (2 * n) * ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal := by
            rw [MeasureTheory.integral_const, smul_eq_mul, hμ,
              MeasureTheory.measureReal_def, mul_comm]
    refine le_trans hvol_int ?_
    have hLampow_nn : 0 ≤ Lam ^ (2 * n) := pow_nonneg hLam_nn _
    have hLn : Lam ^ (2 * n) ≤ MBv ^ (2 * (i + 2)) :=
      le_trans (pow_le_pow_left₀ hLam_nn hMBv_Lam _)
        (pow_le_pow_right₀ hMBv1 (by omega))
    have hbase : Lam ^ (2 * n) *
        ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal ≤
        MBv ^ (2 * (i + 2)) * MBv := by
      apply mul_le_mul hLn hMBv_vol ENNReal.toReal_nonneg (pow_nonneg hMBv_nn _)
    have hpow_le : MBv ^ (2 * (i + 2)) * MBv ≤ MBv ^ (9 * (i + 2)) := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hMBv1 (by omega)
    have hfinal2 : Lam ^ (2 * n) *
        ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal ≤
        MBv ^ (9 * (i + 2)) := le_trans hbase hpow_le
    calc Lam ^ (2 * n) *
          ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal
        ≤ MBv ^ (9 * (i + 2)) := hfinal2
      _ = 1 * (MBv ^ (9 * (i + 2)) * 1) := by ring
      _ ≤ ((i : ℝ) + 2) * (MBv ^ (9 * (i + 2)) * Wsum) := by
          apply mul_le_mul (by have := Nat.cast_nonneg (α := ℝ) i; linarith) _
            (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_left hWsum1 (by positivity)
      _ = (((i : ℝ) + 2) * MBv ^ (9 * (i + 2))) * Wsum := by ring

theorem boundedFactorGrid_cappedTopLayer_integral_flat
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGrid
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 2))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGrid
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 2)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Lam : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R with hLam
  have hLam_nn : 0 ≤ Lam := by rw [hLam]; positivity
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 (2 + 2) k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 (2 + 2) k h).choose_spec.1
    · exact le_refl 0
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal with hvol
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  set MB : ℕ → ℝ := fun i => 1 + vol + Lam + ∑ k ∈ Finset.range (i + 1), Cgn k with hMBdef
  have hsumCgn_nn : ∀ i, 0 ≤ ∑ k ∈ Finset.range (i + 1), Cgn k :=
    fun i => Finset.sum_nonneg (fun k _ => hCgn_nn k)
  have hMB1 : ∀ i, 1 ≤ MB i := by
    intro i; rw [hMBdef]
    have := hsumCgn_nn i; linarith
  have hMB_nn : ∀ i, 0 ≤ MB i := fun i => le_trans zero_le_one (hMB1 i)
  have hMB_Lam : ∀ i, Lam ≤ MB i := by
    intro i; rw [hMBdef]; have := hsumCgn_nn i; linarith
  have hMB_vol : ∀ i, vol ≤ MB i := by
    intro i; rw [hMBdef]; have := hsumCgn_nn i; linarith
  have hMB_Cgn : ∀ i k, k ≤ i → Cgn k ≤ MB i := by
    intro i k hk
    rw [hMBdef]
    have hmem : k ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
    have hle : Cgn k ≤ ∑ k' ∈ Finset.range (i + 1), Cgn k' :=
      Finset.single_le_sum (fun k' _ => hCgn_nn k') hmem
    linarith
  set gcount : ℕ → ℝ := fun i =>
    ∑ n ∈ Finset.range (i + 2 + 1), ((Finset.Nat.antidiagonalTuple n (i + 2)).card : ℝ)
    with hgcount
  have hgcount_nn : ∀ i, 0 ≤ gcount i :=
    fun i => Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)
  refine ⟨fun i => gcount i * (((i : ℝ) + 2) * MB i ^ (9 * (i + 2))),
    fun i => mul_nonneg (hgcount_nn i)
      (mul_nonneg (by positivity) (pow_nonneg (hMB_nn i) _)), ?_⟩
  intro P hPball i
  have hΛsup_low : ∀ (m : ℕ), m ≤ 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2 := by
    intro m hm x
    have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
      calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
          ≤ ∑ j ∈ Finset.range (a + 1 + 1), R ^ 2 := by
            apply Finset.sum_le_sum
            intro j hj
            have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
            nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hPball j hjle, hR]
        _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤
        ∑ m' ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m') x
          ((iteratedCovGrad (I := I) g₀ 0 2 m' P).toSection x) := by
      have hmmem : m ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
      exact Finset.single_le_sum
        (f := fun m' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m') x
          ((iteratedCovGrad (I := I) g₀ 0 2 m' P).toSection x))
        (fun m' _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m') x _) hmmem
    have hLam2 : Lam ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
      rw [hLam, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    have hchain : ∑ m' ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m') x
          ((iteratedCovGrad (I := I) g₀ 0 2 m' P).toSection x) ≤ Lam ^ 2 := by
      refine le_trans (hCemb P x) ?_
      rw [hLam2]
      calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
          ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
            mul_le_mul_of_nonneg_left hsum_le (by positivity)
        _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring
    exact le_trans hsingle hchain
  have hΛsup_v2 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 2 2 P).toSection x) ≤ Lam ^ 2 :=
    hΛsup_low 2 (le_refl 2)
  have hGNv : ∀ (i₀ : ℕ), 1 ≤ i₀ → ∀ (j : ℕ), 0 < j → j < i₀ →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + j) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) j
                (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x)) ^ ((i₀ : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i₀ : ℝ)) ≤
        Cgn i₀ * Lam ^ (2 * (1 - (j : ℝ) / (i₀ : ℝ))) *
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ (2 * (j : ℝ) / (i₀ : ℝ)) := by
    intro i₀ hi₀ j hj0 hji
    have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
      (I := I) (M := M) g₀ 0 (2 + 2) i₀ hi₀).choose_spec.2
    have hb := hGNspec (iteratedCovGrad (I := I) g₀ 0 2 2 P) Lam hLam_nn hΛsup_v2 j hj0 hji
    have hchoose : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 (2 + 2) i₀ hi₀).choose = Cgn i₀ := by
      rw [hCgn]; simp only [dif_pos hi₀]
    rw [hchoose] at hb
    have hnorm : Integral.L2.tensorL2Norm (I := I) g₀ 0 ((2 + 2) + i₀)
        (iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
          (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toFun =
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀ (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ :=
      (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
        (iteratedCovGrad (I := I) g₀ 0 2 2 P))).symm
    rw [hnorm] at hb
    exact hb
  set b : M → ℕ → ℝ := fun x l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb : ∀ (x : M) (l : ℕ), 0 ≤ b x l :=
    fun x l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hcont : ∀ l : ℕ, Continuous (fun x => b x l) := by
    intro l
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 l P)
    refine hc.congr (fun x => ?_)
    change tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x)
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 l P) x]
  have hcell_cont : ∀ (n : ℕ) (e : Fin n → ℕ),
      Continuous (fun x => ∏ m : Fin n, b x (e m)) := by
    intro n e
    exact continuous_finset_prod _ (fun m _ => hcont (e m))
  have hcell_int : ∀ (n : ℕ) (e : Fin n → ℕ),
      MeasureTheory.Integrable (fun x => ∏ m : Fin n, b x (e m))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun n e => (hcell_cont n e).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hgrid_cont : Continuous (fun x =>
      Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2)) := by
    simp only [Combinatorics.boundedFactorGrid]
    refine continuous_finset_sum _ (fun n _ => ?_)
    refine continuous_finset_sum _ (fun e _ => ?_)
    exact continuous_finset_prod _ (fun m _ => hcont (e m))
  have hgrid_int : MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    hgrid_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hgrid_int, ?_⟩
  have hPT : ∀ n ∈ Finset.range (i + 2 + 1),
      ∀ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
      (∫ x, ∏ m : Fin n, b x (e m) ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    intro n hn e he
    have hnle : n ≤ i + 2 := by have := Finset.mem_range.mp hn; omega
    have he_sum : ∑ m, e m = i + 2 :=
      Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp he).1
    have he_cap : ∀ m, e m ≤ i + 1 := (Finset.mem_filter.mp he).2
    exact cappedTopLayerCell_integral_le (I := I) (M := M) g₀ P hLam_nn hΛsup_low
      Cgn hCgn_nn hGNv i n e hnle he_sum he_cap (MB i) (hMB1 i) (hMB_Lam i)
      (hMB_vol i) (fun k hk => hMB_Cgn i k hk)
  have hgrid_eq : (∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
      ∑ n ∈ Finset.range (i + 2 + 1),
        ∑ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
          ∫ x, ∏ m : Fin n, b x (e m) ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    have h1 : (fun x => Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2)) =
        (fun x => ∑ n ∈ Finset.range (i + 2 + 1),
          ∑ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
            ∏ m : Fin n, b x (e m)) := rfl
    rw [h1, MeasureTheory.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro n _
      rw [MeasureTheory.integral_finset_sum]
      intro e _; exact hcell_int n e
    · intro n _
      apply MeasureTheory.integrable_finset_sum
      intro e _; exact hcell_int n e
  rw [hgrid_eq]
  have hKcell_nn : (0 : ℝ) ≤ ((i : ℝ) + 2) * MB i ^ (9 * (i + 2)) :=
    mul_nonneg (by positivity) (pow_nonneg (hMB_nn i) _)
  have hWsum_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j P‖))
    linarith
  calc ∑ n ∈ Finset.range (i + 2 + 1),
        ∑ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
          ∫ x, ∏ m : Fin n, b x (e m) ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
      ≤ ∑ n ∈ Finset.range (i + 2 + 1),
          ∑ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
            (((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
              (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        apply Finset.sum_le_sum; intro n hn
        apply Finset.sum_le_sum; intro e he
        exact hPT n hn e he
    _ = (∑ n ∈ Finset.range (i + 2 + 1),
          (((Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1)).card : ℝ)) *
          ((((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
            (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n _; rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ gcount i *
          ((((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
            (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hKcell_nn hWsum_nn)
        rw [hgcount]
        apply Finset.sum_le_sum
        intro n _
        exact_mod_cast Finset.card_filter_le _ _
    _ = gcount i * (((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        ring

theorem boundedFactorGridWindow_integral_ballUniform_flat_allOrders
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Kflat : ℕ → ℝ, (∀ i, 0 ≤ Kflat i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGridWindow
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              Kflat i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Kt, hKt_nn, hKt⟩ := antidiagonalTupleGrid_integral_ballUniform_tameWindow
    (I := I) (M := M) g₀ a ha_super hR
  obtain ⟨Kc, hKc_nn, hKc⟩ := boundedFactorGrid_cappedTopLayer_integral_flat
    (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => (∑ k ∈ Finset.range (i + 2), Kt k) + Kc i,
    fun i => add_nonneg (Finset.sum_nonneg fun k _ => hKt_nn k) (hKc_nn i), ?_⟩
  intro P hPball i
  set b : M → ℕ → ℝ := fun x l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb : ∀ (x : M) (l : ℕ), 0 ≤ b x l :=
    fun x l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hcont : ∀ l : ℕ, Continuous (fun x => b x l) := by
    intro l
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 l P)
    refine hc.congr (fun x => ?_)
    change tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x)
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 l P) x]
  have hbfg_cont : ∀ (K k : ℕ),
      Continuous (fun x => Combinatorics.boundedFactorGrid (b x) K k) := by
    intro K k
    simp only [Combinatorics.boundedFactorGrid]
    refine continuous_finset_sum _ (fun n _ => ?_)
    refine continuous_finset_sum _ (fun e _ => ?_)
    exact continuous_finset_prod _ (fun m _ => hcont (e m))
  have hbfg_int : ∀ (K k : ℕ), MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGrid (b x) K k)
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun K k => (hbfg_cont K k).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hWcont : Continuous (fun x =>
      Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3)) := by
    simp only [Combinatorics.boundedFactorGridWindow]
    exact continuous_finset_sum _ (fun k _ => hbfg_cont (i + 1) k)
  have hWint : MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    hWcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hWint, ?_⟩
  have hInt_eq : (∫ x, Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
      (∑ k ∈ Finset.range (i + 2), ∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) +
        ∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    have hEq : (fun x => Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3)) =
        (fun x => ∑ k ∈ Finset.range (i + 3),
          Combinatorics.boundedFactorGrid (b x) (i + 1) k) := rfl
    rw [hEq, MeasureTheory.integral_finset_sum _ (fun k _ => hbfg_int (i + 1) k),
      Finset.sum_range_succ]
  rw [hInt_eq]
  have hlayer_le : ∀ k ∈ Finset.range (i + 2),
      (∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        Kt k * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hAint : MeasureTheory.Integrable
        (fun x => Combinatorics.antidiagonalTupleGrid (b x) k)
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := (hKt P hPball k).1
    have hAbound : (∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        Kt k * (1 + ∑ j ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := (hKt P hPball k).2
    calc (∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ ∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) :=
          MeasureTheory.integral_mono (hbfg_int (i + 1) k) hAint
            (fun x => Combinatorics.boundedFactorGrid_le_antidiagonalTupleGrid
              (b x) (hb x) (i + 1) k)
      _ ≤ Kt k * (1 + ∑ j ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := hAbound
      _ ≤ Kt k * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (hKt_nn k)
          have hsub : (∑ j ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤
              ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => sq_nonneg _)
            intro m hm
            rw [Finset.mem_range] at hm ⊢
            omega
          linarith
  have hleaf := (hKc P hPball i).2
  calc (∑ k ∈ Finset.range (i + 2), ∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) +
        ∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
      ≤ (∑ k ∈ Finset.range (i + 2), Kt k * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) +
          Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
        add_le_add (Finset.sum_le_sum hlayer_le) hleaf
    _ = ((∑ k ∈ Finset.range (i + 2), Kt k) + Kc i) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        rw [← Finset.sum_mul, ← add_mul]

end NormedBoundedFactorIntegral

theorem boundedFactorGridWindow_integral_ballUniform_tameWindow_allOrders
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Kflat : ℕ → ℝ, (∀ i, 0 ≤ Kflat i) ∧ ∃ Kleak : ℝ, 0 ≤ Kleak ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGridWindow
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              Kflat i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
                Kleak * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 := by
  obtain ⟨Kflat, hKflat_nn, hK⟩ :=
    boundedFactorGridWindow_integral_ballUniform_flat_allOrders
      (I := I) (M := M) g₀ a ha_super hR
  refine ⟨Kflat, hKflat_nn, 0, le_refl 0, ?_⟩
  intro P hPball i
  obtain ⟨hint, hbound⟩ := hK P hPball i
  refine ⟨hint, ?_⟩
  rw [show (0 : ℝ) * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 = 0 by ring, add_zero]
  exact hbound

theorem ricciArmOrder0BaseCoeff_perOrder_l2_topSeparated_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ∃ Hd : SmoothCcTensor g₀ 2 (2 + i),
            (∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (Hd.toSection x) ≤
                Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) ∧
            ‖Hd‖ ^ 2 ≤ Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 ∧
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - Hd‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨KtCr, hKtCr_nn, KcCr, hKcCr_nn, hCr⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨KtCu, hKtCu_nn, KcCu, hKcCu_nn, hCu⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0CurvCoeff_backgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_iteratedCovGrad_fiberNormSq_bound (I := I) (M := M) g₀ 2 2
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
  obtain ⟨KI, hKI_nn, hKI⟩ := boundedFactorGridWindow_integral_ballUniform_tameWindow
    (I := I) (M := M) g₀ a ha_super hR
  refine ⟨2 * KtCr + 2 * KtCu, by linarith, ?_⟩
  refine ⟨fun i => (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i,
    fun i => mul_nonneg
      (by have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith)
      (hKI_nn i), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hia
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    obtain ⟨HdCr, hCr_head, hCr_res⟩ := hCr g₁ P htie hδ_le hδ0 hδ i
    obtain ⟨HdCu, hCu_head, hCu_res⟩ := hCu g₁ P htie hδ_le hδ0 hδ i
    refine ⟨HdCr - HdCu, ?_, ?_, ?_⟩
    · intro x
      rw [show ((HdCr - HdCu).toSection x) = HdCr.toSection x - HdCu.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
      have h1 := hCr_head x
      have h2 := hCu_head x
      calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCr.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCu.toSection x)
          ≤ 2 * (KtCr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
            2 * (KtCu * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
              (mul_le_mul_of_nonneg_left h2 (by norm_num))
        _ = (2 * KtCr + 2 * KtCu) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by ring
    · have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((HdCr - HdCu).toSection x) ≤
            (2 * KtCr + 2 * KtCu) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by
        intro x
        rw [show ((HdCr - HdCu).toSection x) = HdCr.toSection x - HdCu.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
        have h1 := hCr_head x
        have h2 := hCu_head x
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              (HdCr.toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCu.toSection x)
            ≤ 2 * (KtCr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
              2 * (KtCu * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) :=
              add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
                (mul_le_mul_of_nonneg_left h2 (by norm_num))
          _ = (2 * KtCr + 2 * KtCu) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by ring
      have hF_int : MeasureTheory.Integrable
          (fun x => (2 * KtCr + 2 * KtCu) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
        (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 2))
          (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)).const_mul _
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
        g₀ 2 (2 + i) (HdCr - HdCu) _ hF_int hpt
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      rw [show (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 from by
        rw [SmoothCcTensor.norm_def (I := I) (M := M)
            (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P),
          tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
            g₀ 0 (2 + (i + 2)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)]]
    · have harm0 : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ =
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
          ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)) := by abel
      have hdiff : iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - (HdCr - HdCu) =
          iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)) := by
        rw [harm0]
        rw [show iteratedCovGrad (I := I) g₀ 2 2 i
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))) =
            iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            (iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
             iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)) from by
          rw [iteratedCovGrad_add (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
            ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))]
          rw [iteratedCovGrad_sub (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)]]
        abel
      have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
                (HdCr - HdCu)).toSection x) ≤
            (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
              Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
        intro x
        set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
        have hb : ∀ l, 0 ≤ b l :=
          fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
        have hW_one : 1 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) :=
          Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
        have hW_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
          linarith
        rw [hdiff]
        rw [show ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu))).toSection x) =
            (iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x
            from by rw [SmoothCcTensor.toSection_add]; rfl]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i)
          x _ _) ?_
        have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
            cbg i := hcbg i x
        have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            (((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x) ≤
            2 * (KcCr i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
              2 * (KcCu i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
          rw [show (((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x) =
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr).toSection x -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu).toSection x
              from by rw [SmoothCcTensor.toSection_sub]; rfl]
          refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
          exact add_le_add (mul_le_mul_of_nonneg_left (hCr_res x) (by norm_num))
            (mul_le_mul_of_nonneg_left (hCu_res x) (by norm_num))
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              (((iteratedCovGrad (I := I) g₀ 2 2 i
                  (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                    ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
                (iteratedCovGrad (I := I) g₀ 2 2 i
                  (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                    ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x)
            ≤ 2 * cbg i +
              2 * (2 * (KcCr i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
                2 * (KcCu i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3))) := by
              refine add_le_add ?_ (mul_le_mul_of_nonneg_left h2 (by norm_num))
              have := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 2 by norm_num)
              linarith
          _ ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
              have hc1 : 2 * cbg i ≤ 2 * cbg i *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
                nlinarith [hcbg_nn i, hW_one]
              nlinarith [hKcCr_nn i, hKcCu_nn i, hW_nn]
      obtain ⟨hint, hbound_int⟩ := hKI P hPball i hia
      have hF_int : MeasureTheory.Integrable
          (fun x => (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := hint.const_mul _
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
        g₀ 2 (2 + i)
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - (HdCr - HdCu))
        _ hF_int hpt
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      calc (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            ∫ x, Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
          ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            (KI i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left hbound_int ?_
            have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith
        _ = (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    refine ⟨0, fun x => (IsEmpty.false x).elim, ?_, ?_⟩
    · have hz : ‖(0 : SmoothCcTensor g₀ 2 (2 + i))‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]
      have := sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖
      nlinarith [hKtCr_nn, hKtCu_nn]
    · have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
          (0 : SmoothCcTensor g₀ 2 (2 + i))‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]
      have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      have hKc_nn : (0 : ℝ) ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i :=
        mul_nonneg
          (by have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith)
          (hKI_nn i)
      nlinarith

theorem ricciArmOrder0BaseCoeff_perOrder_l2_topSeparated_generic_allOrders
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ∃ Hd : SmoothCcTensor g₀ 2 (2 + i),
            (∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (Hd.toSection x) ≤
                Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) ∧
            ‖Hd‖ ^ 2 ≤ Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 ∧
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - Hd‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨KtCr, hKtCr_nn, KcCr, hKcCr_nn, hCr⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨KtCu, hKtCu_nn, KcCu, hKcCu_nn, hCu⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0CurvCoeff_backgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_iteratedCovGrad_fiberNormSq_bound (I := I) (M := M) g₀ 2 2
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
  obtain ⟨KI, hKI_nn, hKI⟩ := boundedFactorGridWindow_integral_ballUniform_flat_allOrders
    (I := I) (M := M) g₀ a ha_super hR
  refine ⟨2 * KtCr + 2 * KtCu, by linarith, ?_⟩
  refine ⟨fun i => (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i,
    fun i => mul_nonneg
      (by have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith)
      (hKI_nn i), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    obtain ⟨HdCr, hCr_head, hCr_res⟩ := hCr g₁ P htie hδ_le hδ0 hδ i
    obtain ⟨HdCu, hCu_head, hCu_res⟩ := hCu g₁ P htie hδ_le hδ0 hδ i
    refine ⟨HdCr - HdCu, ?_, ?_, ?_⟩
    · intro x
      rw [show ((HdCr - HdCu).toSection x) = HdCr.toSection x - HdCu.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
      have h1 := hCr_head x
      have h2 := hCu_head x
      calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCr.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCu.toSection x)
          ≤ 2 * (KtCr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
            2 * (KtCu * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
              (mul_le_mul_of_nonneg_left h2 (by norm_num))
        _ = (2 * KtCr + 2 * KtCu) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by ring
    · have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((HdCr - HdCu).toSection x) ≤
            (2 * KtCr + 2 * KtCu) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by
        intro x
        rw [show ((HdCr - HdCu).toSection x) = HdCr.toSection x - HdCu.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
        have h1 := hCr_head x
        have h2 := hCu_head x
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              (HdCr.toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCu.toSection x)
            ≤ 2 * (KtCr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
              2 * (KtCu * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) :=
              add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
                (mul_le_mul_of_nonneg_left h2 (by norm_num))
          _ = (2 * KtCr + 2 * KtCu) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by ring
      have hF_int : MeasureTheory.Integrable
          (fun x => (2 * KtCr + 2 * KtCu) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
        (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 2))
          (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)).const_mul _
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
        g₀ 2 (2 + i) (HdCr - HdCu) _ hF_int hpt
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      rw [show (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 from by
        rw [SmoothCcTensor.norm_def (I := I) (M := M)
            (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P),
          tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
            g₀ 0 (2 + (i + 2)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)]]
    · have harm0 : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ =
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
          ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)) := by abel
      have hdiff : iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - (HdCr - HdCu) =
          iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)) := by
        rw [harm0]
        rw [show iteratedCovGrad (I := I) g₀ 2 2 i
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))) =
            iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            (iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
             iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)) from by
          rw [iteratedCovGrad_add (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
            ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))]
          rw [iteratedCovGrad_sub (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)]]
        abel
      have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
                (HdCr - HdCu)).toSection x) ≤
            (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
              Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
        intro x
        set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
        have hb : ∀ l, 0 ≤ b l :=
          fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
        have hW_one : 1 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) :=
          Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
        have hW_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
          linarith
        rw [hdiff]
        rw [show ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu))).toSection x) =
            (iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x
            from by rw [SmoothCcTensor.toSection_add]; rfl]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i)
          x _ _) ?_
        have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
            cbg i := hcbg i x
        have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            (((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x) ≤
            2 * (KcCr i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
              2 * (KcCu i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
          rw [show (((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x) =
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr).toSection x -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu).toSection x
              from by rw [SmoothCcTensor.toSection_sub]; rfl]
          refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
          exact add_le_add (mul_le_mul_of_nonneg_left (hCr_res x) (by norm_num))
            (mul_le_mul_of_nonneg_left (hCu_res x) (by norm_num))
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              (((iteratedCovGrad (I := I) g₀ 2 2 i
                  (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                    ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
                (iteratedCovGrad (I := I) g₀ 2 2 i
                  (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                    ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x)
            ≤ 2 * cbg i +
              2 * (2 * (KcCr i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
                2 * (KcCu i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3))) := by
              refine add_le_add ?_ (mul_le_mul_of_nonneg_left h2 (by norm_num))
              have := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 2 by norm_num)
              linarith
          _ ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
              have hc1 : 2 * cbg i ≤ 2 * cbg i *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
                nlinarith [hcbg_nn i, hW_one]
              nlinarith [hKcCr_nn i, hKcCu_nn i, hW_nn]
      obtain ⟨hint, hbound_int⟩ := hKI P hPball i
      have hF_int : MeasureTheory.Integrable
          (fun x => (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := hint.const_mul _
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
        g₀ 2 (2 + i)
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - (HdCr - HdCu))
        _ hF_int hpt
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      calc (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            ∫ x, Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
          ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            (KI i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left hbound_int ?_
            have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith
        _ = (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    refine ⟨0, fun x => (IsEmpty.false x).elim, ?_, ?_⟩
    · have hz : ‖(0 : SmoothCcTensor g₀ 2 (2 + i))‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]
      have := sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖
      nlinarith [hKtCr_nn, hKtCu_nn]
    · have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
          (0 : SmoothCcTensor g₀ 2 (2 + i))‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]
      have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      have hKc_nn : (0 : ℝ) ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i :=
        mul_nonneg
          (by have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith)
          (hKI_nn i)
      nlinarith

section TopSeparatedKoszulExport

omit [NeZero (Module.finrank ℝ E)] in
theorem rfns_iteratedCovGrad_raisedKoszul_pointwise_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
      10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) :=
  rfns_iteratedCovGrad_raisedKoszul_pointwise (I := I) (M := M) g₀ g₁ T htie i x
set_option linter.unusedVariables false in



omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem grid_prod_int_le
    (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    {R : ℝ} (hR : 0 ≤ R)
    (i : ℕ) (hi1 : 1 ≤ i)
    {Λ : ℝ} (hΛ_nn : 0 ≤ Λ)
    (hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ ^ 2)
    (hNi : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ≤ R)
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hGNP : ∀ j : ℕ, 0 < j → j < i →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
        C * Λ ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)))
    (n : ℕ) (hn_le : n ≤ i) (e : Fin n → ℕ) (he : ∑ m, e m = i) :
    MeasureTheory.Integrable
        (fun x => ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (i : ℝ) * (max Λ (max C 1)) ^ (7 * i) * R ^ 2 := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hi_pos : 0 < i := hi1
  have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi_pos
  have hiR_ne : (i : ℝ) ≠ 0 := ne_of_gt hiR_pos
  have hnn : ∀ (j : ℕ) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) :=
    fun j x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hcont : ∀ j : ℕ, Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) := by
    intro j
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 j P) x]
  have hint : ∀ j : ℕ, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) μ := by
    intro j
    rw [hμ]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + j)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
  have hint_rpow : ∀ (j : ℕ) (p : ℝ), 0 ≤ p → MeasureTheory.Integrable
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) μ := by
    intro j p hp
    have hcp : Continuous (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) :=
      (hcont j).rpow_const (fun x => Or.inr hp)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_prod : MeasureTheory.Integrable
      (fun x => ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) μ := by
    have hcp : Continuous (fun x => ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) :=
      continuous_finset_prod Finset.univ (fun m _ => hcont (e m))
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint_prod, ?_⟩
  set Mbar : ℝ := max Λ (max C 1) with hMbar
  have hMbar1 : (1 : ℝ) ≤ Mbar := le_trans (le_max_right C 1) (le_max_right Λ _)
  have hMbar_nn : 0 ≤ Mbar := le_trans zero_le_one hMbar1
  have hΛ_le : Λ ≤ Mbar := le_max_left _ _
  have hC_le : C ≤ Mbar := le_trans (le_max_left C 1) (le_max_right Λ _)
  set Sset : Finset (Fin n) := Finset.univ.filter (fun m => 0 < e m) with hSset
  set Zset : Finset (Fin n) := Finset.univ.filter (fun m => ¬ (0 < e m)) with hZset
  have hsplit : ∀ x : M,
      (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
          (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
    intro x
    rw [hSset, hZset]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 0 < e m)
      (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))).symm
  have hZbound : ∀ x : M,
      (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤ Λ ^ (2 * Zset.card) := by
    intro x
    calc (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        ≤ ∏ _m ∈ Zset, Λ ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hnn (e m) x)
          intro m hm
          have hem0 : e m = 0 := by have := (Finset.mem_filter.mp hm).2; omega
          rw [hem0]; exact hΛsup x
      _ = Λ ^ (2 * Zset.card) := by rw [Finset.prod_const, ← pow_mul]
  have hZsum0 : ∑ m ∈ Zset, e m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have := (Finset.mem_filter.mp hm).2; omega
  have hSsum : ∑ m ∈ Sset, e m = i := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => 0 < e m) e
    rw [← hSset, ← hZset, hZsum0, add_zero, he] at h
    exact h
  have hScard_pos : 1 ≤ Sset.card := by
    rcases Nat.eq_zero_or_pos Sset.card with h0 | hp
    · exfalso
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hSsum
      omega
    · exact hp
  rcases Nat.lt_or_ge Sset.card 2 with hScard_lt2 | hScard_ge2
  · have hScard1 : Sset.card = 1 := by omega
    obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hScard1
    have hem₀ : e m₀ = i := by
      have hss : ∑ m ∈ Sset, e m = e m₀ := by rw [hm₀, Finset.sum_singleton]
      rw [hss] at hSsum; exact hSsum
    have hSprod : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x; rw [hm₀, Finset.prod_singleton, hem₀]
    have hpt : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x
      rw [hsplit x, hSprod x]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) * Λ ^ (2 * Zset.card) :=
            mul_le_mul_of_nonneg_left (hZbound x) (hnn i x)
        _ = Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := mul_comm _ _
    have hintFi : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) ≤ R ^ 2 := by
      have heq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
        rw [SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P), hμ]
        exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i)
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection)).symm
      rw [heq]
      nlinarith [hNi, norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i P), hR]
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_mono hint_prod ((hint i).const_mul _) hpt
      _ = Λ ^ (2 * Zset.card) * ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * R ^ 2 := mul_le_mul_of_nonneg_left hintFi hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (7 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _)
              (pow_le_pow_right₀ hMbar1 (by omega))
          have e4 : Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (7 * i) * R ^ 2 :=
            mul_le_mul_of_nonneg_right e1 (sq_nonneg R)
          have e5 : Mbar ^ (7 * i) * R ^ 2 ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
            have h1i : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            have hMR : 0 ≤ Mbar ^ (7 * i) * R ^ 2 :=
              mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R)
            calc Mbar ^ (7 * i) * R ^ 2 = 1 * (Mbar ^ (7 * i) * R ^ 2) := by ring
              _ ≤ (i : ℝ) * (Mbar ^ (7 * i) * R ^ 2) := mul_le_mul_of_nonneg_right h1i hMR
              _ = (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by ring
          exact le_trans e4 e5
  · have hem_lt : ∀ m ∈ Sset, e m < i := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hadd : e m + ∑ m' ∈ Sset.erase m, e m' = ∑ m' ∈ Sset, e m' :=
        Finset.add_sum_erase Sset e hm
      rw [hSsum] at hadd
      have herase_ne : (Sset.erase m).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hm]; omega
      obtain ⟨m', hm'⟩ := herase_ne
      have hm'S : m' ∈ Sset := Finset.mem_of_mem_erase hm'
      have hm'pos : 1 ≤ e m' := (Finset.mem_filter.mp hm'S).2
      have hle : e m' ≤ ∑ m'' ∈ Sset.erase m, e m'' :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) hm'
      omega
    have hAMGM : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      have hz_nn : ∀ m ∈ Sset, 0 ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        fun m _ => Real.rpow_nonneg (hnn (e m) x) _
      have hAM := Real.geom_mean_le_arith_mean_weighted Sset (fun m => (e m : ℝ) / i)
        (fun m => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
        hw_nn hw_sum hz_nn
      have hLHS : (∏ m ∈ Sset, ((riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
            ^ ((e m : ℝ) / i)) =
          ∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
        apply Finset.prod_congr rfl
        intro m hm
        have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
        have hemR_ne : (e m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
        rw [← Real.rpow_mul (hnn (e m) x)]
        rw [show ((i : ℝ) / (e m : ℝ)) * ((e m : ℝ) / i) = 1 by field_simp]
        rw [Real.rpow_one]
      rw [hLHS] at hAM
      exact hAM
    have hfactor : ∀ m ∈ Sset,
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
          Mbar ^ (5 * i) * R ^ 2 := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hem_lt_i : e m < i := hem_lt m hm
      have hemR_pos : (0 : ℝ) < (e m : ℝ) := by exact_mod_cast hmpos
      have hemR_ne : (e m : ℝ) ≠ 0 := ne_of_gt hemR_pos
      have hgn := hGNP (e m) hmpos hem_lt_i
      set Ival : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ
        with hIval
      have hIval_nn : 0 ≤ Ival := by
        rw [hIval]; exact integral_nonneg (fun x => Real.rpow_nonneg (hnn (e m) x) _)
      have hθ_nn : 0 ≤ (e m : ℝ) / i := by positivity
      have hθ_le1 : (e m : ℝ) / i ≤ 1 := by
        rw [div_le_one hiR_pos]; exact_mod_cast Nat.le_of_lt hem_lt_i
      have hexp1_nn : 0 ≤ 2 * (1 - (e m : ℝ) / i) := by nlinarith
      have hexp1_le : 2 * (1 - (e m : ℝ) / i) ≤ 2 := by nlinarith
      have hΛpow : Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 : ℕ) := by
        calc Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 * (1 - (e m : ℝ) / i)) :=
              Real.rpow_le_rpow hΛ_nn hΛ_le hexp1_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp1_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbase_le : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (3 : ℕ) := by
        have h1 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) :=
          mul_le_mul hC_le hΛpow (Real.rpow_nonneg hΛ_nn _) hMbar_nn
        calc C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) := h1
          _ = Mbar ^ (3 : ℕ) := by ring
      have hbase_nn : 0 ≤ C * Λ ^ (2 * (1 - (e m : ℝ) / i)) :=
        mul_nonneg hC_nn (Real.rpow_nonneg hΛ_nn _)
      have hIval_eq : Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := by
        rw [← Real.rpow_mul hIval_nn]
        rw [show ((e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 1 by field_simp]
        rw [Real.rpow_one]
      have hM3_one : (1 : ℝ) ≤ Mbar ^ (3 : ℕ) :=
        le_trans hMbar1 (le_self_pow₀ hMbar1 (by norm_num))
      have hidiv : (i : ℝ) / (e m : ℝ) ≤ (i : ℝ) :=
        div_le_self hiR_pos.le (by exact_mod_cast hmpos)
      have hsplit_pow : (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i))
            ^ ((i : ℝ) / (e m : ℝ)) =
          (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) *
            (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Real.mul_rpow hbase_nn (Real.rpow_nonneg hR _)
      have hRcollapse : (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) = R ^ (2 : ℕ) := by
        rw [← Real.rpow_mul hR]
        rw [show (2 * (e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 2 by field_simp]
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbasepow : (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) ≤
          Mbar ^ (5 * i) := by
        calc (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ))
            ≤ (Mbar ^ (3 : ℕ)) ^ ((i : ℝ) / (e m : ℝ)) :=
              Real.rpow_le_rpow hbase_nn hbase_le (by positivity)
          _ ≤ (Mbar ^ (3 : ℕ)) ^ ((i : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hM3_one hidiv
          _ = (Mbar ^ (3 : ℕ)) ^ (i : ℕ) := by rw [Real.rpow_natCast]
          _ = Mbar ^ (3 * i) := by rw [← pow_mul]
          _ ≤ Mbar ^ (5 * i) := pow_le_pow_right₀ hMbar1 (by omega)
      calc Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hIval_eq
        _ ≤ (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i))
              ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hIval_nn _) hgn (by positivity)
        _ = (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) *
              (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hsplit_pow
        _ = (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) * R ^ (2 : ℕ) := by
            rw [hRcollapse]
        _ ≤ Mbar ^ (5 * i) * R ^ 2 := mul_le_mul_of_nonneg_right hbasepow (sq_nonneg R)
    have hSsum_factor : ∑ m ∈ Sset, ((e m : ℝ) / i) *
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
        Mbar ^ (5 * i) * R ^ 2 := by
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      calc ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ)
          ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) * (Mbar ^ (5 * i) * R ^ 2) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul_of_nonneg_left (hfactor m hm) (hw_nn m hm)
        _ = (∑ m ∈ Sset, (e m : ℝ) / i) * (Mbar ^ (5 * i) * R ^ 2) := by rw [Finset.sum_mul]
        _ = Mbar ^ (5 * i) * R ^ 2 := by rw [hw_sum, one_mul]
    have hpt2 : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      rw [hsplit x]
      have hZnn : 0 ≤ ∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
        Finset.prod_nonneg (fun m _ => hnn (e m) x)
      have hsum_nn : 0 ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hnn (e m) x) _))
      calc (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) *
              Λ ^ (2 * Zset.card) :=
            mul_le_mul (hAMGM x) (hZbound x) hZnn hsum_nn
        _ = Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
            mul_comm _ _
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) μ := by
      apply MeasureTheory.integrable_finset_sum
      intro m _
      exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hint_eq : (∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) =
        ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) := by
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m _; rw [MeasureTheory.integral_const_mul]
      · intro m _
        exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_mono hint_prod (hsum_int.const_mul _) hpt2
      _ = Λ ^ (2 * Zset.card) * ∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2) := by
          rw [hint_eq]
          exact mul_le_mul_of_nonneg_left hSsum_factor hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _) (pow_le_pow_right₀ hMbar1 (by omega))
          have e3 : Mbar ^ (2 * i) * Mbar ^ (5 * i) = Mbar ^ (7 * i) := by
            rw [← pow_add]; congr 1; ring
          have e4 : Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2) ≤
              Mbar ^ (2 * i) * (Mbar ^ (5 * i) * R ^ 2) :=
            mul_le_mul_of_nonneg_right e1
              (mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R))
          have e5 : Mbar ^ (7 * i) * R ^ 2 ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
            have h1i : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            have hMR : 0 ≤ Mbar ^ (7 * i) * R ^ 2 :=
              mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R)
            calc Mbar ^ (7 * i) * R ^ 2 = 1 * (Mbar ^ (7 * i) * R ^ 2) := by ring
              _ ≤ (i : ℝ) * (Mbar ^ (7 * i) * R ^ 2) := mul_le_mul_of_nonneg_right h1i hMR
              _ = (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by ring
          calc Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2)
              ≤ Mbar ^ (2 * i) * (Mbar ^ (5 * i) * R ^ 2) := e4
            _ = Mbar ^ (7 * i) * R ^ 2 := by rw [← mul_assoc, e3]
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := e5


end TopSeparatedKoszulExport

end TopSeparatedResidualIntegrator

end Connection
end Integral
end DifferentialGeometry

end
