import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureRefoldMonomialFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldFamilyJointSmoothness
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldLieCovDerivFamily
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldEndoArmGridWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldCovDerivArmPairTrace


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
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

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem bdMonoRefold_appCc_eq_pairTrace_appCc (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (G : SmoothCcTensor g₀ 0 4) (σ : Equiv.Perm (Fin 4)) :
    operatorFieldApply (I := I) (M := M) g₀ 2 2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (domDomCongrSection (I := I) g₀
                (σ.trans (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) G)))) S =
      operatorFieldApply (I := I) (M := M) g₀ 4 2
        (curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S) σ) G := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCc_toSection, appCc_toSection]
  apply ContinuousLinearMap.ext
  intro t
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [bdTensor0S_zero_rank_decomp (I := I) (M := M) x t]
  simp only [map_smul, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  congr 1
  rw [bdPairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    (domDomCongrSection (I := I) g₀
      (σ.trans (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) G) x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x)
      (unitTensor (I := I) (M := M) x)) v]
  rw [show ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ S)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S) σ).toSection x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from G.toSection x)
        (unitTensor (I := I) (M := M) x))) =
    curvatureActionMonomialTrace (I := I) (M := M) g₁
      (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from G.toSection x)
        (unitTensor (I := I) (M := M) x)) from rfl]
  rw [curvatureActionMonomialTrace, curvatureRefoldMonomialFibFixedFrame_toModel]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  refine congrArg₂ (· * ·) rfl ?_
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from G.toSection x)
        (unitTensor (I := I) (M := M) x)) =
    unitModel (I := I) (M := M) g₀ 4 G x from rfl]
  refine congrArg _ ?_
  funext i
  rw [Equiv.trans_apply]
  generalize σ i = k
  fin_cases k <;> rfl

omit [BoundarylessManifold I M] in
private theorem bdLiePairTraceFamily_appCc_eq_familySecondGradient
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ) (s : ℝ) :
    operatorFieldApply (I := I) (M := M) g₀ 2 2
        (deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ q ε s) T =
      operatorFieldApply (I := I) (M := M) g₀ 4 2
        (deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε s)
        (iteratedCovGrad (I := I) g₀ 0 2 2 T) := by
  rw [deTurckLieCovDerivRefoldPairTraceFamily, deTurckLieCovDerivRefoldC2Family,
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [appCc_smul_left, appCc_add_left]
  rw [bdMonoRefold_appCc_eq_pairTrace_appCc (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (iteratedCovGrad (I := I) g₀ 0 2 2 T) (q 0),
    bdMonoRefold_appCc_eq_pairTrace_appCc (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (iteratedCovGrad (I := I) g₀ 0 2 2 T)
      ((q 0).trans (Equiv.swap (0 : Fin 4) 1)),
    bdMonoRefold_appCc_eq_pairTrace_appCc (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (iteratedCovGrad (I := I) g₀ 0 2 2 T) (q 1),
    bdMonoRefold_appCc_eq_pairTrace_appCc (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (iteratedCovGrad (I := I) g₀ 0 2 2 T)
      ((q 1).trans (Equiv.swap (0 : Fin 4) 1)),
    bdMonoRefold_appCc_eq_pairTrace_appCc (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (iteratedCovGrad (I := I) g₀ 0 2 2 T) (q 2),
    bdMonoRefold_appCc_eq_pairTrace_appCc (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (iteratedCovGrad (I := I) g₀ 0 2 2 T)
      ((q 2).trans (Equiv.swap (0 : Fin 4) 1))]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma lrRealizedFam_zero (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ) :
    realizedFam (I := I) g₀ T 0 hδ hδZ 0 = g₀ := by
  by_cases h : |1 - (0 : ℝ)| * δ + |(0 : ℝ)| * δ < 1
  · refine riemannianMetric_eq_of_inner _ _ (fun b v w => ?_)
    have hmem : (0 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ) := Set.mem_setOf.mpr h
    rw [realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hmem b v w,
      convexPerturbation_zero]
    have hz : ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) b v w = 0 := by
      rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
      ring
    rw [hz, add_zero]
  · rw [realizedFam, dif_neg h]


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lrKoszulCovec_congr {g g' : SmoothRiemannianMetric I M} (h : g = g')
    (S : SmoothCcTensor g 0 2) (S' : SmoothCcTensor g' 0 2)
    (hs : HEq S S') (x : M) (u ζ : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g S x u ζ = linearizedKoszulCovec (I := I) g' S' x u ζ := by
  subst h
  rw [eq_of_heq hs]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lrSymmS_eq_self (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (hsymm : ∀ (x : M) (u w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ S x u w = smoothCcTensorBilinForm (I := I) g₀ S x w u) :
    ccTensor02Symm (I := I) (M := M) g₀ S = S := by
  have hswap : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    rw [domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g₀ 2 S x ![u, w] =
          unitModel (I := I) (M := M) g₀ 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x w u]
      exact hsymm x u w
    have hveta : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  have htwo : S + S = (2 : ℝ) • S := (two_smul ℝ S).symm
  rw [ccTensor02Symm, hswap, htwo, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]


private lemma lrConnDiff_linearization (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M) (u ζ : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x u ζ =
      s • DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) x
        (linearizedKoszulCovec (I := I) g₀ T x u ζ) := by
  classical
  have h0_mem : (0 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt ⟨le_refl (0 : ℝ), zero_le_one⟩
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hzero := lrRealizedFam_zero (I := I) (M := M) g₀ T hδ hδZ
  have hkey := connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T 0 hδ_lt hδ hδ_lt hδZ
    h0_mem hs_mem x u ζ
  rw [sub_zero] at hkey
  have hvel : HEq (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) T := by
    rw [show realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0 =
        ccTensorRetagMetric (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
          (ccTensor02Symm (I := I) (M := M) g₀ (T - 0)) from rfl]
    rw [sub_zero, lrSymmS_eq_self (I := I) (M := M) g₀ T hTsymm]
    rw [hzero]
    exact HEq.rfl
  have hlkc : linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
      (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) x u ζ =
      linearizedKoszulCovec (I := I) g₀ T x u ζ :=
    lrKoszulCovec_congr (I := I) (M := M) hzero
      (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) T hvel x u ζ
  rw [hlkc] at hkey
  calc PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x u ζ
      = PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          (realizedFam (I := I) g₀ T 0 hδ hδZ 0) x u ζ := by rw [hzero]
    _ = s • DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) x
          (linearizedKoszulCovec (I := I) g₀ T x u ζ) := hkey


private lemma lrConnDiff_inner (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M) (u ζ z : TangentSpace I x) :
    (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x u ζ) z =
      s * linearizedKoszulCovec (I := I) g₀ T x u ζ z := by
  rw [lrConnDiff_linearization (I := I) (M := M) g₀ T hδ_lt hδ hδZ hTsymm hs x u ζ,
    map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
    DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp]


private def linearizedKoszulTensor (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    SmoothCcTensor g₀ 0 3 :=
  (1 / 2 : ℝ) •
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2)
        (covGrad (I := I) (M := M) g₀ 0 2 T)
      + domDomCongrSection (I := I) g₀ (finRotate 3)
        (covGrad (I := I) (M := M) g₀ 0 2 T)
      - domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
        (covGrad (I := I) (M := M) g₀ 0 2 T))

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lrKT_unitModel (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (z u ζ : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x ![z, u, ζ] =
      linearizedKoszulCovec (I := I) g₀ T x u ζ z := by
  rw [linearizedKoszulTensor, bdUnitModel_smul, bdUnitModel_sub, bdUnitModel_add]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.add_apply, smul_eq_mul]
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel]
  simp only [ContinuousMultilinearMap.domDomCongr_apply]
  rw [linearizedKoszulCovec_apply]
  have h1 : (fun i => (![z, u, ζ] : Fin 3 → TangentSpace I x)
      ((Equiv.swap (0 : Fin 3) 2) i)) = ![ζ, u, z] := by
    funext i
    fin_cases i <;> rfl
  have h2 : (fun i => (![z, u, ζ] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
      ![u, ζ, z] := by
    funext i
    fin_cases i <;> rfl
  have h3 : (fun i => (![z, u, ζ] : Fin 3 → TangentSpace I x)
      ((Equiv.swap (1 : Fin 3) 2) i)) = ![z, ζ, u] := by
    funext i
    fin_cases i <;> rfl
  rw [h1, h2, h3]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lrUnitEval_tsmdiffAt (g : SmoothRiemannianMetric I M) (n : ℕ)
    (W : SmoothCcTensor g 0 n) (x : M) :
    TensorSectionMDiffAt (I := I) n
      (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace n I y from
          W.toSection y) (unitZeroSec (I := I) (M := M) y)) x := by
  have hsm := ContMDiff.clm_bundle_apply (b := id) W.toSection.contMDiff
    (unitZeroSec (I := I) (M := M)).contMDiff
  exact ((hsm x).mdifferentiableAt (by simp))

omit [NeZero (Module.finrank ℝ E)] in
private lemma lrUnitModel_covGrad_eval (g : SmoothRiemannianMetric I M) (n : ℕ)
    (W : SmoothCcTensor g 0 n) (x : M) (v : Fin (n + 1) → TangentSpace I x) :
    unitModel (I := I) (M := M) g (n + 1) (covGrad (I := I) (M := M) g 0 n W) x v =
      Tensor0SSpace.toModel
        (show Tensor0SSpace n I x from
          Tensor0SNabla.tensor0SCovariantDerivative I M n (LeviCivita (I := I) g)
            (fun y : M =>
              (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace n I y from
                W.toSection y) (unitZeroSec (I := I) (M := M) y)) x (v 0))
        (Matrix.vecTail v) := by
  rw [unitModel]
  rw [show unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x from rfl]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 n W x
    (unitZeroSec (I := I) (M := M) x) v]
  congr 1
  rw [tensorCovDerivAt_def]
  rw [TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) 0 n
    (LeviCivita (I := I) g) W.toSection (unitZeroSec (I := I) (M := M)) x (v 0)]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
      (fun y : M => unitZeroSec (I := I) (M := M) y) x (v 0)) = 0 from
    Tensor0SNabla.tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x (v 0)]
  rw [map_zero, sub_zero]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lrExtDerivFun_apply_scalar (f : M → ℝ) {x : M} (v : TangentSpace I x) :
    extDerivFun (I := I) f x v = mfderiv I 𝓘(ℝ, ℝ) f x v := by
  simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
  rfl


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma lrCovDerivConnDiff_self_zero (g₀ : SmoothRiemannianMetric I M)
    (x : M) (v0 p q : TangentSpace I x) :
    covDerivConnDiff (I := I) g₀ g₀
        (smoothExtensionTangent (I := I) x v0)
        (smoothExtensionTangent (I := I) x q)
        (smoothExtensionTangent (I := I) x p) x = 0 := by
  classical
  have hexpand : covDerivConnDiff (I := I) g₀ g₀
      (smoothExtensionTangent (I := I) x v0)
      (smoothExtensionTangent (I := I) x q)
      (smoothExtensionTangent (I := I) x p) x =
      (LeviCivita (I := I) g₀).toFun
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₀)
            (smoothExtensionTangent (I := I) x q) (smoothExtensionTangent (I := I) x p)) x
          (smoothExtensionTangent (I := I) x v0 x)
        - PDE.DeTurck.connDiff (I := I) g₀ g₀ x (smoothExtensionTangent (I := I) x p x)
            (covApply (LeviCivita (I := I) g₀)
              (smoothExtensionTangent (I := I) x v0)
              (smoothExtensionTangent (I := I) x q) x)
        - PDE.DeTurck.connDiff (I := I) g₀ g₀ x
            (covApply (LeviCivita (I := I) g₀)
              (smoothExtensionTangent (I := I) x v0)
              (smoothExtensionTangent (I := I) x p) x)
            (smoothExtensionTangent (I := I) x q x) := rfl
  rw [hexpand]
  have hdz : diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₀)
      (smoothExtensionTangent (I := I) x q) (smoothExtensionTangent (I := I) x p) =
      (0 : ℝ) • smoothExtensionTangent (I := I) x v0 := by
    funext b
    rw [Pi.smul_apply, zero_smul]
    change PDE.DeTurck.connDiff (I := I) g₀ g₀ b
        (smoothExtensionTangent (I := I) x p b)
        (smoothExtensionTangent (I := I) x q b) = 0
    exact bdConnDiff_self_apply (I := I) (M := M) g₀ b _ _
  rw [hdz]
  have hσX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (smoothExtensionTangent (I := I) x v0 b)) x :=
    smoothExtensionTangent_mdiff (I := I) x v0 x
  have hsmul := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.smul_const
    (σ := smoothExtensionTangent (I := I) x v0) (x := x) (0 : ℝ) hσX (Set.mem_univ x)
  rw [hsmul, ContinuousLinearMap.smul_apply]
  rw [bdConnDiff_self_apply (I := I) (M := M) g₀ x, bdConnDiff_self_apply (I := I) (M := M) g₀ x,
    zero_smul]
  simp

set_option maxHeartbeats 12800000 in

private theorem lrKernel_inner (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M) (v0 v1 p q : TangentSpace I x) :
    (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
        (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x v0 p q) v1 =
      s * unitModel (I := I) (M := M) g₀ 4
          (covGrad (I := I) (M := M) g₀ 0 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T)) x
          ![v0, v1, p, q]
        - (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
            (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x p q)
            (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x v1 v0)
        - (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
            (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x
              (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x p v0)
              q) v1
        - (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
            (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x p
              (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x q v0))
            v1 := by
  classical
  by_cases hs0 : s = 0
  · subst hs0
    rw [lrRealizedFam_zero (I := I) (M := M) g₀ T hδ hδZ]
    have hker0 : connDiffCovDerivOp (I := I) g₀ g₀ x v0 p q = 0 := by
      rw [Integral.Connection.dLaCovKernel_backgroundSplit (I := I) (M := M) g₀ g₀ g₀ x v0 p q]
      simp only [bdConnDiff_self_apply (I := I) (M := M) g₀ x, sub_self, add_zero]
    rw [hker0]
    simp only [bdConnDiff_self_apply (I := I) (M := M) g₀ x, map_zero,
      ContinuousLinearMap.zero_apply, zero_mul, sub_self]
  · have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
    rw [Integral.Connection.dLaCovKernel_backgroundSplit (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x v0 p q]
    rw [lrCovDerivConnDiff_self_zero (I := I) (M := M) g₀ x v0 p q, sub_zero]
    set gs := realizedFam (I := I) g₀ T 0 hδ hδZ s with hgs_def
    set X0 : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v0 with hX0_def
    set Z1 : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v1 with hZ1_def
    set Pe : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x p with hPe_def
    set Qe : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x q with hQe_def
    have hX0x : X0 x = v0 := smoothExtensionTangent_eq (I := I) x v0
    have hZ1x : Z1 x = v1 := smoothExtensionTangent_eq (I := I) x v1
    have hPex : Pe x = p := smoothExtensionTangent_eq (I := I) x p
    have hQex : Qe x = q := smoothExtensionTangent_eq (I := I) x q
    set Ψ : Π b : M, TangentSpace I b := fun b =>
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) gs b
        (linearizedKoszulCovec (I := I) g₀ T b (Pe b) (Qe b)) with hΨ_def
    have hpoint : ∀ (b : M) (u ζ : TangentSpace I b),
        PDE.DeTurck.connDiff (I := I) gs g₀ b u ζ =
          s • DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) gs b
            (linearizedKoszulCovec (I := I) g₀ T b u ζ) :=
      fun b u ζ => lrConnDiff_linearization (I := I) (M := M) g₀ T hδ_lt hδ hδZ hTsymm hs b u ζ
    have hinner_cd : ∀ (b : M) (u ζ z : TangentSpace I b),
        gs.inner b (PDE.DeTurck.connDiff (I := I) gs g₀ b u ζ) z =
          s * linearizedKoszulCovec (I := I) g₀ T b u ζ z :=
      fun b u ζ z => lrConnDiff_inner (I := I) (M := M) g₀ T hδ_lt hδ hδZ hTsymm hs b u ζ z
    have hconn_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (PDE.DeTurck.connDiff (I := I) gs g₀ b (Pe b) (Qe b))) :=
      PDE.DeTurck.connDiff_contMDiff (I := I) gs g₀
        (smoothExtensionTangent_contMDiff (I := I) x p)
        (smoothExtensionTangent_contMDiff (I := I) x q)
    have hΨ_eq : Ψ = fun b : M => s⁻¹ •
        PDE.DeTurck.connDiff (I := I) gs g₀ b (Pe b) (Qe b) := by
      funext b
      rw [hΨ_def]
      rw [hpoint b (Pe b) (Qe b), smul_smul, inv_mul_cancel₀ hs0, one_smul]
    have hΨ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (Ψ b)) := by
      have hsmul' := ContMDiff.smul_section
        (f := fun _ : M => s⁻¹)
        (s := fun b : M => PDE.DeTurck.connDiff (I := I) gs g₀ b (Pe b) (Qe b))
        contMDiff_const hconn_smooth
      refine hsmul'.congr (fun b => ?_)
      refine congrArg (TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b) ?_
      change Ψ b = ((fun _ : M => s⁻¹) • fun b : M =>
        PDE.DeTurck.connDiff (I := I) gs g₀ b (Pe b) (Qe b)) b
      rw [show ((fun _ : M => s⁻¹) • fun b : M =>
          PDE.DeTurck.connDiff (I := I) gs g₀ b (Pe b) (Qe b)) b =
          s⁻¹ • PDE.DeTurck.connDiff (I := I) gs g₀ b (Pe b) (Qe b) from rfl]
      exact congrFun hΨ_eq b
    have hσΨ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (Ψ b)) x :=
      (hΨ_smooth x).mdifferentiableAt (by simp)
    have hσZ1 : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (Z1 b)) x :=
      smoothExtensionTangent_mdiff (I := I) x v1 x
    have hexpand : covDerivConnDiff (I := I) g₀ gs X0 Qe Pe x =
        (LeviCivita (I := I) g₀).toFun
            (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) gs) Qe Pe) x (X0 x)
          - PDE.DeTurck.connDiff (I := I) gs g₀ x (Pe x)
              (covApply (LeviCivita (I := I) g₀) X0 Qe x)
          - PDE.DeTurck.connDiff (I := I) gs g₀ x
              (covApply (LeviCivita (I := I) g₀) X0 Pe x) (Qe x) := rfl
    have hdiffSec : diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) gs) Qe Pe =
        s • Ψ := by
      funext b
      rw [Pi.smul_apply]
      change PDE.DeTurck.connDiff (I := I) gs g₀ b (Pe b) (Qe b) = s • Ψ b
      rw [hΨ_def]
      exact hpoint b (Pe b) (Qe b)
    have hsmul := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.smul_const
      (σ := Ψ) (x := x) s hσΨ (Set.mem_univ x)
    have hE2 : gs.inner x (covDerivConnDiff (I := I) g₀ gs X0 Qe Pe x) v1 =
        s * gs.inner x ((LeviCivita (I := I) g₀).toFun Ψ x v0) v1
          - gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x p
              (covApply (LeviCivita (I := I) g₀) X0 Qe x)) v1
          - gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x
              (covApply (LeviCivita (I := I) g₀) X0 Pe x) q) v1 := by
      rw [hexpand, hdiffSec, hsmul, hX0x, hPex, hQex]
      rw [ContinuousLinearMap.smul_apply]
      rw [map_sub, map_sub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hmc : directionalDeriv (I := I) (fun b : M => gs.inner b (Ψ b) (Z1 b)) x (X0 x)
        - gs.inner x ((LeviCivita (I := I) gs).toFun Ψ x (X0 x)) (Z1 x)
        - gs.inner x (Ψ x) ((LeviCivita (I := I) gs).toFun Z1 x (X0 x)) = 0 :=
      metricCovDeriv_self_eq_zero (I := I) gs hσΨ hσZ1
    rw [hX0x, hZ1x] at hmc
    have hΨhat : (LeviCivita (I := I) gs).toFun Ψ x v0 =
        (LeviCivita (I := I) g₀).toFun Ψ x v0
          + PDE.DeTurck.connDiff (I := I) gs g₀ x (Ψ x) v0 := by
      have h := PDE.DeTurck.connDiff_apply (I := I) gs g₀ (σ := Ψ) hσΨ v0
      rw [h]
      abel
    have hZ1hat : (LeviCivita (I := I) gs).toFun Z1 x v0 =
        (LeviCivita (I := I) g₀).toFun Z1 x v0
          + PDE.DeTurck.connDiff (I := I) gs g₀ x (Z1 x) v0 := by
      have h := PDE.DeTurck.connDiff_apply (I := I) gs g₀ (σ := Z1) hσZ1 v0
      rw [h]
      abel
    rw [hZ1x] at hZ1hat
    have hΨval : Ψ x = DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) gs x
        (linearizedKoszulCovec (I := I) g₀ T x p q) := by
      rw [hΨ_def]
      change DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) gs x
          (linearizedKoszulCovec (I := I) g₀ T x (Pe x) (Qe x)) = _
      rw [hPex, hQex]
    have hΨinner : ∀ w : TangentSpace I x, gs.inner x (Ψ x) w =
        unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x ![w, p, q] := by
      intro w
      rw [hΨval, DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp,
        lrKT_unitModel (I := I) (M := M) g₀ T x w p q]
    set Z1s : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x v1,
        smoothExtensionTangent_contMDiff (I := I) x v1⟩ with hZ1s_def
    set Ps : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x p,
        smoothExtensionTangent_contMDiff (I := I) x p⟩ with hPs_def
    set Qs : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x q,
        smoothExtensionTangent_contMDiff (I := I) x q⟩ with hQs_def
    set KTsec : Π y : M, Tensor0SSpace 3 I y := fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
        (linearizedKoszulTensor (I := I) (M := M) g₀ T).toSection y) (unitZeroSec (I := I) (M := M) y)
      with hKTsec_def
    have hKTsec_toModel : ∀ (y : M) (w : Fin 3 → TangentSpace I y),
        Tensor0SSpace.toModel (KTsec y) w =
          unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) y w := by
      intro y w
      rw [hKTsec_def]
      rw [unitModel, show unitTensor (I := I) (M := M) y =
        unitZeroSec (I := I) (M := M) y from rfl]
    have hscal_eq : (fun b : M => gs.inner b (Ψ b) (Z1 b)) =
        Tensor0SNabla.scalarFn I M
          (fun y : M => Tensor0SNabla.curriedSection I M
            (fun z : M => Tensor0SNabla.curriedSection I M
              (fun u : M => Tensor0SNabla.curriedSection I M KTsec u (Z1s u)) z (Ps z))
            y (Qs y)) := by
      funext b
      rw [curried3_toModel_eval (I := I) (M := M) KTsec Z1s Ps Qs b]
      rw [hKTsec_toModel b ![Z1s b, Ps b, Qs b]]
      change gs.inner b (Ψ b) (Z1 b) =
        unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) b ![Z1 b, Pe b, Qe b]
      rw [hΨ_def]
      change gs.inner b (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) gs b
          (linearizedKoszulCovec (I := I) g₀ T b (Pe b) (Qe b))) (Z1 b) = _
      rw [DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp,
        lrKT_unitModel (I := I) (M := M) g₀ T b (Z1 b) (Pe b) (Qe b)]
    have hW_mdiff : TensorSectionMDiffAt (I := I) 3 KTsec x := by
      rw [hKTsec_def]
      exact lrUnitEval_tsmdiffAt (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
    have hpeel := peel3_core (I := I) (M := M) g₀ KTsec hW_mdiff Z1s Ps Qs v0
    have hZ1s_coe : (fun y : M => (Z1s y : TangentSpace I y)) = Z1 := rfl
    have hPs_coe : (fun y : M => (Ps y : TangentSpace I y)) = Pe := rfl
    have hQs_coe : (fun y : M => (Qs y : TangentSpace I y)) = Qe := rfl
    have hZ1sx : (Z1s x : TangentSpace I x) = v1 := smoothExtensionTangent_eq (I := I) x v1
    have hPsx : (Ps x : TangentSpace I x) = p := smoothExtensionTangent_eq (I := I) x p
    have hQsx : (Qs x : TangentSpace I x) = q := smoothExtensionTangent_eq (I := I) x q
    rw [hZ1s_coe, hPs_coe, hQs_coe, hZ1sx, hPsx, hQsx] at hpeel
    have hbridge : unitModel (I := I) (M := M) g₀ 4
        (covGrad (I := I) (M := M) g₀ 0 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T)) x
        ![v0, v1, p, q] =
        Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
            KTsec x v0) ![v1, p, q] := by
      have h := lrUnitModel_covGrad_eval (I := I) (M := M) g₀ 3
        (linearizedKoszulTensor (I := I) (M := M) g₀ T) x ![v0, v1, p, q]
      rw [h]
      rw [show (![v0, v1, p, q] : Fin 4 → TangentSpace I x) 0 = v0 from rfl]
      rw [show Matrix.vecTail (![v0, v1, p, q] : Fin 4 → TangentSpace I x) = ![v1, p, q] from by
        funext k
        fin_cases k <;> rfl]
    have hED : directionalDeriv (I := I) (fun b : M => gs.inner b (Ψ b) (Z1 b)) x v0 =
        extDerivFun (I := I) (Tensor0SNabla.scalarFn I M
          (fun y : M => Tensor0SNabla.curriedSection I M
            (fun z : M => Tensor0SNabla.curriedSection I M
              (fun u : M => Tensor0SNabla.curriedSection I M KTsec u (Z1s u)) z (Ps z))
            y (Qs y))) x v0 := by
      rw [directionalDeriv_eq, lrExtDerivFun_apply_scalar, hscal_eq]
      rfl
    have hKW : ∀ (a b c : TangentSpace I x),
        Tensor0SSpace.toModel (KTsec x) ![a, b, c] =
          unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x ![a, b, c] :=
      fun a b c => hKTsec_toModel x ![a, b, c]
    rw [hKW, hKW, hKW] at hpeel
    have hQL3 : gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x p
        (covApply (LeviCivita (I := I) g₀) X0 Qe x)) v1 =
        s * unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
          ![v1, p, (LeviCivita (I := I) g₀).toFun Qe x v0] := by
      rw [hinner_cd x p (covApply (LeviCivita (I := I) g₀) X0 Qe x) v1]
      rw [show covApply (LeviCivita (I := I) g₀) X0 Qe x =
        (LeviCivita (I := I) g₀).toFun Qe x (X0 x) from rfl, hX0x]
      rw [← lrKT_unitModel (I := I) (M := M) g₀ T x v1 p
        ((LeviCivita (I := I) g₀).toFun Qe x v0)]
    have hQL2 : gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x
        (covApply (LeviCivita (I := I) g₀) X0 Pe x) q) v1 =
        s * unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
          ![v1, (LeviCivita (I := I) g₀).toFun Pe x v0, q] := by
      rw [hinner_cd x (covApply (LeviCivita (I := I) g₀) X0 Pe x) q v1]
      rw [show covApply (LeviCivita (I := I) g₀) X0 Pe x =
        (LeviCivita (I := I) g₀).toFun Pe x (X0 x) from rfl, hX0x]
      rw [← lrKT_unitModel (I := I) (M := M) g₀ T x v1
        ((LeviCivita (I := I) g₀).toFun Pe x v0) q]
    have hQ0 : gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x
        (PDE.DeTurck.connDiff (I := I) gs g₀ x p q) v0) v1 =
        s * gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x (Ψ x) v0) v1 := by
      have hcdpq : PDE.DeTurck.connDiff (I := I) gs g₀ x p q = s • Ψ x := by
        rw [hΨval]
        exact hpoint x p q
      rw [hcdpq]
      rw [show PDE.DeTurck.connDiff (I := I) gs g₀ x (s • Ψ x) v0 =
          s • PDE.DeTurck.connDiff (I := I) gs g₀ x (Ψ x) v0 from by
        rw [map_smul, ContinuousLinearMap.smul_apply]]
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hQ1 : gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x p q)
        (PDE.DeTurck.connDiff (I := I) gs g₀ x v1 v0) =
        s * gs.inner x (Ψ x) (PDE.DeTurck.connDiff (I := I) gs g₀ x v1 v0) := by
      rw [hinner_cd x p q (PDE.DeTurck.connDiff (I := I) gs g₀ x v1 v0)]
      rw [hΨval, DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp]
    have hΨZ1hat : gs.inner x (Ψ x) ((LeviCivita (I := I) gs).toFun Z1 x v0) =
        unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
            ![(LeviCivita (I := I) g₀).toFun Z1 x v0, p, q]
          + gs.inner x (Ψ x) (PDE.DeTurck.connDiff (I := I) gs g₀ x v1 v0) := by
      rw [hZ1hat, map_add]
      rw [hΨinner ((LeviCivita (I := I) g₀).toFun Z1 x v0)]
    have hmc' : directionalDeriv (I := I) (fun b : M => gs.inner b (Ψ b) (Z1 b)) x v0 =
        gs.inner x ((LeviCivita (I := I) g₀).toFun Ψ x v0) v1
          + gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x (Ψ x) v0) v1
          + (unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
              ![(LeviCivita (I := I) g₀).toFun Z1 x v0, p, q]
            + gs.inner x (Ψ x) (PDE.DeTurck.connDiff (I := I) gs g₀ x v1 v0)) := by
      have h1 : gs.inner x ((LeviCivita (I := I) gs).toFun Ψ x v0) v1 =
          gs.inner x ((LeviCivita (I := I) g₀).toFun Ψ x v0) v1
            + gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x (Ψ x) v0) v1 := by
        rw [hΨhat, map_add, ContinuousLinearMap.add_apply]
      rw [← hΨZ1hat, ← h1]
      linarith [hmc]
    have hpeel' : Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
          KTsec x v0) ![v1, p, q] =
        directionalDeriv (I := I) (fun b : M => gs.inner b (Ψ b) (Z1 b)) x v0
          - unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
              ![(LeviCivita (I := I) g₀).toFun Z1 x v0, p, q]
          - unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
              ![v1, (LeviCivita (I := I) g₀).toFun Pe x v0, q]
          - unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
              ![v1, p, (LeviCivita (I := I) g₀).toFun Qe x v0] := by
      rw [hED]
      exact hpeel
    have hE3 : s * gs.inner x ((LeviCivita (I := I) g₀).toFun Ψ x v0) v1 =
        s * unitModel (I := I) (M := M) g₀ 4
            (covGrad (I := I) (M := M) g₀ 0 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T)) x
            ![v0, v1, p, q]
          + s * unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
              ![v1, (LeviCivita (I := I) g₀).toFun Pe x v0, q]
          + s * unitModel (I := I) (M := M) g₀ 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T) x
              ![v1, p, (LeviCivita (I := I) g₀).toFun Qe x v0]
          - s * gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x (Ψ x) v0) v1
          - s * gs.inner x (Ψ x) (PDE.DeTurck.connDiff (I := I) gs g₀ x v1 v0) := by
      rw [hbridge, hpeel', hmc']
      ring
    rw [show (gs.inner x) (covDerivConnDiff (I := I) g₀ gs X0 Qe Pe x
        + PDE.DeTurck.connDiff (I := I) gs g₀ x
            (PDE.DeTurck.connDiff (I := I) gs g₀ x p q) v0
        - PDE.DeTurck.connDiff (I := I) gs g₀ x
            (PDE.DeTurck.connDiff (I := I) gs g₀ x p v0) q
        - PDE.DeTurck.connDiff (I := I) gs g₀ x p
            (PDE.DeTurck.connDiff (I := I) gs g₀ x q v0)) v1 =
        gs.inner x (covDerivConnDiff (I := I) g₀ gs X0 Qe Pe x) v1
          + gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x
              (PDE.DeTurck.connDiff (I := I) gs g₀ x p q) v0) v1
          - gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x
              (PDE.DeTurck.connDiff (I := I) gs g₀ x p v0) q) v1
          - gs.inner x (PDE.DeTurck.connDiff (I := I) gs g₀ x p
              (PDE.DeTurck.connDiff (I := I) gs g₀ x q v0)) v1 from by
      rw [map_sub, map_sub, map_add]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]]
    rw [hE2, hQL3, hQL2, hQ0, hQ1]
    linarith [hE3]


private def connDiffGmLoweredTensor (g₀ gm : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 3
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 (fullRaisedEndoField (I := I) (M := M) gm g₀))
    (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ gm))

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lrOmegaHat_unitModel_apply (g₀ gm : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm) x m =
      gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 1) (m 2)) (m 0) := by
  rw [unitModel]
  rw [show (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm).toSection x
        (unitTensor (I := I) (M := M) x) =
      slotInsertEndoFib (I := I) (M := M) 3 0 x
        (fullRaisedEndoField (I := I) (M := M) gm g₀ x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (connDiffLoweredCc (I := I) g₀ gm)).toSection x)
          (unitTensor (I := I) (M := M) x)) from by
    rw [connDiffGmLoweredTensor, appCcRS_toSection]
    rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (connDiffLoweredCc (I := I) g₀ gm)).toSection x)
          (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (connDiffLoweredCc (I := I) g₀ gm)) x from rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 3 =>
      Function.update (fun k : Fin 3 => (m k : E)) 0
        (fullRaisedEndoField (I := I) (M := M) gm g₀ x ((fun k : Fin 3 => (m k : E)) 0))
        ((finRotate 3) i)) =
    (fun i : Fin 3 => (((![m 1, m 2,
      (show TangentSpace I x from
        Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) gm g₀ x (m 0))] :
      Fin 3 → TangentSpace I x)) i : E)) from by
    funext i
    fin_cases i
    · change Function.update (fun k : Fin 3 => (m k : E)) 0
          (fullRaisedEndoField (I := I) (M := M) gm g₀ x (m 0)) ((finRotate 3) 0) = (m 1 : E)
      rw [show (finRotate 3) (0 : Fin 3) = 1 from by decide]
      rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]
    · change Function.update (fun k : Fin 3 => (m k : E)) 0
          (fullRaisedEndoField (I := I) (M := M) gm g₀ x (m 0)) ((finRotate 3) 1) = (m 2 : E)
      rw [show (finRotate 3) (1 : Fin 3) = 2 from by decide]
      rw [Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
    · change Function.update (fun k : Fin 3 => (m k : E)) 0
          (fullRaisedEndoField (I := I) (M := M) gm g₀ x (m 0)) ((finRotate 3) 2) =
        (show TangentSpace I x from
          Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) gm g₀ x (m 0))
      rw [show (finRotate 3) (2 : Fin 3) = 0 from by decide]
      rw [Function.update_self]
      rfl]
  rw [bdConnDiffLoweredCc_unitModel_apply (I := I) (M := M) g₀ gm x]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  exact bdG0_inner_lambda (I := I) (M := M) g₀ gm x
    (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 1) (m 2)) (m 0)


private def connDiffQuadraticPairedTensor (g₀ gm : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
    (armSlotEndoCc (I := I) (M := M) g₀ 2 (connDiffEndo (I := I) (M := M) g₀ gm))
    (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm)


private def connDiffQuadraticComposedTensor (g₀ gm : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
    (armSlotEndoCc (I := I) (M := M) g₀ 2 (connDiffEndo (I := I) (M := M) g₀ gm))
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1)
      (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm))

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lrArmSlotTuple (g₀ gm : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    (Function.update (Matrix.vecTail (fun k : Fin 4 => (m k : E))) 0
        (connDiffEndo (I := I) (M := M) g₀ gm x ((fun k : Fin 4 => (m k : E)) 0)
          (Matrix.vecTail (fun k : Fin 4 => (m k : E)) 0))) =
      (fun i : Fin 3 => (((![(show TangentSpace I x from
        PDE.DeTurck.connDiff (I := I) gm g₀ x (m 0) (m 1)), m 2, m 3] :
        Fin 3 → TangentSpace I x)) i : E)) := by
  funext k
  fin_cases k
  · change Function.update (Matrix.vecTail (fun k : Fin 4 => (m k : E))) 0
        (connDiffEndo (I := I) (M := M) g₀ gm x ((fun k : Fin 4 => (m k : E)) 0)
          (Matrix.vecTail (fun k : Fin 4 => (m k : E)) 0)) (0 : Fin 3) =
      ((show TangentSpace I x from
        PDE.DeTurck.connDiff (I := I) gm g₀ x (m 0) (m 1)) : E)
    rw [Function.update_self]
    rfl
  · change Function.update (Matrix.vecTail (fun k : Fin 4 => (m k : E))) 0
        (connDiffEndo (I := I) (M := M) g₀ gm x ((fun k : Fin 4 => (m k : E)) 0)
          (Matrix.vecTail (fun k : Fin 4 => (m k : E)) 0)) (1 : Fin 3) = (m 2 : E)
    rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]
    rfl
  · change Function.update (Matrix.vecTail (fun k : Fin 4 => (m k : E))) 0
        (connDiffEndo (I := I) (M := M) g₀ gm x ((fun k : Fin 4 => (m k : E)) 0)
          (Matrix.vecTail (fun k : Fin 4 => (m k : E)) 0)) (2 : Fin 3) = (m 3 : E)
    rw [Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
    rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lrQB_unitModel_apply (g₀ gm : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (connDiffQuadraticPairedTensor (I := I) (M := M) g₀ gm) x m =
      gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 2) (m 3))
        (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 0) (m 1)) := by
  rw [unitModel]
  rw [show (connDiffQuadraticPairedTensor (I := I) (M := M) g₀ gm).toSection x
        (unitTensor (I := I) (M := M) x) =
      bilinearSlotInsertCLM (I := I) (M := M) 2 x (connDiffEndo (I := I) (M := M) g₀ gm x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm).toSection x)
          (unitTensor (I := I) (M := M) x)) from by
    rw [connDiffQuadraticPairedTensor, appCcRS_toSection]
    rfl]
  rw [armSlotFib_apply_eval (I := I) (M := M) 2 x
    (connDiffEndo (I := I) (M := M) g₀ gm x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm).toSection x)
      (unitTensor (I := I) (M := M) x)) (fun k : Fin 4 => (m k : E))]
  rw [slotInsertEndoFib_apply_eval]
  rw [lrArmSlotTuple (I := I) (M := M) g₀ gm x m]
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm).toSection x)
          (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 3 (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm) x from rfl]
  rw [lrOmegaHat_unitModel_apply (I := I) (M := M) g₀ gm x]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lrQA_unitModel_apply (g₀ gm : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ gm) x m =
      gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x
        (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 0) (m 1)) (m 3)) (m 2) := by
  rw [unitModel]
  rw [show (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ gm).toSection x
        (unitTensor (I := I) (M := M) x) =
      bilinearSlotInsertCLM (I := I) (M := M) 2 x (connDiffEndo (I := I) (M := M) g₀ gm x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1)
            (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm)).toSection x)
          (unitTensor (I := I) (M := M) x)) from by
    rw [connDiffQuadraticComposedTensor, appCcRS_toSection]
    rfl]
  rw [armSlotFib_apply_eval (I := I) (M := M) 2 x
    (connDiffEndo (I := I) (M := M) g₀ gm x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1)
        (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm)).toSection x)
      (unitTensor (I := I) (M := M) x)) (fun k : Fin 4 => (m k : E))]
  rw [slotInsertEndoFib_apply_eval]
  rw [lrArmSlotTuple (I := I) (M := M) g₀ gm x m]
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1)
            (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm)).toSection x)
          (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1)
          (connDiffGmLoweredTensor (I := I) (M := M) g₀ gm)) x from rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 3 =>
      (fun j : Fin 3 => (((![(show TangentSpace I x from
          PDE.DeTurck.connDiff (I := I) gm g₀ x (m 0) (m 1)), m 2, m 3] :
          Fin 3 → TangentSpace I x)) j : E)) ((Equiv.swap (0 : Fin 3) 1) i)) =
    (fun i : Fin 3 => (((![m 2, (show TangentSpace I x from
        PDE.DeTurck.connDiff (I := I) gm g₀ x (m 0) (m 1)), m 3] :
        Fin 3 → TangentSpace I x)) i : E)) from by
    funext i
    fin_cases i <;> rfl]
  rw [lrOmegaHat_unitModel_apply (I := I) (M := M) g₀ gm x]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

private def lrPermA : Equiv.Perm (Fin 4) :=
  ⟨fun i => (![2, 0, 1, 3] : Fin 4 → Fin 4) i,
   fun i => (![1, 2, 0, 3] : Fin 4 → Fin 4) i,
   by decide, by decide⟩

private def lrPermB : Equiv.Perm (Fin 4) :=
  ⟨fun i => (![3, 0, 1, 2] : Fin 4 → Fin 4) i,
   fun i => (![1, 2, 3, 0] : Fin 4 → Fin 4) i,
   by decide, by decide⟩

private def lrPermC : Equiv.Perm (Fin 4) :=
  ⟨fun i => (![3, 1, 0, 2] : Fin 4 → Fin 4) i,
   fun i => (![2, 1, 3, 0] : Fin 4 → Fin 4) i,
   by decide, by decide⟩


private def connDiffQuadraticCurvatureTerm (g₀ gm : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 :=
  domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1) (connDiffQuadraticPairedTensor (I := I) (M := M) g₀ gm)
    + connDiffQuadraticPairedTensor (I := I) (M := M) g₀ gm
    + domDomCongrSection (I := I) g₀ lrPermA (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ gm)
    + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 2) (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ gm)
    + domDomCongrSection (I := I) g₀ lrPermB (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ gm)
    + domDomCongrSection (I := I) g₀ lrPermC (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ gm)

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lrQuadF_unitModel_apply (g₀ gm : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (connDiffQuadraticCurvatureTerm (I := I) (M := M) g₀ gm) x m =
      gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 2) (m 3))
          (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 1) (m 0))
        + gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 2) (m 3))
            (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 0) (m 1))
        + gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x
            (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 2) (m 0)) (m 3)) (m 1)
        + gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x
            (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 2) (m 1)) (m 3)) (m 0)
        + gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x
            (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 3) (m 0)) (m 2)) (m 1)
        + gm.inner x (PDE.DeTurck.connDiff (I := I) gm g₀ x
            (PDE.DeTurck.connDiff (I := I) gm g₀ x (m 3) (m 1)) (m 2)) (m 0) := by
  rw [connDiffQuadraticCurvatureTerm]
  rw [bdUnitModel_add, bdUnitModel_add, bdUnitModel_add, bdUnitModel_add, bdUnitModel_add]
  simp only [ContinuousMultilinearMap.add_apply]
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel]
  simp only [ContinuousMultilinearMap.domDomCongr_apply]
  rw [lrQB_unitModel_apply (I := I) (M := M) g₀ gm x
      (fun i => m ((Equiv.swap (0 : Fin 4) 1) i)),
    lrQB_unitModel_apply (I := I) (M := M) g₀ gm x m,
    lrQA_unitModel_apply (I := I) (M := M) g₀ gm x (fun i => m (lrPermA i)),
    lrQA_unitModel_apply (I := I) (M := M) g₀ gm x
      (fun i => m ((Equiv.swap (0 : Fin 4) 2) i)),
    lrQA_unitModel_apply (I := I) (M := M) g₀ gm x (fun i => m (lrPermB i)),
    lrQA_unitModel_apply (I := I) (M := M) g₀ gm x (fun i => m (lrPermC i))]
  have hswap01 : ∀ k : Fin 4, m ((Equiv.swap (0 : Fin 4) 1) k) =
      (![m 1, m 0, m 2, m 3] : Fin 4 → TangentSpace I x) k := by
    intro k
    fin_cases k <;> rfl
  have hswap02 : ∀ k : Fin 4, m ((Equiv.swap (0 : Fin 4) 2) k) =
      (![m 2, m 1, m 0, m 3] : Fin 4 → TangentSpace I x) k := by
    intro k
    fin_cases k <;> rfl
  have hA : ∀ k : Fin 4, m (lrPermA k) =
      (![m 2, m 0, m 1, m 3] : Fin 4 → TangentSpace I x) k := by
    intro k
    fin_cases k <;> rfl
  have hB : ∀ k : Fin 4, m (lrPermB k) =
      (![m 3, m 0, m 1, m 2] : Fin 4 → TangentSpace I x) k := by
    intro k
    fin_cases k <;> rfl
  have hC : ∀ k : Fin 4, m (lrPermC k) =
      (![m 3, m 1, m 0, m 2] : Fin 4 → TangentSpace I x) k := by
    intro k
    fin_cases k <;> rfl
  rw [hswap01 0, hswap01 1, hswap01 2, hswap01 3, hswap02 0, hswap02 1, hswap02 2,
    hswap02 3, hA 0, hA 1, hA 2, hA 3, hB 0, hB 1, hB 2, hB 3, hC 0, hC 1, hC 2, hC 3]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]

private def lrSigmaW1 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![0, 5, 2, 1, 3, 4] : Fin 6 → Fin 6) i,
   fun i => (![0, 3, 2, 4, 5, 1] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

private def lrSigmaW2 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![4, 0, 2, 1, 3, 5] : Fin 6 → Fin 6) i,
   fun i => (![1, 3, 2, 4, 0, 5] : Fin 6 → Fin 6) i,
   by decide, by decide⟩


private def riemannLoweredContractionA (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lrSigmaW1
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))


private def riemannLoweredContractionB (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lrSigmaW2
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [SigmaCompactSpace M] in
private lemma lrRiemW1_toModel (g₀ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (m : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (riemannLoweredContractionA (I := I) (M := M) g₀).toSection x) D) m =
      ∑ e : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₀ x e x : E), (m 3 : E)] *
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2))
            (smoothOrthoFrame (I := I) g₀ x e x) := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lrSigmaW1
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 0, w 5] *
          unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x ![w 2, w 1, w 3, w 4] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lrSigmaW1
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          tensorRS_domDomCongr lrSigmaW1
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) lrSigmaW1
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [bdSlotExtendIter_two_toModel (I := I) (M := M) g₀
      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x D
      (fun i => w (lrSigmaW1 i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k
      · change w (lrSigmaW1 0) = w 0
        rw [show lrSigmaW1 (0 : Fin 6) = 0 from by decide]
      · change w (lrSigmaW1 1) = w 5
        rw [show lrSigmaW1 (1 : Fin 6) = 5 from by decide]
    · refine congrArg _ ?_
      funext k
      fin_cases k
      · change w (lrSigmaW1 2) = w 2
        rw [show lrSigmaW1 (2 : Fin 6) = 2 from by decide]
      · change w (lrSigmaW1 3) = w 1
        rw [show lrSigmaW1 (3 : Fin 6) = 1 from by decide]
      · change w (lrSigmaW1 4) = w 3
        rw [show lrSigmaW1 (4 : Fin 6) = 3 from by decide]
      · change w (lrSigmaW1 5) = w 4
        rw [show lrSigmaW1 (5 : Fin 6) = 4 from by decide]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
      (riemannLoweredContractionA (I := I) (M := M) g₀).toSection x) D) =
      cometricDoubleTraceFib (I := I) g₀ 4 x Y from by
    rw [hY_def, riemannLoweredContractionA]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y) (fun j => (m j : E))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hYval]
  change Tensor0SSpace.toModel D
      ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E), (m 3 : E)] *
      unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
        ![(m 0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
          (m 1 : E), (m 2 : E)] = _
  rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₀ x
    ![(m 0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
      (m 1 : E), (m 2 : E)]]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [SigmaCompactSpace M] in
private lemma lrRiemW2_toModel (g₀ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (m : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (riemannLoweredContractionB (I := I) (M := M) g₀).toSection x) D) m =
      ∑ e : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(m 2 : E), (smoothOrthoFrame (I := I) g₀ x e x : E)] *
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3))
            (smoothOrthoFrame (I := I) g₀ x e x) := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lrSigmaW2
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 4, w 0] *
          unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x ![w 2, w 1, w 3, w 5] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lrSigmaW2
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          tensorRS_domDomCongr lrSigmaW2
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) lrSigmaW2
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [bdSlotExtendIter_two_toModel (I := I) (M := M) g₀
      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x D
      (fun i => w (lrSigmaW2 i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k
      · change w (lrSigmaW2 0) = w 4
        rw [show lrSigmaW2 (0 : Fin 6) = 4 from by decide]
      · change w (lrSigmaW2 1) = w 0
        rw [show lrSigmaW2 (1 : Fin 6) = 0 from by decide]
    · refine congrArg _ ?_
      funext k
      fin_cases k
      · change w (lrSigmaW2 2) = w 2
        rw [show lrSigmaW2 (2 : Fin 6) = 2 from by decide]
      · change w (lrSigmaW2 3) = w 1
        rw [show lrSigmaW2 (3 : Fin 6) = 1 from by decide]
      · change w (lrSigmaW2 4) = w 3
        rw [show lrSigmaW2 (4 : Fin 6) = 3 from by decide]
      · change w (lrSigmaW2 5) = w 5
        rw [show lrSigmaW2 (5 : Fin 6) = 5 from by decide]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
      (riemannLoweredContractionB (I := I) (M := M) g₀).toSection x) D) =
      cometricDoubleTraceFib (I := I) g₀ 4 x Y from by
    rw [hY_def, riemannLoweredContractionB]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y) (fun j => (m j : E))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hYval]
  change Tensor0SSpace.toModel D
      ![(m 2 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] *
      unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
        ![(m 0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
          (m 1 : E), (m 3 : E)] = _
  rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₀ x
    ![(m 0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
      (m 1 : E), (m 3 : E)]]
  rfl


private def riemannCurvatureCoeffField (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    SmoothCcTensor g₀ 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 (riemannLoweredContractionA (I := I) (M := M) g₀) T
    + ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 (riemannLoweredContractionB (I := I) (M := M) g₀) T

set_option backward.isDefEq.respectTransparency false in
omit [SigmaCompactSpace M] in
private lemma lrCurvF_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (riemannCurvatureCoeffField (I := I) (M := M) g₀ T) x m =
      smoothCcTensorBilinForm (I := I) g₀ T x
          (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2)) (m 3)
        + smoothCcTensorBilinForm (I := I) g₀ T x (m 2)
            (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3)) := by
  classical
  rw [riemannCurvatureCoeffField, bdUnitModel_add, ContinuousMultilinearMap.add_apply]
  have hTu : ∀ (a b : TangentSpace I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T.toSection x)
            (unitTensor (I := I) (M := M) x)) ![(a : E), (b : E)] =
        smoothCcTensorBilinForm (I := I) g₀ T x a b := by
    intro a b
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 2 T x from rfl]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T x a b]
  have h1 : unitModel (I := I) (M := M) g₀ 4
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 (riemannLoweredContractionA (I := I) (M := M) g₀) T) x m =
      smoothCcTensorBilinForm (I := I) g₀ T x
        (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2)) (m 3) := by
    rw [unitModel]
    rw [show (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 (riemannLoweredContractionA (I := I) (M := M) g₀)
          T).toSection x (unitTensor (I := I) (M := M) x) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (riemannLoweredContractionA (I := I) (M := M) g₀).toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T.toSection x)
            (unitTensor (I := I) (M := M) x))) from by
      rw [appCcRS_toSection]
      rfl]
    rw [lrRiemW1_toModel (I := I) (M := M) g₀ x _ m]
    have hexp : riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2) =
        ∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2))
            (smoothOrthoFrame (I := I) g₀ x e x) • smoothOrthoFrame (I := I) g₀ x e x := by
      have hrep := bdOrthoFrame_center_repr (I := I) (M := M) g₀ x
        (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2))
      conv_lhs => rw [hrep]
      refine Finset.sum_congr rfl fun e _ => ?_
      congr 1
      exact g₀.symm x (smoothOrthoFrame (I := I) g₀ x e x)
        (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2))
    conv_rhs => rw [hexp]
    rw [show smoothCcTensorBilinForm (I := I) g₀ T x
        (∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2))
            (smoothOrthoFrame (I := I) g₀ x e x) • smoothOrthoFrame (I := I) g₀ x e x)
        (m 3) =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 2))
            (smoothOrthoFrame (I := I) g₀ x e x) *
          smoothCcTensorBilinForm (I := I) g₀ T x (smoothOrthoFrame (I := I) g₀ x e x) (m 3) from by
      rw [map_sum, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hTu (smoothOrthoFrame (I := I) g₀ x e x) (m 3)]
    ring
  have h2 : unitModel (I := I) (M := M) g₀ 4
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 (riemannLoweredContractionB (I := I) (M := M) g₀) T) x m =
      smoothCcTensorBilinForm (I := I) g₀ T x (m 2)
        (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3)) := by
    rw [unitModel]
    rw [show (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 (riemannLoweredContractionB (I := I) (M := M) g₀)
          T).toSection x (unitTensor (I := I) (M := M) x) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (riemannLoweredContractionB (I := I) (M := M) g₀).toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T.toSection x)
            (unitTensor (I := I) (M := M) x))) from by
      rw [appCcRS_toSection]
      rfl]
    rw [lrRiemW2_toModel (I := I) (M := M) g₀ x _ m]
    have hexp : riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3) =
        ∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3))
            (smoothOrthoFrame (I := I) g₀ x e x) • smoothOrthoFrame (I := I) g₀ x e x := by
      have hrep := bdOrthoFrame_center_repr (I := I) (M := M) g₀ x
        (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3))
      conv_lhs => rw [hrep]
      refine Finset.sum_congr rfl fun e _ => ?_
      congr 1
      exact g₀.symm x (smoothOrthoFrame (I := I) g₀ x e x)
        (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3))
    conv_rhs => rw [hexp]
    rw [show smoothCcTensorBilinForm (I := I) g₀ T x (m 2)
        (∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3))
            (smoothOrthoFrame (I := I) g₀ x e x) • smoothOrthoFrame (I := I) g₀ x e x) =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 1) (m 3))
            (smoothOrthoFrame (I := I) g₀ x e x) *
          smoothCcTensorBilinForm (I := I) g₀ T x (m 2) (smoothOrthoFrame (I := I) g₀ x e x) from by
      rw [map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_smul, smul_eq_mul]]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hTu (m 2) (smoothOrthoFrame (I := I) g₀ x e x)]
    ring
  rw [h1, h2]

private lemma lrVec2_upd_zero {F : Type*} (a b z : F) :
    Function.update ![a, b] 0 z = ![z, b] := by
  funext k
  fin_cases k <;> simp [Function.update]

private lemma lrVec2_upd_one {F : Type*} (a b z : F) :
    Function.update ![a, b] 1 z = ![a, z] := by
  funext k
  fin_cases k <;> simp [Function.update]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lrTensor0sClmExtUnit {s : ℕ} {x : M}
    {φ ψ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x}
    (h : φ (unitZeroSec (I := I) (M := M) x) = ψ (unitZeroSec (I := I) (M := M) x)) :
    φ = ψ := by
  classical
  ext D
  rw [zeroTensor_eq_smul_unit (I := I) (M := M) x D, map_smul, map_smul, h]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lrCoeff_eq_unitScalarRSLift (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (x : M) :
    (P.toSection x : TensorRSSpace 0 2 I x) =
      unitScalarRSLift (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          P.toSection x) (unitZeroSec (I := I) (M := M) x)) := by
  have h : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      P.toSection x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        unitScalarRSLift (I := I) (M := M) x
          ((show Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SSpace 2 I x from P.toSection x)
            (unitZeroSec (I := I) (M := M) x))) := by
    apply lrTensor0sClmExtUnit (I := I) (M := M)
    rw [unitScalarRSLift_apply_unit]
  exact h

set_option maxHeartbeats 12800000 in

omit [NeZero (Module.finrank ℝ E)] in
private lemma lrRIC (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (x : M) (a b c d : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x ![a, b, c, d]
      - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
          ![b, a, c, d] =
    -(smoothCcTensorBilinForm (I := I) g₀ T x (riemannOp (LeviCivita (I := I) g₀) x a b c) d
      + smoothCcTensorBilinForm (I := I) g₀ T x c (riemannOp (LeviCivita (I := I) g₀) x a b d)) := by
  classical
  set X : Π b' : M, TangentSpace I b' := smoothExtensionTangent (I := I) x a with hX_def
  set Y : Π b' : M, TangentSpace I b' := smoothExtensionTangent (I := I) x b with hY_def
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) :=
    smoothExtensionTangent_contMDiff (I := I) x a
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) :=
    smoothExtensionTangent_contMDiff (I := I) x b
  have hXx : X x = a := smoothExtensionTangent_eq (I := I) x a
  have hYx : Y x = b := smoothExtensionTangent_eq (I := I) x b
  rw [← hXx, ← hYx]
  have hicg : iteratedCovGrad (I := I) g₀ 0 2 2 T =
      covGrad (I := I) (M := M) g₀ 0 (2 + 1) (covGrad (I := I) (M := M) g₀ 0 2 T) := rfl
  have hconsXY : (![X x, Y x, c, d] : Fin 4 → TangentSpace I x) =
      Fin.cons (X x) (Fin.cons (Y x) ![c, d]) := by
    funext i
    fin_cases i <;> rfl
  have hconsYX : (![Y x, X x, c, d] : Fin 4 → TangentSpace I x) =
      Fin.cons (Y x) (Fin.cons (X x) ![c, d]) := by
    funext i
    fin_cases i <;> rfl
  have hXY := tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal (I := I) (M := M)
    g₀ 2 T hX hY x ![c, d]
  have hYX := tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal (I := I) (M := M)
    g₀ 2 T hY hX x ![c, d]
  have hUM : ∀ v : Fin 4 → TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SSpace (2 + 1 + 1) I x from
          (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
            (covGrad (I := I) (M := M) g₀ 0 2 T)).toSection x)
          (unitZeroSec (I := I) (M := M) x)) v := by
    intro v
    rw [unitModel, hicg]
    rfl
  rw [hUM ![X x, Y x, c, d], hUM ![Y x, X x, c, d], hconsXY, hconsYX, hXY, hYX]
  have hdiff : Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 X Y (fun y : M => T.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) ![c, d]
      - Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 Y X (fun y : M => T.toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) ![c, d]
      = Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          riemannOp (tensorCov (I := I) g₀ 0 2) x (X x) (Y x)
            ((T.toSection x : TensorRSSpace 0 2 I x)))
          (unitZeroSec (I := I) (M := M) x)) ![c, d] := by
    rw [← tensorSecondCovDeriv_antisymm_eq_riemannOp (I := I) g₀ 0 2 hX hY
      T.toSection.contMDiff]
    rw [show (show Tensor0SSpace 0 I x →L[ℝ]
          Tensor0SSpace 2 I x from
        (tensorSecondCovDeriv (I := I) g₀ 0 2 X Y (fun y : M => T.toSection y) x -
          tensorSecondCovDeriv (I := I) g₀ 0 2 Y X (fun y : M => T.toSection y) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 X Y (fun y : M => T.toSection y) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 Y X (fun y : M => T.toSection y) x) from rfl]
    rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply]
  rw [hdiff]
  rw [show ((T.toSection x : TensorRSSpace 0 2 I x)) =
      unitScalarRSLift (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          T.toSection x) (unitZeroSec (I := I) (M := M) x)) from
    lrCoeff_eq_unitScalarRSLift (I := I) (M := M) g₀ T x]
  rw [riemannOp_tensorCov_unitScalarRSLift_unitEval (I := I) (M := M) g₀ 2 x (X x) (Y x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      T.toSection x) (unitZeroSec (I := I) (M := M) x))]
  set Xb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ⟨fun b' => X b', hX⟩ with hXb_def
  set Yb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ⟨fun b' => Y b', hY⟩ with hYb_def
  set AP : Π y : M, Tensor0SSpace 2 I y := fun y =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
      T.toSection y) (unitZeroSec (I := I) (M := M) y) with hAP_def
  have hAP_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) y (AP y)) := by
    exact ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
      (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel 2 ℝ E)
      (E₁ := fun z : M => Tensor0SSpace 0 I z)
      (E₂ := fun z : M => Tensor0SSpace 2 I z)
      (IM := I) (IB := I) (b := id)
      (ϕ := fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ]
            Tensor0SSpace 2 I y from T.toSection y))
      (v := fun y : M => unitZeroSec (I := I) (M := M) y)
      T.toSection.contMDiff (unitZeroSec (I := I) (M := M)).contMDiff
  have hop : riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M 2
        (LeviCivita (I := I) g₀)) x (X x) (Y x) (AP x) =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀))
        (fun b' => Xb b') (fun b' => Yb b') AP x :=
    riemannOp_apply_smooth
      (cov := Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀))
      hX hY hAP_smooth
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ]
        Tensor0SSpace 2 I x from T.toSection x)
        (unitZeroSec (I := I) (M := M) x)) = AP x from rfl]
  rw [hop]
  rw [riemannSec_tensor0SCov_apply_eval (I := I) (M := M) g₀ 2 Xb Yb AP hAP_smooth x ![c, d]]
  rw [Fin.sum_univ_two]
  rw [show (![c, d] : Fin 2 → TangentSpace I x) 0 = c from rfl,
    show (![c, d] : Fin 2 → TangentSpace I x) 1 = d from rfl,
    lrVec2_upd_zero, lrVec2_upd_one]
  have hbase : ∀ u : TangentSpace I x,
      baseSlotCurv (I := I) g₀ Xb Yb x u =
        riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) u := by
    intro u
    rw [baseSlotCurv]
    have hu := riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀)
      (X := fun b' => Xb b') (Y := fun b' => Yb b')
      (Z := fun b' => smoothExtensionTangent (I := I) x u b') (x := x)
      hX hY (smoothExtensionTangent_contMDiff (I := I) x u)
    beta_reduce at hu
    rw [smoothExtensionTangent_eq (I := I) x u] at hu
    exact hu.symm
  rw [hbase c, hbase d]
  have hAPtoModel : ∀ (m : Fin 2 → TangentSpace I x),
      Tensor0SSpace.toModel (AP x) (fun i => (m i : E)) =
        smoothCcTensorBilinForm (I := I) g₀ T x (m 0) (m 1) := by
    intro m
    have h1 : Tensor0SSpace.toModel (AP x) (fun i => (m i : E)) =
        unitModel (I := I) (M := M) g₀ 2 T x m := rfl
    rw [h1, show m = ![m 0, m 1] from funext (fun i => by fin_cases i <;> rfl),
      unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T x (m 0) (m 1)]
    rfl
  rw [show Tensor0SSpace.toModel (AP x)
        ![(riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) c : E), (d : E)] =
      smoothCcTensorBilinForm (I := I) g₀ T x
        (riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) c) d from
    hAPtoModel ![riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) c, d]]
  rw [show Tensor0SSpace.toModel (AP x)
        ![(c : E), (riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) d : E)] =
      smoothCcTensorBilinForm (I := I) g₀ T x c
        (riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) d) from
    hAPtoModel ![c, riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) d]]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lrUnitEval_ddc_rel (g₀ : SmoothRiemannianMetric I M) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (W : SmoothCcTensor g₀ 0 n) (y : M) :
    (show Tensor0SSpace n I y from
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace n I y from
        (domDomCongrSection (I := I) g₀ σ W).toSection y)
        (unitZeroSec (I := I) (M := M) y)) =
    ContinuousMultilinearMap.domDomCongr σ
      (show ContinuousMultilinearMap ℝ (fun _ : Fin n => TangentSpace I y) ℝ from
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace n I y from W.toSection y)
          (unitZeroSec (I := I) (M := M) y)) := by
  have h : unitModel (I := I) (M := M) g₀ n (domDomCongrSection (I := I) g₀ σ W) y =
      ContinuousMultilinearMap.domDomCongr σ
        (unitModel (I := I) (M := M) g₀ n W y) := by
    rw [domDomCongrSection_unitModel]
  rw [unitModel, unitModel] at h
  exact h

set_option maxHeartbeats 12800000 in

omit [NeZero (Module.finrank ℝ E)] in
private lemma lrCovGrad_ddc_unitModel (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (W : SmoothCcTensor g₀ 0 3) (x : M)
    (w : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (covGrad (I := I) (M := M) g₀ 0 3 (domDomCongrSection (I := I) g₀ σ W)) x w =
      unitModel (I := I) (M := M) g₀ 4 (covGrad (I := I) (M := M) g₀ 0 3 W) x
        (Fin.cons (w 0) (fun j => Matrix.vecTail w (σ j))) := by
  rw [lrUnitModel_covGrad_eval (I := I) (M := M) g₀ 3
    (domDomCongrSection (I := I) g₀ σ W) x w]
  rw [lrUnitModel_covGrad_eval (I := I) (M := M) g₀ 3 W x
    (Fin.cons (w 0) (fun j => Matrix.vecTail w (σ j)))]
  have hW := lrUnitEval_tsmdiffAt (I := I) (M := M) g₀ 3 W x
  have hW' := lrUnitEval_tsmdiffAt (I := I) (M := M) g₀ 3
    (domDomCongrSection (I := I) g₀ σ W) x
  have hstep := tensor0SCovariantDerivative_succ_domDomCongr (I := I) (M := M) 2 g₀ σ
    (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from W.toSection y)
      (unitZeroSec (I := I) (M := M) y))
    (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
      (domDomCongrSection (I := I) g₀ σ W).toSection y)
      (unitZeroSec (I := I) (M := M) y))
    x (w 0) hW hW'
    (fun y => lrUnitEval_ddc_rel (I := I) (M := M) g₀ 3 σ W y)
  rw [show (show Tensor0SSpace 3 I x from
      Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
        (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
          (domDomCongrSection (I := I) g₀ σ W).toSection y)
          (unitZeroSec (I := I) (M := M) y)) x (w 0)) =
    ContinuousMultilinearMap.domDomCongr σ
      (show Tensor0SSpace 3 I x from
        Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
          (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
            W.toSection y) (unitZeroSec (I := I) (M := M) y)) x (w 0)) from hstep]
  rw [show (Fin.cons (w 0) (fun j => Matrix.vecTail w (σ j)) :
    Fin 4 → TangentSpace I x) 0 = w 0 from rfl]
  rw [show Matrix.vecTail (Fin.cons (w 0) (fun j => Matrix.vecTail w (σ j)) :
      Fin 4 → TangentSpace I x) = (fun j => Matrix.vecTail w (σ j)) from
    Matrix.tail_cons _ _]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lrTsec_rel (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v) (y : M) :
    (show Tensor0SSpace 2 I y from
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from T.toSection y)
        (unitZeroSec (I := I) (M := M) y)) =
    ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
      (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I y) ℝ from
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from T.toSection y)
          (unitZeroSec (I := I) (M := M) y)) := by
  have h : unitModel (I := I) (M := M) g₀ 2 T y =
      ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (unitModel (I := I) (M := M) g₀ 2 T y) := by
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hveta : v = ![v 0, v 1] := funext fun i => by fin_cases i <;> rfl
    have hveta2 : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] :=
      funext fun i => by fin_cases i <;> rfl
    rw [hveta2]
    conv_lhs => rw [hveta]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T y (v 0) (v 1),
      unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T y (v 1) (v 0)]
    exact hTsymm y (v 0) (v 1)
  rw [unitModel] at h
  exact h

set_option maxHeartbeats 12800000 in

omit [NeZero (Module.finrank ℝ E)] in
private lemma lrCovGradT_argswap (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (y : M) (w : Fin 3 → TangentSpace I y) :
    unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 T) y w =
      unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 T) y
        ![w 0, w 2, w 1] := by
  rw [lrUnitModel_covGrad_eval (I := I) (M := M) g₀ 2 T y w,
    lrUnitModel_covGrad_eval (I := I) (M := M) g₀ 2 T y ![w 0, w 2, w 1]]
  have hW := lrUnitEval_tsmdiffAt (I := I) (M := M) g₀ 2 T y
  have hstep := tensor0SCovariantDerivative_succ_domDomCongr (I := I) (M := M) 1 g₀
    (Equiv.swap (0 : Fin 2) 1)
    (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from T.toSection z)
      (unitZeroSec (I := I) (M := M) z))
    (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from T.toSection z)
      (unitZeroSec (I := I) (M := M) z))
    y (w 0) hW hW
    (fun z => lrTsec_rel (I := I) (M := M) g₀ T hTsymm z)
  conv_lhs => rw [show (show Tensor0SSpace 2 I y from
      Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
        (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
          T.toSection z) (unitZeroSec (I := I) (M := M) z)) y (w 0)) =
    ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
      (show Tensor0SSpace 2 I y from
        Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
          (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
            T.toSection z) (unitZeroSec (I := I) (M := M) z)) y (w 0)) from hstep]
  rw [show (![w 0, w 2, w 1] : Fin 3 → TangentSpace I y) 0 = w 0 from rfl]
  rw [show Matrix.vecTail (![w 0, w 2, w 1] : Fin 3 → TangentSpace I y) = ![w 2, w 1] from by
    funext k
    fin_cases k <;> rfl]
  rw [show Tensor0SSpace.toModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (show Tensor0SSpace 2 I y from
          Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
            (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
              T.toSection z) (unitZeroSec (I := I) (M := M) z)) y (w 0)))
      (Matrix.vecTail w) =
    Tensor0SSpace.toModel
      (show Tensor0SSpace 2 I y from
        Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
          (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
            T.toSection z) (unitZeroSec (I := I) (M := M) z)) y (w 0))
      (fun i => Matrix.vecTail w ((Equiv.swap (0 : Fin 2) 1) i)) from rfl]
  refine congrArg _ ?_
  funext i
  fin_cases i <;> rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma lrCgTsec_rel (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v) (y : M) :
    (show Tensor0SSpace 3 I y from
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
        (covGrad (I := I) (M := M) g₀ 0 2 T).toSection y)
        (unitZeroSec (I := I) (M := M) y)) =
    ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 3) 2)
      (show ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I y) ℝ from
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
          (covGrad (I := I) (M := M) g₀ 0 2 T).toSection y)
          (unitZeroSec (I := I) (M := M) y)) := by
  have h : unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 T) y =
      ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 3) 2)
        (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 T) y) := by
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hveta : v = ![v 0, v 1, v 2] := funext fun i => by fin_cases i <;> rfl
    have hveta2 : (fun i => v ((Equiv.swap (1 : Fin 3) 2) i)) = ![v 0, v 2, v 1] :=
      funext fun i => by fin_cases i <;> rfl
    rw [hveta2]
    conv_lhs => rw [hveta]
    exact lrCovGradT_argswap (I := I) (M := M) g₀ T hTsymm y ![v 0, v 1, v 2]
  rw [unitModel] at h
  exact h

set_option maxHeartbeats 12800000 in

omit [NeZero (Module.finrank ℝ E)] in
private lemma lrICG2_argswap (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (x : M) (a b c d : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x ![a, b, c, d] =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
        ![a, b, d, c] := by
  have hUM : ∀ v : Fin 4 → TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x v =
      unitModel (I := I) (M := M) g₀ 4
        (covGrad (I := I) (M := M) g₀ 0 3 (covGrad (I := I) (M := M) g₀ 0 2 T)) x v :=
    fun v => rfl
  rw [hUM ![a, b, c, d], hUM ![a, b, d, c]]
  rw [lrUnitModel_covGrad_eval (I := I) (M := M) g₀ 3
    (covGrad (I := I) (M := M) g₀ 0 2 T) x ![a, b, c, d]]
  rw [lrUnitModel_covGrad_eval (I := I) (M := M) g₀ 3
    (covGrad (I := I) (M := M) g₀ 0 2 T) x ![a, b, d, c]]
  have hW := lrUnitEval_tsmdiffAt (I := I) (M := M) g₀ 3
    (covGrad (I := I) (M := M) g₀ 0 2 T) x
  have hstep := tensor0SCovariantDerivative_succ_domDomCongr (I := I) (M := M) 2 g₀
    (Equiv.swap (1 : Fin 3) 2)
    (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 3 I z from
      (covGrad (I := I) (M := M) g₀ 0 2 T).toSection z)
      (unitZeroSec (I := I) (M := M) z))
    (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 3 I z from
      (covGrad (I := I) (M := M) g₀ 0 2 T).toSection z)
      (unitZeroSec (I := I) (M := M) z))
    x ((![a, b, c, d] : Fin 4 → TangentSpace I x) 0) hW hW
    (fun z => lrCgTsec_rel (I := I) (M := M) g₀ T hTsymm z)
  conv_lhs => rw [show (show Tensor0SSpace 3 I x from
      Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
        (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 3 I z from
          (covGrad (I := I) (M := M) g₀ 0 2 T).toSection z)
          (unitZeroSec (I := I) (M := M) z)) x
        ((![a, b, c, d] : Fin 4 → TangentSpace I x) 0)) =
    ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 3) 2)
      (show Tensor0SSpace 3 I x from
        Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
          (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 3 I z from
            (covGrad (I := I) (M := M) g₀ 0 2 T).toSection z)
            (unitZeroSec (I := I) (M := M) z)) x
          ((![a, b, c, d] : Fin 4 → TangentSpace I x) 0)) from hstep]
  rw [show ((![a, b, d, c] : Fin 4 → TangentSpace I x) 0) =
    ((![a, b, c, d] : Fin 4 → TangentSpace I x) 0) from rfl]
  rw [show Tensor0SSpace.toModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 3) 2)
        (show Tensor0SSpace 3 I x from
          Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
            (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 3 I z from
              (covGrad (I := I) (M := M) g₀ 0 2 T).toSection z)
              (unitZeroSec (I := I) (M := M) z)) x
            ((![a, b, c, d] : Fin 4 → TangentSpace I x) 0)))
      (Matrix.vecTail (![a, b, c, d] : Fin 4 → TangentSpace I x)) =
    Tensor0SSpace.toModel
      (show Tensor0SSpace 3 I x from
        Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
          (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 3 I z from
            (covGrad (I := I) (M := M) g₀ 0 2 T).toSection z)
            (unitZeroSec (I := I) (M := M) z)) x
          ((![a, b, c, d] : Fin 4 → TangentSpace I x) 0))
      (fun i => Matrix.vecTail (![a, b, c, d] : Fin 4 → TangentSpace I x)
        ((Equiv.swap (1 : Fin 3) 2) i)) from rfl]
  refine congrArg _ ?_
  funext i
  fin_cases i <;> rfl

set_option maxHeartbeats 12800000 in

omit [NeZero (Module.finrank ℝ E)] in
private lemma lrCovGradKT_unitModel (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (w0 w1 w2 w3 : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (covGrad (I := I) (M := M) g₀ 0 3 (linearizedKoszulTensor (I := I) (M := M) g₀ T)) x
        ![w0, w1, w2, w3] =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
            ![w0, w3, w2, w1]
          + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
              ![w0, w2, w3, w1]
          - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
              ![w0, w1, w3, w2]) := by
  have hUM : ∀ v : Fin 4 → TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x v =
      unitModel (I := I) (M := M) g₀ 4
        (covGrad (I := I) (M := M) g₀ 0 3 (covGrad (I := I) (M := M) g₀ 0 2 T)) x v :=
    fun v => rfl
  rw [hUM ![w0, w3, w2, w1], hUM ![w0, w2, w3, w1], hUM ![w0, w1, w3, w2]]
  rw [linearizedKoszulTensor, covGrad_smul, covGrad_sub, covGrad_add]
  rw [bdUnitModel_smul]
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [bdUnitModel_sub, ContinuousMultilinearMap.sub_apply,
    bdUnitModel_add, ContinuousMultilinearMap.add_apply]
  rw [lrCovGrad_ddc_unitModel (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 2)
      (covGrad (I := I) (M := M) g₀ 0 2 T) x ![w0, w1, w2, w3],
    lrCovGrad_ddc_unitModel (I := I) (M := M) g₀ (finRotate 3)
      (covGrad (I := I) (M := M) g₀ 0 2 T) x ![w0, w1, w2, w3],
    lrCovGrad_ddc_unitModel (I := I) (M := M) g₀ (Equiv.swap (1 : Fin 3) 2)
      (covGrad (I := I) (M := M) g₀ 0 2 T) x ![w0, w1, w2, w3]]
  rw [show (Fin.cons ((![w0, w1, w2, w3] : Fin 4 → TangentSpace I x) 0)
      (fun j => Matrix.vecTail (![w0, w1, w2, w3] : Fin 4 → TangentSpace I x)
        ((Equiv.swap (0 : Fin 3) 2) j)) : Fin 4 → TangentSpace I x) =
    ![w0, w3, w2, w1] from by
    funext k
    fin_cases k <;> rfl]
  rw [show (Fin.cons ((![w0, w1, w2, w3] : Fin 4 → TangentSpace I x) 0)
      (fun j => Matrix.vecTail (![w0, w1, w2, w3] : Fin 4 → TangentSpace I x)
        ((finRotate 3) j)) : Fin 4 → TangentSpace I x) =
    ![w0, w2, w3, w1] from by
    funext k
    fin_cases k <;> rfl]
  rw [show (Fin.cons ((![w0, w1, w2, w3] : Fin 4 → TangentSpace I x) 0)
      (fun j => Matrix.vecTail (![w0, w1, w2, w3] : Fin 4 → TangentSpace I x)
        ((Equiv.swap (1 : Fin 3) 2) j)) : Fin 4 → TangentSpace I x) =
    ![w0, w1, w3, w2] from by
    funext k
    fin_cases k <;> rfl]


private def lrR4 (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g₀ 0 4 :=
  (-(s / 2) : ℝ) • riemannCurvatureCoeffField (I := I) (M := M) g₀ T
    - connDiffQuadraticCurvatureTerm (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s)

set_option maxHeartbeats 25600000 in

private theorem lrSummand (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M) (v0 v1 pf qf : TangentSpace I x) :
    ((realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
        (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x v0 pf qf) v1
      + (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x v1 pf qf) v0)
      + s * ((1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
              ![v0, v1, pf, qf]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
                ![v0, v1, qf, pf])
        - (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
              ![v0, pf, qf, v1]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
                ![v0, qf, pf, v1])
        - (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
              ![v1, pf, qf, v0]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
                ![v1, qf, pf, v0])) =
      unitModel (I := I) (M := M) g₀ 4 (lrR4 (I := I) (M := M) g₀ T hδ hδZ s) x
        ![v0, v1, pf, qf] := by
  classical
  have hR4 : unitModel (I := I) (M := M) g₀ 4 (lrR4 (I := I) (M := M) g₀ T hδ hδZ s) x
      ![v0, v1, pf, qf] =
      (-(s / 2) : ℝ) * unitModel (I := I) (M := M) g₀ 4 (riemannCurvatureCoeffField (I := I) (M := M) g₀ T) x
          ![v0, v1, pf, qf]
        - unitModel (I := I) (M := M) g₀ 4
            (connDiffQuadraticCurvatureTerm (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s)) x
            ![v0, v1, pf, qf] := by
    rw [lrR4, bdUnitModel_sub, ContinuousMultilinearMap.sub_apply, bdUnitModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [hR4, lrQuadF_unitModel_apply (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T 0 hδ hδZ s) x ![v0, v1, pf, qf],
    lrCurvF_unitModel_apply (I := I) (M := M) g₀ T x ![v0, v1, pf, qf]]
  rw [lrKernel_inner (I := I) (M := M) g₀ T hδ_lt hδ hδZ hTsymm hs x v0 v1 pf qf,
    lrKernel_inner (I := I) (M := M) g₀ T hδ_lt hδ hδZ hTsymm hs x v1 v0 pf qf]
  rw [lrCovGradKT_unitModel (I := I) (M := M) g₀ T x v0 v1 pf qf,
    lrCovGradKT_unitModel (I := I) (M := M) g₀ T x v1 v0 pf qf]
  have hswap := lrICG2_argswap (I := I) (M := M) g₀ T hTsymm x v1 v0 pf qf
  have hric := lrRIC (I := I) (M := M) g₀ T x v0 v1 pf qf
  have hcs1 : PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x pf
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x qf v0) =
      PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x qf v0)
        pf :=
    PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x pf
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x qf v0)
  have hcs2 : PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x pf
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x qf v1) =
      PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x qf v1)
        pf :=
    PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x pf
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x qf v1)
  rw [hcs1, hcs2]
  have hqswap : ∀ u w z : TangentSpace I x,
      PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x u w =
        PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x w u :=
    fun u w _ => PDE.DeTurck.connDiff_symm (I := I)
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x u w
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  linear_combination (s / 2) * hric + (s / 2) * hswap

set_option maxHeartbeats 51200000 in

private theorem lrArm_sub_family_eq_pairTrace (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    deTurckLieCovDerivArmField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
      - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
        ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
          Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
          Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
        ![(-1 : ℝ), -1, 1] s =
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hsmul_desc : ∀ (c : ℝ) (F : SmoothCcTensor g₀ 2 2),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          ((c • F).toSection x)) D) v =
      c * Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (F.toSection x)) D) v := by
    intro c F
    rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((c • F).toSection x)) =
        c • (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (F.toSection x)) from by
      rw [show (c • F).toSection x = c • F.toSection x from by
        rw [SmoothCcTensor.toSection_smul]; rfl]
      ]
    rw [ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have hadd_desc : ∀ (F G : SmoothCcTensor g₀ 2 2),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          ((F + G).toSection x)) D) v =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (F.toSection x)) D) v
        + Tensor0SSpace.toModel
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
              (G.toSection x)) D) v := by
    intro F G
    rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((F + G).toSection x)) =
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from (F.toSection x))
          + (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from (G.toSection x)) from by
      rw [show (F + G).toSection x = F.toSection x + G.toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      ]
    rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
      ContinuousMultilinearMap.add_apply]
  have hsub_desc : ∀ (F G : SmoothCcTensor g₀ 2 2),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          ((F - G).toSection x)) D) v =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (F.toSection x)) D) v
        - Tensor0SSpace.toModel
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
              (G.toSection x)) D) v := by
    intro F G
    rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((F - G).toSection x)) =
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from (F.toSection x))
          - (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from (G.toSection x)) from by
      rw [show (F - G).toSection x = F.toSection x - G.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      ]
    rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply]
  have hARM : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((deTurckLieCovDerivArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀).toSection x)) D) v =
      (-1 : ℝ) * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
            (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 0)
              (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
              (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
            (v 1) +
          (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
            (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 1)
              (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
              (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
            (v 0)) *
          Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
              (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((deTurckLieCovDerivArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀).toSection x)) D) =
      connDiffCovDerivBiContrFib (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x D from rfl]
    rw [show (connDiffCovDerivBiContrFib (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x :
        Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x) =
      connDiffCovDerivBiContrFibFixedFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x) x from rfl]
    exact dLaBiContrFibFixedFrame_toModel (I := I)
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
      (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x) x D v
  have hfield : deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
      ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
        Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
        Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
      ![(-1 : ℝ), -1, 1] s =
      s • ((-1 : ℝ) • ((1 / 2 : ℝ) •
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    (((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
                        (Equiv.swap (0 : Fin 4) 1)).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))))
        + (-1 : ℝ) • ((1 / 2 : ℝ) •
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    ((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                        Equiv.swap (0 : Fin 4) 1).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    (((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                          Equiv.swap (0 : Fin 4) 1).trans
                        (Equiv.swap (0 : Fin 4) 1)).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))))
        + (1 : ℝ) • ((1 / 2 : ℝ) •
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    (((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
                        (Equiv.swap (0 : Fin 4) 1)).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))))) := by
    rw [deTurckLieCovDerivRefoldPairTraceFamily, Fin.sum_univ_three]
    rfl
  rw [hfield]
  simp only [hsub_desc, hsmul_desc, hadd_desc]
  rw [hARM]
  rw [bdPairTraceOp_apply_toModel (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (domDomCongrSection (I := I) g₀
        ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
        (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x D v,
    bdPairTraceOp_apply_toModel (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (domDomCongrSection (I := I) g₀
        (((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
            (Equiv.swap (0 : Fin 4) 1)).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
        (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x D v,
    bdPairTraceOp_apply_toModel (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (domDomCongrSection (I := I) g₀
        ((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
            Equiv.swap (0 : Fin 4) 1).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
        (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x D v,
    bdPairTraceOp_apply_toModel (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (domDomCongrSection (I := I) g₀
        (((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
              Equiv.swap (0 : Fin 4) 1).trans
            (Equiv.swap (0 : Fin 4) 1)).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
        (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x D v,
    bdPairTraceOp_apply_toModel (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (domDomCongrSection (I := I) g₀
        ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
        (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x D v,
    bdPairTraceOp_apply_toModel (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (domDomCongrSection (I := I) g₀
        (((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
            (Equiv.swap (0 : Fin 4) 1)).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
        (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x D v]
  rw [bdPairTraceOp_apply_toModel (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T 0 hδ hδZ s)
    (lrR4 (I := I) (M := M) g₀ T hδ hδZ s) x D v]
  rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      ((realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 0)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
          (v 1) +
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 1)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
          (v 0)) *
        Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]) =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
      ((realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 0)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
          (v 1) +
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 1)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
          (v 0)) *
        Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
    from Finset.sum_comm]
  have hpoint : ∀ (b : Fin (Module.finrank ℝ E)) (a : Fin (Module.finrank ℝ E)),
      Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
        unitModel (I := I) (M := M) g₀ 4 (lrR4 (I := I) (M := M) g₀ T hδ hδZ s) x
          ![v 0, v 1,
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] =
      ((realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 0)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
          (v 1) +
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 1)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
          (v 0)) *
        Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
      + s * ((-1 : ℝ) * ((1 / 2 : ℝ) *
          (Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
          + Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                (((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
                    (Equiv.swap (0 : Fin 4) 1)).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]))
        + ((-1 : ℝ) * ((1 / 2 : ℝ) *
          (Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                ((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                    Equiv.swap (0 : Fin 4) 1).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
          + Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                (((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                      Equiv.swap (0 : Fin 4) 1).trans
                    (Equiv.swap (0 : Fin 4) 1)).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]))
        + (1 : ℝ) * ((1 / 2 : ℝ) *
          (Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
          + Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                (((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
                    (Equiv.swap (0 : Fin 4) 1)).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)])))) := by
    intro b a
    have hddc : ∀ (σ : Equiv.Perm (Fin 4)) (m0 m1 m2 m3 : TangentSpace I x),
        unitModel (I := I) (M := M) g₀ 4
          (domDomCongrSection (I := I) g₀ σ (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
          ![m0, m1, m2, m3] =
        unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T) x
          (fun i => (![m0, m1, m2, m3] : Fin 4 → TangentSpace I x) (σ i)) := by
      intro σ m0 m1 m2 m3
      rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [hddc, hddc, hddc, hddc, hddc, hddc]
    rw [show (fun i => (![v 0, v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] :
        Fin 4 → TangentSpace I x)
        (((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) i)) =
      ![v 0,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E),
        v 1] from by
      funext i
      fin_cases i <;> rfl]
    rw [show (fun i => (![v 0, v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] :
        Fin 4 → TangentSpace I x)
        ((((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
            (Equiv.swap (0 : Fin 4) 1)).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) i)) =
      ![v 0,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        v 1] from by
      funext i
      fin_cases i <;> rfl]
    rw [show (fun i => (![v 0, v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] :
        Fin 4 → TangentSpace I x)
        (((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
            Equiv.swap (0 : Fin 4) 1).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) i)) =
      ![v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E),
        v 0] from by
      funext i
      fin_cases i <;> rfl]
    rw [show (fun i => (![v 0, v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] :
        Fin 4 → TangentSpace I x)
        ((((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
              Equiv.swap (0 : Fin 4) 1).trans
            (Equiv.swap (0 : Fin 4) 1)).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) i)) =
      ![v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        v 0] from by
      funext i
      fin_cases i <;> rfl]
    rw [show (fun i => (![v 0, v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] :
        Fin 4 → TangentSpace I x)
        (((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) i)) =
      ![v 0, v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] from by
      funext i
      fin_cases i <;> rfl]
    rw [show (fun i => (![v 0, v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] :
        Fin 4 → TangentSpace I x)
        ((((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
            (Equiv.swap (0 : Fin 4) 1)).trans
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) i)) =
      ![v 0, v 1,
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E)] from by
      funext i
      fin_cases i <;> rfl]
    have hsummand := lrSummand (I := I) (M := M) g₀ T hδ_lt hδ hδZ hTsymm hs x
      (v 0) (v 1)
      (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
      (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x)
    linear_combination (-(Tensor0SSpace.toModel D
      ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
        (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)])) *
      hsummand
  rw [show (∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
        unitModel (I := I) (M := M) g₀ 4 (lrR4 (I := I) (M := M) g₀ T hδ hδZ s) x
          ![v 0, v 1,
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]) =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        (((realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 0)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
          (v 1) +
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner x
          (connDiffCovDerivOp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ x (v 1)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x)
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x))
          (v 0)) *
        Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
            (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
      + s * ((-1 : ℝ) * ((1 / 2 : ℝ) *
          (Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
          + Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                (((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
                    (Equiv.swap (0 : Fin 4) 1)).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]))
        + ((-1 : ℝ) * ((1 / 2 : ℝ) *
          (Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                ((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                    Equiv.swap (0 : Fin 4) 1).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
          + Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                (((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                      Equiv.swap (0 : Fin 4) 1).trans
                    (Equiv.swap (0 : Fin 4) 1)).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]))
        + (1 : ℝ) * ((1 / 2 : ℝ) *
          (Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)]
          + Tensor0SSpace.toModel D
              ![(smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)] *
            unitModel (I := I) (M := M) g₀ 4
              (domDomCongrSection (I := I) g₀
                (((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
                    (Equiv.swap (0 : Fin 4) 1)).trans
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T)) x
              ![v 0, v 1,
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x a x : E),
                (smoothOrthoFrame (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x b x : E)])))))
    from Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => hpoint b a]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private lemma lrSingle_b_le_grid (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (q : ℕ) (hq : 1 ≤ q) :
    b q ≤ Combinatorics.antidiagonalTupleGrid b q := by
  have h := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb 0 q hq
  rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
  rwa [zero_add] at h

private lemma lrBFGW_mono_of_le (b b' : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (hbb : ∀ j, b j ≤ b' j) (K w : ℕ) :
    Combinatorics.boundedFactorGridWindow b K w ≤
      Combinatorics.boundedFactorGridWindow b' K w := by
  rw [Combinatorics.boundedFactorGridWindow, Combinatorics.boundedFactorGridWindow]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Combinatorics.boundedFactorGrid, Combinatorics.boundedFactorGrid]
  refine Finset.sum_le_sum fun n _ => ?_
  refine Finset.sum_le_sum fun e _ => ?_
  exact Finset.prod_le_prod (fun m _ => hb (e m)) (fun m _ => hbb (e m))


private lemma lrWindow_le_bFGW (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {K W W' : ℕ}
    (hK : W ≤ K + 1) (hW : W ≤ W') (_hW1 : 1 ≤ W') :
    Combinatorics.antidiagonalTupleGridWindow b W ≤
      (W : ℝ) * Combinatorics.boundedFactorGridWindow b K W' := by
  rw [Combinatorics.antidiagonalTupleGridWindow]
  calc ∑ k ∈ Finset.range W, Combinatorics.antidiagonalTupleGrid b k
      ≤ ∑ _k ∈ Finset.range W, Combinatorics.boundedFactorGridWindow b K W' := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [Finset.mem_range] at hk
        exact Combinatorics.antidiagonalTupleGrid_le_boundedFactorGridWindow b hb
          (by omega) (by omega)
    _ = (W : ℝ) * Combinatorics.boundedFactorGridWindow b K W' := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


private lemma lrTcell_bfgw (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {Λ0 : ℝ} (hΛ0 : 0 ≤ Λ0)
    (h0 : b 0 ≤ Λ0) {n K W : ℕ} (hnK : n ≤ K) (hnW : n + 1 ≤ W) :
    b n ≤ (Λ0 + 1) * Combinatorics.boundedFactorGridWindow b K W := by
  have hone : (1 : ℝ) ≤ Combinatorics.boundedFactorGridWindow b K W :=
    Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
  have hW_nn : (0 : ℝ) ≤ Combinatorics.boundedFactorGridWindow b K W := by linarith
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    nlinarith [hΛ0, hone, h0, hb 0]
  · have hsingle : b n ≤ Combinatorics.antidiagonalTupleGrid b n :=
      lrSingle_b_le_grid b hb n hn1
    have hgw : Combinatorics.antidiagonalTupleGrid b n ≤
        Combinatorics.boundedFactorGridWindow b K W :=
      Combinatorics.antidiagonalTupleGrid_le_boundedFactorGridWindow b hb hnK (by omega)
    nlinarith [le_trans hsingle hgw, hΛ0, hW_nn]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
private theorem exists_sobolev_pointwise_bound_zero_order (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Csob : ℝ, 0 ≤ Csob ∧
      ∀ (T : SmoothCcTensor g₀ 0 2) {R : ℝ} (_hR : 0 ≤ R),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x) ≤
            (Csob * R) ^ 2 := by
  classical
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_Csob_convexPerturbation_pointwise_C2_le (I := I) (M := M) g₀ a ha_super
  refine ⟨Csob, hCsob_nn, ?_⟩
  intro T R hR hball x
  have hball0 : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j hj
    rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • T from (zero_smul ℝ T).symm,
      iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs, abs_zero, zero_mul]
    exact hR
  have hsum := hCsob T 0 hR hball hball0 1 ⟨by norm_num, le_refl 1⟩ x
  have hterms : ∀ k ∈ Finset.range 3, 0 ≤
      (letI : Bundle.RiemannianBundle
          (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
      ‖(iteratedCovGrad (I := I) g₀ 0 2 k
          (convexPerturbation (I := I) g₀ T 0 1)).toSection x‖) := by
    intro k _
    letI : Bundle.RiemannianBundle
        (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
    exact norm_nonneg _
  have h0 := le_trans (Finset.single_le_sum hterms
    (show (0 : ℕ) ∈ Finset.range 3 from Finset.mem_range.mpr (by norm_num))) hsum
  have hcp1 : convexPerturbation (I := I) g₀ T 0 1 = T := by
    rw [convexPerturbation, smul_zero, zero_add, one_smul]
  rw [hcp1, iteratedCovGrad_zero] at h0
  letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
  have h0' : ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ≤ Csob * R := h0
  have hb : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x) =
      ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 :=
    riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 2 x (T.toSection x)
  have hnn : (0 : ℝ) ≤ ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ :=
    norm_nonneg _
  nlinarith [h0', hb, hnn, mul_nonneg hCsob_nn hR]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
private theorem exists_sobolev_pointwise_bound_first_order (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Csob : ℝ, 0 ≤ Csob ∧
      ∀ (T : SmoothCcTensor g₀ 0 2) {R : ℝ} (_hR : 0 ≤ R),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
            ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) ≤
            (Csob * R) ^ 2 := by
  classical
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_Csob_convexPerturbation_pointwise_C2_le (I := I) (M := M) g₀ a ha_super
  refine ⟨Csob, hCsob_nn, ?_⟩
  intro T R hR hball x
  have hball0 : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j hj
    rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • T from (zero_smul ℝ T).symm,
      iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs, abs_zero, zero_mul]
    exact hR
  have hsum := hCsob T 0 hR hball hball0 1 ⟨by norm_num, le_refl 1⟩ x
  have hterms : ∀ k ∈ Finset.range 3, 0 ≤
      (letI : Bundle.RiemannianBundle
          (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
      ‖(iteratedCovGrad (I := I) g₀ 0 2 k
          (convexPerturbation (I := I) g₀ T 0 1)).toSection x‖) := by
    intro k _
    letI : Bundle.RiemannianBundle
        (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
    exact norm_nonneg _
  have h1 := le_trans (Finset.single_le_sum hterms
    (show (1 : ℕ) ∈ Finset.range 3 from Finset.mem_range.mpr (by norm_num))) hsum
  have hcp1 : convexPerturbation (I := I) g₀ T 0 1 = T := by
    rw [convexPerturbation, smul_zero, zero_add, one_smul]
  rw [hcp1] at h1
  letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + 1) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
  have h1' : ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 (2 + 1) I x)‖ ≤ Csob * R := h1
  have hb : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) =
      ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
        Tensor0SBundle.TensorRSSpace 0 (2 + 1) I x)‖ ^ 2 :=
    riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 1) x _
  have hnn : (0 : ℝ) ≤ ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 (2 + 1) I x)‖ := norm_nonneg _
  nlinarith [h1', hb, hnn, mul_nonneg hCsob_nn hR]


private theorem riemannCurvatureCoeffFieldGridWindow (g₀ : SmoothRiemannianMetric I M) (Λ0 : ℝ) (hΛ0 : 0 ≤ Λ0) :
    ∃ C : ℕ → ℝ, (∀ w, 0 ≤ C w) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hT0 : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x) ≤ Λ0)
        (w K : ℕ) (_hwK : w ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (riemannCurvatureCoeffField (I := I) (M := M) g₀ T)).toSection x) ≤
          C w * Combinatorics.boundedFactorGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x)) K (w + 2) := by
  classical
  obtain ⟨cW1, hcW1_nn, hcW1⟩ := bdExists_fixedField_rfns_jet (I := I) (M := M) g₀ 2 4
    (riemannLoweredContractionA (I := I) (M := M) g₀)
  obtain ⟨cW2, hcW2_nn, hcW2⟩ := bdExists_fixedField_rfns_jet (I := I) (M := M) g₀ 2 4
    (riemannLoweredContractionB (I := I) (M := M) g₀)
  refine ⟨fun w => 2 * (diagonalGridGrowthFactor (E := E) w * ∑ i' ∈ Finset.range (w + 1),
      cW1 i' * (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1)))
    + 2 * (diagonalGridGrowthFactor (E := E) w * ∑ i' ∈ Finset.range (w + 1),
      cW2 i' * (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1))),
    fun w => by
      have h1 : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) w * ∑ i' ∈ Finset.range (w + 1),
          cW1 i' * (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1)) :=
        mul_nonneg (appCcGdiag_nonneg (E := E) w)
          (Finset.sum_nonneg fun i' _ => mul_nonneg (hcW1_nn i')
            (mul_nonneg (Nat.cast_nonneg _) (by linarith)))
      have h2 : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) w * ∑ i' ∈ Finset.range (w + 1),
          cW2 i' * (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1)) :=
        mul_nonneg (appCcGdiag_nonneg (E := E) w)
          (Finset.sum_nonneg fun i' _ => mul_nonneg (hcW2_nn i')
            (mul_nonneg (Nat.cast_nonneg _) (by linarith)))
      linarith, ?_⟩
  intro T hT0 w K hwK x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set W : ℝ := Combinatorics.boundedFactorGridWindow b K (w + 2) with hW_def
  have hW_nn : (0 : ℝ) ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb K (w + 2)
  have hb0 : b 0 ≤ Λ0 := by
    have := hT0 x
    rw [hb_def]
    simpa [iteratedCovGrad_zero] using this
  have hcell : ∀ l' : ℕ, l' ≤ w → b l' ≤ (Λ0 + 1) * W := by
    intro l' hl'
    exact lrTcell_bfgw b hb hΛ0 hb0 (by omega) (by omega)
  have hpart : ∀ (F : SmoothCcTensor g₀ 2 4) (cF : ℕ → ℝ) (hcF_nn : ∀ j, 0 ≤ cF j)
      (hcF : ∀ (j : ℕ) (y : M), riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + j) y
        ((iteratedCovGrad (I := I) g₀ 2 4 j F).toSection y) ≤ cF j),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 F T)).toSection x) ≤
        (diagonalGridGrowthFactor (E := E) w * ∑ i' ∈ Finset.range (w + 1),
          cF i' * (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1))) * W := by
    intro F cF hcF_nn hcF
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ w 0 2 4 F T x) ?_
    have hcell2 : ∀ i' ∈ Finset.range (w + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i') x
            ((iteratedCovGrad (I := I) g₀ 2 4 i' F).toSection x) *
          ∑ l ∈ Finset.range (w + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) ≤
        (cF i' * (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1))) * W := by
      intro i' hi'
      rw [Finset.mem_range] at hi'
      have hA1 := hcF i' x
      have hA2 : (∑ l ∈ Finset.range (w + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) ≤
          (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1)) * W := by
        calc (∑ l ∈ Finset.range (w + 1 - i'), b l)
            ≤ ∑ _l ∈ Finset.range (w + 1 - i'), (Λ0 + 1) * W := by
              refine Finset.sum_le_sum fun l hl => ?_
              rw [Finset.mem_range] at hl
              exact hcell l (by omega)
          _ = (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1)) * W := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
      have hsum_nn : (0 : ℝ) ≤ ∑ l ∈ Finset.range (w + 1 - i'), b l :=
        Finset.sum_nonneg fun l _ => hb l
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i') x
            ((iteratedCovGrad (I := I) g₀ 2 4 i' F).toSection x) *
          ∑ l ∈ Finset.range (w + 1 - i'), b l
          ≤ cF i' * ((((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1)) * W) :=
            mul_le_mul hA1 hA2 hsum_nn (hcF_nn i')
        _ = (cF i' * (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1))) * W := by ring
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell2)
      (appCcGdiag_nonneg (E := E) w)) ?_
    rw [← Finset.sum_mul, ← mul_assoc]
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
      ((iteratedCovGrad (I := I) g₀ 0 4 w (riemannCurvatureCoeffField (I := I) (M := M) g₀ T)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 (riemannLoweredContractionA (I := I) (M := M) g₀)
              T)).toSection x)
        + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 (riemannLoweredContractionB (I := I) (M := M) g₀)
                T)).toSection x) := by
    rw [riemannCurvatureCoeffField]
    exact bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 w _ _ x
  refine le_trans hsplit ?_
  have h1 := hpart (riemannLoweredContractionA (I := I) (M := M) g₀) cW1 hcW1_nn hcW1
  have h2 := hpart (riemannLoweredContractionB (I := I) (M := M) g₀) cW2 hcW2_nn hcW2
  nlinarith [h1, h2, hW_nn]


private theorem lrOmegaHat_gridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ l, 0 ≤ C l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 3 l
              (connDiffGmLoweredTensor (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C l * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (l + 2) := by
  classical
  obtain ⟨CΩ, hCΩ_nn, hCΩ⟩ := bdOmRecover_gridWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun l => diagonalGridGrowthFactor (E := E) l *
      ∑ i' ∈ Finset.range (l + 1), (fr ^ 2 * CΩ i') *
        ∑ l' ∈ Finset.range (l + 1 - i'),
          CA l' * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1),
    fun l => mul_nonneg (appCcGdiag_nonneg (E := E) l)
      (Finset.sum_nonneg fun i' _ => mul_nonneg
        (mul_nonneg (by positivity) (hCΩ_nn i'))
        (Finset.sum_nonneg fun l' _ => mul_nonneg (hCA_nn l')
          (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound l x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set W : ℝ := Combinatorics.antidiagonalTupleGridWindow b (l + 2) with hW_def
  have hW_nn : (0 : ℝ) ≤ W := Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (l + 2)
  rw [connDiffGmLoweredTensor]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ l 0 3 3
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 (fullRaisedEndoField (I := I) (M := M) g₁ g₀))
    (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x) ?_
  have hop : ∀ i' : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + i') x
          ((iteratedCovGrad (I := I) g₀ 3 3 i'
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
              (fullRaisedEndoField (I := I) (M := M) g₁ g₀))).toSection x) ≤
        (fr ^ 2 * CΩ i') * Combinatorics.antidiagonalTupleGridWindow b (i' + 1) := by
    intro i'
    refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 2
      (fullRaisedEndoField (I := I) (M := M) g₁ g₀) i' x) ?_
    rw [bdSlotInsertZero_fullRaisedRev_eq_omRecover (I := I) (M := M) g₀ g₁]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hCΩ g₁ P htie hδ_le hδ0 hbound i' x) (by positivity)
  have hsec : ∀ l' : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 3 l'
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) ≤
        CA l' * Combinatorics.antidiagonalTupleGridWindow b (l' + 2) := by
    intro l'
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁) l' x]
    rw [bdRfns_iCG_connDiffLoweredCc_eq_connDiffSection (I := I) (M := M) g₀ g₁ l' x]
    have h := hCA g₁ P htie hδ_le hδ0 hbound l' x
    rwa [show (∑ k ∈ Finset.range (l' + 2), Combinatorics.antidiagonalTupleGrid b k) =
      Combinatorics.antidiagonalTupleGridWindow b (l' + 2) from rfl] at h
  have hcell : ∀ i' ∈ Finset.range (l + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + i') x
          ((iteratedCovGrad (I := I) g₀ 3 3 i'
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
              (fullRaisedEndoField (I := I) (M := M) g₁ g₀))).toSection x) *
        ∑ l' ∈ Finset.range (l + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
            ((iteratedCovGrad (I := I) g₀ 0 3 l'
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) ≤
        ((fr ^ 2 * CΩ i') * ∑ l' ∈ Finset.range (l + 1 - i'),
          CA l' * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1)) * W := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA2 : (∑ l' ∈ Finset.range (l + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 3 l'
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x)) ≤
        ∑ l' ∈ Finset.range (l + 1 - i'),
          CA l' * Combinatorics.antidiagonalTupleGridWindow b (l' + 2) :=
      Finset.sum_le_sum fun l' _ => hsec l'
    have hsum_nn : (0 : ℝ) ≤ ∑ l' ∈ Finset.range (l + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 3 l'
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) :=
      Finset.sum_nonneg fun l' _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + l') x _
    have hA1_rhs_nn : (0 : ℝ) ≤ (fr ^ 2 * CΩ i') *
        Combinatorics.antidiagonalTupleGridWindow b (i' + 1) :=
      mul_nonneg (mul_nonneg (by positivity) (hCΩ_nn i'))
        (Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i' + 1))
    refine le_trans (mul_le_mul (hop i') hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show ((fr ^ 2 * CΩ i') * ∑ l' ∈ Finset.range (l + 1 - i'),
        CA l' * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1)) * W =
        ∑ l' ∈ Finset.range (l + 1 - i'),
          ((fr ^ 2 * CΩ i') * (CA l' *
            Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1))) * W from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l' hl' => ?_
    rw [Finset.mem_range] at hl'
    have hpair : Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
        Combinatorics.antidiagonalTupleGridWindow b (l' + 1 + 1) ≤
        Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1) *
          Combinatorics.antidiagonalTupleGridWindow b (i' + (l' + 1) + 1) :=
      Combinatorics.antidiagonalTupleGridWindow_mul_le b hb i' (l' + 1)
    have hmono : Combinatorics.antidiagonalTupleGridWindow b (i' + (l' + 1) + 1) ≤ W := by
      rw [hW_def]
      exact Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
    calc (fr ^ 2 * CΩ i') * Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
          (CA l' * Combinatorics.antidiagonalTupleGridWindow b (l' + 2))
        = ((fr ^ 2 * CΩ i') * CA l') *
            (Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
              Combinatorics.antidiagonalTupleGridWindow b (l' + 1 + 1)) := by
          rw [show l' + 2 = l' + 1 + 1 from rfl]
          ring
      _ ≤ ((fr ^ 2 * CΩ i') * CA l') *
            (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1) *
              Combinatorics.antidiagonalTupleGridWindow b (i' + (l' + 1) + 1)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (mul_nonneg (by positivity) (hCΩ_nn i')) (hCA_nn l')
      _ ≤ ((fr ^ 2 * CΩ i') * CA l') *
            (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1) * W) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (mul_nonneg (by positivity) (hCΩ_nn i')) (hCA_nn l'))
          exact mul_le_mul_of_nonneg_left hmono
            (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _)
      _ = ((fr ^ 2 * CΩ i') * (CA l' *
            Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1))) * W := by
          ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) l)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]


private theorem connDiffQuadraticCurvatureTermGridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ w, 0 ≤ C w) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (w K : ℕ) (_hwK : w + 1 ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (connDiffQuadraticCurvatureTerm (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C w * Combinatorics.boundedFactorGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) K (w + 3) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨CΩ, hCΩ_nn, hCΩ⟩ := lrOmegaHat_gridWindow (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set CQ : ℕ → ℝ := fun w => diagonalGridGrowthFactor (E := E) w *
    ∑ u' ∈ Finset.range (w + 1), (fr ^ 2 * CA u') *
      ∑ w' ∈ Finset.range (w + 1 - u'),
        CΩ w' * (((u' + 2 : ℕ) : ℝ) * ((w' + 2 : ℕ) : ℝ) *
          Combinatorics.windowPairCellCount (u' + 2) (w' + 2)) with hCQ_def
  have hCQ_nn : ∀ w, 0 ≤ CQ w := by
    intro w
    rw [hCQ_def]
    exact mul_nonneg (appCcGdiag_nonneg (E := E) w)
      (Finset.sum_nonneg fun u' _ => mul_nonneg
        (mul_nonneg (by positivity) (hCA_nn u'))
        (Finset.sum_nonneg fun w' _ => mul_nonneg (hCΩ_nn w')
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            (Combinatorics.windowPairCellCount_nonneg _ _))))
  refine ⟨fun w => 94 * CQ w, fun w => by have := hCQ_nn w; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound w K hwK x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set W : ℝ := Combinatorics.boundedFactorGridWindow b K (w + 3) with hW_def
  have hW_nn : (0 : ℝ) ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb K (w + 3)
  have hbase : ∀ (S : SmoothCcTensor g₀ 0 3)
      (hS : ∀ (w' : ℕ) (y : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w') y
            ((iteratedCovGrad (I := I) g₀ 0 3 w' S).toSection y) ≤
          CΩ w' * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') y
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection y)) (w' + 2)),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
              (armSlotEndoCc (I := I) (M := M) g₀ 2 (connDiffEndo (I := I) (M := M) g₀ g₁))
              S)).toSection x) ≤
        CQ w * W := by
    intro S hS
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ w 0 3 4
      (armSlotEndoCc (I := I) (M := M) g₀ 2 (connDiffEndo (I := I) (M := M) g₀ g₁)) S x) ?_
    have hcell : ∀ u' ∈ Finset.range (w + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + u') x
            ((iteratedCovGrad (I := I) g₀ 3 4 u'
              (armSlotEndoCc (I := I) (M := M) g₀ 2
                (connDiffEndo (I := I) (M := M) g₀ g₁))).toSection x) *
          ∑ w' ∈ Finset.range (w + 1 - u'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w') x
              ((iteratedCovGrad (I := I) g₀ 0 3 w' S).toSection x) ≤
        ((fr ^ 2 * CA u') * ∑ w' ∈ Finset.range (w + 1 - u'),
          CΩ w' * (((u' + 2 : ℕ) : ℝ) * ((w' + 2 : ℕ) : ℝ) *
            Combinatorics.windowPairCellCount (u' + 2) (w' + 2))) * W := by
      intro u' hu'
      rw [Finset.mem_range] at hu'
      have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + u') x
          ((iteratedCovGrad (I := I) g₀ 3 4 u'
            (armSlotEndoCc (I := I) (M := M) g₀ 2
              (connDiffEndo (I := I) (M := M) g₀ g₁))).toSection x) ≤
          (fr ^ 2 * CA u') * Combinatorics.antidiagonalTupleGridWindow b (u' + 2) := by
        refine le_trans (bdArmSlot2_rfns_le (I := I) (M := M) g₀ g₁ u' x) ?_
        rw [← hfr_def, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h2 := hCA g₁ P htie hδ_le hδ0 hbound u' x
        rwa [show (∑ k ∈ Finset.range (u' + 2), Combinatorics.antidiagonalTupleGrid b k) =
          Combinatorics.antidiagonalTupleGridWindow b (u' + 2) from rfl] at h2
      have hA2 : (∑ w' ∈ Finset.range (w + 1 - u'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w') x
            ((iteratedCovGrad (I := I) g₀ 0 3 w' S).toSection x)) ≤
          ∑ w' ∈ Finset.range (w + 1 - u'),
            CΩ w' * Combinatorics.antidiagonalTupleGridWindow b (w' + 2) :=
        Finset.sum_le_sum fun w' _ => hS w' x
      have hsum_nn : (0 : ℝ) ≤ ∑ w' ∈ Finset.range (w + 1 - u'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w') x
            ((iteratedCovGrad (I := I) g₀ 0 3 w' S).toSection x) :=
        Finset.sum_nonneg fun w' _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + w') x _
      have hA1_rhs_nn : (0 : ℝ) ≤ (fr ^ 2 * CA u') *
          Combinatorics.antidiagonalTupleGridWindow b (u' + 2) :=
        mul_nonneg (mul_nonneg (by positivity) (hCA_nn u'))
          (Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (u' + 2))
      refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
      rw [Finset.mul_sum]
      rw [show ((fr ^ 2 * CA u') * ∑ w' ∈ Finset.range (w + 1 - u'),
          CΩ w' * (((u' + 2 : ℕ) : ℝ) * ((w' + 2 : ℕ) : ℝ) *
            Combinatorics.windowPairCellCount (u' + 2) (w' + 2))) * W =
          ∑ w' ∈ Finset.range (w + 1 - u'),
            ((fr ^ 2 * CA u') * (CΩ w' * (((u' + 2 : ℕ) : ℝ) * ((w' + 2 : ℕ) : ℝ) *
              Combinatorics.windowPairCellCount (u' + 2) (w' + 2)))) * W from by
        rw [Finset.mul_sum, Finset.sum_mul]]
      refine Finset.sum_le_sum fun w' hw' => ?_
      rw [Finset.mem_range] at hw'
      have hbf1 : Combinatorics.antidiagonalTupleGridWindow b (u' + 2) ≤
          ((u' + 2 : ℕ) : ℝ) * Combinatorics.boundedFactorGridWindow b K (u' + 2) :=
        lrWindow_le_bFGW b hb (by omega) (le_refl _) (by omega)
      have hbf2 : Combinatorics.antidiagonalTupleGridWindow b (w' + 2) ≤
          ((w' + 2 : ℕ) : ℝ) * Combinatorics.boundedFactorGridWindow b K (w' + 2) :=
        lrWindow_le_bFGW b hb (by omega) (le_refl _) (by omega)
      have hmul : Combinatorics.boundedFactorGridWindow b K (u' + 2) *
          Combinatorics.boundedFactorGridWindow b K (w' + 2) ≤
          Combinatorics.windowPairCellCount (u' + 2) (w' + 2) *
            Combinatorics.boundedFactorGridWindow b K (u' + 2 + (w' + 2) - 1) :=
        Combinatorics.boundedFactorGridWindow_mul_le b hb K (u' + 2) (w' + 2)
          (by omega) (by omega)
      have hmono : Combinatorics.boundedFactorGridWindow b K (u' + 2 + (w' + 2) - 1) ≤ W := by
        rw [hW_def]
        exact Combinatorics.boundedFactorGridWindow_mono b hb (le_refl K) (by omega)
      have hbf_nn1 : (0 : ℝ) ≤ Combinatorics.boundedFactorGridWindow b K (u' + 2) :=
        Combinatorics.boundedFactorGridWindow_nonneg b hb K _
      have hbf_nn2 : (0 : ℝ) ≤ Combinatorics.boundedFactorGridWindow b K (w' + 2) :=
        Combinatorics.boundedFactorGridWindow_nonneg b hb K _
      have hcnt_nn : (0 : ℝ) ≤ Combinatorics.windowPairCellCount (u' + 2) (w' + 2) :=
        Combinatorics.windowPairCellCount_nonneg _ _
      have hwin1_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (u' + 2) :=
        Combinatorics.antidiagonalTupleGridWindow_nonneg b hb _
      have hwin2_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (w' + 2) :=
        Combinatorics.antidiagonalTupleGridWindow_nonneg b hb _
      calc (fr ^ 2 * CA u') * Combinatorics.antidiagonalTupleGridWindow b (u' + 2) *
            (CΩ w' * Combinatorics.antidiagonalTupleGridWindow b (w' + 2))
          = ((fr ^ 2 * CA u') * CΩ w') *
              (Combinatorics.antidiagonalTupleGridWindow b (u' + 2) *
                Combinatorics.antidiagonalTupleGridWindow b (w' + 2)) := by ring
        _ ≤ ((fr ^ 2 * CA u') * CΩ w') *
              ((((u' + 2 : ℕ) : ℝ) * Combinatorics.boundedFactorGridWindow b K (u' + 2)) *
                (((w' + 2 : ℕ) : ℝ) * Combinatorics.boundedFactorGridWindow b K (w' + 2))) := by
            refine mul_le_mul_of_nonneg_left ?_
              (mul_nonneg (mul_nonneg (by positivity) (hCA_nn u')) (hCΩ_nn w'))
            exact mul_le_mul hbf1 hbf2 hwin2_nn
              (mul_nonneg (Nat.cast_nonneg _) hbf_nn1)
        _ = ((fr ^ 2 * CA u') * CΩ w') * (((u' + 2 : ℕ) : ℝ) * ((w' + 2 : ℕ) : ℝ)) *
              (Combinatorics.boundedFactorGridWindow b K (u' + 2) *
                Combinatorics.boundedFactorGridWindow b K (w' + 2)) := by ring
        _ ≤ ((fr ^ 2 * CA u') * CΩ w') * (((u' + 2 : ℕ) : ℝ) * ((w' + 2 : ℕ) : ℝ)) *
              (Combinatorics.windowPairCellCount (u' + 2) (w' + 2) *
                Combinatorics.boundedFactorGridWindow b K (u' + 2 + (w' + 2) - 1)) := by
            refine mul_le_mul_of_nonneg_left hmul ?_
            exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (hCA_nn u'))
              (hCΩ_nn w')) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        _ ≤ ((fr ^ 2 * CA u') * CΩ w') * (((u' + 2 : ℕ) : ℝ) * ((w' + 2 : ℕ) : ℝ)) *
              (Combinatorics.windowPairCellCount (u' + 2) (w' + 2) * W) := by
            refine mul_le_mul_of_nonneg_left ?_
              (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (hCA_nn u'))
                (hCΩ_nn w')) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
            exact mul_le_mul_of_nonneg_left hmono hcnt_nn
        _ = ((fr ^ 2 * CA u') * (CΩ w' * (((u' + 2 : ℕ) : ℝ) * ((w' + 2 : ℕ) : ℝ) *
              Combinatorics.windowPairCellCount (u' + 2) (w' + 2)))) * W := by ring
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
      (appCcGdiag_nonneg (E := E) w)) ?_
    rw [← Finset.sum_mul, ← mul_assoc, hCQ_def]
  have hΩ : ∀ (w' : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w') y
          ((iteratedCovGrad (I := I) g₀ 0 3 w'
            (connDiffGmLoweredTensor (I := I) (M := M) g₀ g₁)).toSection y) ≤
        CΩ w' * Combinatorics.antidiagonalTupleGridWindow
          (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') y
            ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection y)) (w' + 2) :=
    fun w' y => hCΩ g₁ P htie hδ_le hδ0 hbound w' y
  have hΩswap : ∀ (w' : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w') y
          ((iteratedCovGrad (I := I) g₀ 0 3 w'
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1)
              (connDiffGmLoweredTensor (I := I) (M := M) g₀ g₁))).toSection y) ≤
        CΩ w' * Combinatorics.antidiagonalTupleGridWindow
          (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') y
            ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection y)) (w' + 2) := by
    intro w' y
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 3) 1) (connDiffGmLoweredTensor (I := I) (M := M) g₀ g₁) w' y]
    exact hΩ w' y
  have hQB := hbase (connDiffGmLoweredTensor (I := I) (M := M) g₀ g₁) hΩ
  have hQA := hbase (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1)
    (connDiffGmLoweredTensor (I := I) (M := M) g₀ g₁)) hΩswap
  have hQB' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
      ((iteratedCovGrad (I := I) g₀ 0 4 w (connDiffQuadraticPairedTensor (I := I) (M := M) g₀ g₁)).toSection x) ≤
      CQ w * W := by
    rw [connDiffQuadraticPairedTensor]
    exact hQB
  have hQA' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
      ((iteratedCovGrad (I := I) g₀ 0 4 w (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ g₁)).toSection x) ≤
      CQ w * W := by
    rw [connDiffQuadraticComposedTensor]
    exact hQA
  have hddcQ : ∀ (σ : Equiv.Perm (Fin 4)) (F : SmoothCcTensor g₀ 0 4)
      (hF : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w F).toSection x) ≤ CQ w * W),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w
          (domDomCongrSection (I := I) g₀ σ F)).toSection x) ≤ CQ w * W := by
    intro σ F hF
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      σ F w x]
    exact hF
  rw [connDiffQuadraticCurvatureTerm]
  have hsum6 : ∀ (F1 F2 F3 F4 F5 F6 : SmoothCcTensor g₀ 0 4)
      (h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w F1).toSection x) ≤ CQ w * W)
      (h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w F2).toSection x) ≤ CQ w * W)
      (h3 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w F3).toSection x) ≤ CQ w * W)
      (h4 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w F4).toSection x) ≤ CQ w * W)
      (h5 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w F5).toSection x) ≤ CQ w * W)
      (h6 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w F6).toSection x) ≤ CQ w * W),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w
          (F1 + F2 + F3 + F4 + F5 + F6)).toSection x) ≤ 94 * (CQ w * W) := by
    intro F1 F2 F3 F4 F5 F6 h1 h2 h3 h4 h5 h6
    have ha1 := bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 w (F1 + F2 + F3 + F4 + F5) F6 x
    have ha2 := bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 w (F1 + F2 + F3 + F4) F5 x
    have ha3 := bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 w (F1 + F2 + F3) F4 x
    have ha4 := bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 w (F1 + F2) F3 x
    have ha5 := bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 w F1 F2 x
    have hnn : (0 : ℝ) ≤ CQ w * W := mul_nonneg (hCQ_nn w) hW_nn
    nlinarith [ha1, ha2, ha3, ha4, ha5, h1, h2, h3, h4, h5, h6,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w (F1 + F2 + F3 + F4 + F5)).toSection x),
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w (F1 + F2 + F3 + F4)).toSection x),
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w (F1 + F2 + F3)).toSection x),
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w (F1 + F2)).toSection x)]
  have h6 := hsum6
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1) (connDiffQuadraticPairedTensor (I := I) (M := M) g₀ g₁))
    (connDiffQuadraticPairedTensor (I := I) (M := M) g₀ g₁)
    (domDomCongrSection (I := I) g₀ lrPermA (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ g₁))
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 2) (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ g₁))
    (domDomCongrSection (I := I) g₀ lrPermB (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ g₁))
    (domDomCongrSection (I := I) g₀ lrPermC (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ g₁))
    (hddcQ _ _ hQB') hQB' (hddcQ _ _ hQA') (hddcQ _ _ hQA') (hddcQ _ _ hQA')
    (hddcQ _ _ hQA')
  refine le_trans h6 (le_of_eq ?_)
  ring

private lemma lrGridWindow_mono_of_le (b b' : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (hbb : ∀ j, b j ≤ b' j) (w : ℕ) :
    Combinatorics.antidiagonalTupleGridWindow b w ≤
      Combinatorics.antidiagonalTupleGridWindow b' w := by
  rw [Combinatorics.antidiagonalTupleGridWindow, Combinatorics.antidiagonalTupleGridWindow]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Combinatorics.antidiagonalTupleGrid, Combinatorics.antidiagonalTupleGrid]
  refine Finset.sum_le_sum fun n _ => ?_
  refine Finset.sum_le_sum fun e _ => ?_
  exact Finset.prod_le_prod (fun m _ => hb (e m)) (fun m _ => hbb (e m))


private theorem riemannCurvatureRemainderGridWindow (g₀ : SmoothRiemannianMetric I M) (Λ0 : ℝ) (hΛ0 : 0 ≤ Λ0)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ w, 0 ≤ C w) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hT0 : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x) ≤ Λ0)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
        {s : ℝ} (_hs : s ∈ Set.Icc (0 : ℝ) 1)
        (w K : ℕ) (_hwK : w + 1 ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)).toSection x) ≤
          C w * Combinatorics.boundedFactorGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x)) K (w + 3) := by
  classical
  obtain ⟨CF, hCF_nn, hCF⟩ := riemannCurvatureCoeffFieldGridWindow (I := I) (M := M) g₀ Λ0 hΛ0
  obtain ⟨CQ, hCQ_nn, hCQ⟩ := connDiffQuadraticCurvatureTermGridWindow (I := I) (M := M) g₀ hδ₀
  refine ⟨fun w => 2 * CF w + 2 * CQ w,
    fun w => by have := hCF_nn w; have := hCQ_nn w; linarith, ?_⟩
  intro T hT0 δ hδ_le hδ0 hδ hδZ s hs w K hwK x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set W : ℝ := Combinatorics.boundedFactorGridWindow b K (w + 3) with hW_def
  have hW_nn : (0 : ℝ) ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb K (w + 3)
  obtain ⟨hs0, hs1⟩ := hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt ⟨hs0, hs1⟩
  have htie : ∀ (y : M) (v w' : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w' =
        g₀.inner y v w' +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w' :=
    fun y v w' => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w'
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
    intro y v w'
    have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w'
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rwa [heq] at hraw
  have hcP : convexPerturbation (I := I) g₀ T 0 s = s • T := by
    rw [convexPerturbation, smul_zero, zero_add]
  have hss : 0 ≤ s * s := mul_nonneg hs0 hs0
  have hs2 : s * s ≤ 1 := by nlinarith
  have hPT : ∀ l', riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
      ((iteratedCovGrad (I := I) g₀ 0 2 l'
        (convexPerturbation (I := I) g₀ T 0 s)).toSection x) ≤ b l' := by
    intro l'
    rw [hcP, iteratedCovGrad_smul_real]
    rw [show ((s • iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x) =
        s • ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (2 + l') x]
    nlinarith [hb l', hss, hs2]
  have hsub : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
      ((iteratedCovGrad (I := I) g₀ 0 4 w
        (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            ((-(s / 2) : ℝ) • riemannCurvatureCoeffField (I := I) (M := M) g₀ T)).toSection x)
        + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (connDiffQuadraticCurvatureTerm (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s))).toSection x) := by
    rw [lrR4]
    exact bdRfns_iCG_sub_le (I := I) (M := M) g₀ 0 4 w _ _ x
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
      ((iteratedCovGrad (I := I) g₀ 0 4 w
        ((-(s / 2) : ℝ) • riemannCurvatureCoeffField (I := I) (M := M) g₀ T)).toSection x) ≤
      CF w * W := by
    rw [iteratedCovGrad_smul_real]
    rw [show (((-(s / 2) : ℝ) • iteratedCovGrad (I := I) g₀ 0 4 w
        (riemannCurvatureCoeffField (I := I) (M := M) g₀ T)).toSection x) =
        (-(s / 2) : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 4 w
          (riemannCurvatureCoeffField (I := I) (M := M) g₀ T)).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (4 + w) x]
    have hbase := hCF T hT0 w K (by omega) x
    have hbase' : CF w * Combinatorics.boundedFactorGridWindow b K (w + 2) ≤ CF w * W := by
      refine mul_le_mul_of_nonneg_left ?_ (hCF_nn w)
      rw [hW_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb (le_refl K) (by omega)
    have hsq : (-(s / 2) : ℝ) * -(s / 2) ≤ 1 := by nlinarith
    have hsq0 : (0 : ℝ) ≤ (-(s / 2) : ℝ) * -(s / 2) := by nlinarith
    have hrfns_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + w) x
      ((iteratedCovGrad (I := I) g₀ 0 4 w (riemannCurvatureCoeffField (I := I) (M := M) g₀ T)).toSection x)
    nlinarith [le_trans hbase hbase', hrfns_nn]
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
      ((iteratedCovGrad (I := I) g₀ 0 4 w
        (connDiffQuadraticCurvatureTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s))).toSection x) ≤
      CQ w * W := by
    have hbase := hCQ (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (convexPerturbation (I := I) g₀ T 0 s) htie hδ_le hδ0 hδP w K hwK x
    refine le_trans hbase ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCQ_nn w)
    rw [hW_def]
    exact lrBFGW_mono_of_le _ b
      (fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _)
      (fun l' => hPT l') K (w + 3)
  linarith [hsub, hA, hB]

set_option maxHeartbeats 25600000 in

private theorem deTurckLieCovDerivArmDifferenceGridWindow (g₀ : SmoothRiemannianMetric I M) (Λ0 : ℝ) (hΛ0 : 0 ≤ Λ0)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        (_hT0 : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x) ≤ Λ0)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
        {s : ℝ} (_hs : s ∈ Set.Icc (0 : ℝ) 1) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
                - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
                  ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
                    Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                      Equiv.swap (0 : Fin 4) 1,
                    Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
                  ![(-1 : ℝ), -1, 1] s)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CP, hCP_nn, hCP⟩ := bdPairTraceOp_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨CR, hCR_nn, hCR⟩ := riemannCurvatureRemainderGridWindow (I := I) (M := M) g₀ Λ0 hΛ0 hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      ∑ u ∈ Finset.range (i + 1), (((u + 1 : ℕ) : ℝ) * CP u) *
        ∑ w ∈ Finset.range (i + 1 - u),
          (fr * (fr * CR w)) * Combinatorics.windowPairCellCount (u + 1) (w + 3),
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun u _ => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (hCP_nn u))
        (Finset.sum_nonneg fun w _ => mul_nonneg
          (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCR_nn w)))
          (Combinatorics.windowPairCellCount_nonneg _ _))), ?_⟩
  intro T hTsymm hT0 δ hδ_le hδ0 hδ hδZ s hs i x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set W : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hW_def
  have hW_nn : (0 : ℝ) ≤ W :=
    Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i + 3)
  obtain ⟨hs0, hs1⟩ := hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt ⟨hs0, hs1⟩
  have htie : ∀ (y : M) (v w' : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w' =
        g₀.inner y v w' +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w' :=
    fun y v w' => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w'
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
    intro y v w'
    have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w'
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rwa [heq] at hraw
  have hcP : convexPerturbation (I := I) g₀ T 0 s = s • T := by
    rw [convexPerturbation, smul_zero, zero_add]
  have hss : 0 ≤ s * s := mul_nonneg hs0 hs0
  have hs2 : s * s ≤ 1 := by nlinarith
  have hPT : ∀ (l' : ℕ) (y : M), riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') y
      ((iteratedCovGrad (I := I) g₀ 0 2 l'
        (convexPerturbation (I := I) g₀ T 0 s)).toSection y) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') y
        ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection y) := by
    intro l' y
    rw [hcP, iteratedCovGrad_smul_real]
    rw [show ((s • iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection y) =
        s • ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection y) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (2 + l') y]
    nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') y
      ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection y), hss, hs2]
  have hlift : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieCovDerivArmField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
          - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
            ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
              Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                Equiv.swap (0 : Fin 4) 1,
              Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
            ![(-1 : ℝ), -1, 1] s)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))))).toSection x) := by
    rw [lrArm_sub_family_eq_pairTrace (I := I) (M := M) g₀ T hδ_lt hδ hδZ hTsymm
      ⟨hs0, hs1⟩]
    rw [iteratedCovGrad_smul_real]
    rw [show (((-1 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))))).toSection x) =
        (-1 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [riemannianFiberNormSq_smul]
    norm_num
  rw [hlift]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ i 2 6 2
    (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))) x) ?_
  have hWtower : ∀ w, w ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
        ((iteratedCovGrad (I := I) g₀ 2 6 w
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)))).toSection x) ≤
      (fr * (fr * CR w)) * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
    intro w hw
    have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
        ((iteratedCovGrad (I := I) g₀ 2 6 w
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)))
        (fun y d => by
          rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) w x
    rw [hperm]
    have h1 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
      (slotExtendIter (I := I) (M := M) g₀ 0 4 1
        (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)) w x
    have h2 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
      (lrR4 (I := I) (M := M) g₀ T hδ hδZ s) w x
    have h3 := hCR T hT0 hδ_le hδ0 hδ hδZ ⟨hs0, hs1⟩ w (i + 1) (by omega) x
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))).toSection x)
        ≤ fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + w) x
            ((iteratedCovGrad (I := I) g₀ 1 5 w
              (slotExtendIter (I := I) (M := M) g₀ 0 4 1
                (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))).toSection x) := h1
      _ ≤ fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)).toSection x)) :=
          mul_le_mul_of_nonneg_left h2 hfr_nn
      _ ≤ fr * (fr * (CR w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hfr_nn) hfr_nn
      _ = (fr * (fr * CR w)) * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
          ring
  have hcell : ∀ u ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 6 2 u
            (armPairTraceOpCc (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s))).toSection x) *
        ∑ w ∈ Finset.range (i + 1 - u),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
            ((iteratedCovGrad (I := I) g₀ 2 6 w
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)))).toSection x) ≤
      ((((u + 1 : ℕ) : ℝ) * CP u) * ∑ w ∈ Finset.range (i + 1 - u),
        (fr * (fr * CR w)) * Combinatorics.windowPairCellCount (u + 1) (w + 3)) * W := by
    intro u hu
    rw [Finset.mem_range] at hu
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
        ((iteratedCovGrad (I := I) g₀ 6 2 u
          (armPairTraceOpCc (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s))).toSection x) ≤
        (((u + 1 : ℕ) : ℝ) * CP u) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) := by
      have h0 := hCP (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (convexPerturbation (I := I) g₀ T 0 s) htie hδ_le hδ0 hδP u x
      refine le_trans h0 ?_
      have hmono1 : Combinatorics.antidiagonalTupleGridWindow
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l
              (convexPerturbation (I := I) g₀ T 0 s)).toSection x)) (u + 1) ≤
          Combinatorics.antidiagonalTupleGridWindow b (u + 1) :=
        lrGridWindow_mono_of_le _ b
          (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _)
          (fun l => hPT l x) (u + 1)
      have hmono2 : Combinatorics.antidiagonalTupleGridWindow b (u + 1) ≤
          ((u + 1 : ℕ) : ℝ) * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) :=
        lrWindow_le_bFGW b hb (by omega) (le_refl _) (by omega)
      calc CP u * Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l
                (convexPerturbation (I := I) g₀ T 0 s)).toSection x)) (u + 1)
          ≤ CP u * Combinatorics.antidiagonalTupleGridWindow b (u + 1) :=
            mul_le_mul_of_nonneg_left hmono1 (hCP_nn u)
        _ ≤ CP u * (((u + 1 : ℕ) : ℝ) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1)) :=
            mul_le_mul_of_nonneg_left hmono2 (hCP_nn u)
        _ = (((u + 1 : ℕ) : ℝ) * CP u) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) := by ring
    have hA2 : (∑ w ∈ Finset.range (i + 1 - u),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)))).toSection x)) ≤
        ∑ w ∈ Finset.range (i + 1 - u),
          (fr * (fr * CR w)) * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
      refine Finset.sum_le_sum fun w hw => ?_
      rw [Finset.mem_range] at hw
      exact hWtower w (by omega)
    have hsum_nn : (0 : ℝ) ≤ ∑ w ∈ Finset.range (i + 1 - u),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)))).toSection x) :=
      Finset.sum_nonneg fun w _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + w) x _
    have hA1_rhs_nn : (0 : ℝ) ≤ (((u + 1 : ℕ) : ℝ) * CP u) *
        Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCP_nn u))
        (Combinatorics.boundedFactorGridWindow_nonneg b hb _ _)
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show ((((u + 1 : ℕ) : ℝ) * CP u) * ∑ w ∈ Finset.range (i + 1 - u),
        (fr * (fr * CR w)) * Combinatorics.windowPairCellCount (u + 1) (w + 3)) * W =
        ∑ w ∈ Finset.range (i + 1 - u),
          ((((u + 1 : ℕ) : ℝ) * CP u) * ((fr * (fr * CR w)) *
            Combinatorics.windowPairCellCount (u + 1) (w + 3))) * W from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun w hw => ?_
    rw [Finset.mem_range] at hw
    have hpair : Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
        Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) ≤
        Combinatorics.windowPairCellCount (u + 1) (w + 3) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1 + (w + 3) - 1) :=
      Combinatorics.boundedFactorGridWindow_mul_le b hb (i + 1) (u + 1) (w + 3)
        (by omega) (by omega)
    have hmono : Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1 + (w + 3) - 1) ≤
        W := by
      rw [hW_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) (by omega)
    have hcnt_nn : (0 : ℝ) ≤ Combinatorics.windowPairCellCount (u + 1) (w + 3) :=
      Combinatorics.windowPairCellCount_nonneg _ _
    calc (((u + 1 : ℕ) : ℝ) * CP u) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
          ((fr * (fr * CR w)) * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
        = ((((u + 1 : ℕ) : ℝ) * CP u) * (fr * (fr * CR w))) *
            (Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)) := by ring
      _ ≤ ((((u + 1 : ℕ) : ℝ) * CP u) * (fr * (fr * CR w))) *
            (Combinatorics.windowPairCellCount (u + 1) (w + 3) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1 + (w + 3) - 1)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCP_nn u))
            (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCR_nn w)))
      _ ≤ ((((u + 1 : ℕ) : ℝ) * CP u) * (fr * (fr * CR w))) *
            (Combinatorics.windowPairCellCount (u + 1) (w + 3) * W) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCP_nn u))
              (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCR_nn w))))
          exact mul_le_mul_of_nonneg_left hmono hcnt_nn
      _ = ((((u + 1 : ℕ) : ℝ) * CP u) * ((fr * (fr * CR w)) *
            Combinatorics.windowPairCellCount (u + 1) (w + 3))) * W := by ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem lrJoint0S_add_local {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (B p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem lrJoint0S_smulFun_local {d : ℕ} {S : Set ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (A : ∀ p : M × ℝ, Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (f p.2 • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hfm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.2) :=
    hf.contMDiff.comp contMDiff_snd
  have hfj : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => f p.2) ((Set.univ : Set M) ×ˢ S) p₀ :=
    (hfm.contMDiffAt).contMDiffWithinAt
  refine (hfj.smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul (f p.2) (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      (f p₀.2) (A p₀)


omit [BoundarylessManifold I M] in
private lemma lrFamilyField_eq (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ) (s : ℝ) :
    deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
      ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
        Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
        Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
      ![(-1 : ℝ), -1, 1] s =
      s • ((-1 : ℝ) • ((1 / 2 : ℝ) •
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    (((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
                        (Equiv.swap (0 : Fin 4) 1)).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))))
        + (-1 : ℝ) • ((1 / 2 : ℝ) •
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    ((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                        Equiv.swap (0 : Fin 4) 1).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    (((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                          Equiv.swap (0 : Fin 4) 1).trans
                        (Equiv.swap (0 : Fin 4) 1)).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))))
        + (1 : ℝ) • ((1 / 2 : ℝ) •
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    (((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
                        (Equiv.swap (0 : Fin 4) 1)).trans
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T))))))) := by
  rw [deTurckLieCovDerivRefoldPairTraceFamily, Fin.sum_univ_three]
  rfl

set_option maxHeartbeats 12800000 in

private theorem lrFamily_threeArmHjoint (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
        ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
          Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
          Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
        ![(-1 : ℝ), -1, 1] s) (δ := δ) (δ' := δ) := by
  classical
  have hperY : ∀ (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) p.1
          ((show Tensor0SSpace 2 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 from
            (deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
              ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
                Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                  Equiv.swap (0 : Fin 4) 1,
                Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
              ![(-1 : ℝ), -1, 1] p.2).toSection p.1) (Y p.1)))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    intro Y
    have hbase : ∀ (X : SmoothCcTensor g₀ 2 6),
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
          (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
            (E := fun z : M => Tensor0SSpace 2 I z) q.1
            (cometricDoubleTraceFib (I := I)
              (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 2 q.1
              (cometricDoubleTraceFib (I := I)
                (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
                ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
                  X.toSection q.1) (Y q.1)))))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
      intro X
      have hXapp : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
          (fun x : M => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
            (E := fun z : M => Tensor0SSpace 6 I z) x
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
              X.toSection x) (Y x))) :=
        ContMDiff.clm_bundle_apply (b := id) X.toSection.contMDiff Y.contMDiff
      have hXjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
          (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
            (E := fun z : M => Tensor0SSpace 6 I z) q.1
            ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
              X.toSection q.1) (Y q.1)))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
        (hXapp.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
      have h4 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
        g₀ T 0 hδ hδZ
        (fun q : M × ℝ => (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
          X.toSection q.1) (Y q.1)) hXjoint
      exact cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2)
        g₀ T 0 hδ hδZ
        (fun q : M × ℝ => cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
            X.toSection q.1) (Y q.1))) h4
    have hP00 := hbase (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
          (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
    have hP01 := hbase (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          (((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2).trans
              (Equiv.swap (0 : Fin 4) 1)).trans
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
          (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
    have hP10 := hbase (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          ((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
              Equiv.swap (0 : Fin 4) 1).trans
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
          (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
    have hP11 := hbase (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          (((Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                Equiv.swap (0 : Fin 4) 1).trans
              (Equiv.swap (0 : Fin 4) 1)).trans
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
          (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
    have hP20 := hbase (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
          (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
    have hP21 := hbase (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          (((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3).trans
              (Equiv.swap (0 : Fin 4) 1)).trans
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
          (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
    have hA0 := lrJoint0S_add_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hP00 hP01
    have hH0 := lrJoint0S_smulFun_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (f := fun _ : ℝ => (1 / 2 : ℝ)) contDiff_const _ hA0
    have hE0 := lrJoint0S_smulFun_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (f := fun _ : ℝ => (-1 : ℝ)) contDiff_const _ hH0
    have hA1 := lrJoint0S_add_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hP10 hP11
    have hH1 := lrJoint0S_smulFun_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (f := fun _ : ℝ => (1 / 2 : ℝ)) contDiff_const _ hA1
    have hE1 := lrJoint0S_smulFun_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (f := fun _ : ℝ => (-1 : ℝ)) contDiff_const _ hH1
    have hA2 := lrJoint0S_add_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hP20 hP21
    have hH2 := lrJoint0S_smulFun_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (f := fun _ : ℝ => (1 / 2 : ℝ)) contDiff_const _ hA2
    have hE2 := lrJoint0S_smulFun_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (f := fun _ : ℝ => (1 : ℝ)) contDiff_const _ hH2
    have hZ01 := lrJoint0S_add_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hE0 hE1
    have hZ := lrJoint0S_add_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hZ01 hE2
    have hsmul := lrJoint0S_smulFun_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (f := fun s : ℝ => s) contDiff_id _ hZ
    refine hsmul.congr (fun q _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SSpace 2 I z) q.1 t) ?_
    have hsmulY : ∀ (c : ℝ) (F : SmoothCcTensor g₀ 2 2),
        (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
          ((c • F).toSection q.1)) (Y q.1) =
        c • ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
          (F.toSection q.1)) (Y q.1)) := by
      intro c F
      rw [show ((c • F).toSection q.1) = c • (F.toSection q.1) from by
        rw [SmoothCcTensor.toSection_smul]; rfl]
      rfl
    have haddY : ∀ (F G : SmoothCcTensor g₀ 2 2),
        (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
          ((F + G).toSection q.1)) (Y q.1) =
        (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
            (F.toSection q.1)) (Y q.1)
          + (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
            (G.toSection q.1)) (Y q.1) := by
      intro F G
      rw [show ((F + G).toSection q.1) = F.toSection q.1 + G.toSection q.1 from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      rfl
    have hPY : ∀ (X : SmoothCcTensor g₀ 2 6),
        (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
            X).toSection q.1)) (Y q.1) =
        cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 2 q.1
          (cometricDoubleTraceFib (I := I)
            (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
            ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
              X.toSection q.1) (Y q.1))) := by
      intro X
      rw [appCcRS_toSection]
      rfl
    rw [lrFamilyField_eq (I := I) (M := M) g₀ T hδ hδZ q.2]
    simp only [hsmulY, haddY, hPY]
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SSpace 2 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 from
        (deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
          ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
            Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
              Equiv.swap (0 : Fin 4) 1,
            Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
          ![(-1 : ℝ), -1, 1] p.2).toSection p.1))
    (S := realizedSmallSet (δ := δ) (δ' := δ)) hperY
  refine hCLM.congr (fun p _ => ?_)
  rfl

private lemma lrWindowOneThree_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {B : ℝ}
    (hB1 : b 1 ≤ B) :
    Combinatorics.boundedFactorGridWindow b 1 3 ≤ 1 + B + B ^ 2 := by
  classical
  have hB0 : 0 ≤ B := le_trans (hb 1) hB1
  have hgrid0 : Combinatorics.boundedFactorGrid b 1 0 = 1 :=
    Combinatorics.boundedFactorGrid_zero b 1
  have hgrid1 : Combinatorics.boundedFactorGrid b 1 1 = b 1 := by
    rw [Combinatorics.boundedFactorGrid]
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    rw [show Finset.Nat.antidiagonalTuple 0 1 = ∅ from
      Finset.Nat.antidiagonalTuple_zero_succ 0]
    rw [show Finset.Nat.antidiagonalTuple 1 1 = {![1]} from
      Finset.Nat.antidiagonalTuple_one 1]
    rw [Finset.filter_empty, Finset.sum_empty]
    rw [Finset.filter_singleton]
    rw [if_pos (by decide : ∀ m : Fin 1, (![1] : Fin 1 → ℕ) m ≤ 1)]
    rw [Finset.sum_singleton]
    rw [Fin.prod_univ_one]
    norm_num
  have hgrid2 : Combinatorics.boundedFactorGrid b 1 2 = b 1 * b 1 := by
    rw [Combinatorics.boundedFactorGrid]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    rw [show Finset.Nat.antidiagonalTuple 0 2 = ∅ from
      Finset.Nat.antidiagonalTuple_zero_succ 1]
    rw [show Finset.Nat.antidiagonalTuple 1 2 = {![2]} from
      Finset.Nat.antidiagonalTuple_one 2]
    rw [Finset.filter_empty, Finset.sum_empty]
    rw [Finset.filter_singleton]
    rw [if_neg (by decide : ¬ ∀ m : Fin 1, (![2] : Fin 1 → ℕ) m ≤ 1)]
    rw [Finset.sum_empty]
    have h22 : (Finset.Nat.antidiagonalTuple 2 2).filter
        (fun e : Fin 2 → ℕ => ∀ m, e m ≤ 1) = {![1, 1]} := by
      decide
    rw [h22, Finset.sum_singleton, Fin.prod_univ_two]
    change (0 : ℝ) + 0 + b (![1, 1] 0) * b (![1, 1] 1) = b 1 * b 1
    norm_num
  rw [Combinatorics.boundedFactorGridWindow, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, hgrid0, hgrid1, hgrid2]
  nlinarith [hb 1, hB1, hB0, sq_nonneg (b 1 - B)]


theorem exists_deTurckLieCovDerivArm_basepointBackground_pairTraceResidual_order0_data
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
          (fun s => deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
            - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
              ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
                Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
                Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
              ![(-1 : ℝ), -1, 1] s) (δ := δ) (δ' := δ) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
              - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
                ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
                  Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
                  Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
                ![(-1 : ℝ), -1, 1] s).toSection x) ≤ Λ ^ 2) ∧
        (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
              - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
                ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
                  Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
                  Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
                ![(-1 : ℝ), -1, 1] s)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨Csob0, hCsob0_nn, hCsob0⟩ :=
    exists_sobolev_pointwise_bound_zero_order (I := I) (M := M) g₀ a ha_super
  obtain ⟨Csob1, hCsob1_nn, hCsob1⟩ :=
    exists_sobolev_pointwise_bound_first_order (I := I) (M := M) g₀ a ha_super
  have hΛ0_nn : (0 : ℝ) ≤ (Csob0 * R) ^ 2 := sq_nonneg _
  obtain ⟨C, hC_nn, hpt⟩ :=
    deTurckLieCovDerivArmDifferenceGridWindow (I := I) (M := M) g₀ ((Csob0 * R) ^ 2) hΛ0_nn hδ₁_lt
  obtain ⟨Kflat, hKflat_nn, hKflat⟩ :=
    boundedFactorGridWindow_integral_ballUniform_flat_allOrders (I := I) (M := M) g₀ a
      ha_super hR
  have hcap_nn : (0 : ℝ) ≤ C 0 * (1 + (Csob1 * R) ^ 2 + ((Csob1 * R) ^ 2) ^ 2) := by
    have := hC_nn 0
    positivity
  refine ⟨Real.sqrt (C 0 * (1 + (Csob1 * R) ^ 2 + ((Csob1 * R) ^ 2) ^ 2)),
    Real.sqrt_nonneg _,
    fun i => C i * Kflat i, fun i => mul_nonneg (hC_nn i) (hKflat_nn i), ?_⟩
  intro T hTsymm δ hδ_le hδ hδZ hball
  have hδ_le' : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
  have hT0 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x) ≤
        (Csob0 * R) ^ 2 :=
    fun x => hCsob0 T hR hball x
  refine ⟨?_, ?_, ?_⟩
  · exact threeArmHjoint_sub_local (I := I) (M := M) g₀ _ _
      (covDerivArmField_realizedFam_threeArmHjoint (I := I) (M := M) g₀ T hδ hδZ g₀)
      (lrFamily_threeArmHjoint (I := I) (M := M) g₀ T hδ hδZ)
  · intro s hs x
    have hδ0 : 0 ≤ δ := bdDelta_nonneg (I := I) (M := M) g₀ x T hδ
    have h0 := hpt T hTsymm hT0 hδ_le' hδ0 hδ hδZ hs 0 x
    rw [iteratedCovGrad_zero] at h0
    refine le_trans h0 ?_
    rw [Real.sq_sqrt hcap_nn]
    refine mul_le_mul_of_nonneg_left ?_ (hC_nn 0)
    have hb1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) ≤ (Csob1 * R) ^ 2 :=
      hCsob1 T hR hball x
    exact lrWindowOneThree_le
      (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
        ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x))
      (fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _)
      hb1
  · intro i s hs
    have hwin_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
    by_cases hM : Nonempty M
    · obtain ⟨x₀⟩ := hM
      have hδ0 : 0 ≤ δ := bdDelta_nonneg (I := I) (M := M) g₀ x₀ T hδ
      have hptx : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                    (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
                  - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
                    ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
                      Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                        Equiv.swap (0 : Fin 4) 1,
                      Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
                    ![(-1 : ℝ), -1, 1] s)).toSection x) ≤
            C i * Combinatorics.boundedFactorGridWindow
              (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
                ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x)) (i + 1) (i + 3) :=
        fun x => hpt T hTsymm hT0 hδ_le' hδ0 hδ hδZ hs i x
      obtain ⟨hWint, hWbound⟩ := hKflat T hball i
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
        2 (2 + i)
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
            - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
              ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
                Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                  Equiv.swap (0 : Fin 4) 1,
                Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
              ![(-1 : ℝ), -1, 1] s))
        (fun x => C i * Combinatorics.boundedFactorGridWindow
          (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
            ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x)) (i + 1) (i + 3))
        (hWint.const_mul (C i)) hptx
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      refine le_trans (mul_le_mul_of_nonneg_left hWbound (hC_nn i)) (le_of_eq ?_)
      ring
    · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
      have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
            - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
              ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
                Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                  Equiv.swap (0 : Fin 4) 1,
                Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
              ![(-1 : ℝ), -1, 1] s)‖ = 0 :=
        bdNorm_zero_of_isEmpty (I := I) (M := M) g₀ 2 (2 + i) _
      rw [hz]
      have hK_nn : 0 ≤ C i * Kflat i := mul_nonneg (hC_nn i) (hKflat_nn i)
      nlinarith [hwin_nn, hK_nn]


theorem exists_deTurckLieCovDerivArm_basepointBackground_refold_identity_data
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∃ (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ), (∀ i, |ε i| ≤ 1) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ C0da : ℝ → SmoothCcTensor g₀ 2 2,
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0da (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            operatorFieldApply (I := I) (M := M) g₀ 2 2
                (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              operatorFieldApply (I := I) (M := M) g₀ 2 2 (C0da s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2
                  (deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0da s).toSection x) ≤
              Λ ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0da s)‖ ^ 2 ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨Λ, hΛ_nn, K, hK_nn, hres⟩ :=
    exists_deTurckLieCovDerivArm_basepointBackground_pairTraceResidual_order0_data
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨Λ, hΛ_nn, K, hK_nn,
    ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
      Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
      Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3],
    ![(-1 : ℝ), -1, 1], ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  intro T hTsymm δ hδ_le hδ hδZ hball
  obtain ⟨hjoint, hcap, hwin⟩ := hres T hTsymm hδ_le hδ hδZ hball
  refine ⟨fun s => deTurckLieCovDerivArmField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
    - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
      ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
        Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
        Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
      ![(-1 : ℝ), -1, 1] s, hjoint, ?_, hcap, hwin⟩
  intro s hs
  beta_reduce
  simp only [iteratedCovGrad_zero]
  rw [appCc_sub_left,
    bdLiePairTraceFamily_appCc_eq_familySecondGradient (I := I) (M := M) g₀ T hδ hδZ
      ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
        Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 * Equiv.swap (0 : Fin 4) 1,
        Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
      ![(-1 : ℝ), -1, 1] s]
  abel


theorem exists_deTurckLieCovDerivArm_refold_identity_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∃ (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ), (∀ i, |ε i| ≤ 1) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ C0da : ℝ → SmoothCcTensor g₀ 2 2,
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0da (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            operatorFieldApply (I := I) (M := M) g₀ 2 2
                (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg)
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              operatorFieldApply (I := I) (M := M) g₀ 2 2 (C0da s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2
                  (deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0da s).toSection x) ≤
              Λ ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0da s)‖ ^ 2 ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨Λv, hΛv_nn, Kv, hKv_nn, q, ε, hε, hmov⟩ :=
    exists_deTurckLieCovDerivArm_basepointBackground_refold_identity_data (I := I) (M := M)
      g₀ a ha_super hR hδ₀
  obtain ⟨Λbg, hΛbg_nn, hsup_bg⟩ :=
    deTurckLieDLaCoeffField_realizedFam_rfns_order0_ballUniform (I := I) (M := M)
      g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λz, hΛz_nn, hsup_z⟩ :=
    deTurckLieDLaCoeffField_realizedFam_rfns_order0_ballUniform (I := I) (M := M)
      g₀ g₀ a ha_super hR hδ₀
  obtain ⟨Kd, hKd_nn, henv_d⟩ :=
    exists_deTurckLieCovDerivArm_backgroundDifference_l2JetWindow (I := I) (M := M)
      g₀ g_bg a ha_super hR hδ₀
  have hS_nn : (0 : ℝ) ≤ 2 * Λv ^ 2 + 2 * (2 * Λbg + 2 * Λz) := by positivity
  refine ⟨Real.sqrt (2 * Λv ^ 2 + 2 * (2 * Λbg + 2 * Λz)), Real.sqrt_nonneg _,
    fun i => 2 * Kv i + 2 * Kd i,
    fun i => by have h1 := hKv_nn i; have h2 := hKd_nn i; linarith,
    q, ε, hε, ?_⟩
  intro T hTsymm δ hδ_le hδ hδZ hball
  obtain ⟨C0v, hjv, hidv, hsupv, henvv⟩ := hmov T hTsymm hδ_le hδ hδZ hball
  have hZball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j hj
    have hzero : iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) = 0 := by
      have h := iteratedCovGrad_sub (I := I) (g := g₀) (r := 0) (s := 2) (j := j) T T
      rw [sub_self, sub_self] at h
      exact h
    rw [hzero, norm_zero]
    exact hR
  refine ⟨fun s => C0v s +
      (deTurckLieCovDerivArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
        - deTurckLieCovDerivArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀), ?_, ?_, ?_, ?_⟩
  · exact threeArmHjoint_add_local (I := I) (M := M) g₀ _ _ hjv
      (threeArmHjoint_sub_local (I := I) (M := M) g₀ _ _
        (covDerivArmField_realizedFam_threeArmHjoint (I := I) (M := M) g₀ T hδ hδZ g_bg)
        (covDerivArmField_realizedFam_threeArmHjoint (I := I) (M := M) g₀ T hδ hδZ g₀))
  · intro s hs
    have hsplit : deTurckLieCovDerivArmField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg =
        deTurckLieCovDerivArmField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀ +
          (deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
            - deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀) := by
      rw [add_sub_cancel]
    conv_lhs => rw [hsplit, appCc_add_left, hidv s hs]
    conv_rhs => rw [appCc_add_left]
    abel
  · intro s hs x
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((deTurckLieCovDerivArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg).toSection x) ≤ Λbg := by
      rw [covDerivArmField_eq_dLaCoeffField]
      exact hsup_bg T 0 hδ_le hδ hδ_le hδZ hball hZball s hs x
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((deTurckLieCovDerivArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀).toSection x) ≤ Λz := by
      rw [covDerivArmField_eq_dLaCoeffField]
      exact hsup_z T 0 hδ_le hδ hδ_le hδZ hball hZball s hs x
    have hdiff : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((deTurckLieCovDerivArmField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
          - deTurckLieCovDerivArmField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀).toSection x) ≤
        2 * Λbg + 2 * Λz := by
      rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
      refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 2 x _ _) ?_
      have := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x
      linarith [h1, h2]
    have hsum : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (((fun s => C0v s +
          (deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
            - deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)) s).toSection x) ≤
        2 * Λv ^ 2 + 2 * (2 * Λbg + 2 * Λz) := by
      rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 2 x _ _) ?_
      have h3 := hsupv s hs x
      linarith [hdiff]
    rw [Real.sq_sqrt hS_nn]
    exact hsum
  · intro i s hs
    have hlin : iteratedCovGrad (I := I) g₀ 2 2 i
        (C0v s +
          (deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
            - deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)) =
        iteratedCovGrad (I := I) g₀ 2 2 i (C0v s) +
          iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
              - deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀) :=
      iteratedCovGrad_add (I := I) (g := g₀) (r := 2) (s := 2) (j := i) _ _
    have hv := henvv i s hs
    have hd := henv_d T hδ_le hδ hδZ hball i s hs
    have htri : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (C0v s +
          (deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
            - deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀))‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0v s)‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
              - deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)‖ ^ 2 := by
      rw [hlin]
      have hn := norm_add_le (iteratedCovGrad (I := I) g₀ 2 2 i (C0v s))
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
            - deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀))
      nlinarith [mul_le_mul hn hn
          (norm_nonneg (iteratedCovGrad (I := I) g₀ 2 2 i (C0v s) +
            iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
                - deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)))
          (add_nonneg (norm_nonneg (iteratedCovGrad (I := I) g₀ 2 2 i (C0v s)))
            (norm_nonneg (iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
                - deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)))),
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 2 2 i (C0v s)‖ -
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
              - deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)‖)]
    refine le_trans htri ?_
    have hwin_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
    nlinarith [hv, hd, hwin_nn]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
