import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldInputSlotSymmetrization
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.FlatArmCoeffConnectionDifferenceBridge


noncomputable section

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
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_smul_value (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (x : M) (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

section helpers

variable (g₀ g₁ : SmoothRiemannianMetric I M)

private def gInvQuadRefoldArm : SmoothCcTensor g₀ 1 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 1 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
    (slotExtend (I := I) (M := M) g₀ 0 3 (connDiffLoweredCc (I := I) g₀ g₁))

private def gInvQuadRefoldWeight : SmoothCcTensor g₀ 2 1 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 1 (cometricDoubleTraceField (I := I) g₀ 1)
    (reindexCoeffGen (I := I) (M := M) g₀ 2 3
      (slotExtend (I := I) (M := M) g₀ 1 2 (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁))
      (Equiv.swap (0 : Fin 2) 1))

section NormedMetricFrameHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable (g₀ : SmoothRiemannianMetric I M)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma tensor0S_rank0_eq_smul_unit (x : M) (c : Tensor0SSpace 0 I x) :
    c = Tensor0SSpace.toModel c (fun i : Fin 0 => i.elim0) •
      unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have h1 : Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) v = (1 : ℝ) := rfl
  rw [h1, mul_one]
  congr 1
  funext i
  exact i.elim0

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem orthoFrame_basis_at_center (x : M) :
    ∃ bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ i, bse i = smoothOrthoFrame (I := I) g₀ x i x := by
  classical
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
        (smoothOrthoFrame (I := I) g₀ x b x) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ x a b
  have he_li : LinearIndependent ℝ
      (fun i => smoothOrthoFrame (I := I) g₀ x i x) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g₀.inner x (smoothOrthoFrame (I := I) g₀ x k x)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g₀ x j x) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g₀.inner x (smoothOrthoFrame (I := I) g₀ x k x)
        (c j • smoothOrthoFrame (I := I) g₀ x j x) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g₀.inner x (smoothOrthoFrame (I := I) g₀ x k x)).map_smul (c j),
        smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E :=
    Fintype.card_fin _
  exact ⟨basisOfLinearIndependentOfCardEqFinrank he_li hcard,
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i⟩

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem orthoFrame_expansion_at_center (x : M) (u : TangentSpace I x) :
    u = ∑ i : Fin (Module.finrank ℝ E),
      g₀.inner x u (smoothOrthoFrame (I := I) g₀ x i x) •
        smoothOrthoFrame (I := I) g₀ x i x := by
  classical
  obtain ⟨bse, hbse⟩ := orthoFrame_basis_at_center (I := I) (M := M) g₀ x
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
        (smoothOrthoFrame (I := I) g₀ x b x) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ x a b
  have hcoeff : ∀ j : Fin (Module.finrank ℝ E),
      g₀.inner x u (smoothOrthoFrame (I := I) g₀ x j x) = bse.repr u j := by
    intro j
    rw [g₀.symm x u (smoothOrthoFrame (I := I) g₀ x j x)]
    conv_lhs => rw [← bse.sum_repr u]
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [(g₀.inner x (smoothOrthoFrame (I := I) g₀ x j x)).map_smul (bse.repr u i),
        smul_eq_mul, hbse i, horth j i])]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [if_pos rfl, mul_one]
    · intro i _ hij
      rw [if_neg (fun h => hij h.symm), mul_zero]
  calc u = ∑ i : Fin (Module.finrank ℝ E), bse.repr u i • bse i := (bse.sum_repr u).symm
    _ = ∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x u (smoothOrthoFrame (I := I) g₀ x i x) •
          smoothOrthoFrame (I := I) g₀ x i x := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoeff i, hbse i]

end NormedMetricFrameHelpers

section NormedConnectionDifferenceRiemannianNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable (g₀ g₁ : SmoothRiemannianMetric I M)

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma connDiffLowered_unitModel_value (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  have hbase : unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x =
      Tensor0SSpace.toModel (connDiffLoweredCovec (I := I) g₀ g₁ x) := by
    rw [unitModel]
    change Tensor0SSpace.toModel
        ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) g₀ g₁ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
            (1 : ℝ))) =
      Tensor0SSpace.toModel (connDiffLoweredCovec (I := I) g₀ g₁ x)
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
    rfl
  rw [hbase]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma interiorProduct_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
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

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma connDiffSection_eq_raise_lowered :
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
    rw [interiorProduct_toModel_eval (I := I) (M := M) (1 + 1) x
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
  rw [connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x ![YZ 0, YZ 1, u]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [g₀.symm x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1))]

omit [NeZero (Module.finrank ℝ E)] in
lemma rfns_icg_connDiffLowered_eq_connDiffSection (n : ℕ) (x : M) :
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
        rw [connDiffSection_eq_raise_lowered (I := I) (M := M) g₀ g₁]

end NormedConnectionDifferenceRiemannianNorm

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma cometricDoubleTraceFib_toModel_center (p : ℕ) (x : M)
    (D : Tensor0SSpace (p + 2) I x) (m : Fin p → E) :
    Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₀ p x D) m =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E) m)) := by
  rw [show Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₀ p x D) m =
      modelDoubleTrace (E := E) p (cometricLmodel (I := I) g₀ x)
        (Tensor0SSpace.toModel D) m from by
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ p x D]]
  rw [modelDoubleTrace_apply (E := E) p (cometricLmodel (I := I) g₀ x)
    (Tensor0SSpace.toModel D) m]
  exact cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ (s := p) x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel D) m

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma slotExtend_connDiffLowered_toModel (x : M)
    (om : Tensor0SSpace 1 I x) (v0 : E) (vs : Fin 3 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtend (I := I) (M := M) g₀ 0 3
            (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) om)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel om ![v0] *
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (vs 0) (vs 1)) (vs 2) := by
  have h0 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtend (I := I) (M := M) g₀ 0 3
          (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) om) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        (slotExtendPointwise (I := I) (M := M) g₀ 0 3 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (connDiffLoweredCc (I := I) g₀ g₁).toSection x) om) (Fin.cons v0 vs) := rfl
  rw [h0]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 0 3 x
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (connDiffLoweredCc (I := I) g₀ g₁).toSection x) om v0 vs]
  have hc : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x om v0 =
      Tensor0SSpace.toModel om ![v0] • unitTensor (I := I) (M := M) x := by
    have h1 := tensor0S_rank0_eq_smul_unit (I := I) (M := M) x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x om v0)
    rw [h1]
    congr 1
  rw [hc, ContinuousLinearMap.map_smul, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  have hu := connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x vs
  rw [unitModel] at hu
  exact hu

set_option backward.isDefEq.respectTransparency false in
omit [SigmaCompactSpace M] in
private lemma gInvQuadRefoldArm_toModel (x : M) (om : Tensor0SSpace 1 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁).toSection x) om) m =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel om ![((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)] *
          g₀.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (smoothOrthoFrame (I := I) g₀ x c x) (m 0)) (m 1) := by
  have h0 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁).toSection x) om) m =
      Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) g₀ 2 x
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
            (slotExtend (I := I) (M := M) g₀ 0 3
              (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) om)) m := rfl
  rw [h0]
  rw [cometricDoubleTraceFib_toModel_center (I := I) (M := M) g₀ 2 x
    ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
      (slotExtend (I := I) (M := M) g₀ 0 3
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) om) m]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [slotExtend_connDiffLowered_toModel (I := I) (M := M) g₀ g₁ x om
    ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)
    (Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E) m)]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [SigmaCompactSpace M] in
private lemma gInvQuadRefoldWeight_toModel (x : M) (D : Tensor0SSpace 2 I x) (m : Fin 1 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
          (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁).toSection x) D) m =
      ∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E),
              ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E)] *
          g₀.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (smoothOrthoFrame (I := I) g₀ x c x) (smoothOrthoFrame (I := I) g₀ x a x))
            (m 0) := by
  have h0 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
        (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁).toSection x) D) m =
      Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) g₀ 1 x
          (reindexCoeffFibGen (I := I) 2 3 (Equiv.swap (0 : Fin 2) 1) x
            (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
              (slotExtend (I := I) (M := M) g₀ 1 2
                (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)).toSection x) D)) m := rfl
  rw [h0]
  rw [cometricDoubleTraceFib_toModel_center (I := I) (M := M) g₀ 1 x
    (reindexCoeffFibGen (I := I) 2 3 (Equiv.swap (0 : Fin 2) 1) x
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (slotExtend (I := I) (M := M) g₀ 1 2
          (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)).toSection x) D) m]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [reindexCoeffFibGen_apply (I := I) 2 3 (Equiv.swap (0 : Fin 2) 1) x
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
      (slotExtend (I := I) (M := M) g₀ 1 2
        (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)).toSection x) D]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
      (slotExtend (I := I) (M := M) g₀ 1 2
        (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)).toSection x) =
      slotExtendPointwise (I := I) (M := M) g₀ 1 2 x
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁).toSection x) from rfl]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 1 2 x
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁).toSection x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel D)))
    ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E)
    (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) m)]
  rw [gInvQuadRefoldArm_toModel (I := I) (M := M) g₀ g₁ x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
      (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel D)))
      ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E))
    (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) m)]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  · rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel D)))
      (v0 := ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E))
      (vs := ![((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)])]
    rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext i
    fin_cases i <;> rfl

set_option backward.isDefEq.respectTransparency false in
private theorem gInvDiffQuadResidualField_eq_refold :
    gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 2
        (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)
        (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 2 2 x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  have hsplit : ∀ u : TangentSpace I x,
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u (v 0)) (v 1) =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x u (smoothOrthoFrame (I := I) g₀ x e x) *
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (smoothOrthoFrame (I := I) g₀ x e x) (v 0)) (v 1) := by
    intro u
    conv_lhs => rw [orthoFrame_expansion_at_center (I := I) (M := M) g₀ x u]
    rw [map_sum (PDE.DeTurck.connDiff (I := I) g₁ g₀ x) _ Finset.univ,
      ContinuousLinearMap.sum_apply, map_sum (g₀.inner x) _ Finset.univ,
      ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_smul (PDE.DeTurck.connDiff (I := I) g₁ g₀ x),
      ContinuousLinearMap.smul_apply, map_smul (g₀.inner x),
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 2
          (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)
          (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁)).toSection x) D) v =
      ∑ e : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
            ![((smoothOrthoFrame (I := I) g₀ x q x : TangentSpace I x) : E),
              ((smoothOrthoFrame (I := I) g₀ x p x : TangentSpace I x) : E)] *
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (smoothOrthoFrame (I := I) g₀ x q x) (smoothOrthoFrame (I := I) g₀ x p x))
            (smoothOrthoFrame (I := I) g₀ x e x)) *
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (smoothOrthoFrame (I := I) g₀ x e x) (v 0)) (v 1) := by
    have hr0 : Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 2
            (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)
            (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁)).toSection x) D) v =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁).toSection x)
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
              (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁).toSection x) D)) v := rfl
    rw [hr0]
    rw [gInvQuadRefoldArm_toModel (I := I) (M := M) g₀ g₁ x
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
        (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁).toSection x) D) v]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [gInvQuadRefoldWeight_toModel (I := I) (M := M) g₀ g₁ x D
      ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)]]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rfl
  calc Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁).toSection x) D) v
      = ∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (smoothOrthoFrame (I := I) g₀ x q x) (smoothOrthoFrame (I := I) g₀ x p x))
              (v 0)) (v 1) *
            Tensor0SSpace.toModel D
              ![((smoothOrthoFrame (I := I) g₀ x q x : TangentSpace I x) : E),
                ((smoothOrthoFrame (I := I) g₀ x p x : TangentSpace I x) : E)] := by
        rw [show Tensor0SSpace.toModel
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
              (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁).toSection x) D) v =
            Tensor0SSpace.toModel
              (connDiffBiContrFibFixedFrame (I := I) g₁ g₀ g₁ g₀
                (smoothOrthoFrame (I := I) g₀ x) x D) v from rfl]
        exact connDiffBiContrFibFixedFrame_toModel (I := I) g₁ g₀ g₁ g₀
          (smoothOrthoFrame (I := I) g₀ x) x D v
    _ = ∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          ∑ e : Fin (Module.finrank ℝ E),
          (Tensor0SSpace.toModel D
              ![((smoothOrthoFrame (I := I) g₀ x q x : TangentSpace I x) : E),
                ((smoothOrthoFrame (I := I) g₀ x p x : TangentSpace I x) : E)] *
            g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (smoothOrthoFrame (I := I) g₀ x q x) (smoothOrthoFrame (I := I) g₀ x p x))
              (smoothOrthoFrame (I := I) g₀ x e x)) *
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (smoothOrthoFrame (I := I) g₀ x e x) (v 0)) (v 1) := by
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
        rw [hsplit (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (smoothOrthoFrame (I := I) g₀ x q x) (smoothOrthoFrame (I := I) g₀ x p x))]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun e _ => ?_
        ring
    _ = ∑ q : Fin (Module.finrank ℝ E), ∑ e : Fin (Module.finrank ℝ E),
          ∑ p : Fin (Module.finrank ℝ E),
          (Tensor0SSpace.toModel D
              ![((smoothOrthoFrame (I := I) g₀ x q x : TangentSpace I x) : E),
                ((smoothOrthoFrame (I := I) g₀ x p x : TangentSpace I x) : E)] *
            g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (smoothOrthoFrame (I := I) g₀ x q x) (smoothOrthoFrame (I := I) g₀ x p x))
              (smoothOrthoFrame (I := I) g₀ x e x)) *
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (smoothOrthoFrame (I := I) g₀ x e x) (v 0)) (v 1) :=
        Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ e : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
          ∑ p : Fin (Module.finrank ℝ E),
          (Tensor0SSpace.toModel D
              ![((smoothOrthoFrame (I := I) g₀ x q x : TangentSpace I x) : E),
                ((smoothOrthoFrame (I := I) g₀ x p x : TangentSpace I x) : E)] *
            g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (smoothOrthoFrame (I := I) g₀ x q x) (smoothOrthoFrame (I := I) g₀ x p x))
              (smoothOrthoFrame (I := I) g₀ x e x)) *
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (smoothOrthoFrame (I := I) g₀ x e x) (v 0)) (v 1) :=
        Finset.sum_comm
    _ = ∑ e : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          ∑ q : Fin (Module.finrank ℝ E),
          (Tensor0SSpace.toModel D
              ![((smoothOrthoFrame (I := I) g₀ x q x : TangentSpace I x) : E),
                ((smoothOrthoFrame (I := I) g₀ x p x : TangentSpace I x) : E)] *
            g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (smoothOrthoFrame (I := I) g₀ x q x) (smoothOrthoFrame (I := I) g₀ x p x))
              (smoothOrthoFrame (I := I) g₀ x e x)) *
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (smoothOrthoFrame (I := I) g₀ x e x) (v 0)) (v 1) :=
        Finset.sum_congr rfl fun e _ => Finset.sum_comm
    _ = Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 2
            (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)
            (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁)).toSection x) D) v := hRHS.symm

private lemma sum_range_mono_of_nonneg (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    {m n : ℕ} (hmn : m ≤ n) :
    ∑ w ∈ Finset.range m, a w ≤ ∑ w ∈ Finset.range n, a w := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hmn) ?_
  intro j _ _
  exact ha j

private lemma sum_rect_le_sum_triangle (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    {k l i : ℕ} (hkl : k + l ≤ i) :
    (∑ j₁ ∈ Finset.range (k + 1), a j₁) * (∑ j₂ ∈ Finset.range (l + 1), a j₂) ≤
      ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁), a j₁ * a j₂ := by
  rw [Finset.sum_mul]
  have h1 : ∀ j₁ ∈ Finset.range (k + 1),
      a j₁ * ∑ j₂ ∈ Finset.range (l + 1), a j₂ ≤
        ∑ j₂ ∈ Finset.range (i + 1 - j₁), a j₁ * a j₂ := by
    intro j₁ hj₁
    rw [Finset.mul_sum]
    simp only [Finset.mem_range] at hj₁
    have hle : l + 1 ≤ i + 1 - j₁ := by omega
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hle) ?_
    intro j _ _
    exact mul_nonneg (ha j₁) (ha j)
  calc ∑ j₁ ∈ Finset.range (k + 1), a j₁ * ∑ j₂ ∈ Finset.range (l + 1), a j₂
      ≤ ∑ j₁ ∈ Finset.range (k + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁), a j₁ * a j₂ :=
        Finset.sum_le_sum h1
    _ ≤ ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁), a j₁ * a j₂ := by
        have hki : k + 1 ≤ i + 1 := by omega
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr hki) ?_
        intro j _ _
        exact Finset.sum_nonneg fun j₂ _ => mul_nonneg (ha j) (ha j₂)

end helpers


theorem exists_riemannianFiberNormSq_iteratedCovGrad_gInvDiffQuadResidualField_connDiffSection_diagonalProductGrid
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x) ≤
          K i * ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
                ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                  (connDiffSection (I := I) g₁ g₀)).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
                ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                  (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  classical
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set Kd2 : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + u)
      (iteratedCovGrad (I := I) g₀ 4 2 u (cometricDoubleTraceField (I := I) g₀ 2))).choose
    with hKd2_def
  have hKd2_nn : ∀ u, 0 ≤ Kd2 u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + u)
      (iteratedCovGrad (I := I) g₀ 4 2 u (cometricDoubleTraceField (I := I) g₀ 2))).choose_spec.1
  have hKd2_bound : ∀ u (b : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) b
          ((iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection b) ≤ Kd2 u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + u)
      (iteratedCovGrad (I := I) g₀ 4 2 u (cometricDoubleTraceField (I := I) g₀ 2))).choose_spec.2
  set Kd1 : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (1 + u)
      (iteratedCovGrad (I := I) g₀ 3 1 u (cometricDoubleTraceField (I := I) g₀ 1))).choose
    with hKd1_def
  have hKd1_nn : ∀ u, 0 ≤ Kd1 u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (1 + u)
      (iteratedCovGrad (I := I) g₀ 3 1 u (cometricDoubleTraceField (I := I) g₀ 1))).choose_spec.1
  have hKd1_bound : ∀ u (b : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + u) b
          ((iteratedCovGrad (I := I) g₀ 3 1 u
            (cometricDoubleTraceField (I := I) g₀ 1)).toSection b) ≤ Kd1 u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (1 + u)
      (iteratedCovGrad (I := I) g₀ 3 1 u (cometricDoubleTraceField (I := I) g₀ 1))).choose_spec.2
  set C1 : ℕ → ℝ := fun k =>
    diagonalGridGrowthFactor (E := E) k * ((∑ u ∈ Finset.range (k + 1), Kd2 u) * fr) with hC1_def
  have hG_nn : ∀ j, 0 ≤ diagonalGridGrowthFactor (E := E) j := fun j => by
    rw [diagonalGridGrowthFactor]
    positivity
  have hC1_nn : ∀ k, 0 ≤ C1 k := fun k =>
    mul_nonneg (hG_nn k)
      (mul_nonneg (Finset.sum_nonneg fun u _ => hKd2_nn u) hfr_nn)
  set C2 : ℕ → ℝ := fun l =>
    diagonalGridGrowthFactor (E := E) l *
      ((∑ u ∈ Finset.range (l + 1), Kd1 u) *
        (fr * ∑ w ∈ Finset.range (l + 1), C1 w)) with hC2_def
  have hC2_nn : ∀ l, 0 ≤ C2 l := fun l =>
    mul_nonneg (hG_nn l)
      (mul_nonneg (Finset.sum_nonneg fun u _ => hKd1_nn u)
        (mul_nonneg hfr_nn (Finset.sum_nonneg fun w _ => hC1_nn w)))
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      ∑ k ∈ Finset.range (i + 1), C1 k * ∑ l ∈ Finset.range (i + 1 - k), C2 l,
    fun i => mul_nonneg (hG_nn i) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (hC1_nn k) (Finset.sum_nonneg fun l _ => hC2_nn l)), ?_⟩
  intro g₁ i x
  have ha_nn : ∀ j : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + j) x _
  have hT_nn : ∀ k : ℕ, 0 ≤ ∑ w ∈ Finset.range (k + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
        ((iteratedCovGrad (I := I) g₀ 1 2 w (connDiffSection (I := I) g₁ g₀)).toSection x) :=
    fun k => Finset.sum_nonneg fun w _ => ha_nn w
  have hSEL : ∀ w : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 1 4 w
            (slotExtend (I := I) (M := M) g₀ 0 3
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
          ((iteratedCovGrad (I := I) g₀ 1 2 w
            (connDiffSection (I := I) g₁ g₀)).toSection x) := by
    intro w
    have h := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁) w x
    rw [rfns_icg_connDiffLowered_eq_connDiffSection (I := I) (M := M) g₀ g₁ w x] at h
    exact h
  have hArm : ∀ k : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 1 2 k
            (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)).toSection x) ≤
        C1 k * ∑ w ∈ Finset.range (k + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
            ((iteratedCovGrad (I := I) g₀ 1 2 w
              (connDiffSection (I := I) g₁ g₀)).toSection x) := by
    intro k
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le (I := I)
      (M := M) g₀ k 1 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
      (slotExtend (I := I) (M := M) g₀ 0 3 (connDiffLoweredCc (I := I) g₀ g₁)) x) ?_
    calc diagonalGridGrowthFactor (E := E) k *
          ∑ u ∈ Finset.range (k + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
                ((iteratedCovGrad (I := I) g₀ 4 2 u
                  (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
              ∑ w ∈ Finset.range (k + 1 - u),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (4 + w) x
                  ((iteratedCovGrad (I := I) g₀ 1 4 w
                    (slotExtend (I := I) (M := M) g₀ 0 3
                      (connDiffLoweredCc (I := I) g₀ g₁))).toSection x)
        ≤ diagonalGridGrowthFactor (E := E) k *
            ∑ u ∈ Finset.range (k + 1), Kd2 u *
              (fr * ∑ w ∈ Finset.range (k + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 w
                    (connDiffSection (I := I) g₁ g₀)).toSection x)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => ?_) (hG_nn k)
          refine mul_le_mul (hKd2_bound u x) ?_
            (Finset.sum_nonneg fun w _ =>
              riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (4 + w) x _)
            (hKd2_nn u)
          calc ∑ w ∈ Finset.range (k + 1 - u),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 1 4 w
                  (slotExtend (I := I) (M := M) g₀ 0 3
                    (connDiffLoweredCc (I := I) g₀ g₁))).toSection x)
              ≤ ∑ w ∈ Finset.range (k + 1 - u),
                  fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 w
                      (connDiffSection (I := I) g₁ g₀)).toSection x) :=
                Finset.sum_le_sum fun w _ => hSEL w
            _ = fr * ∑ w ∈ Finset.range (k + 1 - u),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 w
                      (connDiffSection (I := I) g₁ g₀)).toSection x) := by
                rw [Finset.mul_sum]
            _ ≤ fr * ∑ w ∈ Finset.range (k + 1),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 w
                      (connDiffSection (I := I) g₁ g₀)).toSection x) :=
                mul_le_mul_of_nonneg_left
                  (sum_range_mono_of_nonneg _ ha_nn (by omega)) hfr_nn
      _ = C1 k * ∑ w ∈ Finset.range (k + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
              ((iteratedCovGrad (I := I) g₀ 1 2 w
                (connDiffSection (I := I) g₁ g₀)).toSection x) := by
          rw [← Finset.sum_mul, hC1_def]
          beta_reduce
          ring
  have hcore : ∀ w : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 3 w
            (reindexCoeffGen (I := I) (M := M) g₀ 2 3
              (slotExtend (I := I) (M := M) g₀ 1 2
                (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁))
              (Equiv.swap (0 : Fin 2) 1))).toSection x) ≤
        (fr * C1 w) * ∑ u ∈ Finset.range (w + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + u) x
            ((iteratedCovGrad (I := I) g₀ 1 2 u
              (connDiffSection (I := I) g₁ g₀)).toSection x) := by
    intro w
    rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 3
      (slotExtend (I := I) (M := M) g₀ 1 2
        (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁))
      (Equiv.swap (0 : Fin 2) 1) w x]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
      (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁) w x) ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hArm w) hfr_nn
  have hW : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 1 l
            (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁)).toSection x) ≤
        C2 l * ∑ w ∈ Finset.range (l + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
            ((iteratedCovGrad (I := I) g₀ 1 2 w
              (connDiffSection (I := I) g₁ g₀)).toSection x) := by
    intro l
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le (I := I)
      (M := M) g₀ l 2 3 1 (cometricDoubleTraceField (I := I) g₀ 1)
      (reindexCoeffGen (I := I) (M := M) g₀ 2 3
        (slotExtend (I := I) (M := M) g₀ 1 2
          (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁))
        (Equiv.swap (0 : Fin 2) 1)) x) ?_
    calc diagonalGridGrowthFactor (E := E) l *
          ∑ u ∈ Finset.range (l + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + u) x
                ((iteratedCovGrad (I := I) g₀ 3 1 u
                  (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) *
              ∑ w ∈ Finset.range (l + 1 - u),
                riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + w) x
                  ((iteratedCovGrad (I := I) g₀ 2 3 w
                    (reindexCoeffGen (I := I) (M := M) g₀ 2 3
                      (slotExtend (I := I) (M := M) g₀ 1 2
                        (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁))
                      (Equiv.swap (0 : Fin 2) 1))).toSection x)
        ≤ diagonalGridGrowthFactor (E := E) l *
            ∑ u ∈ Finset.range (l + 1), Kd1 u *
              ((fr * ∑ w ∈ Finset.range (l + 1), C1 w) *
                ∑ w ∈ Finset.range (l + 1),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 w
                      (connDiffSection (I := I) g₁ g₀)).toSection x)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => ?_) (hG_nn l)
          refine mul_le_mul (hKd1_bound u x) ?_
            (Finset.sum_nonneg fun w _ =>
              riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (3 + w) x _)
            (hKd1_nn u)
          calc ∑ w ∈ Finset.range (l + 1 - u),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + w) x
                ((iteratedCovGrad (I := I) g₀ 2 3 w
                  (reindexCoeffGen (I := I) (M := M) g₀ 2 3
                    (slotExtend (I := I) (M := M) g₀ 1 2
                      (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁))
                    (Equiv.swap (0 : Fin 2) 1))).toSection x)
              ≤ ∑ w ∈ Finset.range (l + 1 - u),
                  (fr * C1 w) * ∑ v ∈ Finset.range (l + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + v) x
                      ((iteratedCovGrad (I := I) g₀ 1 2 v
                        (connDiffSection (I := I) g₁ g₀)).toSection x) := by
                refine Finset.sum_le_sum fun w hw => ?_
                refine le_trans (hcore w) ?_
                refine mul_le_mul_of_nonneg_left ?_
                  (mul_nonneg hfr_nn (hC1_nn w))
                refine sum_range_mono_of_nonneg _ ha_nn ?_
                simp only [Finset.mem_range] at hw
                omega
            _ = (∑ w ∈ Finset.range (l + 1 - u), fr * C1 w) *
                  ∑ v ∈ Finset.range (l + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + v) x
                      ((iteratedCovGrad (I := I) g₀ 1 2 v
                        (connDiffSection (I := I) g₁ g₀)).toSection x) := by
                rw [Finset.sum_mul]
            _ ≤ (∑ w ∈ Finset.range (l + 1), fr * C1 w) *
                  ∑ v ∈ Finset.range (l + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + v) x
                      ((iteratedCovGrad (I := I) g₀ 1 2 v
                        (connDiffSection (I := I) g₁ g₀)).toSection x) := by
                refine mul_le_mul_of_nonneg_right ?_ (hT_nn l)
                refine sum_range_mono_of_nonneg _
                  (fun w => mul_nonneg hfr_nn (hC1_nn w)) (by omega)
            _ = (fr * ∑ w ∈ Finset.range (l + 1), C1 w) *
                  ∑ v ∈ Finset.range (l + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + v) x
                      ((iteratedCovGrad (I := I) g₀ 1 2 v
                        (connDiffSection (I := I) g₁ g₀)).toSection x) := by
                rw [← Finset.mul_sum]
      _ = C2 l * ∑ w ∈ Finset.range (l + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
              ((iteratedCovGrad (I := I) g₀ 1 2 w
                (connDiffSection (I := I) g₁ g₀)).toSection x) := by
          rw [← Finset.sum_mul, hC2_def]
          beta_reduce
          ring
  rw [gInvDiffQuadResidualField_eq_refold (I := I) (M := M) g₀ g₁]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le (I := I)
    (M := M) g₀ i 2 1 2 (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)
    (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁) x) ?_
  calc diagonalGridGrowthFactor (E := E) i *
        ∑ k ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + k) x
              ((iteratedCovGrad (I := I) g₀ 1 2 k
                (gInvQuadRefoldArm (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - k),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 1 l
                  (gInvQuadRefoldWeight (I := I) (M := M) g₀ g₁)).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) i *
          ∑ k ∈ Finset.range (i + 1),
            (C1 k * ∑ w ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                ((iteratedCovGrad (I := I) g₀ 1 2 w
                  (connDiffSection (I := I) g₁ g₀)).toSection x)) *
            ∑ l ∈ Finset.range (i + 1 - k),
              (C2 l * ∑ w ∈ Finset.range (l + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 w
                    (connDiffSection (I := I) g₁ g₀)).toSection x)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (hG_nn i)
        refine mul_le_mul (hArm k) (Finset.sum_le_sum fun l _ => hW l) ?_ ?_
        · exact Finset.sum_nonneg fun l _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (1 + l) x _
        · exact mul_nonneg (hC1_nn k) (hT_nn k)
    _ ≤ diagonalGridGrowthFactor (E := E) i *
          ((∑ k ∈ Finset.range (i + 1), C1 k * ∑ l ∈ Finset.range (i + 1 - k), C2 l) *
            ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                    (connDiffSection (I := I) g₁ g₀)).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                    (connDiffSection (I := I) g₁ g₀)).toSection x)) := by
        refine mul_le_mul_of_nonneg_left ?_ (hG_nn i)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun k hk => ?_
        calc (C1 k * ∑ w ∈ Finset.range (k + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 w
                    (connDiffSection (I := I) g₁ g₀)).toSection x)) *
              ∑ l ∈ Finset.range (i + 1 - k),
                (C2 l * ∑ w ∈ Finset.range (l + 1),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 w
                      (connDiffSection (I := I) g₁ g₀)).toSection x))
            = ∑ l ∈ Finset.range (i + 1 - k),
                (C1 k * ∑ w ∈ Finset.range (k + 1),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 w
                      (connDiffSection (I := I) g₁ g₀)).toSection x)) *
                (C2 l * ∑ w ∈ Finset.range (l + 1),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 w
                      (connDiffSection (I := I) g₁ g₀)).toSection x)) := by
              rw [Finset.mul_sum]
          _ ≤ ∑ l ∈ Finset.range (i + 1 - k),
                (C1 k * C2 l) *
                  ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
                        ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                          (connDiffSection (I := I) g₁ g₀)).toSection x) *
                      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
                        ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                          (connDiffSection (I := I) g₁ g₀)).toSection x) := by
              refine Finset.sum_le_sum fun l hl => ?_
              have hkl : k + l ≤ i := by
                simp only [Finset.mem_range] at hk hl
                omega
              calc (C1 k * ∑ w ∈ Finset.range (k + 1),
                      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                        ((iteratedCovGrad (I := I) g₀ 1 2 w
                          (connDiffSection (I := I) g₁ g₀)).toSection x)) *
                    (C2 l * ∑ w ∈ Finset.range (l + 1),
                      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                        ((iteratedCovGrad (I := I) g₀ 1 2 w
                          (connDiffSection (I := I) g₁ g₀)).toSection x))
                  = (C1 k * C2 l) *
                      ((∑ w ∈ Finset.range (k + 1),
                        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                          ((iteratedCovGrad (I := I) g₀ 1 2 w
                            (connDiffSection (I := I) g₁ g₀)).toSection x)) *
                       ∑ w ∈ Finset.range (l + 1),
                        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + w) x
                          ((iteratedCovGrad (I := I) g₀ 1 2 w
                            (connDiffSection (I := I) g₁ g₀)).toSection x)) := by
                    ring
                _ ≤ (C1 k * C2 l) *
                      ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁),
                        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
                            ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                              (connDiffSection (I := I) g₁ g₀)).toSection x) *
                          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
                            ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                              (connDiffSection (I := I) g₁ g₀)).toSection x) := by
                    refine mul_le_mul_of_nonneg_left ?_
                      (mul_nonneg (hC1_nn k) (hC2_nn l))
                    exact sum_rect_le_sum_triangle
                      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
                        ((iteratedCovGrad (I := I) g₀ 1 2 j
                          (connDiffSection (I := I) g₁ g₀)).toSection x)) ha_nn hkl
          _ = (C1 k * ∑ l ∈ Finset.range (i + 1 - k), C2 l) *
                ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
                      ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                        (connDiffSection (I := I) g₁ g₀)).toSection x) *
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
                      ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                        (connDiffSection (I := I) g₁ g₀)).toSection x) := by
              rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = (diagonalGridGrowthFactor (E := E) i *
          ∑ k ∈ Finset.range (i + 1), C1 k * ∑ l ∈ Finset.range (i + 1 - k), C2 l) *
          ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
                ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                  (connDiffSection (I := I) g₁ g₀)).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
                ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                  (connDiffSection (I := I) g₁ g₀)).toSection x) := by
        rw [mul_assoc]


theorem riemannianFiberNormSq_iteratedCovGrad_gInvDiffQuadResidualFieldInputSymm_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSlotSymm (I := I) (M := M) g₀
                (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨K, hK_nn, hK⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_gInvDiffQuadResidualField_connDiffSection_diagonalProductGrid
      (I := I) (M := M) g₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  have hSW_ex : ∀ q : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 2 q
          (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) ≤ c := fun q =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + q)
      (iteratedCovGrad (I := I) g₀ 2 2 q (ccInputSlotSwapField (I := I) (M := M) g₀))
  choose SW hSW_nn hSW using hSW_ex
  set Cq : ℕ → ℝ := fun n => K n *
    ∑ j₁ ∈ Finset.range (n + 1), ∑ j₂ ∈ Finset.range (n + 1 - j₁),
      CA j₁ * CA j₂ * Combinatorics.windowPairCellCount (j₁ + 2) (j₂ + 2) with hCq_def
  have hCq_nn : ∀ n, 0 ≤ Cq n := by
    intro n
    refine mul_nonneg (hK_nn n) (Finset.sum_nonneg fun j₁ _ => Finset.sum_nonneg fun j₂ _ => ?_)
    exact mul_nonneg (mul_nonneg (hCA_nn j₁) (hCA_nn j₂))
      (Combinatorics.windowPairCellCount_nonneg _ _)
  refine ⟨fun i => (1 / 2 : ℝ) * Cq i +
      (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), Cq i') *
        (∑ l ∈ Finset.range (i + 1), SW l)), ?_, ?_⟩
  · intro i
    have h2 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), Cq i' := Finset.sum_nonneg fun i' _ => hCq_nn i'
    have h3 : 0 ≤ ∑ l ∈ Finset.range (i + 1), SW l := Finset.sum_nonneg fun l _ => hSW_nn l
    have h4 : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
    have h1 : 0 ≤ Cq i := hCq_nn i
    positivity
  · intro g₁ P htie δ hδ_le hδ0 hbound i x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
    have hb_nn : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set W : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hW_def
    have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
    have hAjet : ∀ j : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
        CA j * Combinatorics.boundedFactorGridWindow b (j + 1) (j + 2) := by
      intro j
      have h := hCA g₁ P htie hδ_le hδ0 hbound j x
      have heq : (∑ k ∈ Finset.range (j + 2), Combinatorics.antidiagonalTupleGrid b k) =
          Combinatorics.boundedFactorGridWindow b (j + 1) (j + 2) := by
        rw [Combinatorics.boundedFactorGridWindow]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_range] at hk
        exact Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b (by omega)
      rw [← heq]
      exact h
    have hQ : ∀ n : ℕ, n ≤ i →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x) ≤
        Cq n * W := by
      intro n hn
      refine le_trans (hK g₁ n x) ?_
      have hsum : (∑ j₁ ∈ Finset.range (n + 1), ∑ j₂ ∈ Finset.range (n + 1 - j₁),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
              ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                (connDiffSection (I := I) g₁ g₀)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
              ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                (connDiffSection (I := I) g₁ g₀)).toSection x)) ≤
          (∑ j₁ ∈ Finset.range (n + 1), ∑ j₂ ∈ Finset.range (n + 1 - j₁),
            CA j₁ * CA j₂ * Combinatorics.windowPairCellCount (j₁ + 2) (j₂ + 2)) * W := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun j₁ hj₁ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun j₂ hj₂ => ?_
        rw [Finset.mem_range] at hj₁ hj₂
        have hA₁ := hAjet j₁
        have hA₂ := hAjet j₂
        have hrfns₂_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + j₂) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j₂ (connDiffSection (I := I) g₁ g₀)).toSection x)
        have hwin₁_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (j₁ + 1) (j₁ + 2) :=
          Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
                ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                  (connDiffSection (I := I) g₁ g₀)).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
                ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                  (connDiffSection (I := I) g₁ g₀)).toSection x)
            ≤ (CA j₁ * Combinatorics.boundedFactorGridWindow b (j₁ + 1) (j₁ + 2)) *
                (CA j₂ * Combinatorics.boundedFactorGridWindow b (j₂ + 1) (j₂ + 2)) :=
              mul_le_mul hA₁ hA₂ hrfns₂_nn
                (mul_nonneg (hCA_nn j₁) hwin₁_nn)
          _ = (CA j₁ * CA j₂) * (Combinatorics.boundedFactorGridWindow b (j₁ + 1) (j₁ + 2) *
                Combinatorics.boundedFactorGridWindow b (j₂ + 1) (j₂ + 2)) := by ring
          _ ≤ (CA j₁ * CA j₂) * (Combinatorics.boundedFactorGridWindow b (i + 1) (j₁ + 2) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (j₂ + 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCA_nn j₁) (hCA_nn j₂))
              refine mul_le_mul
                (Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (le_refl _))
                (Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (le_refl _))
                (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _)
                (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _)
          _ ≤ (CA j₁ * CA j₂) * (Combinatorics.windowPairCellCount (j₁ + 2) (j₂ + 2) *
                Combinatorics.boundedFactorGridWindow b (i + 1) ((j₁ + 2) + (j₂ + 2) - 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCA_nn j₁) (hCA_nn j₂))
              exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn (i + 1) (j₁ + 2)
                (j₂ + 2) (by omega) (by omega)
          _ ≤ (CA j₁ * CA j₂) * (Combinatorics.windowPairCellCount (j₁ + 2) (j₂ + 2) * W) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCA_nn j₁) (hCA_nn j₂))
              refine mul_le_mul_of_nonneg_left ?_
                (Combinatorics.windowPairCellCount_nonneg _ _)
              rw [hW_def]
              exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
          _ = CA j₁ * CA j₂ * Combinatorics.windowPairCellCount (j₁ + 2) (j₂ + 2) * W := by
              ring
      refine le_trans (mul_le_mul_of_nonneg_left hsum (hK_nn n)) (le_of_eq ?_)
      simp only [hCq_def]
      ring
    have hsubject : ccInputSlotSymm (I := I) (M := M) g₀
        (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁) =
        (1 / 2 : ℝ) • (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀)) := rfl
    rw [hsubject]
    have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
        ((1 / 2 : ℝ) • (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀)))).toSection x =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
              (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
              (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) := by
      rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
        SmoothCcTensor.toSection_smul]
      rfl
    rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
      show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
    have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 i
        (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
              (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
              (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
      rfl
    rw [hsplit]
    refine le_trans (mul_le_mul_of_nonneg_left
      (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
    have hQi : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x) ≤ Cq i * W :=
      hQ i (le_refl i)
    have hApp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
        diagonalGridGrowthFactor (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Cq i') *
          ((∑ l ∈ Finset.range (i + 1), SW l) * W)) := by
      refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
        (I := I) (M := M) g₀ i 2 2 2
        (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
        (ccInputSlotSwapField (I := I) (M := M) g₀) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i' hi' => ?_
      rw [Finset.mem_range] at hi'
      have hswapsum : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1), SW l := by
        refine le_trans (Finset.sum_le_sum fun l _ => hSW l x) ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega)) ?_
        exact fun l _ _ => hSW_nn l
      have hQi' := hQ i' (by omega)
      have hswap_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 2 2 i'
                (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l
                  (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)
          ≤ (Cq i' * W) * (∑ l ∈ Finset.range (i + 1), SW l) :=
            mul_le_mul hQi' hswapsum hswap_nn (mul_nonneg (hCq_nn i') hW_nn)
        _ = Cq i' * ((∑ l ∈ Finset.range (i + 1), SW l) * W) := by ring
    calc (1 / 4 : ℝ) * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
                (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
                (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x))
        ≤ (1 / 4 : ℝ) * (2 * (Cq i * W)
            + 2 * (diagonalGridGrowthFactor (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Cq i') *
              ((∑ l ∈ Finset.range (i + 1), SW l) * W)))) := by
          nlinarith [hQi, hApp]
      _ = ((1 / 2 : ℝ) * Cq i +
            (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), Cq i') *
              (∑ l ∈ Finset.range (i + 1), SW l))) * W := by ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
