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
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldLinearizedRefoldIdentity
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldMonomialRefoldL2JetWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldRicciFoldWeightKernel


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

def koszulCovGradRaw (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) :
    SmoothCcTensor g₀ 0 3 :=
  (1 / 2 : ℝ) •
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2)
          (covGrad (I := I) (M := M) g₀ 0 2 S)
        + domDomCongrSection (I := I) g₀ (finRotate 3)
          (covGrad (I := I) (M := M) g₀ 0 2 S)
        - domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
          (covGrad (I := I) (M := M) g₀ 0 2 S))

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdKRaw_unitModel (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (a b c : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (koszulCovGradRaw (I := I) (M := M) g₀ S) x ![c, a, b] =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x ![b, a, c]
          + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x ![a, b, c]
          - unitModel (I := I) (M := M) g₀ 3
              (covGrad (I := I) (M := M) g₀ 0 2 S) x ![c, b, a]) := by
  classical
  set W : SmoothCcTensor g₀ 0 3 := covGrad (I := I) (M := M) g₀ 0 2 S with hW
  have hperm : ∀ (σ : Equiv.Perm (Fin 3)) (m : Fin 3 → TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 3 (domDomCongrSection (I := I) g₀ σ W) x m =
        unitModel (I := I) (M := M) g₀ 3 W x (fun i => m (σ i)) := by
    intro σ m
    rw [domDomCongrSection_unitModel (I := I) g₀ σ W x,
      ContinuousMultilinearMap.domDomCongr_apply]
  have hlin : unitModel (I := I) (M := M) g₀ 3 (koszulCovGradRaw (I := I) (M := M) g₀ S) x ![c, a, b] =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 3 (domDomCongrSection (I := I) g₀
              (Equiv.swap (0 : Fin 3) 2) W) x ![c, a, b]
          + unitModel (I := I) (M := M) g₀ 3 (domDomCongrSection (I := I) g₀ (finRotate 3) W) x
              ![c, a, b]
          - unitModel (I := I) (M := M) g₀ 3 (domDomCongrSection (I := I) g₀
              (Equiv.swap (1 : Fin 3) 2) W) x ![c, a, b]) := by
    simp only [koszulCovGradRaw, unitModel, SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_add,
      SmoothCcTensor.toSection_sub, ContMDiffSection.coe_smul, ContMDiffSection.coe_add,
      ContMDiffSection.coe_sub, Pi.smul_apply, Pi.add_apply, Pi.sub_apply]
    rfl
  rw [hlin, hperm, hperm, hperm]
  have e1 : (fun i => (![c, a, b] : Fin 3 → TangentSpace I x) ((Equiv.swap (0 : Fin 3) 2) i)) =
      ![b, a, c] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  have e2 : (fun i => (![c, a, b] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
      ![a, b, c] := by
    funext i; fin_cases i <;> simp [finRotate_succ_apply]
  have e3 : (fun i => (![c, a, b] : Fin 3 → TangentSpace I x) ((Equiv.swap (1 : Fin 3) 2) i)) =
      ![c, b, a] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  rw [e1, e2, e3]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdKRaw_unitModel_eq_linearizedKoszul (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (a b c : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (koszulCovGradRaw (I := I) (M := M) g₀ S) x ![c, a, b] =
      linearizedKoszulCovec (I := I) g₀ S x a b c := by
  rw [bdKRaw_unitModel (I := I) (M := M) g₀ S x a b c,
    linearizedKoszulCovec_apply (I := I) g₀ S x a b c]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdInner_sharpKoszul_left (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (a b z : TangentSpace I x) :
    g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x a b) z =
      linearizedKoszulCovec (I := I) g₀ S x a b z := by
  rw [sharpRaisedKoszulVec]
  exact DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp (I := I) g₁ x
    (linearizedKoszulCovec (I := I) g₀ S x a b) z

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdInner_sharpKoszul_right (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (a b z : TangentSpace I x) :
    g₁.inner x z (sharpRaisedKoszulVec (I := I) g₀ g₁ S x a b) =
      linearizedKoszulCovec (I := I) g₀ S x a b z := by
  rw [sharpRaisedKoszulVec]
  exact DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp_right (I := I) g₁ x
    (linearizedKoszulCovec (I := I) g₀ S x a b) z

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdKoszulCc_unitModel_eq_g1_inner (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (a b c : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x ![c, a, b] =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b) c := by
  rw [koszulCovecCc_unitModel (I := I) g₀ P x a b c]
  rw [connDiffInner_g1_eq_half_covGradSymmS (I := I) g₀ g₁ P htie x a b c]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma bdSlotExtendIter_three_toModel (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 3) (x : M) (D : Tensor0SSpace 3 I x)
    (u : Fin 6 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 X).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1, u 2] *
        unitModel (I := I) (M := M) g₀ 3 X x (fun k : Fin 3 => u (Fin.natAdd 3 k)) := by
  rw [show ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 X).toSection x) D) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 5 x).symm
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2 X).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D)) from rfl]
  have hkey1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 5)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 5 x).symm
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 2 X).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D)))
    (v0 := u 0) (vs := Matrix.vecTail u)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey1
  rw [show (Fin.cons (u 0) (Matrix.vecTail u) : Fin 6 → TangentSpace I x) = u from by
    funext k
    refine Fin.cases rfl (fun i => rfl) k] at hkey1
  rw [← hkey1]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 2 X).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D) (u 0)) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 4 x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 1 X).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)))) from rfl]
  rw [show (Matrix.vecTail u : Fin 5 → TangentSpace I x) =
      Fin.cons (u 1) (fun k : Fin 4 => u (Fin.natAdd 2 k)) from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · rfl
    · change u (Fin.succ (Fin.succ i)) = u (Fin.natAdd 2 i)
      congr 1
      exact Fin.ext (by simp [Fin.succ, Fin.natAdd]; omega)]
  have hkey2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 4)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 4 x).symm
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 X).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)))))
    (v0 := u 1) (vs := fun k : Fin 4 => u (Fin.natAdd 2 k))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey2
  rw [← hkey2]
  rw [show (fun k : Fin 4 => u (Fin.natAdd 2 k)) =
      Fin.cons (u 2) (fun k : Fin 3 => u (Fin.natAdd 3 k)) from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · rfl
    · change u (Fin.natAdd 2 (Fin.succ i)) = u (Fin.natAdd 3 i)
      congr 1
      exact Fin.ext (by simp [Fin.succ, Fin.natAdd]; omega)]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 X).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0))) (u 1)) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x).symm
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from X.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
              (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)))) from rfl]
  have hkey3 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 3)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x).symm
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from X.toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)))))
    (v0 := u 2) (vs := fun k : Fin 3 => u (Fin.natAdd 3 k))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey3
  rw [← hkey3]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from X.toSection x).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1))) (u 2)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from X.toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)) (u 2)) from rfl]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)) (u 2) with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![u 0, u 1, u 2] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)) (v0 := u 2)
      (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (v0 := u 1)
      (vs := Fin.cons (u 2) (fun i : Fin 0 => i.elim0))
    rw [h2]
    have h3 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2)
      (T := D) (v0 := u 0)
      (vs := Fin.cons (u 1) (Fin.cons (u 2) (fun i : Fin 0 => i.elim0)))
    rw [h3]
    refine congrArg _ ?_
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    refine Fin.cases rfl (fun i2 => ?_) i
    refine Fin.cases rfl (fun i3 => i3.elim0) i2
  have hdecomp := bdTensor0S_zero_rank_decomp (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rfl

def bdSGKTau1 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![3, 4, 0, 1, 5, 2] : Fin 6 → Fin 6) i,
   fun i => (![2, 3, 5, 0, 1, 4] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

def bdSGKTau2 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![0, 4, 3, 1, 5, 2] : Fin 6 → Fin 6) i,
   fun i => (![0, 3, 5, 2, 1, 4] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

def bdSGKTau3 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![3, 2, 0, 1, 5, 4] : Fin 6 → Fin 6) i,
   fun i => (![2, 3, 1, 0, 5, 4] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

def bdSGKTau4 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![0, 2, 3, 1, 5, 4] : Fin 6 → Fin 6) i,
   fun i => (![0, 3, 1, 2, 5, 4] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [BoundarylessManifold I M] in
private lemma bdSGKMvWeight_unitModel_gen (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 6)) (P S : SmoothCcTensor g₀ 0 2) (x : M) (m : Fin 4 → E) :
    unitModel (I := I) (M := M) g₀ 4
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ S))
              (koszulCovecCc (I := I) g₀ P)))) x m =
      ∑ e : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((Fin.cons ((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 0)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 1)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 2))] *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovGradRaw (I := I) (M := M) g₀ S) x
            ![((Fin.cons ((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 3)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 4)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 5))] := by
  classical
  set κ3 : SmoothCcTensor g₀ 0 3 := koszulCovGradRaw (I := I) (M := M) g₀ S with hκ3_def
  set Cval : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (koszulCovecCc (I := I) g₀ P).toSection x)
      (unitTensor (I := I) (M := M) x) with hCval_def
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
          (koszulCovecCc (I := I) g₀ P))).toSection x)
      (unitTensor (I := I) (M := M) x) with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel Cval ![(w (σ 0) : E), (w (σ 1) : E), (w (σ 2) : E)] *
          unitModel (I := I) (M := M) g₀ 3 κ3 x
            ![(w (σ 3) : E), (w (σ 4) : E), (w (σ 5) : E)] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
            (koszulCovecCc (I := I) g₀ P))).toSection x)
        (unitTensor (I := I) (M := M) x)) =
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
          tensorRS_domDomCongr σ
            ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
              (koszulCovecCc (I := I) g₀ P)).toSection x))
          (unitTensor (I := I) (M := M) x)) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) σ
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
        (koszulCovecCc (I := I) g₀ P)).toSection x)
      (unitTensor (I := I) (M := M) x)]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
          (koszulCovecCc (I := I) g₀ P)).toSection x)
        (unitTensor (I := I) (M := M) x)) =
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3).toSection x) Cval) from by
      rw [appCcRS_toSection]
      rfl]
    rw [bdSlotExtendIter_three_toModel (I := I) (M := M) g₀ κ3 x Cval (fun i => w (σ i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · rw [show unitModel (I := I) (M := M) g₀ 3 κ3 x
          (fun k : Fin 3 => ((fun i => w (σ i)) (Fin.natAdd 3 k) : E)) =
          unitModel (I := I) (M := M) g₀ 3 κ3 x
            ![(w (σ 3) : E), (w (σ 4) : E), (w (σ 5) : E)] from by
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
  rw [show unitModel (I := I) (M := M) g₀ 4
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
            (koszulCovecCc (I := I) g₀ P)))) x =
      Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₁ 4 x Y) from by
    rw [unitModel, hY_def]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₁ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y) m]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hYval]
  rfl

def sharpGradKoszulWeightedTerm (g₀ g₁ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 6))
    (P S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ S))
        (koszulCovecCc (I := I) g₀ P)))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
private lemma bdSGKWeights_unitModel_eq_kernel (g₀ g₁ : SmoothRiemannianMetric I M)
    (P S : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (p q v0 v1 : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 P S +
            sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 P S) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 P S +
            sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 P S)) x
        ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x p q v0 v1 := by
  classical
  have hM1 : unitModel (I := I) (M := M) g₀ 4
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 P S) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E), (p : E),
              ((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E)] *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovGradRaw (I := I) (M := M) g₀ S) x
            ![((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E),
              (q : E), (v0 : E)] := by
    rw [show sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 P S =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau1
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ S))
              (koszulCovecCc (I := I) g₀ P))) from rfl]
    rw [bdSGKMvWeight_unitModel_gen (I := I) (M := M) g₀ g₁ bdSGKTau1 P S x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
  have hM2 : unitModel (I := I) (M := M) g₀ 4
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 P S) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E),
              (p : E), (v1 : E)] *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovGradRaw (I := I) (M := M) g₀ S) x
            ![((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E),
              (q : E), (v0 : E)] := by
    rw [show sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 P S =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau2
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ S))
              (koszulCovecCc (I := I) g₀ P))) from rfl]
    rw [bdSGKMvWeight_unitModel_gen (I := I) (M := M) g₀ g₁ bdSGKTau2 P S x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
  have hM3 : unitModel (I := I) (M := M) g₀ 4
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 P S) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E), (v0 : E),
              ((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E)] *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovGradRaw (I := I) (M := M) g₀ S) x
            ![((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E),
              (q : E), (p : E)] := by
    rw [show sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 P S =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau3
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ S))
              (koszulCovecCc (I := I) g₀ P))) from rfl]
    rw [bdSGKMvWeight_unitModel_gen (I := I) (M := M) g₀ g₁ bdSGKTau3 P S x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
  have hM4 : unitModel (I := I) (M := M) g₀ 4
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 P S) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E),
              (v0 : E), (v1 : E)] *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovGradRaw (I := I) (M := M) g₀ S) x
            ![((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E),
              (q : E), (p : E)] := by
    rw [show sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 P S =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau4
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ S))
              (koszulCovecCc (I := I) g₀ P))) from rfl]
    rw [bdSGKMvWeight_unitModel_gen (I := I) (M := M) g₀ g₁ bdSGKTau4 P S x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
  have hT1 : g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p
      (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q v0)) v1 =
      ∑ e : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E), (p : E),
              ((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E)] *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovGradRaw (I := I) (M := M) g₀ S) x
            ![((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E),
              (q : E), (v0 : E)] := by
    conv_lhs => rw [bdOrthoFrame_center_repr (I := I) (M := M) g₁ x
      (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q v0)]
    rw [map_sum, map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_smul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [bdInner_sharpKoszul_right (I := I) (M := M) g₀ g₁ S x q v0
      (smoothOrthoFrame (I := I) g₁ x e x)]
    rw [bdKoszulCc_unitModel_eq_g1_inner (I := I) (M := M) g₀ g₁ P htie x p
      (smoothOrthoFrame (I := I) g₁ x e x) v1]
    rw [bdKRaw_unitModel_eq_linearizedKoszul (I := I) (M := M) g₀ S x q v0
      (smoothOrthoFrame (I := I) g₁ x e x)]
    ring
  have hT2 : g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q v0)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v1) =
      ∑ e : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E),
              (p : E), (v1 : E)] *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovGradRaw (I := I) (M := M) g₀ S) x
            ![((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E),
              (q : E), (v0 : E)] := by
    conv_lhs => rw [bdOrthoFrame_center_repr (I := I) (M := M) g₁ x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v1)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_smul, smul_eq_mul]
    rw [bdInner_sharpKoszul_left (I := I) (M := M) g₀ g₁ S x q v0
      (smoothOrthoFrame (I := I) g₁ x e x)]
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x e x)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v1)]
    rw [← bdKoszulCc_unitModel_eq_g1_inner (I := I) (M := M) g₀ g₁ P htie x p v1
      (smoothOrthoFrame (I := I) g₁ x e x)]
    rw [← bdKRaw_unitModel_eq_linearizedKoszul (I := I) (M := M) g₀ S x q v0
      (smoothOrthoFrame (I := I) g₁ x e x)]
  have hT3 : g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0
      (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q p)) v1 =
      ∑ e : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E), (v0 : E),
              ((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E)] *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovGradRaw (I := I) (M := M) g₀ S) x
            ![((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E),
              (q : E), (p : E)] := by
    conv_lhs => rw [bdOrthoFrame_center_repr (I := I) (M := M) g₁ x
      (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q p)]
    rw [map_sum, map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_smul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [bdInner_sharpKoszul_right (I := I) (M := M) g₀ g₁ S x q p
      (smoothOrthoFrame (I := I) g₁ x e x)]
    rw [bdKoszulCc_unitModel_eq_g1_inner (I := I) (M := M) g₀ g₁ P htie x v0
      (smoothOrthoFrame (I := I) g₁ x e x) v1]
    rw [bdKRaw_unitModel_eq_linearizedKoszul (I := I) (M := M) g₀ S x q p
      (smoothOrthoFrame (I := I) g₁ x e x)]
    ring
  have hT4 : g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q p)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 v1) =
      ∑ e : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E),
              (v0 : E), (v1 : E)] *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovGradRaw (I := I) (M := M) g₀ S) x
            ![((smoothOrthoFrame (I := I) g₁ x e x : TangentSpace I x) : E),
              (q : E), (p : E)] := by
    conv_lhs => rw [bdOrthoFrame_center_repr (I := I) (M := M) g₁ x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 v1)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_smul, smul_eq_mul]
    rw [bdInner_sharpKoszul_left (I := I) (M := M) g₀ g₁ S x q p
      (smoothOrthoFrame (I := I) g₁ x e x)]
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x e x)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 v1)]
    rw [← bdKoszulCc_unitModel_eq_g1_inner (I := I) (M := M) g₀ g₁ P htie x v0 v1
      (smoothOrthoFrame (I := I) g₁ x e x)]
    rw [← bdKRaw_unitModel_eq_linearizedKoszul (I := I) (M := M) g₀ S x q p
      (smoothOrthoFrame (I := I) g₁ x e x)]
  rw [bdUnitModel_sub (I := I) (M := M) g₀ 4 _ _ x,
    bdUnitModel_add (I := I) (M := M) g₀ 4 _ _ x,
    bdUnitModel_add (I := I) (M := M) g₀ 4 _ _ x,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply]
  rw [hM1, hM2, hM3, hM4]
  rw [sharpGradKoszulKernelBilin_apply (I := I) g₀ g₁ S x p q v0 v1]
  rw [hT1, hT2, hT3, hT4]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
lemma bdSGK_eq_refold (g₀ g₁ : SmoothRiemannianMetric I M)
    (P S : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁ S =
      (2 : ℝ) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 P S +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 P S) -
                (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 P S +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 P S)))) := by
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
  have hRHSsmul : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (((2 : ℝ) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 P S +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 P S) -
                (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 P S +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 P S))))).toSection x)) D) =
      (2 : ℝ) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 P S +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 P S) -
                (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 P S +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 P S))))).toSection x) D) := by
    rw [show ((((2 : ℝ) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 P S +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 P S) -
                (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 P S +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 P S))))).toSection x)) =
        (2 : ℝ) •
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 P S +
                    sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 P S) -
                  (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 P S +
                    sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 P S))))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl
  rw [hRHSsmul, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [bdPairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 P S +
        sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 P S) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 P S +
        sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 P S)) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁ S).toSection x) D) =
      sharpGradKoszulBiContrFib (I := I) g₀ g₁ S x D from rfl]
  rw [show sharpGradKoszulBiContrFib (I := I) g₀ g₁ S x =
      sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S
        (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  rw [sharpGradKoszulBiContrFibFixedFrame_toModel (I := I) g₀ g₁ S
    (smoothOrthoFrame (I := I) g₁ x) x D v]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show unitModel (I := I) (M := M) g₀ 4
      ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 P S +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 P S) -
        (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 P S +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 P S)) x
      ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] =
      sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x
        (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
        (v 0) (v 1) from
    bdSGKWeights_unitModel_eq_kernel (I := I) (M := M) g₀ g₁ P S htie x
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
      (v 0) (v 1)]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdCovGrad_unitModel_smul (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (c : ℝ) (x : M) (v : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 (c • T)) x v =
      c * unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 T) x v := by
  rw [covGrad_smul (I := I) (M := M)]
  rw [bdUnitModel_smul (I := I) (M := M) g₀ 3 c (covGrad (I := I) (M := M) g₀ 0 2 T) x]
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdSymmSCovGrad3_unitModel_smul (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (c : ℝ) (x : M) (v : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (symmSCovGrad3 (I := I) g₀ (c • T)) x v =
      c * unitModel (I := I) (M := M) g₀ 3 (symmSCovGrad3 (I := I) g₀ T) x v := by
  rw [symmSCovGrad3_def, symmSCovGrad3_def, symmS_smul (I := I) (M := M) g₀ c T]
  exact bdCovGrad_unitModel_smul (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ T) c x v

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdKoszulCc_unitModel_smul (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (c : ℝ) (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ (c • T)) x m =
      c * unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ T) x m := by
  rw [show m = ![m 0, m 1, m 2] from by
    funext k
    fin_cases k <;> rfl]
  rw [koszulCovecCc_unitModel (I := I) g₀ (c • T) x (m 1) (m 2) (m 0),
    koszulCovecCc_unitModel (I := I) g₀ T x (m 1) (m 2) (m 0)]
  rw [bdSymmSCovGrad3_unitModel_smul (I := I) (M := M) g₀ T c x,
    bdSymmSCovGrad3_unitModel_smul (I := I) (M := M) g₀ T c x,
    bdSymmSCovGrad3_unitModel_smul (I := I) (M := M) g₀ T c x]
  ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdKRaw_unitModel_smul (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (c : ℝ) (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (koszulCovGradRaw (I := I) (M := M) g₀ (c • T)) x m =
      c * unitModel (I := I) (M := M) g₀ 3 (koszulCovGradRaw (I := I) (M := M) g₀ T) x m := by
  rw [show m = ![m 0, m 1, m 2] from by
    funext k
    fin_cases k <;> rfl]
  rw [bdKRaw_unitModel (I := I) (M := M) g₀ (c • T) x (m 1) (m 2) (m 0),
    bdKRaw_unitModel (I := I) (M := M) g₀ T x (m 1) (m 2) (m 0)]
  rw [bdCovGrad_unitModel_smul (I := I) (M := M) g₀ T c x,
    bdCovGrad_unitModel_smul (I := I) (M := M) g₀ T c x,
    bdCovGrad_unitModel_smul (I := I) (M := M) g₀ T c x]
  ring

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [BoundarylessManifold I M] in
private lemma bdSGKMvWeight_smul (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 6)) (T : SmoothCcTensor g₀ 0 2) (c : ℝ) :
    sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ σ (c • T) (c • T) =
      (c * c) • sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ σ T T := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro t
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hdecomp := bdTensor0S_zero_rank_decomp (I := I) (M := M) x t
  rw [hdecomp, map_smul, map_smul]
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
  refine congrArg _ ?_
  change unitModel (I := I) (M := M) g₀ 4
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ σ (c • T) (c • T)) x m =
    unitModel (I := I) (M := M) g₀ 4
      ((c * c) • sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ σ T T) x m
  rw [bdUnitModel_smul (I := I) (M := M) g₀ 4 (c * c)
    (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ σ T T) x]
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [show sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ σ (c • T) (c • T) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3
              (koszulCovGradRaw (I := I) (M := M) g₀ (c • T)))
            (koszulCovecCc (I := I) g₀ (c • T)))) from rfl]
  rw [show sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ σ T T =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
            (koszulCovecCc (I := I) g₀ T))) from rfl]
  rw [bdSGKMvWeight_unitModel_gen (I := I) (M := M) g₀ g₁ σ (c • T) (c • T) x m,
    bdSGKMvWeight_unitModel_gen (I := I) (M := M) g₀ g₁ σ T T x m]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [bdKoszulCc_unitModel_smul (I := I) (M := M) g₀ T c x,
    bdKRaw_unitModel_smul (I := I) (M := M) g₀ T c x]
  ring

omit [BoundarylessManifold I M] in
private lemma bdSGKWeights_pair_smul (g₀ g₁ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (c : ℝ) :
    (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 (c • T) (c • T) +
        sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 (c • T) (c • T)) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 (c • T) (c • T) +
        sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 (c • T) (c • T)) =
      (c * c) •
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T +
            sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T +
            sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T)) := by
  rw [bdSGKMvWeight_smul (I := I) (M := M) g₀ g₁ bdSGKTau1 T c,
    bdSGKMvWeight_smul (I := I) (M := M) g₀ g₁ bdSGKTau2 T c,
    bdSGKMvWeight_smul (I := I) (M := M) g₀ g₁ bdSGKTau3 T c,
    bdSGKMvWeight_smul (I := I) (M := M) g₀ g₁ bdSGKTau4 T c]
  rw [← smul_add, ← smul_add, ← smul_sub]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma bdXiChain_toModel (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (x : M) (D : Tensor0SSpace 2 I x) (w : Fin 6 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D) w =
      Tensor0SSpace.toModel D
          ![(fun i => w (armPairTraceSlotPerm6 i)) 0, (fun i => w (armPairTraceSlotPerm6 i)) 1] *
        unitModel (I := I) (M := M) g₀ 4 X x
          (fun k : Fin 4 => (fun i => w (armPairTraceSlotPerm6 i)) (Fin.natAdd 2 k)) := by
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D) =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        tensorRS_domDomCongr armPairTraceSlotPerm6
          ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x)) D) from by
    rw [rsDomDomCongrSection_toSection]]
  rw [toModel_rsDomDomCongr_apply (I := I) (M := M) armPairTraceSlotPerm6
    ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  exact bdSlotExtendIter_two_toModel (I := I) (M := M) g₀ X x D
    (fun i => w (armPairTraceSlotPerm6 i))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [BoundarylessManifold I M] in
lemma bdSGKXi_smul (g₀ g₁ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (c : ℝ) :
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 (c • T) (c • T) +
            sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 (c • T) (c • T)) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 (c • T) (c • T) +
            sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 (c • T) (c • T)))) =
    (c * c) • rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T +
            sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
          (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T +
            sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T))) := by
  classical
  rw [bdSGKWeights_pair_smul (I := I) (M := M) g₀ g₁ T c]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (((c * c) • rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T +
              sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
            (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T +
              sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T)))).toSection x)) D) =
      (c * c) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T +
                sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
              (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T +
                sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T)))).toSection x) D) from by
    rw [show ((((c * c) • rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T +
              sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
            (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T +
              sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T)))).toSection x)) =
        (c * c) • ((rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T +
                sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
              (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T +
                sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T)))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl]
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [bdXiChain_toModel (I := I) (M := M) g₀ ((c * c) •
      ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
        (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T))) x D w,
    bdXiChain_toModel (I := I) (M := M) g₀
      ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
        (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T +
          sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T)) x D w]
  rw [bdUnitModel_smul (I := I) (M := M) g₀ 4 (c * c)
    ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau1 T T +
        sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau3 T T +
        sharpGradKoszulWeightedTerm (I := I) (M := M) g₀ g₁ bdSGKTau4 T T)) x]
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma bdTensorProd_toModel (x : M) (D : Tensor0SSpace 2 I x)
    (W : Tensor0SSpace 4 I x) (u : Fin 6 → E) :
    Tensor0SSpace.toModel (tensorProdWithCLM (I := I) 2 4 x D W) u =
      Tensor0SSpace.toModel D ![u 0, u 1] *
        Tensor0SSpace.toModel W ![u 2, u 3, u 4, u 5] := by
  rw [tensorProdWithCLM_apply (I := I) 2 4 x D W, Tensor0SSpace.toModel_ofModel]
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine congrArg _ ?_
    funext k
    fin_cases k <;> rfl
  · refine congrArg _ ?_
    funext k
    fin_cases k <;> rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma bdSGKProd_toSection (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D =
      Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr armPairTraceSlotPerm6
          (Tensor0SSpace.toModel (tensorProdWithCLM (I := I) 2 4 x D
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x)
              (unitTensor (I := I) (M := M) x))))) := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  beta_reduce
  rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [bdTensorProd_toModel (I := I) (M := M) x D]
  rw [bdXiChain_toModel (I := I) (M := M) g₀ X x D w]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine congrArg _ ?_
    funext k
    fin_cases k <;> rfl
  · rw [show unitModel (I := I) (M := M) g₀ 4 X x
        (fun k : Fin 4 => (fun i => w (armPairTraceSlotPerm6 i)) (Fin.natAdd 2 k)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x)
            (unitTensor (I := I) (M := M) x))
          (fun k : Fin 4 => (fun i => w (armPairTraceSlotPerm6 i)) (Fin.natAdd 2 k)) from rfl]
    refine congrArg _ ?_
    funext k
    fin_cases k <;> rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem bdJointTotalSpace0S_add_local {d : ℕ} {S : Set ℝ}
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
private theorem bdJointTotalSpace0S_sub_local {d : ℕ} {S : Set ℝ}
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
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p - B p))
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
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem bdTensorProdField_jointContMDiffOn (m k : ℕ) {S : Set ℝ}
    (P : ∀ p : M × ℝ, Tensor0SSpace m I p.1)
    (Q : ∀ p : M × ℝ, Tensor0SSpace k I p.1)
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel m ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel m ℝ E)
        (E := fun z : M => Tensor0SSpace m I z) p.1 (P p))
      ((Set.univ : Set M) ×ˢ S))
    (hQ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel k ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel k ℝ E)
        (E := fun z : M => Tensor0SSpace k I z) p.1 (Q p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel (m + k) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel (m + k) ℝ E)
        (E := fun z : M => Tensor0SSpace (m + k) I z) p.1
        (tensorProdWithCLM (I := I) m k p.1 (P p) (Q p)))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) m
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) k
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (m + k)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hP' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SModel m ℝ E)
    (E := fun z : M => Tensor0SSpace m I z)).mp (hP p₀ hp₀)
  have hQ' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SModel k ℝ E)
    (E := fun z : M => Tensor0SSpace k I z)).mp (hQ p₀ hp₀)
  have h_combine : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SModel (m + k) ℝ E) ∞
      (fun p : M × ℝ => Bundle.continuousMultilinearMap.modelProductL (𝕜 := ℝ) (F := E) m k
        ((trivializationAt (Tensor0SModel m ℝ E)
          (fun z : M => Tensor0SSpace m I z) x₀ ⟨p.1, P p⟩).2)
        ((trivializationAt (Tensor0SModel k ℝ E)
          (fun z : M => Tensor0SSpace k I z) x₀ ⟨p.1, Q p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    ((contMDiffWithinAt_const (c := Bundle.continuousMultilinearMap.modelProductL
        (𝕜 := ℝ) (F := E) m k)).clm_apply hP'.2).clm_apply hQ'.2
  have hpointwise : ∀ p : M × ℝ,
      p.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
      (trivializationAt (Tensor0SModel (m + k) ℝ E)
        (fun z : M => Tensor0SSpace (m + k) I z) x₀
        ⟨p.1, tensorProdWithCLM (I := I) m k p.1 (P p) (Q p)⟩).2 =
      Bundle.continuousMultilinearMap.modelProductL (𝕜 := ℝ) (F := E) m k
        ((trivializationAt (Tensor0SModel m ℝ E)
          (fun z : M => Tensor0SSpace m I z) x₀ ⟨p.1, P p⟩).2)
        ((trivializationAt (Tensor0SModel k ℝ E)
          (fun z : M => Tensor0SSpace k I z) x₀ ⟨p.1, Q p⟩).2) := by
    intro p hx
    apply ContinuousMultilinearMap.ext
    intro v
    rw [Bundle.continuousMultilinearMap.modelProductL_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    set symmL := (trivializationAt E (TangentSpace I) x₀).symmL ℝ p.1 with hsymmL
    change (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
        (Tensor0SSpace.toModel (P p))
        (Tensor0SSpace.toModel (Q p)))
        (fun i => symmL (v i)) = _
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rfl
  refine h_combine.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact hpointwise p hx
  · exact hpointwise p₀ (by rw [← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)


theorem ricciArmSharpGradKoszulResidualField_realizedFam_threeArmHjoint
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)) (δ := δ) (δ' := δ) := by
  classical
  have hperY : ∀ (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) p.1
          (sharpGradKoszulBiContrFib (I := I) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) (p.2 • T) p.1 (Y p.1)))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    intro Y
    have hZjoint : ∀ (τ : Equiv.Perm (Fin 6)),
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
          (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
            (E := fun z : M => Tensor0SSpace 6 I z) q.1
            (unitEvalSection (I := I) (M := M) g₀ 6
              (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 τ
                (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                  (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                    (koszulCovGradRaw (I := I) (M := M) g₀ T))
                  (koszulCovecCc (I := I) g₀ T))) q.1))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := fun τ =>
      ((contMDiff_unitEvalSection (I := I) (M := M) g₀ 6
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 τ
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3
              (koszulCovGradRaw (I := I) (M := M) g₀ T))
            (koszulCovecCc (I := I) g₀ T)))).comp_contMDiffOn
        contMDiffOn_fst).mono (Set.subset_univ _)
    have hV1 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
      g₀ T 0 hδ hδZ
      (fun q : M × ℝ => unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau1
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1)
      (hZjoint bdSGKTau1)
    have hV2 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
      g₀ T 0 hδ hδZ
      (fun q : M × ℝ => unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau2
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1)
      (hZjoint bdSGKTau2)
    have hV3 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
      g₀ T 0 hδ hδZ
      (fun q : M × ℝ => unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau3
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1)
      (hZjoint bdSGKTau3)
    have hV4 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
      g₀ T 0 hδ hδZ
      (fun q : M × ℝ => unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau4
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1)
      (hZjoint bdSGKTau4)
    have hX12 := bdJointTotalSpace0S_add_local (I := I) (M := M) (d := 4)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hV1 hV2
    have hX34 := bdJointTotalSpace0S_add_local (I := I) (M := M) (d := 4)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hV3 hV4
    have hX := bdJointTotalSpace0S_sub_local (I := I) (M := M) (d := 4)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hX12 hX34
    have hYj : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) q.1 (Y q.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
      (Y.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
    have hTP := bdTensorProdField_jointContMDiffOn (I := I) (M := M) 2 4
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (fun q : M × ℝ => Y q.1)
      (fun q : M × ℝ => ((cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau1
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1) +
        cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau2
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1)) -
        (cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau3
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1) +
        cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau4
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1))))
      hYj hX
    have hRX := domDomCongrField_jointContMDiffOn (I := I) (M := M) (d := 6) armPairTraceSlotPerm6
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (fun q : M × ℝ => tensorProdWithCLM (I := I) 2 4 q.1 (Y q.1)
        ((cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau1
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1) +
        cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau2
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1)) -
        (cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau3
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1) +
        cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau4
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1))))
      hTP
    have hDT4 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
      g₀ T 0 hδ hδZ
      (fun q : M × ℝ => Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := q.1)
          (ContinuousMultilinearMap.domDomCongr armPairTraceSlotPerm6
            (Tensor0SSpace.toModel (tensorProdWithCLM (I := I) 2 4 q.1 (Y q.1)
              ((cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau1
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1) +
        cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau2
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1)) -
        (cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau3
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1) +
        cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau4
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1)))))))
      hRX
    have hDT2 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2)
      g₀ T 0 hδ hδZ
      (fun q : M × ℝ => cometricDoubleTraceFib (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
        (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := q.1)
          (ContinuousMultilinearMap.domDomCongr armPairTraceSlotPerm6
            (Tensor0SSpace.toModel (tensorProdWithCLM (I := I) 2 4 q.1 (Y q.1)
              ((cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau1
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1) +
        cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau2
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1)) -
        (cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau3
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1) +
        cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau4
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1))))))))
      hDT4
    have hsmul := bdJointTotalSpace0S_smulFun_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (f := fun s : ℝ => (2 : ℝ) * (s * s))
      ((contDiff_const.mul (contDiff_id.mul contDiff_id) :
        ContDiff ℝ ∞ (fun s : ℝ => (2 : ℝ) * (s * s))))
      (fun q : M × ℝ => cometricDoubleTraceFib (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 2 q.1
        (cometricDoubleTraceFib (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
        (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := q.1)
          (ContinuousMultilinearMap.domDomCongr armPairTraceSlotPerm6
            (Tensor0SSpace.toModel (tensorProdWithCLM (I := I) 2 4 q.1 (Y q.1)
              ((cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau1
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1) +
        cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau2
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1)) -
        (cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau3
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1) +
        cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau4
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1)))))))))
      hDT2
    refine hsmul.congr (fun q hq => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SSpace 2 I z) q.1 t) ?_
    have hs : q.2 ∈ realizedSmallSet (δ := δ) (δ' := δ) := hq.2
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T 0 hδ hδZ q.2).inner y v w =
          g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ (q.2 • T) y v w := by
      intro y v w
      have h0 := realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs y v w
      rwa [show convexPerturbation (I := I) g₀ T 0 q.2 = q.2 • T from by
        rw [convexPerturbation, smul_zero, zero_add]] at h0
    have h1 : sharpGradKoszulBiContrFib (I := I) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) (q.2 • T) q.1 (Y q.1) =
        (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
          (((2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau1 (q.2 • T) (q.2 • T) +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau2 (q.2 • T) (q.2 • T)) -
                (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau3 (q.2 • T) (q.2 • T) +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau4 (q.2 • T) (q.2 • T)))))).toSection q.1)) (Y q.1) := by
      rw [← bdSGK_eq_refold (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2)
        (q.2 • T) (q.2 • T) htie]
      rfl
    rw [h1]
    rw [bdSGKXi_smul (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) T q.2]
    rw [appCcRS_smul_right (I := I) (M := M) g₀ 2 6 2 (q.2 * q.2)
      (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau1 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau2 T T) -
                (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau3 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau4 T T))))]
    rw [show ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
        (((2 : ℝ) • (q.2 * q.2) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau1 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau2 T T) -
                (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau3 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau4 T T))))).toSection q.1)) (Y q.1)) =
        ((2 : ℝ) * (q.2 * q.2)) •
          ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
            ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau1 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau2 T T) -
                (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau3 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau4 T T))))).toSection q.1)) (Y q.1)) from by
      rw [show ((((2 : ℝ) • (q.2 * q.2) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau1 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau2 T T) -
                (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau3 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau4 T T))))).toSection q.1)) =
          (2 : ℝ) • (q.2 * q.2) • ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau1 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau2 T T) -
                (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau3 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau4 T T))))).toSection q.1) from by
        rw [SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_smul]; rfl]
      rw [show (((2 : ℝ) • (q.2 * q.2) • ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau1 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau2 T T) -
                (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau3 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau4 T T))))).toSection q.1)) : _) =
          ((2 : ℝ) * (q.2 * q.2)) • ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau1 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau2 T T) -
                (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau3 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau4 T T))))).toSection q.1) from by
        rw [smul_smul]]
      rfl]
    refine congrArg (fun t => ((2 : ℝ) * (q.2 * q.2)) • t) ?_
    rw [show ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau1 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau2 T T) -
                (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau3 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau4 T T))))).toSection q.1)) (Y q.1)) =
        cometricDoubleTraceFib (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 2 q.1
          (cometricDoubleTraceFib (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
            ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau1 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau2 T T) -
                (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau3 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau4 T T)))).toSection q.1) (Y q.1))) from by
      rw [appCcRS_toSection]
      rfl]
    rw [bdSGKProd_toSection (I := I) (M := M) g₀
      ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau1 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau2 T T) -
                (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau3 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau4 T T)) q.1 (Y q.1)]
    refine congrArg (fun t => cometricDoubleTraceFib (I := I)
      (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 2 q.1
      (cometricDoubleTraceFib (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1 t)) ?_
    refine congrArg (fun t => Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := q.1)
      (ContinuousMultilinearMap.domDomCongr armPairTraceSlotPerm6
        (Tensor0SSpace.toModel (tensorProdWithCLM (I := I) 2 4 q.1 (Y q.1) t)))) ?_
    rw [show ((show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
        (((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau1 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau2 T T) -
                (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau3 T T +
                  sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau4 T T))).toSection q.1))
        (unitTensor (I := I) (M := M) q.1) =
        (((show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
            (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau1 T T).toSection q.1)
          (unitTensor (I := I) (M := M) q.1) +
          (show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
            (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau2 T T).toSection q.1)
          (unitTensor (I := I) (M := M) q.1)) -
          ((show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
            (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau3 T T).toSection q.1)
          (unitTensor (I := I) (M := M) q.1) +
          (show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
            (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau4 T T).toSection q.1)
          (unitTensor (I := I) (M := M) q.1))) from by
      rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add,
        SmoothCcTensor.toSection_add]
      rfl]
    rw [show (show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
        (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau1 T T).toSection q.1)
        (unitTensor (I := I) (M := M) q.1) =
        cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau1
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1) from by
      rw [show sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau1 T T =
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4
            (cometricDoubleTraceCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau1
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) from rfl]
      rw [appCcRS_toSection]
      rfl]
    rw [show (show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
        (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau2 T T).toSection q.1)
        (unitTensor (I := I) (M := M) q.1) =
        cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau2
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1) from by
      rw [show sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau2 T T =
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4
            (cometricDoubleTraceCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau2
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) from rfl]
      rw [appCcRS_toSection]
      rfl]
    rw [show (show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
        (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau3 T T).toSection q.1)
        (unitTensor (I := I) (M := M) q.1) =
        cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau3
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1) from by
      rw [show sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau3 T T =
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4
            (cometricDoubleTraceCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau3
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) from rfl]
      rw [appCcRS_toSection]
      rfl]
    rw [show (show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
        (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau4 T T).toSection q.1)
        (unitTensor (I := I) (M := M) q.1) =
        cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          (unitEvalSection (I := I) (M := M) g₀ 6
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau4
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) q.1) from by
      rw [show sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) bdSGKTau4 T T =
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4
            (cometricDoubleTraceCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau4
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovGradRaw (I := I) (M := M) g₀ T))
                (koszulCovecCc (I := I) g₀ T))) from rfl]
      rw [appCcRS_toSection]
      rfl]
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => sharpGradKoszulBiContrFib (I := I) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) (p.2 • T) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ)) hperY
  refine hCLM.congr (fun p _ => ?_)
  rfl


theorem ricciArmRicciFoldRemainderField_realizedFam_threeArmHjoint
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)) (δ := δ) (δ' := δ) := by
  classical
  have hperY : ∀ (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) p.1
          (ricciFoldBiContrFib (I := I) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ p.2)
            (p.2 • T) p.1 (Y p.1)))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    intro Y
    have hXiApp : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
          (E := fun z : M => Tensor0SSpace 6 I z) x
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                  palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection x) (Y x))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
              palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection.contMDiff Y.contMDiff
    have hXiJoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
        (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
          (E := fun z : M => Tensor0SSpace 6 I z) q.1
          ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                  palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection q.1) (Y q.1)))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
      (hXiApp.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
    have hcdtf4 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
      g₀ T 0 hδ hδZ
      (fun q : M × ℝ => (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
              palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection q.1) (Y q.1)) hXiJoint
    have hcdtf2 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2)
      g₀ T 0 hδ hδZ
      (fun q : M × ℝ => cometricDoubleTraceFib (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
        ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection q.1) (Y q.1))) hcdtf4
    have hsmul := bdJointTotalSpace0S_smulFun_local (I := I) (M := M) (d := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ))
      (f := fun s : ℝ => (-(1 / 2) : ℝ) * s)
      ((contDiff_const.mul contDiff_id :
        ContDiff ℝ ∞ (fun s : ℝ => (-(1 / 2) : ℝ) * s)))
      (fun q : M × ℝ => cometricDoubleTraceFib (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 2 q.1
        (cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
          ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                  palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection q.1) (Y q.1))))
      hcdtf2
    refine hsmul.congr (fun q _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SSpace 2 I z) q.1 t) ?_
    have h1 : ricciFoldBiContrFib (I := I) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2)
        (q.2 • T) q.1 (Y q.1) =
        (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
          (((-(1 / 2) : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (palatiniRicciFoldWeightA (I := I) (M := M) g₀ (q.2 • T) +
                  palatiniRicciFoldWeightB (I := I) (M := M) g₀ (q.2 • T))))).toSection q.1))
          (Y q.1) := by
      rw [← bdRicciFold_eq_refold (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) (q.2 • T)]
      rfl
    rw [h1]
    rw [bdRicciFoldXi_smul (I := I) (M := M) g₀ T q.2]
    rw [appCcRS_smul_right (I := I) (M := M) g₀ 2 6 2 q.2
      (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
            palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))]
    rw [show ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
        (((-(1 / 2) : ℝ) • q.2 • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection q.1)) (Y q.1)) =
        ((-(1 / 2) : ℝ) * q.2) • ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                  palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection q.1)) (Y q.1)) from by
      rw [show ((((-(1 / 2) : ℝ) • q.2 • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection q.1)) =
          (-(1 / 2) : ℝ) • q.2 • ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                  palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection q.1) from by
        rw [SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_smul]; rfl]
      rw [show (((-(1 / 2) : ℝ) • q.2 • ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection q.1)) : _) =
          ((-(1 / 2) : ℝ) * q.2) • ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                  palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection q.1) from by
        rw [smul_smul]]
      rfl]
    refine congrArg (fun t => ((-(1 / 2) : ℝ) * q.2) • t) ?_
    rw [show ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection q.1)) (Y q.1)) =
        cometricDoubleTraceFib (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 2 q.1
          (cometricDoubleTraceFib (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 4 q.1
            ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                    palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection q.1) (Y q.1))) from by
      rw [appCcRS_toSection]
      rfl]
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => ricciFoldBiContrFib (I := I) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) (p.2 • T) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ)) hperY
  refine hCLM.congr (fun p _ => ?_)
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
