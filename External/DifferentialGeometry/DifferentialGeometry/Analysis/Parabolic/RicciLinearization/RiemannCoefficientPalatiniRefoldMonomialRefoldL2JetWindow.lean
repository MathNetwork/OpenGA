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

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma riemannianFiberNormSq_add3_le (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (x : M) (u v w : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (u + v + w) ≤
      3 * (riemannianFiberNormSq (I := I) (M := M) g r s x u +
        (riemannianFiberNormSq (I := I) (M := M) g r s x v +
          riemannianFiberNormSq (I := I) (M := M) g r s x w)) := by
  classical
  have h := riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g r s x
    Finset.univ (![u, v, w])
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at h
  rw [show (![u, v, w] : Fin 3 → TensorRSSpace r s I x) 0 = u from rfl,
    show (![u, v, w] : Fin 3 → TensorRSSpace r s I x) 1 = v from rfl] at h
  rw [Finset.card_univ, Fintype.card_fin] at h
  refine le_trans h ?_
  rw [show ((3 : ℕ) : ℝ) = (3 : ℝ) from by norm_num]
  rw [show (![u, v, w] : Fin 3 → TensorRSSpace r s I x) 2 = w from rfl]
  nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x u,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x v,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x w]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_unitValue_symmS_abs_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (y : M) (v w : TangentSpace I y) :
    |Tensor0SSpace.toModel (𝕜 := ℝ)
        (ccTensorUnitValueSection (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T) y) ![(v : E), (w : E)]| ≤
      δ * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) := by
  have hval : Tensor0SSpace.toModel (𝕜 := ℝ)
      (ccTensorUnitValueSection (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T) y) ![(v : E), (w : E)] =
      ccTensorBilinSymm (I := I) g₀ T y v w := by
    have h1 : ccTensorUnitValueSection (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T) y =
        (1 / 2 : ℝ) • (ccTensorUnitValueSection (I := I) (M := M) g₀ T y +
          ccTensorUnitValueSection (I := I) (M := M) g₀
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) y) := by
      rw [show ccTensor02Symm (I := I) (M := M) g₀ T = (1 / 2 : ℝ) •
          (T + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) from rfl]
      rw [ccTensorUnitValueSection_smul, ccTensorUnitValueSection_add]
    rw [h1, Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_add,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.add_apply,
      smul_eq_mul,
      toModel_ccTensorUnitValueSection_domDomCongrSection_swap (I := I) (M := M) g₀ T y v w]
    have h2 : ∀ (p q' : TangentSpace I y),
        Tensor0SSpace.toModel (𝕜 := ℝ)
          (ccTensorUnitValueSection (I := I) (M := M) g₀ T y) ![(p : E), (q' : E)] =
        smoothCcTensorBilinForm (I := I) g₀ T y p q' := by
      intro p q'
      have hb : Tensor0SSpace.toModel (𝕜 := ℝ)
          (ccTensorUnitValueSection (I := I) (M := M) g₀ T y) =
          unitModel (I := I) (M := M) g₀ 2 T y := rfl
      rw [hb]
      exact unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T y p q'
    rw [h2 v w, h2 w v, ccTensorBilinSymm_apply]
  rw [hval]
  exact hδ y v w

private def curvatureRefoldSlotPerm (σ : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 6) :=
  ((finSumFinEquiv (m := 4) (n := 2)).permCongr
    (Equiv.sumCongr σ (Equiv.refl (Fin 2)))).trans armPairTraceSlotPerm6

private lemma curvatureRefoldSlotPerm_castAdd (σ : Equiv.Perm (Fin 4)) (j : Fin 4) :
    curvatureRefoldSlotPerm σ (Fin.castAdd 2 j) = (![1, 3, 4, 5] : Fin 4 → Fin 6) (σ j) := by
  have hpad : (finSumFinEquiv (m := 4) (n := 2)).permCongr
      (Equiv.sumCongr σ (Equiv.refl (Fin 2))) (Fin.castAdd 2 j) =
      Fin.castAdd 2 (σ j) := by
    rw [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd]
    rfl
  rw [curvatureRefoldSlotPerm, Equiv.trans_apply, hpad]
  exact (by decide : ∀ k : Fin 4,
    armPairTraceSlotPerm6 (Fin.castAdd 2 k) = (![1, 3, 4, 5] : Fin 4 → Fin 6) k) (σ j)

private lemma curvatureRefoldSlotPerm_natAdd (σ : Equiv.Perm (Fin 4)) (k : Fin 2) :
    curvatureRefoldSlotPerm σ (Fin.natAdd 4 k) = (![0, 2] : Fin 2 → Fin 6) k := by
  have hpad : (finSumFinEquiv (m := 4) (n := 2)).permCongr
      (Equiv.sumCongr σ (Equiv.refl (Fin 2))) (Fin.natAdd 4 k) =
      Fin.natAdd 4 k := by
    rw [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_natAdd]
    rfl
  rw [curvatureRefoldSlotPerm, Equiv.trans_apply, hpad]
  exact (by decide : ∀ k' : Fin 2,
    armPairTraceSlotPerm6 (Fin.natAdd 4 k') = (![0, 2] : Fin 2 → Fin 6) k') k

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotExtendIterFour_toModel (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (G : Tensor0SSpace 4 I x)
    (u : Fin 6 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 2 4 S).toSection x) G) u =
      Tensor0SSpace.toModel G ![u 0, u 1, u 2, u 3] *
        unitModel (I := I) (M := M) g₀ 2 S x (fun k : Fin 2 => u (Fin.natAdd 4 k)) := by
  rw [show ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 2 4 S).toSection x) G) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 5 x).symm
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 2 3 S).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G)) from rfl]
  have hkey1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 5)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 5 x).symm
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 2 3 S).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G)))
    (v0 := u 0) (vs := Matrix.vecTail u)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey1
  rw [show (Fin.cons (u 0) (Matrix.vecTail u) : Fin 6 → TangentSpace I x) = u from by
    funext k
    refine Fin.cases rfl (fun i => rfl) k] at hkey1
  rw [← hkey1]
  rw [show ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 2 3 S).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G) (u 0)) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 4 x).symm
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 2 2 S).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G (u 0)))) from rfl]
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
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 2 2 S).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G (u 0)))))
    (v0 := u 1) (vs := fun k : Fin 4 => u (Fin.natAdd 2 k))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey2
  rw [← hkey2]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 2 2 S).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G (u 0))) (u 1)) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 2 1 S).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
              (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G (u 0)) (u 1)))) from rfl]
  rw [show ((fun k : Fin 4 => u (Fin.natAdd 2 k)) : Fin 4 → TangentSpace I x) =
      Fin.cons (u 2) (fun k : Fin 3 => u (Fin.natAdd 3 k)) from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · rfl
    · change u (Fin.natAdd 2 (Fin.succ i)) = u (Fin.natAdd 3 i)
      congr 1
      exact Fin.ext (by simp [Fin.succ, Fin.natAdd]; omega)]
  have hkey3 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 3)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x).symm
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 2 1 S).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G (u 0)) (u 1)))))
    (v0 := u 2) (vs := fun k : Fin 3 => u (Fin.natAdd 3 k))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey3
  rw [← hkey3]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 2 1 S).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G (u 0)) (u 1))) (u 2)) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x).symm
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
              (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
                (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G (u 0)) (u 1)) (u 2)))) from rfl]
  rw [show ((fun k : Fin 3 => u (Fin.natAdd 3 k)) : Fin 3 → TangentSpace I x) =
      Fin.cons (u 3) (fun k : Fin 2 => u (Fin.natAdd 4 k)) from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · rfl
    · change u (Fin.natAdd 3 (Fin.succ i)) = u (Fin.natAdd 4 i)
      congr 1
      exact Fin.ext (by simp [Fin.succ, Fin.natAdd]; omega)]
  have hkey4 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x).symm
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
              (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G (u 0)) (u 1)) (u 2)))))
    (v0 := u 3) (vs := fun k : Fin 2 => u (Fin.natAdd 4 k))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey4
  rw [← hkey4]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G (u 0)) (u 1)) (u 2))) (u 3)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
              (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G (u 0)) (u 1)) (u 2)) (u 3)) from rfl]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G (u 0)) (u 1)) (u 2)) (u 3) with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel G ![u 0, u 1, u 2, u 3] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G (u 0)) (u 1)) (u 2))
      (v0 := u 3) (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G (u 0)) (u 1))
      (v0 := u 2) (vs := Fin.cons (u 3) (fun i : Fin 0 => i.elim0))
    rw [h2]
    have h3 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x G (u 0))
      (v0 := u 1) (vs := Fin.cons (u 2) (Fin.cons (u 3) (fun i : Fin 0 => i.elim0)))
    rw [h3]
    have h4 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 3)
      (T := G) (v0 := u 0)
      (vs := Fin.cons (u 1) (Fin.cons (u 2) (Fin.cons (u 3) (fun i : Fin 0 => i.elim0))))
    rw [h4]
    refine congrArg _ ?_
    funext k
    fin_cases k <;> rfl
  have hdecomp := bdTensor0S_zero_rank_decomp (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem curvatureRefoldMonomialCoeffField_eq_pairTrace (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (σ : Equiv.Perm (Fin 4)) :
    curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ S)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S) σ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 4 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 4 6 (curvatureRefoldSlotPerm σ)
          (slotExtendIter (I := I) (M := M) g₀ 0 2 4 S)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro G
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 4 6 (curvatureRefoldSlotPerm σ)
        (slotExtendIter (I := I) (M := M) g₀ 0 2 4 S)).toSection x) G with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel G
            (fun j : Fin 4 => w ((![1, 3, 4, 5] : Fin 4 → Fin 6) (σ j))) *
          unitModel (I := I) (M := M) g₀ 2 S x ![w 0, w 2] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 4 6 (curvatureRefoldSlotPerm σ)
          (slotExtendIter (I := I) (M := M) g₀ 0 2 4 S)).toSection x) G) =
        ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 6 I x from
          tensorRS_domDomCongr (curvatureRefoldSlotPerm σ)
            ((slotExtendIter (I := I) (M := M) g₀ 0 2 4 S).toSection x)) G) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (curvatureRefoldSlotPerm σ)
      ((slotExtendIter (I := I) (M := M) g₀ 0 2 4 S).toSection x) G]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [slotExtendIterFour_toModel (I := I) (M := M) g₀ S x G
      (fun i => w (curvatureRefoldSlotPerm σ i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext j
      fin_cases j
      · exact congrArg w (curvatureRefoldSlotPerm_castAdd σ 0)
      · exact congrArg w (curvatureRefoldSlotPerm_castAdd σ 1)
      · exact congrArg w (curvatureRefoldSlotPerm_castAdd σ 2)
      · exact congrArg w (curvatureRefoldSlotPerm_castAdd σ 3)
    · refine congrArg _ ?_
      funext k
      fin_cases k
      · exact congrArg w (curvatureRefoldSlotPerm_natAdd σ 0)
      · exact congrArg w (curvatureRefoldSlotPerm_natAdd σ 1)
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S) σ).toSection x) G) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel (𝕜 := ℝ) (ccTensorUnitValueSection (I := I) (M := M) g₀ S x)
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          Tensor0SSpace.toModel (𝕜 := ℝ) G
            (fun i => (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : E))
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : E)) v) : Fin 4 → E)
              (σ i)) := by
    rw [show ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S) σ).toSection x) G) =
        curvatureActionMonomialFrameTrace (I := I) (M := M)
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ
          (smoothOrthoFrame (I := I) g₁ x) x G from rfl]
    exact curvatureRefoldMonomialFibFixedFrame_toModel (I := I) (M := M)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ
      (smoothOrthoFrame (I := I) g₁ x) x G v
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 4 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 4 6 (curvatureRefoldSlotPerm σ)
            (slotExtendIter (I := I) (M := M) g₀ 0 2 4 S))).toSection x) G) v =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Y
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
                  (fun j => (v j : E)))))) := by
    rw [show ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 4 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 4 6 (curvatureRefoldSlotPerm σ)
            (slotExtendIter (I := I) (M := M) g₀ 0 2 4 S))).toSection x) G) =
        cometricDoubleTraceFib (I := I) g₁ 2 x
          (cometricDoubleTraceFib (I := I) g₁ 4 x Y) from by
      rw [hY_def]
      rw [appCcRS_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ 2 x]
    rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₁ 4 x Y))
      (fun j => (v j : E))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ 4 x Y]
    rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel Y)
      (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
          (fun j => (v j : E))))]
  rw [hLHS, hRHS]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hYval, mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine congrArg _ ?_
    funext i
    have htuple : ∀ k : Fin 4,
        (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : E))
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : E)) v) : Fin 4 → E) k =
        ((Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
                (fun j => (v j : E)))))) : Fin 6 → E)
          ((![1, 3, 4, 5] : Fin 4 → Fin 6) k) := by
      intro k
      fin_cases k <;> rfl
    exact htuple (σ i)
  · have hWm : Tensor0SSpace.toModel
        (ccTensorUnitValueSection (I := I) (M := M) g₀ S x) =
        unitModel (I := I) (M := M) g₀ 2 S x := rfl
    rw [hWm]
    refine congrArg _ ?_
    funext j
    fin_cases j <;> rfl

lemma bdGridWindow_mono_of_le (b b' : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (hbb : ∀ j, b j ≤ b' j) (w : ℕ) :
    Combinatorics.antidiagonalTupleGridWindow b w ≤
      Combinatorics.antidiagonalTupleGridWindow b' w := by
  rw [Combinatorics.antidiagonalTupleGridWindow, Combinatorics.antidiagonalTupleGridWindow]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Combinatorics.antidiagonalTupleGrid, Combinatorics.antidiagonalTupleGrid]
  refine Finset.sum_le_sum fun n _ => ?_
  refine Finset.sum_le_sum fun e _ => ?_
  exact Finset.prod_le_prod (fun m _ => hb (e m)) (fun m _ => hbb (e m))

lemma bdSingle_b_le_grid (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (q : ℕ) (hq : 1 ≤ q) :
    b q ≤ Combinatorics.antidiagonalTupleGrid b q := by
  have h := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb 0 q hq
  rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
  rwa [zero_add] at h

private theorem curvatureRefoldMonomialCoeffField_pointwise_gridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (σ : Equiv.Perm (Fin 4)) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P S : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hboundP : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hboundS : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ S) δ)
        (_hPS : ∀ (l : ℕ) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) ≤
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l S).toSection x))
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 4 2 i
              (curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
                (ccTensorUnitValueSection (I := I) (M := M) g₀
                  (ccTensor02Symm (I := I) (M := M) g₀ S))
                (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
                  (ccTensor02Symm (I := I) (M := M) g₀ S)) σ)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' S).toSection x)) (i + 2) := by
  classical
  obtain ⟨CP, hCP_nn, hCP⟩ := bdPairTraceOp_tgrid (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set CS : ℕ → ℝ := fun l => if l = 0 then fr ^ 2 * δ₀ ^ 2 else 1 with hCS_def
  have hCS_nn : ∀ l, 0 ≤ CS l := by
    intro l
    rw [hCS_def]
    dsimp only
    split_ifs
    · positivity
    · norm_num
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i * ∑ i' ∈ Finset.range (i + 1),
      CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * (fr * (fr * CS l)))) *
          Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1),
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hCP_nn i')
        (Finset.sum_nonneg fun l _ => mul_nonneg
          (mul_nonneg hfr_nn (mul_nonneg hfr_nn (mul_nonneg hfr_nn
            (mul_nonneg hfr_nn (hCS_nn l)))))
          (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _))), ?_⟩
  intro g₁ P S htie δ hδ_le hδ0 hboundP hboundS hPS i x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' S).toSection x) with hb_def
  set bP : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hbP_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  have hbP : ∀ l', 0 ≤ bP l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  have hbPb : ∀ l', bP l' ≤ b l' := fun l' => hPS l' x
  set W : ℝ := Combinatorics.antidiagonalTupleGridWindow b (i + 2) with hW_def
  have hW_nn : (0 : ℝ) ≤ W := Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i + 2)
  have hWtower : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 4 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 4 6 (curvatureRefoldSlotPerm σ)
            (slotExtendIter (I := I) (M := M) g₀ 0 2 4
              (ccTensor02Symm (I := I) (M := M) g₀ S)))).toSection x) ≤
      (fr * (fr * (fr * (fr * CS l)))) *
        Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by
    intro l
    have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 4 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 4 6 (curvatureRefoldSlotPerm σ)
            (slotExtendIter (I := I) (M := M) g₀ 0 2 4
              (ccTensor02Symm (I := I) (M := M) g₀ S)))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 4 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 2 4
              (ccTensor02Symm (I := I) (M := M) g₀ S))).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 4 6
        (curvatureRefoldSlotPerm σ)
        (slotExtendIter (I := I) (M := M) g₀ 0 2 4 (ccTensor02Symm (I := I) (M := M) g₀ S))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 4 6 (curvatureRefoldSlotPerm σ)
          (slotExtendIter (I := I) (M := M) g₀ 0 2 4 (ccTensor02Symm (I := I) (M := M) g₀ S)))
        (fun y d => by
          rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) l x
    rw [hperm]
    have h4 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 4 6 l
          (slotExtendIter (I := I) (M := M) g₀ 0 2 4
            (ccTensor02Symm (I := I) (M := M) g₀ S))).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (5 + l) x
          ((iteratedCovGrad (I := I) g₀ 3 5 l
            (slotExtendIter (I := I) (M := M) g₀ 0 2 3
              (ccTensor02Symm (I := I) (M := M) g₀ S))).toSection x) :=
      rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 3 5
        (slotExtendIter (I := I) (M := M) g₀ 0 2 3 (ccTensor02Symm (I := I) (M := M) g₀ S)) l x
    have h3 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (5 + l) x
        ((iteratedCovGrad (I := I) g₀ 3 5 l
          (slotExtendIter (I := I) (M := M) g₀ 0 2 3
            (ccTensor02Symm (I := I) (M := M) g₀ S))).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 4 l
            (slotExtendIter (I := I) (M := M) g₀ 0 2 2
              (ccTensor02Symm (I := I) (M := M) g₀ S))).toSection x) :=
      rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 4
        (slotExtendIter (I := I) (M := M) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ S)) l x
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 4 l
          (slotExtendIter (I := I) (M := M) g₀ 0 2 2
            (ccTensor02Symm (I := I) (M := M) g₀ S))).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 3 l
            (slotExtendIter (I := I) (M := M) g₀ 0 2 1
              (ccTensor02Symm (I := I) (M := M) g₀ S))).toSection x) :=
      rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 3
        (slotExtendIter (I := I) (M := M) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ S)) l x
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 3 l
          (slotExtendIter (I := I) (M := M) g₀ 0 2 1
            (ccTensor02Symm (I := I) (M := M) g₀ S))).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l
            (ccTensor02Symm (I := I) (M := M) g₀ S)).toSection x) :=
      rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 2
        (ccTensor02Symm (I := I) (M := M) g₀ S) l x
    have hbase : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l
          (ccTensor02Symm (I := I) (M := M) g₀ S)).toSection x) ≤
        CS l * Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by
      rcases Nat.eq_zero_or_pos l with hl0 | hl1
      · subst hl0
        have hzero := riemannianFiberNormSq_symmS_le_of_gFibreOpBound (I := I) (M := M) g₀ S hδ0 hboundS x
        have hδsq : δ ^ 2 ≤ δ₀ ^ 2 := by nlinarith
        have hone : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (0 + 2) :=
          Combinatorics.one_le_antidiagonalTupleGridWindow b hb (by norm_num)
        have hCS0 : CS 0 = fr ^ 2 * δ₀ ^ 2 := by simp [hCS_def]
        have hstep : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ S)).toSection x) ≤ fr ^ 2 * δ₀ ^ 2 := by
          rw [iteratedCovGrad_zero]
          refine le_trans hzero ?_
          rw [hfr_def]
          nlinarith [sq_nonneg (Module.finrank ℝ E : ℝ)]
        rw [hCS0]
        refine le_trans hstep ?_
        have hcs_nn : (0 : ℝ) ≤ fr ^ 2 * δ₀ ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hone hcs_nn]
      · have hsymm := bdRfns_iCG_symmS_le (I := I) (M := M) g₀ S l x
        have hsingle : b l ≤ Combinatorics.antidiagonalTupleGrid b l :=
          bdSingle_b_le_grid b hb l hl1
        have hgw : Combinatorics.antidiagonalTupleGrid b l ≤
            Combinatorics.antidiagonalTupleGridWindow b (l + 2) :=
          Combinatorics.antidiagonalTupleGrid_le_window b hb (by omega)
        have hCSl : CS l = 1 := by
          rw [hCS_def]
          dsimp only
          rw [if_neg (by omega)]
        rw [hCSl, one_mul]
        exact le_trans hsymm (le_trans hsingle hgw)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 4 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 2 4
              (ccTensor02Symm (I := I) (M := M) g₀ S))).toSection x)
        ≤ fr * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (5 + l) x
            ((iteratedCovGrad (I := I) g₀ 3 5 l
              (slotExtendIter (I := I) (M := M) g₀ 0 2 3
                (ccTensor02Symm (I := I) (M := M) g₀ S))).toSection x) := h4
      _ ≤ fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 4 l
              (slotExtendIter (I := I) (M := M) g₀ 0 2 2
                (ccTensor02Symm (I := I) (M := M) g₀ S))).toSection x)) :=
          mul_le_mul_of_nonneg_left h3 hfr_nn
      _ ≤ fr * (fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 3 l
              (slotExtendIter (I := I) (M := M) g₀ 0 2 1
                (ccTensor02Symm (I := I) (M := M) g₀ S))).toSection x))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hfr_nn) hfr_nn
      _ ≤ fr * (fr * (fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l
              (ccTensor02Symm (I := I) (M := M) g₀ S)).toSection x)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h1 hfr_nn) hfr_nn) hfr_nn
      _ ≤ fr * (fr * (fr * (fr * (CS l *
            Combinatorics.antidiagonalTupleGridWindow b (l + 2))))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbase hfr_nn)
              hfr_nn) hfr_nn) hfr_nn
      _ = (fr * (fr * (fr * (fr * CS l)))) *
            Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by ring
  have hlift : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 4 2 i
        (curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀
            (ccTensor02Symm (I := I) (M := M) g₀ S))
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
            (ccTensor02Symm (I := I) (M := M) g₀ S)) σ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 4 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 4 6 (curvatureRefoldSlotPerm σ)
              (slotExtendIter (I := I) (M := M) g₀ 0 2 4
                (ccTensor02Symm (I := I) (M := M) g₀ S))))).toSection x) := by
    rw [curvatureRefoldMonomialCoeffField_eq_pairTrace (I := I) (M := M) g₀ g₁
      (ccTensor02Symm (I := I) (M := M) g₀ S) σ]
  rw [hlift]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ i 4 6 2
    (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 4 6 (curvatureRefoldSlotPerm σ)
      (slotExtendIter (I := I) (M := M) g₀ 0 2 4
        (ccTensor02Symm (I := I) (M := M) g₀ S))) x) ?_
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 6 2 i'
            (armPairTraceOpCc (I := I) (M := M) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 4 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 4 6 (curvatureRefoldSlotPerm σ)
                (slotExtendIter (I := I) (M := M) g₀ 0 2 4
                  (ccTensor02Symm (I := I) (M := M) g₀ S)))).toSection x) ≤
      (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * (fr * (fr * CS l)))) *
          Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) * W := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 6 2 i'
          (armPairTraceOpCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CP i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 1) := by
      refine le_trans (hCP g₁ P htie hδ_le hδ0 hboundP i' x) ?_
      exact mul_le_mul_of_nonneg_left
        (bdGridWindow_mono_of_le bP b hbP hbPb (i' + 1)) (hCP_nn i')
    have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 4 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 4 6 (curvatureRefoldSlotPerm σ)
              (slotExtendIter (I := I) (M := M) g₀ 0 2 4
                (ccTensor02Symm (I := I) (M := M) g₀ S)))).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - i'),
          (fr * (fr * (fr * (fr * CS l)))) *
            Combinatorics.antidiagonalTupleGridWindow b (l + 2) :=
      Finset.sum_le_sum fun l _ => hWtower l
    have hsum_nn : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 4 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 4 6 (curvatureRefoldSlotPerm σ)
              (slotExtendIter (I := I) (M := M) g₀ 0 2 4
                (ccTensor02Symm (I := I) (M := M) g₀ S)))).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 (6 + l) x _
    have hA1_rhs_nn : (0 : ℝ) ≤ CP i' *
        Combinatorics.antidiagonalTupleGridWindow b (i' + 1) :=
      mul_nonneg (hCP_nn i')
        (Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i' + 1))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * (fr * (fr * CS l)))) *
          Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) * W =
        ∑ l ∈ Finset.range (i + 1 - i'),
          (CP i' * ((fr * (fr * (fr * (fr * CS l)))) *
            Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1))) * W from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have hpair : Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
        Combinatorics.antidiagonalTupleGridWindow b (l + 1 + 1) ≤
        Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) *
          Combinatorics.antidiagonalTupleGridWindow b (i' + (l + 1) + 1) :=
      Combinatorics.antidiagonalTupleGridWindow_mul_le b hb i' (l + 1)
    have hmono : Combinatorics.antidiagonalTupleGridWindow b (i' + (l + 1) + 1) ≤ W := by
      rw [hW_def]
      exact Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
    have hfr4CS_nn : (0 : ℝ) ≤ fr * (fr * (fr * (fr * CS l))) :=
      mul_nonneg hfr_nn (mul_nonneg hfr_nn (mul_nonneg hfr_nn
        (mul_nonneg hfr_nn (hCS_nn l))))
    calc CP i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
          ((fr * (fr * (fr * (fr * CS l)))) *
            Combinatorics.antidiagonalTupleGridWindow b (l + 2))
        = (CP i' * (fr * (fr * (fr * (fr * CS l))))) *
            (Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
              Combinatorics.antidiagonalTupleGridWindow b (l + 1 + 1)) := by
          rw [show l + 2 = l + 1 + 1 from rfl]
          ring
      _ ≤ (CP i' * (fr * (fr * (fr * (fr * CS l))))) *
            (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) *
              Combinatorics.antidiagonalTupleGridWindow b (i' + (l + 1) + 1)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (hCP_nn i') hfr4CS_nn
      _ ≤ (CP i' * (fr * (fr * (fr * (fr * CS l))))) *
            (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) * W) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCP_nn i') hfr4CS_nn)
          exact mul_le_mul_of_nonneg_left hmono
            (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _)
      _ = (CP i' * ((fr * (fr * (fr * (fr * CS l)))) *
            Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1))) * W := by
          ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]

private theorem iteratedCovGrad_normSq_tameEnvelope_of_gridWindow_rank42 (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Kg : ℕ → ℝ, (∀ k, 0 ≤ Kg k) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ) (C : ℝ), 0 ≤ C → ∀ (V : SmoothCcTensor g₀ 4 2),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 4 2 i V).toSection x) ≤
          C * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2)) →
        ‖iteratedCovGrad (I := I) g₀ 4 2 i V‖ ^ 2 ≤
          (C * ∑ k ∈ Finset.range (i + 2), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨Kg, hKg_nn, ?_⟩
  intro P hPball i C hC V hpt
  have hwin_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpt' : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 4 2 i V).toSection x) ≤
        C * ∑ k ∈ Finset.range (i + 2),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
    intro x
    refine le_trans (hpt x) (le_of_eq ?_)
    congr 1
  have hF_int : MeasureTheory.Integrable
      (fun x => C * ∑ k ∈ Finset.range (i + 2),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum _
      (fun k hk => (hKg P hPball k).1)).const_mul C
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 4 (2 + i)
    (iteratedCovGrad (I := I) g₀ 4 2 i V)
    (fun x => C * ∑ k ∈ Finset.range (i + 2),
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
    hF_int hpt'
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finset_sum _ (fun k hk => (hKg P hPball k).1)]
  have hsum_le : ∑ k ∈ Finset.range (i + 2),
        (∫ x, ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      (∑ k ∈ Finset.range (i + 2), Kg k) *
        (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    refine le_trans (hKg P hPball k).2 ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKg_nn k)
    have hsub : ∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
        ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
      rw [Finset.mem_range] at hk
      omega
    linarith
  calc C * ∑ k ∈ Finset.range (i + 2),
          (∫ x, ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
      ≤ C * ((∑ k ∈ Finset.range (i + 2), Kg k) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum_le hC
    _ = (C * ∑ k ∈ Finset.range (i + 2), Kg k) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        ring


theorem exists_curvatureRefoldMonomialCoeffField_symmS_realizedFam_l2JetWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (σ : Equiv.Perm (Fin 4)) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              (ccTensorUnitValueSection (I := I) (M := M) g₀
                (ccTensor02Symm (I := I) (M := M) g₀ T))
              (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
                (ccTensor02Symm (I := I) (M := M) g₀ T)) σ)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨C, hC_nn, hpt⟩ := curvatureRefoldMonomialCoeffField_pointwise_gridWindow (I := I) (M := M) g₀ hδ₁_lt σ
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    iteratedCovGrad_normSq_tameEnvelope_of_gridWindow_rank42 (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 2), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg fun k _ => hKg_nn k), ?_⟩
  intro T δ hδ_le hδ hδZ hball i s hs
  have hwin_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := bdDelta_nonneg (I := I) (M := M) g₀ x₀ T hδ
    have hδ_le' : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
          g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w :=
      fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
    obtain ⟨hs0, hs1⟩ := hs
    have habs : |s| ≤ 1 := by
      rw [abs_of_nonneg hs0]
      exact hs1
    have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
      intro y v w
      have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w
      have heq : |1 - s| * δ + |s| * δ = δ := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
        ring
      rwa [heq] at hraw
    have hcP : convexPerturbation (I := I) g₀ T 0 s = s • T := by
      rw [convexPerturbation, smul_zero, zero_add]
    have hPS : ∀ (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l
              (convexPerturbation (I := I) g₀ T 0 s)).toSection x) ≤
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) := by
      intro l x
      rw [hcP, iteratedCovGrad_smul_real]
      rw [show ((s • iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) =
          s • ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) from by
        rw [SmoothCcTensor.toSection_smul]
        rfl]
      rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (2 + l) x]
      have hs2 : s ^ 2 ≤ 1 := by nlinarith
      nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)]
    exact hKg T hball i (C i) (hC_nn i)
      (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) σ)
      (fun x => hpt (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (convexPerturbation (I := I) g₀ T 0 s) T htie hδ_le' hδ0 hδP hδ hPS i x)
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
            (ccTensor02Symm (I := I) (M := M) g₀ T)) σ)‖ = 0 :=
      bdNorm_zero_of_isEmpty (I := I) (M := M) g₀ 4 (2 + i) _
    rw [hz]
    have hK_nn : 0 ≤ C i * ∑ k ∈ Finset.range (i + 2), Kg k :=
      mul_nonneg (hC_nn i) (Finset.sum_nonneg fun k _ => hKg_nn k)
    nlinarith [hwin_nn, hK_nn]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
