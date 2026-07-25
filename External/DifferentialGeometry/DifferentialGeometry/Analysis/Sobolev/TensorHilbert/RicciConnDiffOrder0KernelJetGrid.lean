import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciConnDiffOrder1TameEnvelope

set_option linter.flexible false


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connDiffContrInsertionInnerFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 3 I z) x
        (show Tensor0SBundle.TensorRSSpace 2 3 I x from
          connContrCLM (I := I) 1 1 x ((connDiffSection (I := I) g₁ g₀).toSection x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z)
    (φ := fun x : M => connContrCLM (I := I) 1 1 x
      ((connDiffSection (I := I) g₁ g₀).toSection x))
  intro Y
  have h := connContrCLM_field_contMDiff (I := I) 1 1
    (fun x => (connDiffSection (I := I) g₁ g₀).toSection x)
    (connDiffSection (I := I) g₁ g₀).toSection.contMDiff
    (fun x => Y x) Y.contMDiff
  refine h.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x t) rfl

def connDiffContrInsertionInnerField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 3 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 2 3 I x from
          connContrCLM (I := I) 1 1 x ((connDiffSection (I := I) g₁ g₀).toSection x))
      contMDiff_toFun := connDiffContrInsertionInnerFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem connDiffContrInsertionInnerField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connDiffContrInsertionInnerField (I := I) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 3 I x from
        connContrCLM (I := I) 1 1 x ((connDiffSection (I := I) g₁ g₀).toSection x)) := rfl

def innerContractionSwapPerm : Equiv.Perm (Fin 2) :=
  ⟨![1, 0], ![1, 0], by decide, by decide⟩


omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connDiffContrInsertionInnerField_eq_reindex_slotExtend
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffContrInsertionInnerField (I := I) g₀ g₁ =
      reindexCoeffGen (I := I) (M := M) g₀ 2 3
        (slotExtend (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))
        innerContractionSwapPerm := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  refine tensorRSSpace_ext 2 3 x (fun D => ?_)
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun u => ?_)
  have hL : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (connDiffContrInsertionInnerField (I := I) g₀ g₁).toSection x) D) u =
      Tensor0SSpace.toModel D
        ![((PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((u 1 : E)) ((u 2 : E)) :
            TangentSpace I x) : E), u 0] := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (connDiffContrInsertionInnerField (I := I) g₀ g₁).toSection x) D) =
        connContrCLM (I := I) 1 1 x ((connDiffSection (I := I) g₁ g₀).toSection x) D from rfl]
    exact connContr11_insert (I := I) (M := M) g₁ g₀ x D u
  have hR : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 3
          (slotExtend (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))
          innerContractionSwapPerm).toSection x) D) u =
      Tensor0SSpace.toModel D
        ![((PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((u 1 : E)) ((u 2 : E)) :
            TangentSpace I x) : E), u 0] := by
    set D' : Tensor0SSpace 2 I x := Tensor0SSpace.ofModel (I := I) (x := x)
      (ContinuousMultilinearMap.domDomCongr innerContractionSwapPerm
        (Tensor0SSpace.toModel D)) with hD'_def
    have h1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 3
          (slotExtend (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))
          innerContractionSwapPerm).toSection x) D) =
        slotExtendPointwise (I := I) (M := M) g₀ 1 2 x
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (connDiffSection (I := I) g₁ g₀).toSection x) D' := by
      rw [hD'_def]
      exact reindexCoeffFibGen_apply (I := I) 2 3 innerContractionSwapPerm x _ D
    rw [h1]
    conv_lhs => rw [show u = Fin.cons (u 0) (Matrix.vecTail u) from (Fin.cons_self_tail u).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 1 2 x
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffSection (I := I) g₁ g₀).toSection x) D' (u 0) (Matrix.vecTail u)]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          (connDiffSection (I := I) g₁ g₀).toSection x)
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) D' (u 0)))
        (Matrix.vecTail u) =
        Tensor0SSpace.toModel
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) D' (u 0))
          (fun _ : Fin 1 => ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((u 1 : E)) ((u 2 : E)) : TangentSpace I x) : E)) from rfl]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1) D' (u 0)
      (fun _ : Fin 1 => ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        ((u 1 : E)) ((u 2 : E)) : TangentSpace I x) : E))]
    rw [hD'_def, Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext j
    fin_cases j <;> rfl
  exact hL.trans hR.symm

omit [NeZero (Module.finrank ℝ E)] in
private lemma cDualBasis_eq_coord' (B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (k : Fin (Module.finrank ℝ E)) :
    B.cDualBasis k = LinearMap.toContinuousLinearMap (B.coord k) := by
  rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
  exact congrArg (fun L : E →ₗ[ℝ] ℝ => LinearMap.toContinuousLinearMap L)
    (congrFun (Module.Basis.coe_dualBasis B) k)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rs13ContrVec_pairing (x : M) (B : Tensor0SBundle.TensorRSSpace 1 3 I x)
    (β : Tensor0SBundle.Tensor0SSpace 1 I x) (v : Fin 3 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from B) β) v =
      Tensor0SSpace.toModel β
        (fun _ : Fin 1 => rs13ContrVec (I := I) (M := M) x B v) := by
  classical
  have hci : ∀ i : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).cDualBasis i)
          (rs13ContrVec (I := I) (M := M) x B v) =
        (Tensor0SBundle.TensorRSSpace.toModel B
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i))) v := by
    intro i
    rw [rs13ContrVec, cDualBasis_eq_coord' (Module.finBasis ℝ E) i]
    rw [map_sum]
    rw [show (∑ j : Fin (Module.finrank ℝ E),
        LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)
          (((Tensor0SBundle.TensorRSSpace.toModel B
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))) v) • (Module.finBasis ℝ E) j)) =
        ∑ j : Fin (Module.finrank ℝ E),
          ((Tensor0SBundle.TensorRSSpace.toModel B
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))) v) *
            ((Module.finBasis ℝ E).repr ((Module.finBasis ℝ E) j) i) from
      Finset.sum_congr rfl (fun j _ => by
        rw [map_smul]
        rfl)]
    rw [Finset.sum_congr rfl (fun j _ => by
      rw [Module.Basis.repr_self,
        show (Finsupp.single j (1 : ℝ)) i = if j = i then (1 : ℝ) else 0 from
          Finsupp.single_apply,
        mul_ite, mul_one, mul_zero])]
    rw [Finset.sum_ite_eq' Finset.univ i]
    simp
    rw [cDualBasis_eq_coord' (Module.finBasis ℝ E) i]
  have hexp : Tensor0SSpace.toModel β =
      ∑ i : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel β (Fin.cons ((Module.finBasis ℝ E) i) ![])) •
          Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i) := by
    refine ContinuousMultilinearMap.ext (fun w => ?_)
    rw [ContinuousMultilinearMap.sum_apply]
    rw [Finset.sum_congr rfl (fun i _ => by
      rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul,
        Tensor0SBundle.model_covectorOfCLM_apply])]
    rw [sum_cons_cDual_collapse (I := I) (M := M) β ![] (w 0)]
    congr 1
    funext j
    fin_cases j
    rfl
  have hL0 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from B) β) =
      Tensor0SBundle.TensorRSSpace.toModel B (Tensor0SSpace.toModel β) :=
    toModel_tensorRS_apply (I := I) 1 3 x B β
  have hRHS : Tensor0SSpace.toModel β
      (fun _ : Fin 1 => rs13ContrVec (I := I) (M := M) x B v) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel β (Fin.cons ((Module.finBasis ℝ E) i) ![]) *
          (Tensor0SBundle.TensorRSSpace.toModel B
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis i))) v := by
    rw [show Tensor0SSpace.toModel β
        (fun _ : Fin 1 => rs13ContrVec (I := I) (M := M) x B v) =
        Tensor0SSpace.toModel β
          (Fin.cons (rs13ContrVec (I := I) (M := M) x B v) ![]) from
      congrArg (fun w => Tensor0SSpace.toModel β w)
        (funext (fun j => by fin_cases j; rfl))]
    rw [← sum_cons_cDual_collapse (I := I) (M := M) β ![]
      (rs13ContrVec (I := I) (M := M) x B v)]
    exact Finset.sum_congr rfl (fun i _ => by rw [hci i])
  rw [hL0, hRHS]
  conv_lhs => rw [hexp]
  rw [map_sum, ContinuousMultilinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul])


omit [NeZero (Module.finrank ℝ E)] in
theorem connDiffGradContrInsertionFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 4 I z) x
        (show Tensor0SBundle.TensorRSSpace 2 4 I x from
          connContrCLM (I := I) 1 2 x
            ((covGrad (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I) g₁ g₀)).toSection x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z)
    (φ := fun x : M => connContrCLM (I := I) 1 2 x
      ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x))
  intro Y
  have h := connContrCLM_field_contMDiff (I := I) 1 2
    (fun x => (covGrad (I := I) (M := M) g₀ 1 2
      (connDiffSection (I := I) g₁ g₀)).toSection x)
    (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection.contMDiff
    (fun x => Y x) Y.contMDiff
  refine h.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x t) rfl

def connDiffGradContrInsertionField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 4 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 2 4 I x from
          connContrCLM (I := I) 1 2 x
            ((covGrad (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I) g₁ g₀)).toSection x))
      contMDiff_toFun := connDiffGradContrInsertionFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem connDiffGradContrInsertionField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connDiffGradContrInsertionField (I := I) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 4 I x from
        connContrCLM (I := I) 1 2 x
          ((covGrad (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I) g₁ g₀)).toSection x)) := rfl


omit [NeZero (Module.finrank ℝ E)] in
theorem connDiffGradContrInsertionField_eq_reindex_slotExtend
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffGradContrInsertionField (I := I) g₀ g₁ =
      reindexCoeffGen (I := I) (M := M) g₀ 2 4
        (slotExtend (I := I) (M := M) g₀ 1 3
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)))
        innerContractionSwapPerm := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  refine tensorRSSpace_ext 2 4 x (fun D => ?_)
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun u => ?_)
  have hvec : Matrix.vecTail u = ![u 1, u 2, u 3] := by
    funext j
    fin_cases j <;> rfl
  have hL : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (connDiffGradContrInsertionField (I := I) g₀ g₁).toSection x) D) u =
      Tensor0SSpace.toModel D
        ![rs13ContrVec (I := I) (M := M) x
          (show Tensor0SBundle.TensorRSSpace 1 3 I x from
            (covGrad (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I) g₁ g₀)).toSection x) ![u 1, u 2, u 3], u 0] := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (connDiffGradContrInsertionField (I := I) g₀ g₁).toSection x) D) =
        connContrCLM (I := I) 1 2 x
          ((covGrad (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I) g₁ g₀)).toSection x) D from rfl]
    exact connContr12_insert (I := I) (M := M) x _ D u
  have hR : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 4
          (slotExtend (I := I) (M := M) g₀ 1 3
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)))
          innerContractionSwapPerm).toSection x) D) u =
      Tensor0SSpace.toModel D
        ![rs13ContrVec (I := I) (M := M) x
          (show Tensor0SBundle.TensorRSSpace 1 3 I x from
            (covGrad (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I) g₁ g₀)).toSection x) ![u 1, u 2, u 3], u 0] := by
    set D' : Tensor0SSpace 2 I x := Tensor0SSpace.ofModel (I := I) (x := x)
      (ContinuousMultilinearMap.domDomCongr innerContractionSwapPerm
        (Tensor0SSpace.toModel D)) with hD'_def
    have h1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 4
          (slotExtend (I := I) (M := M) g₀ 1 3
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)))
          innerContractionSwapPerm).toSection x) D) =
        slotExtendPointwise (I := I) (M := M) g₀ 1 3 x
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
            (covGrad (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I) g₁ g₀)).toSection x) D' := by
      rw [hD'_def]
      exact reindexCoeffFibGen_apply (I := I) 2 4 innerContractionSwapPerm x _ D
    rw [h1]
    conv_lhs => rw [show u = Fin.cons (u 0) (Matrix.vecTail u) from (Fin.cons_self_tail u).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 1 3 x
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (covGrad (I := I) (M := M) g₀ 1 2
          (connDiffSection (I := I) g₁ g₀)).toSection x) D' (u 0) (Matrix.vecTail u)]
    rw [rs13ContrVec_pairing (I := I) (M := M) x
      (show Tensor0SBundle.TensorRSSpace 1 3 I x from
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) D' (u 0)) (Matrix.vecTail u)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1) D' (u 0)
      (fun _ : Fin 1 => rs13ContrVec (I := I) (M := M) x
        (show Tensor0SBundle.TensorRSSpace 1 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I) g₁ g₀)).toSection x) (Matrix.vecTail u))]
    rw [hD'_def, Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [hvec]
    congr 1
    funext j
    fin_cases j <;> rfl
  exact hL.trans hR.symm


omit [NeZero (Module.finrank ℝ E)] in
theorem linearizedRicciConnDiffOrder0KernelFib_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 4 I z) x
        (show Tensor0SBundle.TensorRSSpace 2 4 I x from
          linearizedRicciConnDiffOrder0CLM (I := I) x
            ((connDiffSection (I := I) g₁ g₀).toSection x)
            ((covGrad (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I) g₁ g₀)).toSection x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z)
    (φ := fun x : M => linearizedRicciConnDiffOrder0CLM (I := I) x
      ((connDiffSection (I := I) g₁ g₀).toSection x)
      ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x))
  intro Y
  have hE0 := linearizedRicciConnDiffOrder0CLM_field_contMDiff (I := I) g₀ g₁
    (fun x => Y x) Y.contMDiff
  refine hE0.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x t) rfl

def linearizedRicciConnDiffOrder0KernelField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 4 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 2 4 I x from
          linearizedRicciConnDiffOrder0CLM (I := I) x
            ((connDiffSection (I := I) g₁ g₀).toSection x)
            ((covGrad (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I) g₁ g₀)).toSection x))
      contMDiff_toFun := linearizedRicciConnDiffOrder0KernelFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem linearizedRicciConnDiffOrder0KernelField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 4 I x from
        linearizedRicciConnDiffOrder0CLM (I := I) x
          ((connDiffSection (I := I) g₁ g₀).toSection x)
          ((covGrad (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I) g₁ g₀)).toSection x)) := rfl


omit [NeZero (Module.finrank ℝ E)] in
theorem linearizedRicciConnDiffOrder0CoeffField_eq_ricciCometricFourTrace_comp_kernelField
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
        (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
        (linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

private def kOut0Perm3201 : Equiv.Perm (Fin 4) :=
  ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

private def kOut0Perm2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

private def kOut0Perm3102 : Equiv.Perm (Fin 4) :=
  ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩

private def kOut0Perm1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

private def kOut0Perm1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

private def kOut0Perm2103 : Equiv.Perm (Fin 4) :=
  ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩

private def kOut0Perm3012 : Equiv.Perm (Fin 4) :=
  ⟨![3, 0, 1, 2], ![1, 2, 3, 0], by decide, by decide⟩

private def kOut0Perm2013 : Equiv.Perm (Fin 4) :=
  ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩

private def kMid0Perm102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def kMid0Perm120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem slotPermCc0Fib_contMDiff (_g₀ : SmoothRiemannianMetric I M) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel d d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel d d ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace d d I z) x
        (show Tensor0SBundle.TensorRSSpace d d I x from slotPermCLM (I := I) ρ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel d ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)
    (F₂ := Tensor0SBundle.Tensor0SModel d ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)
    (φ := fun x : M => slotPermCLM (I := I) ρ x)
  intro Y
  have h := slotPermCLM_field_contMDiff (I := I) ρ (fun x => Y x) Y.contMDiff
  refine h.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x t) rfl

private def slotPermCc0 (g₀ : SmoothRiemannianMetric I M) {d : ℕ} (ρ : Equiv.Perm (Fin d)) :
    SmoothCcTensor g₀ d d where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace d d I x from slotPermCLM (I := I) ρ x)
      contMDiff_toFun := slotPermCc0Fib_contMDiff (I := I) (M := M) g₀ ρ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] in
private theorem order0KernelField_eq_arm_combination (g₀ g₁ : SmoothRiemannianMetric I M) :
    linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁ =
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm3201)
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (slotPermCc0 (I := I) (M := M) g₀ kMid0Perm102)
              (connDiffContrInsertionInnerField (I := I) g₀ g₁)))
        + reindexCoeffGen (I := I) (M := M) g₀ 2 4
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm2301)
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
                (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
                  (slotPermCc0 (I := I) (M := M) g₀ kMid0Perm102)
                  (connDiffContrInsertionInnerField (I := I) g₀ g₁)))) innerContractionSwapPerm
        + ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm3102)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
                (slotPermCc0 (I := I) (M := M) g₀ kMid0Perm120)
                (connDiffContrInsertionInnerField (I := I) g₀ g₁)))
        + reindexCoeffGen (I := I) (M := M) g₀ 2 4
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm1302)
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
                (connDiffContrInsertionInnerField (I := I) g₀ g₁))) innerContractionSwapPerm
        + ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm1203)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
              (connDiffContrInsertionInnerField (I := I) g₀ g₁))
        + reindexCoeffGen (I := I) (M := M) g₀ 2 4
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm2103)
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
                (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
                  (slotPermCc0 (I := I) (M := M) g₀ kMid0Perm120)
                  (connDiffContrInsertionInnerField (I := I) g₀ g₁)))) innerContractionSwapPerm)
      - ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm3012)
          (connDiffGradContrInsertionField (I := I) g₀ g₁)
      - reindexCoeffGen (I := I) (M := M) g₀ 2 4
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm2013)
            (connDiffGradContrInsertionField (I := I) g₀ g₁)) innerContractionSwapPerm := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

private theorem armOuter24_rfns_eq (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (W : SmoothCcTensor g₀ 2 4) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 4 q
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4
            (slotPermCc0 (I := I) (M := M) g₀ σ) W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 4 q W).toSection x) := by
  refine riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 4 σ
    W (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ σ) W)
    (fun y d => ?_) q x
  have hy : (show Tensor0SSpace 2 I y →L[ℝ] Tensor0SSpace 4 I y from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4
        (slotPermCc0 (I := I) (M := M) g₀ σ) W).toSection y) d =
      slotPermCLM (I := I) σ y
        ((show Tensor0SSpace 2 I y →L[ℝ] Tensor0SSpace 4 I y from W.toSection y) d) := rfl
  rw [hy, slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

private theorem armOuter23_rfns_eq (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (W : SmoothCcTensor g₀ 2 3) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 3 q
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
            (slotPermCc0 (I := I) (M := M) g₀ σ) W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 3 q W).toSection x) := by
  refine riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 3 σ
    W (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (slotPermCc0 (I := I) (M := M) g₀ σ) W)
    (fun y d => ?_) q x
  have hy : (show Tensor0SSpace 2 I y →L[ℝ] Tensor0SSpace 3 I y from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
        (slotPermCc0 (I := I) (M := M) g₀ σ) W).toSection y) d =
      slotPermCLM (I := I) σ y
        ((show Tensor0SSpace 2 I y →L[ℝ] Tensor0SSpace 3 I y from W.toSection y) d) := rfl
  rw [hy, slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma o0IteratedCovGrad_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma o0Rfns_smul (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring


private theorem quadArm_rfns_windowGrid_le (g₀ : SmoothRiemannianMetric I M)
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (core : SmoothCcTensor g₀ 3 4) (W23 : SmoothCcTensor g₀ 2 3)
    (CA : ℕ → ℝ) (hCA_nn : ∀ j, 0 ≤ CA j) {fr : ℝ} (hfr : 0 ≤ fr)
    (l : ℕ) (x : M)
    (hcore : ∀ n, n ≤ l → riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + n) x
      ((iteratedCovGrad (I := I) g₀ 3 4 n core).toSection x) ≤
      fr ^ 2 * CA n * Combinatorics.antidiagonalTupleGridWindow b (n + 2))
    (hW : ∀ m, m ≤ l → riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
      ((iteratedCovGrad (I := I) g₀ 2 3 m W23).toSection x) ≤
      fr * CA m * Combinatorics.antidiagonalTupleGridWindow b (m + 2)) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 4 l
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 core W23)).toSection x) ≤
      (diagonalGridGrowthFactor (E := E) l *
          ∑ n ∈ Finset.range (l + 1), ∑ m ∈ Finset.range (l + 1 - n),
            fr ^ 3 * CA n * CA m *
              Combinatorics.antidiagonalTupleGridWindowMulConst (n + 1) (m + 1)) *
        Combinatorics.antidiagonalTupleGridWindow b (l + 3) := by
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ l 2 3 4 core W23 x) ?_
  have hwin_nn : ∀ w : ℕ, 0 ≤ Combinatorics.antidiagonalTupleGridWindow b w :=
    fun w => Combinatorics.antidiagonalTupleGridWindow_nonneg b hb w
  have hterm : ∀ n ∈ Finset.range (l + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + n) x
          ((iteratedCovGrad (I := I) g₀ 3 4 n core).toSection x) *
        ∑ m ∈ Finset.range (l + 1 - n),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
            ((iteratedCovGrad (I := I) g₀ 2 3 m W23).toSection x) ≤
      (∑ m ∈ Finset.range (l + 1 - n),
        fr ^ 3 * CA n * CA m *
          Combinatorics.antidiagonalTupleGridWindowMulConst (n + 1) (m + 1)) *
        Combinatorics.antidiagonalTupleGridWindow b (l + 3) := by
    intro n hn
    rw [Finset.mem_range] at hn
    have h1 := hcore n (by omega)
    have h2 : (∑ m ∈ Finset.range (l + 1 - n),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
          ((iteratedCovGrad (I := I) g₀ 2 3 m W23).toSection x)) ≤
        ∑ m ∈ Finset.range (l + 1 - n),
          fr * CA m * Combinatorics.antidiagonalTupleGridWindow b (m + 2) := by
      refine Finset.sum_le_sum (fun m hm => ?_)
      rw [Finset.mem_range] at hm
      exact hW m (by omega)
    have hprod : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + n) x
          ((iteratedCovGrad (I := I) g₀ 3 4 n core).toSection x) *
        (∑ m ∈ Finset.range (l + 1 - n),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
            ((iteratedCovGrad (I := I) g₀ 2 3 m W23).toSection x)) ≤
        (fr ^ 2 * CA n * Combinatorics.antidiagonalTupleGridWindow b (n + 2)) *
          ∑ m ∈ Finset.range (l + 1 - n),
            fr * CA m * Combinatorics.antidiagonalTupleGridWindow b (m + 2) :=
      mul_le_mul h1 h2
        (Finset.sum_nonneg (fun m _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (3 + m) x _))
        (mul_nonneg (mul_nonneg (pow_nonneg hfr 2) (hCA_nn n)) (hwin_nn (n + 2)))
    refine le_trans hprod ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum (fun m hm => ?_)
    rw [Finset.mem_range] at hm
    have hww := Combinatorics.antidiagonalTupleGridWindow_mul_le b hb (n + 1) (m + 1)
    have hmono : Combinatorics.antidiagonalTupleGridWindow b (n + 1 + (m + 1) + 1) ≤
        Combinatorics.antidiagonalTupleGridWindow b (l + 3) :=
      Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
    have hc_nn : (0 : ℝ) ≤ fr ^ 3 * CA n * CA m :=
      mul_nonneg (mul_nonneg (pow_nonneg hfr 3) (hCA_nn n)) (hCA_nn m)
    calc (fr ^ 2 * CA n * Combinatorics.antidiagonalTupleGridWindow b (n + 2)) *
            (fr * CA m * Combinatorics.antidiagonalTupleGridWindow b (m + 2))
        = (fr ^ 3 * CA n * CA m) *
            (Combinatorics.antidiagonalTupleGridWindow b (n + 2) *
              Combinatorics.antidiagonalTupleGridWindow b (m + 2)) := by ring
      _ ≤ (fr ^ 3 * CA n * CA m) *
            (Combinatorics.antidiagonalTupleGridWindowMulConst (n + 1) (m + 1) *
              Combinatorics.antidiagonalTupleGridWindow b (n + 1 + (m + 1) + 1)) :=
          mul_le_mul_of_nonneg_left hww hc_nn
      _ ≤ (fr ^ 3 * CA n * CA m) *
            (Combinatorics.antidiagonalTupleGridWindowMulConst (n + 1) (m + 1) *
              Combinatorics.antidiagonalTupleGridWindow b (l + 3)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmono
              (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg (n + 1) (m + 1)))
            hc_nn
      _ = fr ^ 3 * CA n * CA m *
            Combinatorics.antidiagonalTupleGridWindowMulConst (n + 1) (m + 1) *
            Combinatorics.antidiagonalTupleGridWindow b (l + 3) := by ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (appCcGdiag_nonneg (E := E) l)) ?_
  rw [← Finset.sum_mul]
  exact le_of_eq (by ring)

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rfns_eightArm_cascade (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v1 v2 v3 v4 v5 v6 v7 v8 : TensorRSSpace r s I x) {Q L w : ℝ}
    (h1 : riemannianFiberNormSq (I := I) (M := M) g r s x v1 ≤ Q * w)
    (h2 : riemannianFiberNormSq (I := I) (M := M) g r s x v2 ≤ Q * w)
    (h3 : riemannianFiberNormSq (I := I) (M := M) g r s x v3 ≤ Q * w)
    (h4 : riemannianFiberNormSq (I := I) (M := M) g r s x v4 ≤ Q * w)
    (h5 : riemannianFiberNormSq (I := I) (M := M) g r s x v5 ≤ Q * w)
    (h6 : riemannianFiberNormSq (I := I) (M := M) g r s x v6 ≤ Q * w)
    (h7 : riemannianFiberNormSq (I := I) (M := M) g r s x v7 ≤ L * w)
    (h8 : riemannianFiberNormSq (I := I) (M := M) g r s x v8 ≤ L * w) :
    riemannianFiberNormSq (I := I) (M := M) g r s x
        (v1 + v2 + v3 + v4 + v5 + v6 - v7 - v8) ≤
      376 * (Q * w) + 6 * (L * w) := by
  have c12 := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x v1 v2
  have c123 := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x (v1 + v2) v3
  have c1234 := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x (v1 + v2 + v3) v4
  have c12345 := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x
    (v1 + v2 + v3 + v4) v5
  have c123456 := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x
    (v1 + v2 + v3 + v4 + v5) v6
  have cm7 := riemannianFiberNormSq_sub_le (I := I) (M := M) g r s x
    (v1 + v2 + v3 + v4 + v5 + v6) v7
  have cm8 := riemannianFiberNormSq_sub_le (I := I) (M := M) g r s x
    (v1 + v2 + v3 + v4 + v5 + v6 - v7) v8
  linarith [c12, c123, c1234, c12345, c123456, cm7, cm8, h1, h2, h3, h4, h5, h6, h7, h8]


theorem rfns_iteratedCovGrad_linearizedRicciConnDiffOrder0KernelField_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ l, 0 ≤ C l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 4 l
              (linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x) ≤
          C l * ∑ k ∈ Finset.range (l + 3),
            Combinatorics.antidiagonalTupleGrid
              (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
                ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  set CQ : ℕ → ℝ := fun l => diagonalGridGrowthFactor (E := E) l *
    ∑ n ∈ Finset.range (l + 1), ∑ m ∈ Finset.range (l + 1 - n),
      fr ^ 3 * CA n * CA m *
        Combinatorics.antidiagonalTupleGridWindowMulConst (n + 1) (m + 1) with hCQ_def
  have hCQ_nn : ∀ l, 0 ≤ CQ l := by
    intro l
    simp only [hCQ_def]
    refine mul_nonneg (appCcGdiag_nonneg (E := E) l) ?_
    refine Finset.sum_nonneg (fun n _ => Finset.sum_nonneg (fun m _ => ?_))
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hfr 3) (hCA_nn n)) (hCA_nn m))
      (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg (n + 1) (m + 1))
  set CL : ℕ → ℝ := fun l => fr * CA (l + 1) with hCL_def
  have hCL_nn : ∀ l, 0 ≤ CL l := by
    intro l
    simp only [hCL_def]
    exact mul_nonneg hfr (hCA_nn (l + 1))
  refine ⟨fun l => 376 * CQ l + 6 * CL l,
    fun l => by have := hCQ_nn l; have := hCL_nn l; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound l x
  have hcomb := order0KernelField_eq_arm_combination (I := I) (M := M) g₀ g₁
  set b : ℕ → ℝ := fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
    ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x) with hb_def
  have hb : ∀ j', 0 ≤ b j' :=
    fun j' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j') x _
  have hwin_nn : ∀ w : ℕ, 0 ≤ Combinatorics.antidiagonalTupleGridWindow b w :=
    fun w => Combinatorics.antidiagonalTupleGridWindow_nonneg b hb w
  have hA : ∀ j : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      CA j * Combinatorics.antidiagonalTupleGridWindow b (j + 2) :=
    fun j => hCA g₁ P htie hδ_le hδ0 hbound j x
  have hInner : ∀ m : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
      ((iteratedCovGrad (I := I) g₀ 2 3 m
        (connDiffContrInsertionInnerField (I := I) g₀ g₁)).toSection x) ≤
      fr * CA m * Combinatorics.antidiagonalTupleGridWindow b (m + 2) := by
    intro m
    have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 2 3 m
          (connDiffContrInsertionInnerField (I := I) g₀ g₁)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
          ((iteratedCovGrad (I := I) g₀ 2 3 m
            (slotExtend (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I) g₁ g₀))).toSection x) := by
      rw [connDiffContrInsertionInnerField_eq_reindex_slotExtend (I := I) (M := M) g₀ g₁]
      exact riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 3
        (slotExtend (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))
        innerContractionSwapPerm m x
    rw [h0]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
      (connDiffSection (I := I) g₁ g₀) m x) ?_
    calc fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 1 2 m
              (connDiffSection (I := I) g₁ g₀)).toSection x)
        ≤ fr * (CA m * Combinatorics.antidiagonalTupleGridWindow b (m + 2)) :=
          mul_le_mul_of_nonneg_left (hA m) hfr
      _ = fr * CA m * Combinatorics.antidiagonalTupleGridWindow b (m + 2) := by ring
  have hCore34 : ∀ n : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + n) x
      ((iteratedCovGrad (I := I) g₀ 3 4 n
        (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) ≤
      fr ^ 2 * CA n * Combinatorics.antidiagonalTupleGridWindow b (n + 2) := by
    intro n
    have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + n) x
        ((iteratedCovGrad (I := I) g₀ 3 4 n
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + n) x
          ((iteratedCovGrad (I := I) g₀ 3 4 n
            (slotExtend (I := I) (M := M) g₀ 2 3
              (slotExtend (I := I) (M := M) g₀ 1 2
                (connDiffSection (I := I) g₁ g₀)))).toSection x) := by
      rw [connDiffContrInsertionField_eq_reindex_slotExtend_two (I := I) (M := M) g₀ g₁]
      exact riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 3 4
        (slotExtend (I := I) (M := M) g₀ 2 3
          (slotExtend (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)))
        connDiffContrInsertionReindexPerm n x
    rw [h0]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 3
      (slotExtend (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)) n x) ?_
    have h2 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
      (connDiffSection (I := I) g₁ g₀) n x
    calc fr * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 2 3 n
              (slotExtend (I := I) (M := M) g₀ 1 2
                (connDiffSection (I := I) g₁ g₀))).toSection x)
        ≤ fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 2 n
              (connDiffSection (I := I) g₁ g₀)).toSection x)) :=
          mul_le_mul_of_nonneg_left h2 hfr
      _ ≤ fr * (fr * (CA n * Combinatorics.antidiagonalTupleGridWindow b (n + 2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hA n) hfr) hfr
      _ = fr ^ 2 * CA n * Combinatorics.antidiagonalTupleGridWindow b (n + 2) := by ring
  have hGrad : ∀ q : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + q) x
      ((iteratedCovGrad (I := I) g₀ 2 4 q
        (connDiffGradContrInsertionField (I := I) g₀ g₁)).toSection x) ≤
      CL q * Combinatorics.antidiagonalTupleGridWindow b (q + 3) := by
    intro q
    have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 4 q
          (connDiffGradContrInsertionField (I := I) g₀ g₁)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + q) x
          ((iteratedCovGrad (I := I) g₀ 2 4 q
            (slotExtend (I := I) (M := M) g₀ 1 3
              (covGrad (I := I) (M := M) g₀ 1 2
                (connDiffSection (I := I) g₁ g₀)))).toSection x) := by
      rw [connDiffGradContrInsertionField_eq_reindex_slotExtend (I := I) (M := M) g₀ g₁]
      exact riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 4
        (slotExtend (I := I) (M := M) g₀ 1 3
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)))
        innerContractionSwapPerm q x
    rw [h0]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 3
      (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)) q x) ?_
    have hcomm : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + q) x
        ((iteratedCovGrad (I := I) g₀ 1 3 q
          (covGrad (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I) g₁ g₀))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (q + 1)) x
          ((iteratedCovGrad (I := I) g₀ 1 2 (q + 1)
            (connDiffSection (I := I) g₁ g₀)).toSection x) :=
      rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2 q
        (connDiffSection (I := I) g₁ g₀) x
    rw [hcomm]
    refine le_trans (mul_le_mul_of_nonneg_left (hA (q + 1)) hfr) ?_
    rw [hCL_def]
    exact le_of_eq (by ring)
  have hMidBound : ∀ (ρ : Equiv.Perm (Fin 3)) (m : ℕ),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 2 3 m
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (slotPermCc0 (I := I) (M := M) g₀ ρ)
            (connDiffContrInsertionInnerField (I := I) g₀ g₁))).toSection x) ≤
      fr * CA m * Combinatorics.antidiagonalTupleGridWindow b (m + 2) := by
    intro ρ m
    rw [armOuter23_rfns_eq (I := I) (M := M) g₀ ρ
      (connDiffContrInsertionInnerField (I := I) g₀ g₁) m x]
    exact hInner m
  have hQuadPerm : ∀ (ρ : Equiv.Perm (Fin 3)),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 4 l
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (slotPermCc0 (I := I) (M := M) g₀ ρ)
              (connDiffContrInsertionInnerField (I := I) g₀ g₁)))).toSection x) ≤
      CQ l * Combinatorics.antidiagonalTupleGridWindow b (l + 3) := by
    intro ρ
    rw [hCQ_def]
    exact quadArm_rfns_windowGrid_le (I := I) (M := M) g₀ b hb
      (connDiffContrInsertionField (I := I) g₀ g₁)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (slotPermCc0 (I := I) (M := M) g₀ ρ)
        (connDiffContrInsertionInnerField (I := I) g₀ g₁))
      CA hCA_nn hfr l x (fun n _ => hCore34 n) (fun m _ => hMidBound ρ m)
  have hQuadPlain : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 2 4 l
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
          (connDiffContrInsertionInnerField (I := I) g₀ g₁))).toSection x) ≤
      CQ l * Combinatorics.antidiagonalTupleGridWindow b (l + 3) := by
    rw [hCQ_def]
    exact quadArm_rfns_windowGrid_le (I := I) (M := M) g₀ b hb
      (connDiffContrInsertionField (I := I) g₀ g₁)
      (connDiffContrInsertionInnerField (I := I) g₀ g₁)
      CA hCA_nn hfr l x (fun n _ => hCore34 n) (fun m _ => hInner m)
  have hB1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 2 4 l
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm3201)
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
              (slotPermCc0 (I := I) (M := M) g₀ kMid0Perm102)
              (connDiffContrInsertionInnerField (I := I) g₀ g₁))))).toSection x) ≤
      CQ l * Combinatorics.antidiagonalTupleGridWindow b (l + 3) := by
    rw [armOuter24_rfns_eq (I := I) (M := M) g₀ kOut0Perm3201 _ l x]
    exact hQuadPerm kMid0Perm102
  have hB2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 2 4 l
        (reindexCoeffGen (I := I) (M := M) g₀ 2 4
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4
            (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm2301)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
                (slotPermCc0 (I := I) (M := M) g₀ kMid0Perm102)
                (connDiffContrInsertionInnerField (I := I) g₀ g₁))))
          innerContractionSwapPerm)).toSection x) ≤
      CQ l * Combinatorics.antidiagonalTupleGridWindow b (l + 3) := by
    rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 4 _
      innerContractionSwapPerm l x]
    rw [armOuter24_rfns_eq (I := I) (M := M) g₀ kOut0Perm2301 _ l x]
    exact hQuadPerm kMid0Perm102
  have hB3 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 2 4 l
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm3102)
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
              (slotPermCc0 (I := I) (M := M) g₀ kMid0Perm120)
              (connDiffContrInsertionInnerField (I := I) g₀ g₁))))).toSection x) ≤
      CQ l * Combinatorics.antidiagonalTupleGridWindow b (l + 3) := by
    rw [armOuter24_rfns_eq (I := I) (M := M) g₀ kOut0Perm3102 _ l x]
    exact hQuadPerm kMid0Perm120
  have hB4 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 2 4 l
        (reindexCoeffGen (I := I) (M := M) g₀ 2 4
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4
            (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm1302)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
              (connDiffContrInsertionInnerField (I := I) g₀ g₁)))
          innerContractionSwapPerm)).toSection x) ≤
      CQ l * Combinatorics.antidiagonalTupleGridWindow b (l + 3) := by
    rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 4 _
      innerContractionSwapPerm l x]
    rw [armOuter24_rfns_eq (I := I) (M := M) g₀ kOut0Perm1302 _ l x]
    exact hQuadPlain
  have hB5 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 2 4 l
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm1203)
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
            (connDiffContrInsertionInnerField (I := I) g₀ g₁)))).toSection x) ≤
      CQ l * Combinatorics.antidiagonalTupleGridWindow b (l + 3) := by
    rw [armOuter24_rfns_eq (I := I) (M := M) g₀ kOut0Perm1203 _ l x]
    exact hQuadPlain
  have hB6 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 2 4 l
        (reindexCoeffGen (I := I) (M := M) g₀ 2 4
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4
            (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm2103)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
                (slotPermCc0 (I := I) (M := M) g₀ kMid0Perm120)
                (connDiffContrInsertionInnerField (I := I) g₀ g₁))))
          innerContractionSwapPerm)).toSection x) ≤
      CQ l * Combinatorics.antidiagonalTupleGridWindow b (l + 3) := by
    rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 4 _
      innerContractionSwapPerm l x]
    rw [armOuter24_rfns_eq (I := I) (M := M) g₀ kOut0Perm2103 _ l x]
    exact hQuadPerm kMid0Perm120
  have hB7 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 2 4 l
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm3012)
          (connDiffGradContrInsertionField (I := I) g₀ g₁))).toSection x) ≤
      CL l * Combinatorics.antidiagonalTupleGridWindow b (l + 3) := by
    rw [armOuter24_rfns_eq (I := I) (M := M) g₀ kOut0Perm3012 _ l x]
    exact hGrad l
  have hB8 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 2 4 l
        (reindexCoeffGen (I := I) (M := M) g₀ 2 4
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4
            (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm2013)
            (connDiffGradContrInsertionField (I := I) g₀ g₁))
          innerContractionSwapPerm)).toSection x) ≤
      CL l * Combinatorics.antidiagonalTupleGridWindow b (l + 3) := by
    rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 4 _
      innerContractionSwapPerm l x]
    rw [armOuter24_rfns_eq (I := I) (M := M) g₀ kOut0Perm2013 _ l x]
    exact hGrad l
  have hsec : (iteratedCovGrad (I := I) g₀ 2 4 l
      (linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x =
      ((((((iteratedCovGrad (I := I) g₀ 2 4 l
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm3201)
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
              (slotPermCc0 (I := I) (M := M) g₀ kMid0Perm102)
              (connDiffContrInsertionInnerField (I := I) g₀ g₁))))).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 4 l
        (reindexCoeffGen (I := I) (M := M) g₀ 2 4
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4
            (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm2301)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
                (slotPermCc0 (I := I) (M := M) g₀ kMid0Perm102)
                (connDiffContrInsertionInnerField (I := I) g₀ g₁))))
          innerContractionSwapPerm)).toSection x)
      + (iteratedCovGrad (I := I) g₀ 2 4 l
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm3102)
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
              (slotPermCc0 (I := I) (M := M) g₀ kMid0Perm120)
              (connDiffContrInsertionInnerField (I := I) g₀ g₁))))).toSection x)
      + (iteratedCovGrad (I := I) g₀ 2 4 l
        (reindexCoeffGen (I := I) (M := M) g₀ 2 4
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4
            (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm1302)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
              (connDiffContrInsertionInnerField (I := I) g₀ g₁)))
          innerContractionSwapPerm)).toSection x)
      + (iteratedCovGrad (I := I) g₀ 2 4 l
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm1203)
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
            (connDiffContrInsertionInnerField (I := I) g₀ g₁)))).toSection x)
      + (iteratedCovGrad (I := I) g₀ 2 4 l
        (reindexCoeffGen (I := I) (M := M) g₀ 2 4
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4
            (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm2103)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (connDiffContrInsertionField (I := I) g₀ g₁)
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
                (slotPermCc0 (I := I) (M := M) g₀ kMid0Perm120)
                (connDiffContrInsertionInnerField (I := I) g₀ g₁))))
          innerContractionSwapPerm)).toSection x)
      - (iteratedCovGrad (I := I) g₀ 2 4 l
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm3012)
          (connDiffGradContrInsertionField (I := I) g₀ g₁))).toSection x
      - (iteratedCovGrad (I := I) g₀ 2 4 l
        (reindexCoeffGen (I := I) (M := M) g₀ 2 4
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4
            (slotPermCc0 (I := I) (M := M) g₀ kOut0Perm2013)
            (connDiffGradContrInsertionField (I := I) g₀ g₁))
          innerContractionSwapPerm)).toSection x := by
    rw [hcomb, iteratedCovGrad_sub, iteratedCovGrad_sub, iteratedCovGrad_add,
      iteratedCovGrad_add, iteratedCovGrad_add, iteratedCovGrad_add, iteratedCovGrad_add]
    rfl
  rw [hsec]
  have hgoal : (376 * CQ l + 6 * CL l) *
      (∑ k ∈ Finset.range (l + 3),
        Combinatorics.antidiagonalTupleGrid b k) =
      376 * (CQ l * Combinatorics.antidiagonalTupleGridWindow b (l + 3)) +
        6 * (CL l * Combinatorics.antidiagonalTupleGridWindow b (l + 3)) := by
    rw [show (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) =
        Combinatorics.antidiagonalTupleGridWindow b (l + 3) from rfl]
    ring
  rw [hgoal]
  exact rfns_eightArm_cascade (I := I) (M := M) g₀ 2 (4 + l) x
    _ _ _ _ _ _ _ _ hB1 hB2 hB3 hB4 hB5 hB6 hB7 hB8


theorem rfns_iteratedCovGrad_ricciCometricFourTraceCastG0_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 4 2 n
              (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x) ≤
          C n * ∑ k ∈ Finset.range (n + 1),
            Combinatorics.antidiagonalTupleGrid
              (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
                ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k := by
  classical
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  have hSΦ_ex : ∀ q : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 4 2 q
          (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) ≤ K :=
    fun q => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + q)
      (iteratedCovGrad (I := I) g₀ 4 2 q (cometricDoubleTraceField (I := I) g₀ 2))
  choose SΦ hSΦ_nn hSΦ using hSΦ_ex
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  set CD : ℕ → ℝ := fun n => diagonalGridGrowthFactor (E := E) n *
    (∑ a ∈ Finset.range (n + 1), SΦ a) *
      (fr ^ 3 * ∑ q ∈ Finset.range (n + 1), Cb q) with hCD_def
  have hCD_nn : ∀ n, 0 ≤ CD n := by
    intro n
    simp only [hCD_def]
    exact mul_nonneg (mul_nonneg (appCcGdiag_nonneg (E := E) n)
      (Finset.sum_nonneg (fun a _ => hSΦ_nn a)))
      (mul_nonneg (pow_nonneg hfr 3) (Finset.sum_nonneg (fun q _ => hCb_nn q)))
  refine ⟨fun n => 6 * (2 * SΦ n + 2 * CD n),
    fun n => by have := hSΦ_nn n; have := hCD_nn n; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound n x
  set b : ℕ → ℝ := fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
    ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x) with hb_def
  have hb : ∀ j', 0 ≤ b j' :=
    fun j' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j') x _
  have hone : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (n + 1) :=
    Combinatorics.one_le_antidiagonalTupleGridWindow b hb (by omega)
  have hwin_nn : 0 ≤ Combinatorics.antidiagonalTupleGridWindow b (n + 1) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (n + 1)
  have hWgrid : ∀ q : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + q) x
      ((iteratedCovGrad (I := I) g₀ 4 4 q
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
      fr ^ 3 * Cb q * Combinatorics.antidiagonalTupleGrid b q := by
    intro q
    refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 3
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) q x) ?_
    have h2 := hCb g₁ P htie hδ_le hδ0 hbound q x
    calc fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) x
            ((iteratedCovGrad (I := I) g₀ 1 1 q
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
        ≤ fr ^ 3 * (Cb q * Combinatorics.antidiagonalTupleGrid b q) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hfr 3)
      _ = fr ^ 3 * Cb q * Combinatorics.antidiagonalTupleGrid b q := by ring
  have hD : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 4 2 n
        (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) ≤
      CD n * Combinatorics.antidiagonalTupleGridWindow b (n + 1) := by
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ n 4 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
        (gInvDiffRaisedEndoField (I := I) g₀ g₁)) x) ?_
    have hterm : ∀ a ∈ Finset.range (n + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + a) x
            ((iteratedCovGrad (I := I) g₀ 4 2 a
              (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
          ∑ q ∈ Finset.range (n + 1 - a),
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + q) x
              ((iteratedCovGrad (I := I) g₀ 4 4 q
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
        SΦ a * ((fr ^ 3 * ∑ q ∈ Finset.range (n + 1), Cb q) *
          Combinatorics.antidiagonalTupleGridWindow b (n + 1)) := by
      intro a ha
      rw [Finset.mem_range] at ha
      have hsum : (∑ q ∈ Finset.range (n + 1 - a),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + q) x
            ((iteratedCovGrad (I := I) g₀ 4 4 q
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)) ≤
          (fr ^ 3 * ∑ q ∈ Finset.range (n + 1), Cb q) *
            Combinatorics.antidiagonalTupleGridWindow b (n + 1) := by
        have h1 : (∑ q ∈ Finset.range (n + 1 - a),
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + q) x
              ((iteratedCovGrad (I := I) g₀ 4 4 q
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)) ≤
            ∑ q ∈ Finset.range (n + 1 - a),
              fr ^ 3 * Cb q * Combinatorics.antidiagonalTupleGridWindow b (n + 1) := by
          refine Finset.sum_le_sum (fun q hq => ?_)
          rw [Finset.mem_range] at hq
          refine le_trans (hWgrid q) ?_
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (pow_nonneg hfr 3) (hCb_nn q))
          exact Combinatorics.antidiagonalTupleGrid_le_window b hb (by omega)
        refine le_trans h1 ?_
        rw [← Finset.sum_mul, Finset.mul_sum]
        refine mul_le_mul_of_nonneg_right ?_ hwin_nn
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (by omega)) ?_
        intro q _ _
        exact mul_nonneg (pow_nonneg hfr 3) (hCb_nn q)
      refine mul_le_mul (hSΦ a x) hsum
        (Finset.sum_nonneg (fun q _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 (4 + q) x _))
        (hSΦ_nn a)
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
      (appCcGdiag_nonneg (E := E) n)) ?_
    rw [← Finset.sum_mul, hCD_def]
    exact le_of_eq (by ring)
  have hpure : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 4 2 n
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)).toSection x) ≤
      (2 * SΦ n + 2 * CD n) * Combinatorics.antidiagonalTupleGridWindow b (n + 1) := by
    have hxid : (iteratedCovGrad (I := I) g₀ 4 2 n
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)).toSection x =
        (iteratedCovGrad (I := I) g₀ 4 2 n
          (cometricDoubleTraceField (I := I) g₀ 2)).toSection x +
        (iteratedCovGrad (I := I) g₀ 4 2 n
          (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x := by
      rw [ricciArmPrincipalCoeffPure_eq_doubleTrace_add_appCcRS (I := I) g₀ g₁,
        iteratedCovGrad_add, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
        Pi.add_apply]
    rw [hxid]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 4 (2 + n) x _ _) ?_
    have hΦw : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 4 2 n
          (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) ≤
        SΦ n * Combinatorics.antidiagonalTupleGridWindow b (n + 1) := by
      refine le_trans (hSΦ n x) ?_
      exact le_mul_of_one_le_right (hSΦ_nn n) hone
    have hDw := hD
    nlinarith [hΦw, hDw, hwin_nn, hSΦ_nn n, hCD_nn n]
  have hR1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 4 2 n
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
          fourTraceCyclePerm123)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 4 2 n
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 2
      (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁) fourTraceCyclePerm123 n x
  have hR2 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 4 2 n
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
          fourTraceSwap13Perm)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 4 2 n
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 2
      (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁) fourTraceSwap13Perm n x
  have hR3 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 4 2 n
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
          fourTraceDoubleTranspositionPerm)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 4 2 n
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 2
      (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁) fourTraceDoubleTranspositionPerm n x
  have hsec : (iteratedCovGrad (I := I) g₀ 4 2 n
      (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x =
      ((1 : ℝ) / 2) •
        ((iteratedCovGrad (I := I) g₀ 4 2 n
          (reindexCoeffGen (I := I) (M := M) g₀ 4 2
            (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
            fourTraceCyclePerm123)).toSection x
        + (iteratedCovGrad (I := I) g₀ 4 2 n
          (reindexCoeffGen (I := I) (M := M) g₀ 4 2
            (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
            fourTraceSwap13Perm)).toSection x
        - (iteratedCovGrad (I := I) g₀ 4 2 n
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)).toSection x
        - (iteratedCovGrad (I := I) g₀ 4 2 n
          (reindexCoeffGen (I := I) (M := M) g₀ 4 2
            (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
            fourTraceDoubleTranspositionPerm)).toSection x) := by
    rw [ricciCometricFourTraceCastG0_eq_reindex_combination (I := I) g₀ g₁,
      o0IteratedCovGrad_smul, iteratedCovGrad_sub, iteratedCovGrad_sub, iteratedCovGrad_add,
      SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  rw [hsec, o0Rfns_smul (I := I) (M := M) g₀ 4 (2 + n) x]
  have c12 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 4 (2 + n) x
    ((iteratedCovGrad (I := I) g₀ 4 2 n
      (reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
        fourTraceCyclePerm123)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 4 2 n
      (reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
        fourTraceSwap13Perm)).toSection x)
  have c3 := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 4 (2 + n) x
    ((iteratedCovGrad (I := I) g₀ 4 2 n
      (reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
        fourTraceCyclePerm123)).toSection x
    + (iteratedCovGrad (I := I) g₀ 4 2 n
      (reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
        fourTraceSwap13Perm)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 4 2 n
      (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)).toSection x)
  have c4 := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 4 (2 + n) x
    ((iteratedCovGrad (I := I) g₀ 4 2 n
      (reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
        fourTraceCyclePerm123)).toSection x
    + (iteratedCovGrad (I := I) g₀ 4 2 n
      (reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
        fourTraceSwap13Perm)).toSection x
    - (iteratedCovGrad (I := I) g₀ 4 2 n
      (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 4 2 n
      (reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
        fourTraceDoubleTranspositionPerm)).toSection x)
  rw [hR1, hR2] at c12
  rw [hR3] at c4
  have hgoal : 6 * (2 * SΦ n + 2 * CD n) *
      (∑ k ∈ Finset.range (n + 1), Combinatorics.antidiagonalTupleGrid b k) =
      6 * ((2 * SΦ n + 2 * CD n) *
        Combinatorics.antidiagonalTupleGridWindow b (n + 1)) := by
    rw [show (∑ k ∈ Finset.range (n + 1), Combinatorics.antidiagonalTupleGrid b k) =
        Combinatorics.antidiagonalTupleGridWindow b (n + 1) from rfl]
    ring
  rw [hgoal]
  have hpn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 (2 + n) x
    ((iteratedCovGrad (I := I) g₀ 4 2 n
      (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)).toSection x)
  nlinarith [c12, c3, c4, hpure, hpn]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
