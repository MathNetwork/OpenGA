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

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma bdDelta_nonneg (g₀ : SmoothRiemannianMetric I M) (x₀ : M)
    (P : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ) :
    0 ≤ δ := by
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
    have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
    exact mul_neg_of_neg_of_pos h1 hsqrt_pos
  linarith [le_trans habs_nn hbound]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
lemma bdNorm_zero_of_isEmpty [IsEmpty M] (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (V : SmoothCcTensor g₀ r s) : ‖V‖ = 0 := by
  rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
    MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]

def armPairTraceSlotPerm6 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![1, 3, 4, 5, 0, 2] : Fin 6 → Fin 6) i,
   fun i => (![4, 0, 5, 1, 2, 3] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma bdTensor0S_zero_rank_decomp (x : M) (t : Tensor0SSpace 0 I x) :
    t = (Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0)) • unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [show m = (fun i : Fin 0 => i.elim0 : Fin 0 → E) from by
    funext k
    exact k.elim0]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [show Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x)
      (fun i : Fin 0 => i.elim0) = 1 from by
    rw [unitTensor, Tensor0SSpace.toModel_ofModel]
    rfl]
  rw [smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma bdSlotExtendIter_two_toModel (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (x : M) (D : Tensor0SSpace 2 I x)
    (u : Fin 6 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1] *
        unitModel (I := I) (M := M) g₀ 4 X x (fun k : Fin 4 => u (Fin.natAdd 2 k)) := by
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 5 x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D)) from rfl]
  have hkey1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 5)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 5 x).symm
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D)))
    (v0 := u 0) (vs := Matrix.vecTail u)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey1
  rw [show (Fin.cons (u 0) (Matrix.vecTail u) : Fin 6 → TangentSpace I x) = u from by
    funext k
    refine Fin.cases rfl (fun i => rfl) k] at hkey1
  rw [← hkey1]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D) (u 0)) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 4 x).symm
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)))) from rfl]
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
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)))))
    (v0 := u 1) (vs := fun k : Fin 4 => u (Fin.natAdd 2 k))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey2
  rw [← hkey2]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0))) (u 1)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1)) from rfl]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1) with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![u 0, u 1] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (v0 := u 1)
      (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D) (v0 := u 0) (vs := Fin.cons (u 1) (fun i : Fin 0 => i.elim0))
    rw [h2]
    refine congrArg _ ?_
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    refine Fin.cases rfl (fun i2 => i2.elim0) i
  have hdecomp := bdTensor0S_zero_rank_decomp (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rfl

def cometricDoubleTraceCc (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g₀ (s + 2) s where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (s + 2) s I x from cometricDoubleTraceFib (I := I) g₁ s x)
      contMDiff_toFun := cometricDoubleTraceFib_contMDiff (I := I) g₁ s }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma bdToModel_cons_sum_smul (_x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 1) ℝ E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons (∑ c, t c • u c) rest) =
      ∑ c, t c * Zm (Fin.cons (u c) rest) := by
  classical
  have h1 : ∀ v : E, (Fin.cons v rest : Fin (n + 1) → E) =
      Function.update (Fin.cons (0 : E) rest) 0 v := by
    intro v
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons (0 : E) rest) 0 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons (0 : E) rest) 0 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

omit [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma bdToModel_cons_cons_sum_smul (_x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 2) ℝ E) (aa : E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons aa (Fin.cons (∑ c, t c • u c) rest)) =
      ∑ c, t c * Zm (Fin.cons aa (Fin.cons (u c) rest)) := by
  classical
  have h1 : ∀ v : E, (Fin.cons aa (Fin.cons v rest) : Fin (n + 2) → E) =
      Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 v := by
    intro v
    rw [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl]
    rw [← Fin.cons_update]
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma bdOrthoFrame_center_repr (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    v = ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x) v • smoothOrthoFrame (I := I) g x i x := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  have horth : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hlin : LinearIndependent ℝ B := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpair : g.inner x (∑ i, c i • B i) (B j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
    have hsimp : ∀ i, g.inner x (c i • B i) (B j) = c i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)] at hpair
    have hcol : (∑ i, c i * (if i = j then (1 : ℝ) else 0)) = c j := by simp
    rw [hcol] at hpair
    exact hpair
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  set bB : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard with hbB_def
  have hbB_coe : ∀ i, bB i = B i := by
    intro i
    rw [hbB_def]
    change (basisOfLinearIndependentOfCardEqFinrank hlin hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I x) i = B i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hrepr : ∀ (w : TangentSpace I x) (j : Fin (Module.finrank ℝ E)),
      bB.repr w j = g.inner x (B j) w := by
    intro w j
    conv_rhs => rw [← bB.sum_repr w]
    rw [map_sum]
    have hsimp : ∀ i, g.inner x (B j) (bB.repr w i • bB i) =
        bB.repr w i * (if j = i then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, smul_eq_mul, hbB_coe i, horth j i]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
    simp
  conv_lhs => rw [← bB.sum_repr v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hrepr v i, hbB_coe i]

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (metricComparisonEndo gInvRaisedEndo_apply
  gInvRaisedEndo_eq_diff_add_id inverseMetricSharpFib_g0FlatCLM cotangentToDual_g0FlatCLM
  g0FlatCLM) in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma bdG1_inner_gInvRaisedEndo_left (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g₁.inner x (metricComparisonEndo (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
  rw [gInvRaisedEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
  rw [show cotangentToDualLinear (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w from rfl]
  rw [cotangentToDual_g0FlatCLM]

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (metricComparisonEndo gInvRaisedEndo_apply
  inverseMetricSharpFib_g0FlatCLM g0FlatCLM) in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma bdPureDT_eq_trace_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M)
    (s : ℕ) :
    cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ s =
      ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro Z
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro mm
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ s).toSection x) Z) mm =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ s).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₁ s x Z from rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ s x Z]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) (Tensor0SSpace.toModel Z) mm]
  rw [hLHS]
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) mm =
      ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from metricComparisonEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₀ s x
          (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z) from by
      rw [appCcRS_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ s x]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z)) mm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [slotInsertEndoFib_apply_eval]
    rw [Fin.update_cons_zero]
    rfl
  rw [hRHS]
  have hGrep : ∀ a : Fin (Module.finrank ℝ E),
      (show E from metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x)) =
        ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)) •
            (smoothOrthoFrame (I := I) g₁ x c x : E) := by
    intro a
    have h1 := bdOrthoFrame_center_repr (I := I) (M := M) g₁ x
      (metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))
    rw [show (show E from metricComparisonEndo (I := I) g₀ g₁ x
        (smoothOrthoFrame (I := I) g₀ x a x)) =
        metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x) from rfl]
    conv_lhs => rw [h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x c x)
      (metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))]
    rw [bdG1_inner_gInvRaisedEndo_left (I := I) (M := M) g₀ g₁ x
      (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)]
  symm
  calc (∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from metricComparisonEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)))
      = ∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hGrep a]
        exact bdToModel_cons_sum_smul (E := E) x (Tensor0SSpace.toModel Z)
          (Module.finrank ℝ E)
          (fun c => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun c => (smoothOrthoFrame (I := I) g₁ x c x : E))
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)
    _ = ∑ c : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) :=
        Finset.sum_comm
    _ = ∑ c : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hsum := bdToModel_cons_cons_sum_smul (E := E) x (Tensor0SSpace.toModel Z)
          ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
          (Module.finrank ℝ E)
          (fun a => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun a => (smoothOrthoFrame (I := I) g₀ x a x : E)) mm
        rw [← hsum]
        congr 2
        have hrep0 := bdOrthoFrame_center_repr (I := I) (M := M) g₀ x
          (smoothOrthoFrame (I := I) g₁ x c x)
        rw [show (∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
              (smoothOrthoFrame (I := I) g₁ x c x) •
              (smoothOrthoFrame (I := I) g₀ x a x : E)) =
            ((∑ a : Fin (Module.finrank ℝ E),
              g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
                (smoothOrthoFrame (I := I) g₁ x c x) •
                smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) from rfl]
        rw [← hrep0]

def armPairTraceOpCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 6 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
    (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 2)
    (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma bdPairTraceOp_apply_toModel (g₀ gm : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (x : M) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ gm)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) v =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) gm x a x : E),
              (smoothOrthoFrame (I := I) gm x b x : E)] *
          unitModel (I := I) (M := M) g₀ 4 X x
            ![v 0, v 1, (smoothOrthoFrame (I := I) gm x a x : E),
              (smoothOrthoFrame (I := I) gm x b x : E)] := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 1, w 3] *
          unitModel (I := I) (M := M) g₀ 4 X x ![w 4, w 5, w 0, w 2] := by
    intro w
    rw [hY_def]
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
    rw [bdSlotExtendIter_two_toModel (I := I) (M := M) g₀ X x D
      (fun i => w (armPairTraceSlotPerm6 i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ gm)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) =
      cometricDoubleTraceFib (I := I) gm 2 x
        (cometricDoubleTraceFib (I := I) gm 4 x Y) from by
    rw [hY_def]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) gm 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) gm x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) gm x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) gm 4 x Y))
    (fun j => (v j : E))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cometricDoubleTraceFib_toModel (I := I) gm 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) gm x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) gm x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y)
    (Fin.cons ((smoothOrthoFrame (I := I) gm x b x : TangentSpace I x) : E)
      (Fin.cons ((smoothOrthoFrame (I := I) gm x b x : TangentSpace I x) : E)
        (fun j => (v j : E))))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hYval]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma bdSlotInsertEndoCc_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ s (A + B) =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ s A +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ s A +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x) =
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ s A).toSection x +
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (metricComparisonEndo gInvRaisedEndo_apply
  gInvRaisedEndo_eq_diff_add_id inverseMetricSharpFib_g0FlatCLM g0FlatCLM) in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma bdFullRaised_diff_split (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g₀ g₁ =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) =
      DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonDiffEndo (I := I) g₀ g₁ x
    from rfl]
  rw [fullRaisedEndoField_apply]
  rw [gInvRaisedEndo_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show metricComparisonEndo (I := I) g₀ g₀ x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (metricComparisonEndo gInvRaisedEndo_apply
  inverseMetricSharpFib_g0FlatCLM g0FlatCLM) in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma bdEndoCovDeriv_fullRaised_id_zero (g₀ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x v) (Y x) = 0 := by
  have hLeib := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (fullRaisedEndoField (I := I) (M := M) g₀ g₀) Y x v
  have hΛapp : (fun y : M => (fullRaisedEndoField (I := I) (M := M) g₀ g₀ y) (Y y)) =
      (fun y : M => Y y) := by
    funext y
    rw [fullRaisedEndoField_apply]
    rw [show metricComparisonEndo (I := I) g₀ g₀ y (Y y) = Y y from by
      rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [hLeib, hΛapp]
  rw [fullRaisedEndoField_apply]
  rw [show metricComparisonEndo (I := I) g₀ g₀ x
      ((LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v) =
      (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [sub_self]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdCovGrad_slotInsert_fullRaised_id_zero (g₀ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 1 1
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 1 1
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) x D m]
  rw [tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g₀ 0
    (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x (m 0)]
  rw [show ((endoCovariantDerivative (I := I) (M := M) g₀)
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x (m 0)) =
      (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from by
    apply ContinuousLinearMap.ext
    intro w
    rw [ContinuousLinearMap.zero_apply]
    obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x w
    rw [← hY]
    exact bdEndoCovDeriv_fullRaised_id_zero (I := I) (M := M) g₀ Y x (m 0)]
  rw [show slotInsertEndoFib (I := I) (M := M) (0 + 1) 0 x
        (0 : TangentSpace I x →L[ℝ] TangentSpace I x) = 0 from by
    rw [show (0 : TangentSpace I x →L[ℝ] TangentSpace I x) =
        (0 : ℝ) • (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from (zero_smul ℝ _).symm,
      slotInsertEndoFib_smul_left, zero_smul]]
  simp [SmoothCcTensor.toSection_zero]

omit [NeZero (Module.finrank ℝ E)] in
private lemma bdICG_slotInsert_fullRaised_id_succ_zero
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact bdCovGrad_slotInsert_fullRaised_id_zero (I := I) (M := M) g₀
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

private theorem fullRaisedEndoField_iteratedCovGrad_gridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ S : ℕ → ℝ, (∀ l, 0 ≤ S l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
          Combinatorics.antidiagonalTupleGrid
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) l * S l := by
  classical
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cid, hcid_nn, hcid⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 1 1
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₀))
  refine ⟨fun l => 2 * CD l + 2 * cid,
    fun l => by have := hCD_nn l; linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound l x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b l :=
    Combinatorics.antidiagonalTupleGrid_nonneg b hb l
  have hsplit : endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁) =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁) +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀) := by
    rw [bdFullRaised_diff_split (I := I) (M := M) g₀ g₁,
      bdSlotInsertEndoCc_add (I := I) (M := M) g₀ 0]
  rw [hsplit]
  refine le_trans (bdRfns_iCG_add_le (I := I) (M := M) g₀ 1 1 l _ _ x) ?_
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
      CD l * Combinatorics.antidiagonalTupleGrid b l := by
    refine le_trans (hCD g₁ T htie hδ_le hδ0 hbound l x) (le_of_eq ?_)
    rw [Combinatorics.antidiagonalTupleGrid]
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x) ≤
      cid * Combinatorics.antidiagonalTupleGrid b l := by
    match l with
    | 0 =>
        rw [iteratedCovGrad_zero]
        rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one]
        exact hcid x
    | (m + 1) =>
        rw [bdICG_slotInsert_fullRaised_id_succ_zero (I := I) (M := M) g₀ m]
        rw [bdRfns_zero_toSection]
        exact mul_nonneg hcid_nn
          (Combinatorics.antidiagonalTupleGrid_nonneg b hb (m + 1))
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x)
      ≤ 2 * (CD l * Combinatorics.antidiagonalTupleGrid b l) +
          2 * (cid * Combinatorics.antidiagonalTupleGrid b l) := by
        have h1 := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
        linarith
    _ = Combinatorics.antidiagonalTupleGrid b l * (2 * CD l + 2 * cid) := by ring

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (metricComparisonEndo gInvRaisedEndo_apply
  inverseMetricSharpFib_g0FlatCLM cotangentToDual_g0FlatCLM g0FlatCLM) in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma bdSlotInsertZero_fullRaisedRev_eq_omRecover
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₁ g₀) =
      omRecoverEndoCc (I := I) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₁ g₀)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (fullRaisedEndoField (I := I) (M := M) g₁ g₀ x) om from rfl]
  rw [bdCotangentToDual_slotInsertEndoFib (I := I) (M := M) x
    (fullRaisedEndoField (I := I) (M := M) g₁ g₀ x) om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (omRecoverEndoCc (I := I) g₀ g₁).toSection x) om =
      g0FlatCLM (I := I) g₁ x (inverseMetricSharpFib (I := I) g₀ x om) from by
    rw [omRecoverEndoCc_toSection]; rfl]
  rw [cotangentToDual_g0FlatCLM]
  rw [show (fullRaisedEndoField (I := I) (M := M) g₁ g₀ x) w =
      inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x w) from by
    rw [fullRaisedEndoField_apply, gInvRaisedEndo_apply]]
  rw [show cotangentToDual (I := I) om
        (inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x w)) =
      cotangentToDualLinear (I := I) (x := x) om
        (inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x w)) from rfl]
  rw [← inverseMetricSharpFib_inner (I := I) g₀ x om
    (inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x w))]
  rw [g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
    (inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x w))]
  rw [inverseMetricSharpFib_inner (I := I) g₀ x (g0FlatCLM (I := I) g₁ x w)
    (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [show cotangentToDualLinear (I := I) (x := x) (g0FlatCLM (I := I) g₁ x w)
        (inverseMetricSharpFib (I := I) g₀ x om) =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₁ x w)
        (inverseMetricSharpFib (I := I) g₀ x om) from rfl]
  rw [cotangentToDual_g0FlatCLM]
  rw [g₁.symm x w (inverseMetricSharpFib (I := I) g₀ x om)]

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (metricComparisonEndo gInvRaisedEndo_apply
  inverseMetricSharpFib_g0FlatCLM cotangentToDual_g0FlatCLM g0FlatCLM) in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma bdOmRecover_eq_idEndo_add_raise
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    omRecoverEndoCc (I := I) g₀ g₁ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀) +
        cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (ccTensor02Symm (I := I) (M := M) g₀ T) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  rw [show (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) +
        cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x =
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀)).toSection x +
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)).toSection x +
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x)) om =
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₀ g₀)).toSection x) om +
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) om from rfl]
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [show cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₀)).toSection x) om +
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) om) w =
      cotangentToDual (I := I)
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₀)).toSection x) om) w +
        cotangentToDual (I := I)
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) om) w from by
    rw [← cotangentToDualLinear_apply, ← cotangentToDualLinear_apply,
      ← cotangentToDualLinear_apply, map_add, LinearMap.add_apply]]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (omRecoverEndoCc (I := I) g₀ g₁).toSection x) om =
      g0FlatCLM (I := I) g₁ x (inverseMetricSharpFib (I := I) g₀ x om) from by
    rw [omRecoverEndoCc_toSection]; rfl]
  rw [cotangentToDual_g0FlatCLM]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀ x) om from rfl]
  rw [bdCotangentToDual_slotInsertEndoFib (I := I) (M := M) x
    (fullRaisedEndoField (I := I) (M := M) g₀ g₀ x) om w]
  rw [show (fullRaisedEndoField (I := I) (M := M) g₀ g₀ x) w = w from by
    rw [fullRaisedEndoField_apply, gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [show cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) om) w =
      ccTensorBilinSymm (I := I) g₀ T x (inverseMetricSharpFib (I := I) g₀ x om) w from by
    rw [cotangentToDual_apply]
    rw [cometricRaiseSlot0Field_toSection]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
                (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
              (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w) : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
                (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
              (unitTensor (I := I) (M := M) x)))
          (fun _ : Fin 1 => w) from rfl]
    rw [bdInterior_product_toModel_eval (I := I) (M := M) (0 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
          (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
        (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w)]
    rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
            (unitTensor (I := I) (M := M) x))
          (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
            (fun _ : Fin 1 => (show E from w))) =
        unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ T) x
          ![inverseMetricSharpFib (I := I) g₀ x om, w] from by
      rw [unitModel]
      congr 1
      funext k
      refine Fin.cases ?_ (fun j => ?_) k
      · simp only [Fin.cons_zero, Matrix.cons_val_zero]
      · simp only [Fin.cons_succ]
        fin_cases j
        rfl]
    rw [unitModel_eq_ccTensorBilin_local, ccTensorBilin_symmS]]
  rw [show cotangentToDual (I := I) om w =
      cotangentToDualLinear (I := I) (x := x) om w from rfl]
  rw [← inverseMetricSharpFib_inner (I := I) g₀ x om w]
  rw [g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om) w] at *
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₀ x om) w]
  rw [htie x w (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [g₀.symm x w (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [show ccTensorBilinSymm (I := I) g₀ T x w (inverseMetricSharpFib (I := I) g₀ x om) =
      ccTensorBilinSymm (I := I) g₀ T x (inverseMetricSharpFib (I := I) g₀ x om) w from by
    rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply]
    ring]

omit [NeZero (Module.finrank ℝ E)] in
lemma bdRfns_iCG_symmS_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x +
        (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 2 j
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x := by
    rw [iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ T j, SmoothCcTensor.toSection_add]
    rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j T).toSection +
        ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection) x =
        ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x +
          ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x from rfl]
    rw [SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_smul]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + j) x _ _) ?_
  rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (2 + j) x,
    riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (2 + j) x]
  have hperm := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) T j x
  rw [hperm]
  ring_nf
  nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_symmS_le_of_gFibreOpBound (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 0 2 x
    ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) e bse hnE hbse horth]
  have hcof : coframeS (I := I) (M := M) g₀ x 0 e = fun _ : Fin 0 → Fin n =>
      unitTensor (I := I) (M := M) x := by
    funext K
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [show Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 0 e K) v =
        coframeS (I := I) (M := M) g₀ x 0 e K v from rfl]
    rw [coframeS_apply (I := I) (M := M) g₀ x 0 e K v]
    rw [show Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) v =
        unitTensor (I := I) (M := M) x v from rfl]
    rw [Fin.prod_univ_zero]
    rw [unitTensor, Tensor0SSpace.ofModel]
    rfl
  have hcomp : ∀ (K : Fin 0 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2 ≤ δ ^ 2 := by
    intro K J
    have hval : fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) n e K J =
        ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)) := by
      rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) n e K J =
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
              (coframeS (I := I) (M := M) g₀ x 0 e K))
            (fun i : Fin 2 => (e (J i) : E)) from rfl]
      rw [hcof]
      rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
            (unitTensor (I := I) (M := M) x))
          (fun i : Fin 2 => (e (J i) : E)) =
          unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ T) x
            ![e (J 0), e (J 1)] from by
        rw [unitModel]
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T) x (e (J 0)) (e (J 1))]
      rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T x (e (J 0)) (e (J 1))]
    rw [hval]
    have habs := hbound x (e (J 0)) (e (J 1))
    have h00 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by
      rw [horth (J 0) (J 0), if_pos rfl]
    have h11 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by
      rw [horth (J 1) (J 1), if_pos rfl]
    rw [h00, h11, Real.sqrt_one, mul_one, mul_one] at habs
    have := abs_nonneg (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))
    nlinarith [habs, sq_abs (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))]
  calc (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2)
      ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, δ ^ 2 :=
        Finset.sum_le_sum fun K _ => Finset.sum_le_sum fun J _ => hcomp K J
    _ = (Fintype.card (Fin 0 → Fin n) : ℝ) * ((Fintype.card (Fin 2 → Fin n) : ℝ) * δ ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
        have hc0 : (Fintype.card (Fin 0 → Fin n) : ℝ) = 1 := by
          simp
        have hc2 : (Fintype.card (Fin 2 → Fin n) : ℝ) = (n : ℝ) ^ 2 := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring
        rw [hc0, hc2, one_mul, hnE]

omit [NeZero (Module.finrank ℝ E)] in
theorem bdOmRecover_gridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (_hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ l, 0 ≤ C l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l
              (omRecoverEndoCc (I := I) g₀ g₁)).toSection x) ≤
          C l * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) (l + 1) := by
  classical
  obtain ⟨cid, hcid_nn, hcid⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 1 1
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₀))
  refine ⟨fun l => 2 * cid + 2 * ((Module.finrank ℝ E : ℝ) ^ 2 * (max δ₀ 0) ^ 2) + 2,
    fun l => by positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound l x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hW1 : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (l + 1) :=
    Combinatorics.one_le_antidiagonalTupleGridWindow b hb (by omega)
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (l + 1) := by linarith
  rw [bdOmRecover_eq_idEndo_add_raise (I := I) (M := M) g₀ g₁ T htie]
  refine le_trans (bdRfns_iCG_add_le (I := I) (M := M) g₀ 1 1 l _ _ x) ?_
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x) ≤ cid := by
    match l with
    | 0 =>
        rw [iteratedCovGrad_zero]
        exact hcid x
    | (m + 1) =>
        rw [bdICG_slotInsert_fullRaised_id_succ_zero (I := I) (M := M) g₀ m]
        rw [bdRfns_zero_toSection]
        exact hcid_nn
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ T))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * (max δ₀ 0) ^ 2 +
        Combinatorics.antidiagonalTupleGridWindow b (l + 1) := by
    rw [riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
      (ccTensor02Symm (I := I) (M := M) g₀ T) l x]
    match l with
    | 0 =>
        have h1 := riemannianFiberNormSq_symmS_le_of_gFibreOpBound (I := I) (M := M) g₀ T hδ0 hbound x
        have hδle : δ ^ 2 ≤ (max δ₀ 0) ^ 2 := by
          have h2 : δ ≤ max δ₀ 0 := le_trans hδ_le (le_max_left _ _)
          nlinarith [hδ0]
        have h3 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤
            (Module.finrank ℝ E : ℝ) ^ 2 * (max δ₀ 0) ^ 2 := by
          rw [iteratedCovGrad_zero]
          refine le_trans h1 ?_
          have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 := by positivity
          nlinarith [hδle, hfr]
        linarith [h3, hW_nn]
    | (m + 1) =>
        have h1 := bdRfns_iCG_symmS_le (I := I) (M := M) g₀ T (m + 1) x
        have h2 : b (m + 1) ≤ Combinatorics.antidiagonalTupleGridWindow b (m + 1 + 1) := by
          have h3 : b (m + 1) * Combinatorics.antidiagonalTupleGrid b 0 ≤
              Combinatorics.antidiagonalTupleGrid b (0 + (m + 1)) :=
            Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb 0 (m + 1)
              (by omega)
          rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h3
          refine le_trans h3 ?_
          rw [show 0 + (m + 1) = m + 1 from by omega]
          exact Combinatorics.antidiagonalTupleGrid_le_window b hb (by omega)
        have hnn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (max δ₀ 0) ^ 2 := by positivity
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (m + 1)
                (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x)
            ≤ b (m + 1) := h1
          _ ≤ Combinatorics.antidiagonalTupleGridWindow b (m + 1 + 1) := h2
          _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (max δ₀ 0) ^ 2 +
              Combinatorics.antidiagonalTupleGridWindow b (m + 1 + 1) := by linarith
  have hfrδ_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (max δ₀ 0) ^ 2 := by positivity
  have hstep : 2 * cid + 2 * ((Module.finrank ℝ E : ℝ) ^ 2 * (max δ₀ 0) ^ 2) +
      2 * Combinatorics.antidiagonalTupleGridWindow b (l + 1) ≤
      (2 * cid + 2 * ((Module.finrank ℝ E : ℝ) ^ 2 * (max δ₀ 0) ^ 2) + 2) *
        Combinatorics.antidiagonalTupleGridWindow b (l + 1) := by
    nlinarith [hW1, hcid_nn, hfrδ_nn]
  linarith [hA, hB, hstep]

private theorem bdLambdaSlotInsert3_gridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ l, 0 ≤ C l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 4 4 l
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
                (fullRaisedEndoField (I := I) (M := M) g₁ g₀))).toSection x) ≤
          C l * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) (l + 1) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := bdOmRecover_gridWindow (I := I) (M := M) g₀ hδ₀
  refine ⟨fun l => (Module.finrank ℝ E : ℝ) ^ 3 * C l,
    fun l => mul_nonneg (by positivity) (hC_nn l), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound l x
  refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 3
    (fullRaisedEndoField (I := I) (M := M) g₁ g₀) l x) ?_
  rw [bdSlotInsertZero_fullRaisedRev_eq_omRecover (I := I) (M := M) g₀ g₁]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC g₁ T htie hδ_le hδ0 hbound l x) (by positivity)

def connDiffEndo (g₀ gc : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => PDE.DeTurck.connDiff (I := I) gc g₀ x,
    bilinEndoField_contMDiff (I := I) (M := M)
      (fun x : M => PDE.DeTurck.connDiff (I := I) gc g₀ x)
      (fun V0 W => PDE.DeTurck.connDiff_contMDiff (I := I) gc g₀ V0.contMDiff W.contMDiff)⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma bdConnPair_apply (g₀ gc : SmoothRiemannianMetric I M) (x : M) :
    connDiffEndo (I := I) (M := M) g₀ gc x = PDE.DeTurck.connDiff (I := I) gc g₀ x := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma bdConnDiffSection_eq_armSlotEndoCc_zero (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g₁ g₀ =
      armSlotEndoCc (I := I) (M := M) g₀ 0 (connDiffEndo (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (armSlotEndoCc (I := I) (M := M) g₀ 0
          (connDiffEndo (I := I) (M := M) g₀ g₁)).toSection x) om) =
      bilinearSlotInsertCLM (I := I) (M := M) 0 x (connDiffEndo (I := I) (M := M) g₀ g₁ x) om
      from rfl]
  rw [armSlotFib_apply_eval (I := I) (M := M) 0 x
    (connDiffEndo (I := I) (M := M) g₀ g₁ x) om v]
  rw [slotInsertEndoFib_apply_eval]
  rw [show (Function.update (Matrix.vecTail (fun k : Fin 2 => (v k : E))) 0
        (connDiffEndo (I := I) (M := M) g₀ g₁ x (v 0)
          (Matrix.vecTail (fun k : Fin 2 => (v k : E)) 0))) =
      (fun _ : Fin 1 => (show E from
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) (v 1))) from by
    funext k
    rw [show k = (0 : Fin 1) from Subsingleton.elim k 0]
    rw [Function.update_self]
    rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffSection (I := I) g₁ g₀).toSection x) om) =
      connDiffPairing (I := I) g₁ g₀ x om from rfl]
  change connDiffPairing (I := I) g₁ g₀ x om v = _
  rw [connDiffPairing_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma bdArmSlotEndoCc_one_eq_reindex_slotExtend (g₀ : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    armSlotEndoCc (I := I) (M := M) g₀ 1 Arm =
      reindexCoeffGen (I := I) (M := M) g₀ 2 3
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
          (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
        (Equiv.swap (0 : Fin 2) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hτ0 : (finRotate 3).symm (0 : Fin 3) = (2 : Fin 3) := by decide
  have hτ1 : (finRotate 3).symm (1 : Fin 3) = (0 : Fin 3) := by decide
  have hτ2 : (finRotate 3).symm (2 : Fin 3) = (1 : Fin 3) := by decide
  set D' : Tensor0SSpace 2 I x := Tensor0SSpace.ofModel
    (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
      (Tensor0SSpace.toModel D)) with hD'_def
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm).toSection x) D) w =
      Tensor0SSpace.toModel D
        (Function.update (Matrix.vecTail w) 0 (Arm x (w 0) (Matrix.vecTail w 0))) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm).toSection x) D) =
        bilinearSlotInsertCLM (I := I) (M := M) 1 x (Arm x) D from rfl]
    rw [armSlotFib_apply_eval (I := I) (M := M) 1 x (Arm x) D w]
    rw [slotInsertEndoFib_apply_eval]
  have e1 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 3
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) w =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          tensorRS_domDomCongr (finRotate 3).symm
            ((slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') w := by
    have h1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 3
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          tensorRS_domDomCongr (finRotate 3).symm
            ((slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') := by
      rw [reindexCoeffGen_toSection]
      rw [reindexCoeffFibGen_apply (I := I) 2 3 (Equiv.swap (0 : Fin 2) 1) x
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm))).toSection x) D]
      rw [← hD'_def]
      rw [rsDomDomCongrSection_toSection]
    exact congrArg (fun t : Tensor0SSpace 3 I x => Tensor0SSpace.toModel t w) h1
  have e2 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        tensorRS_domDomCongr (finRotate 3).symm
          ((slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') w =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D')
        (fun i => w ((finRotate 3).symm i)) := by
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (finRotate 3).symm
      ((slotExtend (I := I) (M := M) g₀ 1 2
        (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D']
    rw [ContinuousMultilinearMap.domDomCongr_apply]
  have e3 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (slotExtend (I := I) (M := M) g₀ 1 2
          (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D')
      (fun i => w ((finRotate 3).symm i)) =
      Tensor0SSpace.toModel
        (bilinearSlotInsertCLM (I := I) (M := M) 0 x (Arm x)
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0))))
        (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D') =
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x).symm
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm).toSection x).comp
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D')) from rfl]
    rw [show (fun i => w ((finRotate 3).symm i)) =
        Fin.cons (w ((finRotate 3).symm 0))
          (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) from by
      funext k
      refine Fin.cases rfl (fun j => rfl) k]
    have hkey := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2)
      (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D')))
      (v0 := w ((finRotate 3).symm 0))
      (vs := Matrix.vecTail (fun i => w ((finRotate 3).symm i)))
    rw [ContinuousLinearEquiv.apply_symm_apply] at hkey
    rw [← hkey]
    rfl
  have e4 : Tensor0SSpace.toModel
      (bilinearSlotInsertCLM (I := I) (M := M) 0 x (Arm x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0))))
      (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
        (fun _ : Fin 1 => (show E from
          Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2)))) := by
    rw [armSlotFib_apply_eval (I := I) (M := M) 0 x (Arm x)
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
      (Matrix.vecTail (fun i => w ((finRotate 3).symm i)))]
    rw [slotInsertEndoFib_apply_eval]
    congr 1
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [Function.update_self]
    rfl
  have e5 : Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
      (fun _ : Fin 1 => (show E from
        Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2)))) =
      Tensor0SSpace.toModel D'
        (Fin.cons (w ((finRotate 3).symm 0))
          (fun _ : Fin 1 => (show E from
            Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))) :=
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D') (v0 := w ((finRotate 3).symm 0))
      (vs := fun _ : Fin 1 => (show E from
        Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))
  have e6 : Tensor0SSpace.toModel D'
      (Fin.cons (w ((finRotate 3).symm 0))
        (fun _ : Fin 1 => (show E from
          Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))) =
      Tensor0SSpace.toModel D
        (Function.update (Matrix.vecTail w) 0 (Arm x (w 0) (Matrix.vecTail w 0))) := by
    rw [hD'_def, Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [hτ0, hτ1, hτ2]
    congr 1
    funext k
    refine Fin.cases ?_ ?_ k
    · rw [show (Function.update (Matrix.vecTail w) 0
            (Arm x (w 0) (Matrix.vecTail w 0)) (0 : Fin 2)) =
          Arm x (w 0) (Matrix.vecTail w 0) from Function.update_self _ _ _]
      rfl
    · intro j
      refine Fin.cases ?_ (fun j2 => j2.elim0) j
      rw [show (Fin.succ (0 : Fin 1)) = (1 : Fin 2) from rfl]
      rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      rfl
  rw [hLHS, e1, e2, e3, e4, e5, e6]

private def armSlotEndoCcReindexPerm4 : Equiv.Perm (Fin 4) :=
  ⟨fun i => (![2, 0, 1, 3] : Fin 4 → Fin 4) i,
   fun i => (![1, 2, 0, 3] : Fin 4 → Fin 4) i,
   by decide, by decide⟩

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma bdArmSlotEndoCc_two_eq_reindex_slotExtend (g₀ : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    armSlotEndoCc (I := I) (M := M) g₀ 2 Arm =
      reindexCoeffGen (I := I) (M := M) g₀ 3 4
        (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 armSlotEndoCcReindexPerm4
          (slotExtend (I := I) (M := M) g₀ 2 3 (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm)))
        (Equiv.swap (0 : Fin 3) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hτ0 : armSlotEndoCcReindexPerm4 (0 : Fin 4) = (2 : Fin 4) := by decide
  have hτ1 : armSlotEndoCcReindexPerm4 (1 : Fin 4) = (0 : Fin 4) := by decide
  have hτ2 : armSlotEndoCcReindexPerm4 (2 : Fin 4) = (1 : Fin 4) := by decide
  have hτ3 : armSlotEndoCcReindexPerm4 (3 : Fin 4) = (3 : Fin 4) := by decide
  set D' : Tensor0SSpace 3 I x := Tensor0SSpace.ofModel
    (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 3) 1)
      (Tensor0SSpace.toModel D)) with hD'_def
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 4 I x from
        (armSlotEndoCc (I := I) (M := M) g₀ 2 Arm).toSection x) D) w =
      Tensor0SSpace.toModel D
        (Function.update (Matrix.vecTail w) 0 (Arm x (w 0) (Matrix.vecTail w 0))) := by
    rw [show ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 4 I x from
          (armSlotEndoCc (I := I) (M := M) g₀ 2 Arm).toSection x) D) =
        bilinearSlotInsertCLM (I := I) (M := M) 2 x (Arm x) D from rfl]
    rw [armSlotFib_apply_eval (I := I) (M := M) 2 x (Arm x) D w]
    rw [slotInsertEndoFib_apply_eval]
  have e1 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 4 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 3 4
          (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 armSlotEndoCcReindexPerm4
            (slotExtend (I := I) (M := M) g₀ 2 3 (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm)))
          (Equiv.swap (0 : Fin 3) 1)).toSection x) D) w =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 4 I x from
          tensorRS_domDomCongr armSlotEndoCcReindexPerm4
            ((slotExtend (I := I) (M := M) g₀ 2 3
              (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm)).toSection x)) D') w := by
    have h1 : ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 4 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 3 4
          (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 armSlotEndoCcReindexPerm4
            (slotExtend (I := I) (M := M) g₀ 2 3 (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm)))
          (Equiv.swap (0 : Fin 3) 1)).toSection x) D) =
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 4 I x from
          tensorRS_domDomCongr armSlotEndoCcReindexPerm4
            ((slotExtend (I := I) (M := M) g₀ 2 3
              (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm)).toSection x)) D') := by
      rw [reindexCoeffGen_toSection]
      rw [reindexCoeffFibGen_apply (I := I) 3 4 (Equiv.swap (0 : Fin 3) 1) x
        (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 4 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 armSlotEndoCcReindexPerm4
            (slotExtend (I := I) (M := M) g₀ 2 3
              (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm))).toSection x) D]
      rw [← hD'_def]
      rw [rsDomDomCongrSection_toSection]
    exact congrArg (fun t : Tensor0SSpace 4 I x => Tensor0SSpace.toModel t w) h1
  have e2 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 4 I x from
        tensorRS_domDomCongr armSlotEndoCcReindexPerm4
          ((slotExtend (I := I) (M := M) g₀ 2 3
            (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm)).toSection x)) D') w =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtend (I := I) (M := M) g₀ 2 3
            (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm)).toSection x) D')
        (fun i => w (armSlotEndoCcReindexPerm4 i)) := by
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) armSlotEndoCcReindexPerm4
      ((slotExtend (I := I) (M := M) g₀ 2 3
        (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm)).toSection x) D']
    rw [ContinuousMultilinearMap.domDomCongr_apply]
  have e3 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtend (I := I) (M := M) g₀ 2 3
          (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm)).toSection x) D')
      (fun i => w (armSlotEndoCcReindexPerm4 i)) =
      Tensor0SSpace.toModel
        (bilinearSlotInsertCLM (I := I) (M := M) 1 x (Arm x)
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D' (w (armSlotEndoCcReindexPerm4 0))))
        (Matrix.vecTail (fun i => w (armSlotEndoCcReindexPerm4 i))) := by
    rw [show ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtend (I := I) (M := M) g₀ 2 3
            (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm)).toSection x) D') =
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x).symm
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
              (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm).toSection x).comp
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D')) from rfl]
    rw [show (fun i => w (armSlotEndoCcReindexPerm4 i)) =
        Fin.cons (w (armSlotEndoCcReindexPerm4 0))
          (Matrix.vecTail (fun i => w (armSlotEndoCcReindexPerm4 i))) from by
      funext k
      refine Fin.cases rfl (fun j => rfl) k]
    have hkey := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 3)
      (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x).symm
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
            (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D')))
      (v0 := w (armSlotEndoCcReindexPerm4 0))
      (vs := Matrix.vecTail (fun i => w (armSlotEndoCcReindexPerm4 i)))
    rw [ContinuousLinearEquiv.apply_symm_apply] at hkey
    rw [← hkey]
    rfl
  have e4 : Tensor0SSpace.toModel
      (bilinearSlotInsertCLM (I := I) (M := M) 1 x (Arm x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D' (w (armSlotEndoCcReindexPerm4 0))))
      (Matrix.vecTail (fun i => w (armSlotEndoCcReindexPerm4 i))) =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D' (w (armSlotEndoCcReindexPerm4 0)))
        (Function.update (Matrix.vecTail (Matrix.vecTail (fun i => w (armSlotEndoCcReindexPerm4 i)))) 0
          (Arm x (w (armSlotEndoCcReindexPerm4 1)) (w (armSlotEndoCcReindexPerm4 2)))) := by
    rw [armSlotFib_apply_eval (I := I) (M := M) 1 x (Arm x)
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D' (w (armSlotEndoCcReindexPerm4 0)))
      (Matrix.vecTail (fun i => w (armSlotEndoCcReindexPerm4 i)))]
    rw [slotInsertEndoFib_apply_eval]
    rfl
  have e5 : Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D' (w (armSlotEndoCcReindexPerm4 0)))
      (Function.update (Matrix.vecTail (Matrix.vecTail (fun i => w (armSlotEndoCcReindexPerm4 i)))) 0
        (Arm x (w (armSlotEndoCcReindexPerm4 1)) (w (armSlotEndoCcReindexPerm4 2)))) =
      Tensor0SSpace.toModel D'
        (Fin.cons (w (armSlotEndoCcReindexPerm4 0))
          (Function.update (Matrix.vecTail (Matrix.vecTail (fun i => w (armSlotEndoCcReindexPerm4 i)))) 0
            (Arm x (w (armSlotEndoCcReindexPerm4 1)) (w (armSlotEndoCcReindexPerm4 2))))) :=
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2)
      (T := D') (v0 := w (armSlotEndoCcReindexPerm4 0))
      (vs := Function.update (Matrix.vecTail (Matrix.vecTail (fun i => w (armSlotEndoCcReindexPerm4 i)))) 0
        (Arm x (w (armSlotEndoCcReindexPerm4 1)) (w (armSlotEndoCcReindexPerm4 2))))
  have e6 : Tensor0SSpace.toModel D'
      (Fin.cons (w (armSlotEndoCcReindexPerm4 0))
        (Function.update (Matrix.vecTail (Matrix.vecTail (fun i => w (armSlotEndoCcReindexPerm4 i)))) 0
          (Arm x (w (armSlotEndoCcReindexPerm4 1)) (w (armSlotEndoCcReindexPerm4 2))))) =
      Tensor0SSpace.toModel D
        (Function.update (Matrix.vecTail w) 0 (Arm x (w 0) (Matrix.vecTail w 0))) := by
    rw [hD'_def, Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext k
    fin_cases k
    · change ((Arm x) (w (armSlotEndoCcReindexPerm4 1))) (w (armSlotEndoCcReindexPerm4 2)) =
        Function.update (Matrix.vecTail w) 0
          (((Arm x) (w 0)) (Matrix.vecTail w 0)) (0 : Fin 3)
      rw [Function.update_self, hτ1, hτ2]
      rfl
    · change w (armSlotEndoCcReindexPerm4 0) =
        Function.update (Matrix.vecTail w) 0
          (((Arm x) (w 0)) (Matrix.vecTail w 0)) (1 : Fin 3)
      rw [hτ0, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]
      rfl
    · change w (armSlotEndoCcReindexPerm4 3) =
        Function.update (Matrix.vecTail w) 0
          (((Arm x) (w 0)) (Matrix.vecTail w 0)) (2 : Fin 3)
      rw [hτ3, Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
      rfl
  rw [hLHS, e1, e2, e3, e4, e5, e6]

lemma bdArmSlot2_rfns_le (g₀ g₁ : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + j) x
        ((iteratedCovGrad (I := I) g₀ 3 4 j
          (armSlotEndoCc (I := I) (M := M) g₀ 2
            (connDiffEndo (I := I) (M := M) g₀ g₁))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  rw [bdArmSlotEndoCc_two_eq_reindex_slotExtend (I := I) (M := M) g₀
    (connDiffEndo (I := I) (M := M) g₀ g₁)]
  rw [rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 3 4
    (Equiv.swap (0 : Fin 3) 1) armSlotEndoCcReindexPerm4
    (slotExtend (I := I) (M := M) g₀ 2 3
      (armSlotEndoCc (I := I) (M := M) g₀ 1 (connDiffEndo (I := I) (M := M) g₀ g₁))) j x]
  refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 3
    (armSlotEndoCc (I := I) (M := M) g₀ 1 (connDiffEndo (I := I) (M := M) g₀ g₁)) j x) ?_
  rw [pow_two, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [bdArmSlotEndoCc_one_eq_reindex_slotExtend (I := I) (M := M) g₀
    (connDiffEndo (I := I) (M := M) g₀ g₁)]
  rw [rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 3
    (Equiv.swap (0 : Fin 2) 1) (finRotate 3).symm
    (slotExtend (I := I) (M := M) g₀ 1 2
      (armSlotEndoCc (I := I) (M := M) g₀ 0 (connDiffEndo (I := I) (M := M) g₀ g₁))) j x]
  refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
    (armSlotEndoCc (I := I) (M := M) g₀ 0 (connDiffEndo (I := I) (M := M) g₀ g₁)) j x) ?_
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (Nat.cast_nonneg _)
  rw [← bdConnDiffSection_eq_armSlotEndoCc_zero (I := I) (M := M) g₀ g₁]

private noncomputable def bdKernelCLM (gA gB : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => connDiffCovDerivOp (I := I) gA gB x v0
      map_add' := fun v0 v0' => by
        apply ContinuousLinearMap.ext
        intro p
        apply ContinuousLinearMap.ext
        intro q
        simp only [ContinuousLinearMap.add_apply]
        exact dLaCovKernel_add_left (I := I) gA gB x v0 v0' p q
      map_smul' := fun c v0 => by
        apply ContinuousLinearMap.ext
        intro p
        apply ContinuousLinearMap.ext
        intro q
        simp only [RingHom.id_apply, ContinuousLinearMap.smul_apply]
        exact dLaCovKernel_smul_left (I := I) gA gB x c v0 p q }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdKernelCLM_apply (gA gB : SmoothRiemannianMetric I M) (x : M)
    (v0 p q : TangentSpace I x) :
    bdKernelCLM (I := I) (M := M) gA gB x v0 p q =
      connDiffCovDerivOp (I := I) gA gB x v0 p q := by
  rw [bdKernelCLM, LinearMap.coe_toContinuousLinearMap']
  rfl

private noncomputable def bdFixLoweredCovec (g₀ gA gB : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 4 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ from
    { toFun := fun m =>
        g₀.inner x (bdKernelCLM (I := I) (M := M) gA gB x (m 1) (m 2) (m 3)) (m 0)
      map_update_add' := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h10 : (1 : Fin 4) ≠ 0 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h20 : (2 : Fin 4) ≠ 0 := by decide
        have h21 : (2 : Fin 4) ≠ 1 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32,
            not_false_eq_true, map_add, ContinuousLinearMap.add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h10 : (1 : Fin 4) ≠ 0 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h20 : (2 : Fin 4) ≠ 0 := by decide
        have h21 : (2 : Fin 4) ≠ 1 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32,
            not_false_eq_true, map_smul, ContinuousLinearMap.smul_apply]
      cont := by
        have hK : Continuous (fun m : Fin 4 → TangentSpace I x =>
            bdKernelCLM (I := I) (M := M) gA gB x (m 1) (m 2) (m 3)) :=
          (((bdKernelCLM (I := I) (M := M) gA gB x).continuous.comp
            (continuous_apply 1)).clm_apply (continuous_apply 2)).clm_apply (continuous_apply 3)
        exact ((g₀.inner x).continuous.comp hK).clm_apply (continuous_apply 0) }
    : Tensor0SSpace 4 I x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdFixLoweredCovec_apply (g₀ gA gB : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    bdFixLoweredCovec (I := I) g₀ gA gB x m =
      g₀.inner x (connDiffCovDerivOp (I := I) gA gB x (m 1) (m 2) (m 3)) (m 0) := by
  change g₀.inner x (bdKernelCLM (I := I) (M := M) gA gB x (m 1) (m 2) (m 3)) (m 0) = _
  rw [bdKernelCLM_apply]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdFixLoweredScalar_global (g₀ gA gB : SmoothRiemannianMetric I M)
    {V0 W p q : Π b : M, TangentSpace I b}
    (hV0 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V0))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (connDiffCovDerivOp (I := I) gA gB x (V0 x) (p x) (q x)) (W x)) := by
  classical
  have hAsec := deTurckLieCovDerivA_section_contMDiff (I := I) gA gB V0 p q hV0 hp hq
  have hcongr : (fun x : M => g₀.inner x
        (connDiffCovDerivOp (I := I) gA gB x (V0 x) (p x) (q x)) (W x)) =
      (fun x : M => g₀.inner x (deTurckConnDiffCovDeriv (I := I) gA gB V0 p q x) (W x)) := by
    funext x
    rw [dLaCovKernel_apply_field3 (I := I) gA gB x V0 p q
      (hV0.contMDiffAt.mdifferentiableAt (by simp))
      (hp.contMDiffAt.mdifferentiableAt (by simp))
      (hq.contMDiffAt.mdifferentiableAt (by simp))]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₀
    ⟨fun b => deTurckConnDiffCovDeriv (I := I) gA gB V0 p q b, hAsec⟩ ⟨fun b => W b, hW⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdFixLoweredScalar_contMDiffAt (g₀ gA gB : SmoothRiemannianMetric I M)
    (V0 V1 V2 V3 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        g₀.inner x (connDiffCovDerivOp (I := I) gA gB x (V1 x) (V2 x) (V3 x)) (V0 x)) x₀ := by
  have hglob := bdFixLoweredScalar_global (I := I) (M := M) g₀ gA gB
    (V0 := fun b => V1 b) (W := fun b => V0 b) (p := fun b => V2 b) (q := fun b => V3 b)
    V1.contMDiff V0.contMDiff V2.contMDiff V3.contMDiff
  exact hglob.contMDiffAt

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem bdFixLoweredCovec_section_contMDiff (g₀ gA gB : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) x
        (bdFixLoweredCovec (I := I) g₀ gA gB x)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (bdFixLoweredCovec (I := I) g₀ gA gB x :
        Bundle.continuousMultilinearMap ℝ 4 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (connDiffCovDerivOp (I := I) gA gB x (Y (σ 1) x) (Y (σ 2) x) (Y (σ 3) x))
        (Y (σ 0) x)) x₀ :=
    bdFixLoweredScalar_contMDiffAt (I := I) (M := M) g₀ gA gB
      (Y (σ 0)) (Y (σ 1)) (Y (σ 2)) (Y (σ 3)) x₀
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframeEq : ∀ k : Fin 4, e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
    intro k
    rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change bdFixLoweredCovec (I := I) g₀ gA gB x (fun k => e₁.symmL ℝ x (b (σ k))) = _
  rw [bdFixLoweredCovec_apply]
  rw [hframeEq 0, hframeEq 1, hframeEq 2, hframeEq 3]

private def bdFixLoweredField (g₀ gA gB : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 4 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  ⟨fun x => bdFixLoweredCovec (I := I) g₀ gA gB x,
    bdFixLoweredCovec_section_contMDiff (I := I) (M := M) g₀ gA gB⟩

private def bdFixLoweredCc (g₀ gA gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 4 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (bdFixLoweredField (I := I) (M := M) g₀ gA gB)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdFixLoweredCc_unitModel (g₀ gA gB : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 4 (bdFixLoweredCc (I := I) (M := M) g₀ gA gB) x =
      Tensor0SSpace.toModel (bdFixLoweredCovec (I := I) g₀ gA gB x) := by
  rw [unitModel]
  rw [show (bdFixLoweredCc (I := I) (M := M) g₀ gA gB).toSection x
        (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (bdFixLoweredField (I := I) (M := M) g₀ gA gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdFixLoweredCc_unitModel_apply (g₀ gA gB : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (bdFixLoweredCc (I := I) (M := M) g₀ gA gB) x m =
      g₀.inner x (connDiffCovDerivOp (I := I) gA gB x (m 1) (m 2) (m 3)) (m 0) := by
  rw [bdFixLoweredCc_unitModel]
  exact bdFixLoweredCovec_apply (I := I) (M := M) g₀ gA gB x m

private def connDiffQuadraticLoweredCc (g₀ gArm gOut : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
    (armSlotEndoCc (I := I) (M := M) g₀ 2 (connDiffEndo (I := I) (M := M) g₀ gArm))
    (connDiffLoweredCc (I := I) g₀ gOut)

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma bdQuadLowCc_unitModel_apply (g₀ gArm gOut : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ gArm gOut) x m =
      g₀.inner x
        (PDE.DeTurck.connDiff (I := I) gOut g₀ x
          (PDE.DeTurck.connDiff (I := I) gArm g₀ x (m 0) (m 1)) (m 2)) (m 3) := by
  rw [unitModel]
  rw [show (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ gArm gOut).toSection x
        (unitTensor (I := I) (M := M) x) =
      bilinearSlotInsertCLM (I := I) (M := M) 2 x (connDiffEndo (I := I) (M := M) g₀ gArm x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (connDiffLoweredCc (I := I) g₀ gOut).toSection x)
          (unitTensor (I := I) (M := M) x)) from by
    rw [connDiffQuadraticLoweredCc, appCcRS_toSection]
    rfl]
  rw [armSlotFib_apply_eval (I := I) (M := M) 2 x
    (connDiffEndo (I := I) (M := M) g₀ gArm x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (connDiffLoweredCc (I := I) g₀ gOut).toSection x)
      (unitTensor (I := I) (M := M) x)) m]
  rw [slotInsertEndoFib_apply_eval]
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (connDiffLoweredCc (I := I) g₀ gOut).toSection x)
          (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ gOut) x from rfl]
  rw [show (Function.update (Matrix.vecTail m) 0
        (connDiffEndo (I := I) (M := M) g₀ gArm x (m 0) (Matrix.vecTail m 0))) =
      (![(show TangentSpace I x from
          PDE.DeTurck.connDiff (I := I) gArm g₀ x (m 0) (m 1)), m 2, m 3] :
        Fin 3 → TangentSpace I x) from by
    funext k
    fin_cases k
    · change Function.update (Matrix.vecTail m) 0
          (connDiffEndo (I := I) (M := M) g₀ gArm x (m 0) (Matrix.vecTail m 0)) (0 : Fin 3) =
        (show TangentSpace I x from PDE.DeTurck.connDiff (I := I) gArm g₀ x (m 0) (m 1))
      rw [Function.update_self]
      rfl
    · change Function.update (Matrix.vecTail m) 0
          (connDiffEndo (I := I) (M := M) g₀ gArm x (m 0) (Matrix.vecTail m 0)) (1 : Fin 3) =
        m 2
      rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]
      rfl
    · change Function.update (Matrix.vecTail m) 0
          (connDiffEndo (I := I) (M := M) g₀ gArm x (m 0) (Matrix.vecTail m 0)) (2 : Fin 3) =
        m 3
      rw [Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
      rfl]
  rw [bdConnDiffLoweredCc_unitModel_apply (I := I) (M := M) g₀ gOut x]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma bdConnDiff_self_apply (g₀ : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₀ g₀ x u v = 0 := by
  have h := Integral.Connection.connDiff_cocycle (I := I) (M := M) g₀ g₀ g₀ x u v
  have h2 : PDE.DeTurck.connDiff (I := I) g₀ g₀ x u v +
      PDE.DeTurck.connDiff (I := I) g₀ g₀ x u v =
      PDE.DeTurck.connDiff (I := I) g₀ g₀ x u v := h
  have h3 := add_right_cancel (a := PDE.DeTurck.connDiff (I := I) g₀ g₀ x u v)
    (b := PDE.DeTurck.connDiff (I := I) g₀ g₀ x u v) (c := 0)
  apply h3
  rw [zero_add]
  exact h2

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma dLaCovKernel_diff_eq_dLaCovKernel_connDiff_expansion (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 p q : TangentSpace I x) :
    connDiffCovDerivOp (I := I) g₁ g_bg x v0 p q - connDiffCovDerivOp (I := I) g₁ g₀ x v0 p q =
      -connDiffCovDerivOp (I := I) g_bg g₀ x v0 p q
        + PDE.DeTurck.connDiff (I := I) g_bg g₀ x
            (PDE.DeTurck.connDiff (I := I) g_bg g₀ x p q) v0
        - PDE.DeTurck.connDiff (I := I) g_bg g₀ x
            (PDE.DeTurck.connDiff (I := I) g_bg g₀ x p v0) q
        - PDE.DeTurck.connDiff (I := I) g_bg g₀ x p
            (PDE.DeTurck.connDiff (I := I) g_bg g₀ x q v0)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g_bg g₀ x p q) v0
        + PDE.DeTurck.connDiff (I := I) g_bg g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0) q
        + PDE.DeTurck.connDiff (I := I) g_bg g₀ x p
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) := by
  classical
  have hcc : ∀ u v : TangentSpace I x,
      PDE.DeTurck.connDiff (I := I) g₁ g_bg x u v =
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v -
          PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v := by
    intro u v
    have h := Integral.Connection.connDiff_cocycle (I := I) (M := M) g₁ g_bg g₀ x u v
    exact eq_sub_of_add_eq h
  have hS1 := Integral.Connection.dLaCovKernel_backgroundSplit (I := I) (M := M)
    g₀ g₁ g_bg x v0 p q
  have hS2 := Integral.Connection.dLaCovKernel_backgroundSplit (I := I) (M := M)
    g₀ g₁ g₀ x v0 p q
  have hS3 := Integral.Connection.dLaCovKernel_backgroundSplit (I := I) (M := M)
    g₀ g_bg g₀ x v0 p q
  rw [hS1, hS2, hS3]
  have hT1 : PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      (PDE.DeTurck.connDiff (I := I) g₁ g_bg x p q) v0 =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p q) v0 -
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x p q) v0 := by
    rw [hcc p q, map_sub, ContinuousLinearMap.sub_apply]
  have hT2 : PDE.DeTurck.connDiff (I := I) g₁ g_bg x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0) q =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0) q -
        PDE.DeTurck.connDiff (I := I) g_bg g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0) q :=
    hcc (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0) q
  have hT3 : PDE.DeTurck.connDiff (I := I) g₁ g_bg x p
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x p
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) -
        PDE.DeTurck.connDiff (I := I) g_bg g₀ x p
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) :=
    hcc p (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
  have hT4 : PDE.DeTurck.connDiff (I := I) g₁ g_bg x
      (PDE.DeTurck.connDiff (I := I) g_bg g₀ x p q) v0 =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x p q) v0 -
        PDE.DeTurck.connDiff (I := I) g_bg g₀ x
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x p q) v0 :=
    hcc (PDE.DeTurck.connDiff (I := I) g_bg g₀ x p q) v0
  have hT1' : PDE.DeTurck.connDiff (I := I) g₁ g_bg x p q =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x p q -
        PDE.DeTurck.connDiff (I := I) g_bg g₀ x p q := hcc p q
  rw [hT1', hT2, hT3]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p q -
          PDE.DeTurck.connDiff (I := I) g_bg g₀ x p q) v0 =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p q) v0 -
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x p q) v0 from by
    rw [map_sub, ContinuousLinearMap.sub_apply]]
  abel

private def bdSigma2 : Equiv.Perm (Fin 4) :=
  ⟨fun i => (![2, 3, 1, 0] : Fin 4 → Fin 4) i,
   fun i => (![3, 2, 0, 1] : Fin 4 → Fin 4) i,
   by decide, by decide⟩

private def bdSigma3 : Equiv.Perm (Fin 4) :=
  ⟨fun i => (![2, 1, 3, 0] : Fin 4 → Fin 4) i,
   fun i => (![3, 1, 0, 2] : Fin 4 → Fin 4) i,
   by decide, by decide⟩

private def bdSigma4 : Equiv.Perm (Fin 4) :=
  ⟨fun i => (![3, 1, 2, 0] : Fin 4 → Fin 4) i,
   fun i => (![3, 1, 2, 0] : Fin 4 → Fin 4) i,
   by decide, by decide⟩

private def dLaCovKernelDiffLoweredCc (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 :=
  (-1 : ℝ) • bdFixLoweredCc (I := I) (M := M) g₀ g_bg g₀
    + domDomCongrSection (I := I) g₀ bdSigma2 (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ g_bg g_bg)
    - domDomCongrSection (I := I) g₀ bdSigma3 (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ g_bg g_bg)
    - domDomCongrSection (I := I) g₀ bdSigma4 (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ g_bg g_bg)
    - domDomCongrSection (I := I) g₀ bdSigma2 (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ g_bg g₁)
    + domDomCongrSection (I := I) g₀ bdSigma3 (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ g₁ g_bg)
    + domDomCongrSection (I := I) g₀ bdSigma4 (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ g₁ g_bg)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma bdUnitModel_smul (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ)
    (A : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (c • A) x =
      c • unitModel (I := I) (M := M) g₀ s A x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul]

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdLow0_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (dLaCovKernelDiffLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x m =
      g₀.inner x
        (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3) -
          connDiffCovDerivOp (I := I) g₁ g₀ x (m 1) (m 2) (m 3)) (m 0) := by
  classical
  rw [dLaCovKernelDiffLoweredCc]
  rw [bdUnitModel_add, bdUnitModel_add, bdUnitModel_sub, bdUnitModel_sub, bdUnitModel_sub,
    bdUnitModel_add, bdUnitModel_smul]
  simp only [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel, domDomCongrSection_unitModel]
  simp only [ContinuousMultilinearMap.domDomCongr_apply]
  rw [bdFixLoweredCc_unitModel_apply (I := I) (M := M) g₀ g_bg g₀ x m]
  rw [bdQuadLowCc_unitModel_apply (I := I) (M := M) g₀ g_bg g_bg x
      (fun i => m (bdSigma2 i)),
    bdQuadLowCc_unitModel_apply (I := I) (M := M) g₀ g_bg g_bg x
      (fun i => m (bdSigma3 i)),
    bdQuadLowCc_unitModel_apply (I := I) (M := M) g₀ g_bg g_bg x
      (fun i => m (bdSigma4 i)),
    bdQuadLowCc_unitModel_apply (I := I) (M := M) g₀ g_bg g₁ x
      (fun i => m (bdSigma2 i)),
    bdQuadLowCc_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (fun i => m (bdSigma3 i)),
    bdQuadLowCc_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (fun i => m (bdSigma4 i))]
  have hs2_0 : bdSigma2 (0 : Fin 4) = 2 := by decide
  have hs2_1 : bdSigma2 (1 : Fin 4) = 3 := by decide
  have hs2_2 : bdSigma2 (2 : Fin 4) = 1 := by decide
  have hs2_3 : bdSigma2 (3 : Fin 4) = 0 := by decide
  have hs3_0 : bdSigma3 (0 : Fin 4) = 2 := by decide
  have hs3_1 : bdSigma3 (1 : Fin 4) = 1 := by decide
  have hs3_2 : bdSigma3 (2 : Fin 4) = 3 := by decide
  have hs3_3 : bdSigma3 (3 : Fin 4) = 0 := by decide
  have hs4_0 : bdSigma4 (0 : Fin 4) = 3 := by decide
  have hs4_1 : bdSigma4 (1 : Fin 4) = 1 := by decide
  have hs4_2 : bdSigma4 (2 : Fin 4) = 2 := by decide
  have hs4_3 : bdSigma4 (3 : Fin 4) = 0 := by decide
  rw [hs2_0, hs2_1, hs2_2, hs2_3, hs3_0, hs3_1, hs3_2, hs3_3, hs4_0, hs4_1, hs4_2, hs4_3]
  rw [dLaCovKernel_diff_eq_dLaCovKernel_connDiff_expansion (I := I) (M := M) g₀ g₁ g_bg x (m 1) (m 2) (m 3)]
  have hsymm4 : PDE.DeTurck.connDiff (I := I) g_bg g₀ x (m 2)
      (PDE.DeTurck.connDiff (I := I) g_bg g₀ x (m 3) (m 1)) =
      PDE.DeTurck.connDiff (I := I) g_bg g₀ x
        (PDE.DeTurck.connDiff (I := I) g_bg g₀ x (m 3) (m 1)) (m 2) :=
    PDE.DeTurck.connDiff_symm (I := I) g_bg g₀ x (m 2)
      (PDE.DeTurck.connDiff (I := I) g_bg g₀ x (m 3) (m 1))
  have hsymm7 : PDE.DeTurck.connDiff (I := I) g_bg g₀ x (m 2)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 3) (m 1)) =
      PDE.DeTurck.connDiff (I := I) g_bg g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 3) (m 1)) (m 2) :=
    PDE.DeTurck.connDiff_symm (I := I) g_bg g₀ x (m 2)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 3) (m 1))
  simp only [map_add, map_sub, map_neg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply]
  rw [← hsymm4, ← hsymm7]
  ring

private def deTurckArmCoeffDiffHalfCc (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 4
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3 (fullRaisedEndoField (I := I) (M := M) g₁ g₀))
    (dLaCovKernelDiffLoweredCc (I := I) (M := M) g₀ g₁ g_bg)

private def deTurckArmCoeffDiffCc (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 :=
  domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (deTurckArmCoeffDiffHalfCc (I := I) (M := M) g₀ g₁ g_bg)
    + deTurckArmCoeffDiffHalfCc (I := I) (M := M) g₀ g₁ g_bg

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (metricComparisonEndo gInvRaisedEndo_apply
  inverseMetricSharpFib_g0FlatCLM cotangentToDual_g0FlatCLM g0FlatCLM) in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma bdG0_inner_lambda (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    g₀.inner x u (metricComparisonEndo (I := I) g₁ g₀ x v) = g₁.inner x u v := by
  rw [gInvRaisedEndo_apply]
  rw [g₀.symm x u (inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x v))]
  rw [inverseMetricSharpFib_inner (I := I) g₀ x (g0FlatCLM (I := I) g₁ x v) u]
  rw [show cotangentToDualLinear (I := I) (x := x) (g0FlatCLM (I := I) g₁ x v) u =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₁ x v) u from rfl]
  rw [cotangentToDual_g0FlatCLM]
  rw [g₁.symm x v u]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdXdHalf_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (deTurckArmCoeffDiffHalfCc (I := I) (M := M) g₀ g₁ g_bg) x m =
      g₁.inner x
        (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3) -
          connDiffCovDerivOp (I := I) g₁ g₀ x (m 1) (m 2) (m 3)) (m 0) := by
  rw [unitModel]
  rw [show (deTurckArmCoeffDiffHalfCc (I := I) (M := M) g₀ g₁ g_bg).toSection x
        (unitTensor (I := I) (M := M) x) =
      slotInsertEndoFib (I := I) (M := M) 4 0 x
        (fullRaisedEndoField (I := I) (M := M) g₁ g₀ x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
          (dLaCovKernelDiffLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
          (unitTensor (I := I) (M := M) x)) from by
    rw [deTurckArmCoeffDiffHalfCc, appCcRS_toSection]
    rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
          (dLaCovKernelDiffLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
          (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 4 (dLaCovKernelDiffLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x from rfl]
  rw [show (Function.update (fun k : Fin 4 => (m k : E)) 0
        (fullRaisedEndoField (I := I) (M := M) g₁ g₀ x ((fun k : Fin 4 => (m k : E)) 0))) =
      (fun k : Fin 4 => ((Function.update m 0
        (fullRaisedEndoField (I := I) (M := M) g₁ g₀ x (m 0)) k : TangentSpace I x) : E))
      from by
    funext k
    by_cases hk : k = 0
    · subst hk
      rfl
    · rw [Function.update_of_ne hk]]
  rw [bdLow0_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
    (Function.update m 0 (fullRaisedEndoField (I := I) (M := M) g₁ g₀ x (m 0)))]
  rw [show (Function.update m 0
      (fullRaisedEndoField (I := I) (M := M) g₁ g₀ x (m 0)) (1 : Fin 4)) = m 1 from
    Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0) _ _]
  rw [show (Function.update m 0
      (fullRaisedEndoField (I := I) (M := M) g₁ g₀ x (m 0)) (2 : Fin 4)) = m 2 from
    Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0) _ _]
  rw [show (Function.update m 0
      (fullRaisedEndoField (I := I) (M := M) g₁ g₀ x (m 0)) (3 : Fin 4)) = m 3 from
    Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0) _ _]
  rw [show (Function.update m 0
      (fullRaisedEndoField (I := I) (M := M) g₁ g₀ x (m 0)) (0 : Fin 4)) =
      fullRaisedEndoField (I := I) (M := M) g₁ g₀ x (m 0) from
    Function.update_self _ _ _]
  rw [fullRaisedEndoField_apply]
  exact bdG0_inner_lambda (I := I) (M := M) g₀ g₁ x
    (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3) -
      connDiffCovDerivOp (I := I) g₁ g₀ x (m 1) (m 2) (m 3)) (m 0)

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdXd_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg) x m =
      g₁.inner x
          (connDiffCovDerivOp (I := I) g₁ g_bg x (m 0) (m 2) (m 3) -
            connDiffCovDerivOp (I := I) g₁ g₀ x (m 0) (m 2) (m 3)) (m 1) +
        g₁.inner x
          (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3) -
            connDiffCovDerivOp (I := I) g₁ g₀ x (m 1) (m 2) (m 3)) (m 0) := by
  rw [deTurckArmCoeffDiffCc, bdUnitModel_add, ContinuousMultilinearMap.add_apply]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [bdXdHalf_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
    (fun i => m ((Equiv.swap (0 : Fin 4) 1) i))]
  rw [bdXdHalf_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x m]
  rw [show (Equiv.swap (0 : Fin 4) 1) 0 = 1 from Equiv.swap_apply_left 0 1,
    show (Equiv.swap (0 : Fin 4) 1) 1 = 0 from Equiv.swap_apply_right 0 1,
    show (Equiv.swap (0 : Fin 4) 1) 2 = 2 from by decide,
    show (Equiv.swap (0 : Fin 4) 1) 3 = 3 from by decide]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
private theorem bdCovDerivArmDiff_eq_pairTrace
    (g₀ g_bg g₁ : SmoothRiemannianMetric I M) :
    deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g₀ =
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hsmul : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (((-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg)))).toSection x)) D) =
      (-1 : ℝ) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg)))).toSection x)) D) := by
    rw [show ((((-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg)))).toSection x)) =
        (-1 : ℝ) • ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg)))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rfl
  rw [hsmul]
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [bdPairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      ((deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g₀).toSection x)) D) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D -
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g₀).toSection x) D from by
    rw [show ((deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g₀).toSection x) =
        (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x -
          (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g₀).toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rfl]
  rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D =
      connDiffCovDerivBiContrFib (I := I) g₁ g_bg x D from rfl]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g₀).toSection x) D =
      connDiffCovDerivBiContrFib (I := I) g₁ g₀ x D from rfl]
  rw [show (connDiffCovDerivBiContrFib (I := I) g₁ g_bg x : Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x) =
      connDiffCovDerivBiContrFibFixedFrame (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  rw [show (connDiffCovDerivBiContrFib (I := I) g₁ g₀ x : Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x) =
      connDiffCovDerivBiContrFibFixedFrame (I := I) g₁ g₀ (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  rw [dLaBiContrFibFixedFrame_toModel (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x) x D v]
  rw [dLaBiContrFibFixedFrame_toModel (I := I) g₁ g₀ (smoothOrthoFrame (I := I) g₁ x) x D v]
  have hXval : ∀ a b : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4 (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg) x
        ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
          (smoothOrthoFrame (I := I) g₁ x b x : E)] =
      (g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (v 0)
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) +
        g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (v 1)
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 0)) -
      (g₁.inner x (connDiffCovDerivOp (I := I) g₁ g₀ x (v 0)
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) +
        g₁.inner x (connDiffCovDerivOp (I := I) g₁ g₀ x (v 1)
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 0)) := by
    intro a b
    rw [bdXd_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x)]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x) 0 = v 0 from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x) 1 = v 1 from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x) 2 =
      smoothOrthoFrame (I := I) g₁ x a x from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x) 3 =
      smoothOrthoFrame (I := I) g₁ x b x from rfl]
    rw [map_sub, ContinuousLinearMap.sub_apply, map_sub, ContinuousLinearMap.sub_apply]
    ring
  rw [show (∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        unitModel (I := I) (M := M) g₀ 4 (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg) x
          ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)]) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          unitModel (I := I) (M := M) g₀ 4 (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg) x
            ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] from Finset.sum_comm]
  rw [neg_one_mul, neg_one_mul, neg_one_mul]
  have hS : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        unitModel (I := I) (M := M) g₀ 4 (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg) x
          ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)]) =
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (v 0)
            (smoothOrthoFrame (I := I) g₁ x a x)
            (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) +
          g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (v 1)
            (smoothOrthoFrame (I := I) g₁ x a x)
            (smoothOrthoFrame (I := I) g₁ x b x)) (v 0)) *
          Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)]) -
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (g₁.inner x (connDiffCovDerivOp (I := I) g₁ g₀ x (v 0)
            (smoothOrthoFrame (I := I) g₁ x a x)
            (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) +
          g₁.inner x (connDiffCovDerivOp (I := I) g₁ g₀ x (v 1)
            (smoothOrthoFrame (I := I) g₁ x a x)
            (smoothOrthoFrame (I := I) g₁ x b x)) (v 0)) *
          Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)]) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hXval a b]
    ring
  linear_combination hS
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma bdRfns_neg (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [show (-v) = (-1 : ℝ) • v from by rw [neg_one_smul]]
  rw [riemannianFiberNormSq_smul]
  norm_num

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma bdRfns_iCG_sub_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (j : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
        ((iteratedCovGrad (I := I) g r s j (A - B)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j A).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j B).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g r s j (A - B)).toSection x =
      (iteratedCovGrad (I := I) g r s j A).toSection x +
        (-(iteratedCovGrad (I := I) g r s j B).toSection x) := by
    rw [sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_neg, SmoothCcTensor.toSection_add]
    rw [show ((iteratedCovGrad (I := I) g r s j A).toSection +
        (-iteratedCovGrad (I := I) g r s j B).toSection) x =
        (iteratedCovGrad (I := I) g r s j A).toSection x +
          (-iteratedCovGrad (I := I) g r s j B).toSection x from rfl]
    rw [SmoothCcTensor.toSection_neg]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + j) x _ _) ?_
  rw [bdRfns_neg (I := I) (M := M) g r (s + j) x]

theorem bdPureDT_tgrid (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + j) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s j
              (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ s)).toSection x) ≤
          C j * Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (j + 1) := by
  classical
  obtain ⟨S, hS_nn, hS⟩ := fullRaisedEndoField_iteratedCovGrad_gridWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨c0, hc0_nn, hc0⟩ := bdExists_fixedField_rfns_jet (I := I) (M := M) g₀ (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun j => diagonalGridGrowthFactor (E := E) j *
      (c0 0 * ∑ l ∈ Finset.range (j + 1), fr ^ (s + 1) * S l),
    fun j => mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (mul_nonneg (hc0_nn 0) (Finset.sum_nonneg fun l _ =>
        mul_nonneg (by positivity) (hS_nn l))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hsFlat : ∀ l : ℕ, l < j + 1 →
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
      (fr ^ (s + 1) * S l) * Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by
    intro l hl
    refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ (s + 1)
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁) l x) ?_
    rw [← hfr_def]
    have hins : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 1 l
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        Combinatorics.antidiagonalTupleGrid b l * S l :=
      hS g₁ T htie hδ_le hδ0 hbound l x
    calc fr ^ (s + 1) * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)
        ≤ fr ^ (s + 1) * (Combinatorics.antidiagonalTupleGrid b l * S l) :=
          mul_le_mul_of_nonneg_left hins (by positivity)
      _ ≤ fr ^ (s + 1) * (Combinatorics.antidiagonalTupleGridWindow b (j + 1) * S l) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right
            (Combinatorics.antidiagonalTupleGrid_le_window b hb hl) (hS_nn l)
      _ = (fr ^ (s + 1) * S l) * Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by
          ring
  rw [bdPureDT_eq_trace_fullRaised (I := I) (M := M) g₀ g₁ s]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ j (s + 2) (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) x) ?_
  have hzero : ∀ i' ∈ Finset.range (j + 1), i' ≠ 0 →
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i') x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s i'
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) = 0 := by
    intro i' _ hi'0
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi'0
    rw [bdICG_succ_cometricDT_zero (I := I) (M := M) g₀ s m]
    rw [bdRfns_zero_toSection, zero_mul]
  have hsum_eq : (∑ i' ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i') x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s i'
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)) =
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 0) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s 0
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - 0),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) := by
    refine Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_
    intro i' hi' hi'0
    exact hzero i' hi' hi'0
  rw [hsum_eq]
  have hc0' : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 0) x
      ((iteratedCovGrad (I := I) g₀ (s + 2) s 0
        (cometricDoubleTraceField (I := I) g₀ s)).toSection x) ≤ c0 0 := hc0 0 x
  have hsumS : (∑ l ∈ Finset.range (j + 1 - 0),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)) ≤
      (∑ l ∈ Finset.range (j + 1), fr ^ (s + 1) * S l) *
        Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by
    rw [show j + 1 - 0 = j + 1 from rfl]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    exact hsFlat l (by omega)
  have hrfns_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 0) x
      ((iteratedCovGrad (I := I) g₀ (s + 2) s 0
        (cometricDoubleTraceField (I := I) g₀ s)).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) (s + 0) x _
  have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - 0),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) :=
    Finset.sum_nonneg fun l _ =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x _
  refine le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hc0' hsumS hsum_nn (hc0_nn 0)) (appCcGdiag_nonneg (E := E) j)) ?_
  rw [← mul_assoc, ← mul_assoc]
  rw [mul_assoc (diagonalGridGrowthFactor (E := E) j) (c0 0)]

theorem bdPairTraceOp_tgrid (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 6 2 j
              (armPairTraceOpCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C j * Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (j + 1) := by
  classical
  obtain ⟨C2, hC2_nn, hC2⟩ := bdPureDT_tgrid (I := I) (M := M) g₀ 2 hδ₀
  obtain ⟨C4, hC4_nn, hC4⟩ := bdPureDT_tgrid (I := I) (M := M) g₀ 4 hδ₀
  refine ⟨fun j => diagonalGridGrowthFactor (E := E) j * ∑ i' ∈ Finset.range (j + 1),
      C2 i' * ∑ l ∈ Finset.range (j + 1 - i'),
        C4 l * Combinatorics.antidiagonalTupleGridWindowMulConst i' l,
    fun j => mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hC2_nn i')
        (Finset.sum_nonneg fun l _ => mul_nonneg (hC4_nn l)
          (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := Combinatorics.antidiagonalTupleGridWindow b (j + 1) with hW_def
  have hW_nn : 0 ≤ W := Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (j + 1)
  rw [armPairTraceOpCc]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ j 6 4 2
    (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 2)
    (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4) x) ?_
  have hcell : ∀ i' ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 4 2 i'
            (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 2)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 6 4 l
              (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)).toSection x) ≤
      (C2 i' * ∑ l ∈ Finset.range (j + 1 - i'),
        C4 l * Combinatorics.antidiagonalTupleGridWindowMulConst i' l) * W := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 4 2 i'
          (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 2)).toSection x) ≤
        C2 i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 1) :=
      hC2 g₁ T htie hδ_le hδ0 hbound i' x
    have hA2 : (∑ l ∈ Finset.range (j + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 6 4 l
            (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)).toSection x)) ≤
        ∑ l ∈ Finset.range (j + 1 - i'),
          C4 l * Combinatorics.antidiagonalTupleGridWindow b (l + 1) :=
      Finset.sum_le_sum fun l _ => hC4 g₁ T htie hδ_le hδ0 hbound l x
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 6 4 l
            (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (4 + l) x _
    have hA1_rhs_nn : 0 ≤ C2 i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 1) :=
      mul_nonneg (hC2_nn i') (Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i' + 1))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show (C2 i' * ∑ l ∈ Finset.range (j + 1 - i'),
        C4 l * Combinatorics.antidiagonalTupleGridWindowMulConst i' l) * W =
        ∑ l ∈ Finset.range (j + 1 - i'),
          (C2 i' * (C4 l * Combinatorics.antidiagonalTupleGridWindowMulConst i' l)) * W from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have hpair : Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
        Combinatorics.antidiagonalTupleGridWindow b (l + 1) ≤
        Combinatorics.antidiagonalTupleGridWindowMulConst i' l *
          Combinatorics.antidiagonalTupleGridWindow b (i' + l + 1) :=
      Combinatorics.antidiagonalTupleGridWindow_mul_le b hb i' l
    have hmono : Combinatorics.antidiagonalTupleGridWindow b (i' + l + 1) ≤ W := by
      rw [hW_def]
      exact Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
    calc C2 i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
          (C4 l * Combinatorics.antidiagonalTupleGridWindow b (l + 1))
        = (C2 i' * C4 l) * (Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
            Combinatorics.antidiagonalTupleGridWindow b (l + 1)) := by ring
      _ ≤ (C2 i' * C4 l) * (Combinatorics.antidiagonalTupleGridWindowMulConst i' l *
            Combinatorics.antidiagonalTupleGridWindow b (i' + l + 1)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (hC2_nn i') (hC4_nn l)
      _ ≤ (C2 i' * C4 l) * (Combinatorics.antidiagonalTupleGridWindowMulConst i' l * W) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hC2_nn i') (hC4_nn l))
          exact mul_le_mul_of_nonneg_left hmono
            (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _)
      _ = (C2 i' * (C4 l * Combinatorics.antidiagonalTupleGridWindowMulConst i' l)) * W := by
          ring
  calc diagonalGridGrowthFactor (E := E) j *
        ∑ i' ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 4 2 i'
                (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 2)).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 6 4 l
                  (cometricDoubleTraceCc (I := I) (M := M) g₀ g₁ 4)).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) j *
          ∑ i' ∈ Finset.range (j + 1),
            (C2 i' * ∑ l ∈ Finset.range (j + 1 - i'),
              C4 l * Combinatorics.antidiagonalTupleGridWindowMulConst i' l) * W :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) j)
    _ = _ := by
        rw [← Finset.sum_mul, ← mul_assoc]

private theorem bdQuadLow_movingOuter_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ l, 0 ≤ C l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ g_bg g₁)).toSection x) ≤
          C l * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (l + 2) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨cAS, hcAS_nn, hcAS⟩ := bdExists_fixedField_rfns_jet (I := I) (M := M) g₀ 3 4
    (armSlotEndoCc (I := I) (M := M) g₀ 2 (connDiffEndo (I := I) (M := M) g₀ g_bg))
  refine ⟨fun l => diagonalGridGrowthFactor (E := E) l *
      ∑ i' ∈ Finset.range (l + 1), cAS i' * ∑ l' ∈ Finset.range (l + 1 - i'), CA l',
    fun l => mul_nonneg (appCcGdiag_nonneg (E := E) l)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hcAS_nn i')
        (Finset.sum_nonneg fun l' _ => hCA_nn l')), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound l x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (l + 2) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (l + 2)
  rw [connDiffQuadraticLoweredCc]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ l 0 3 4
    (armSlotEndoCc (I := I) (M := M) g₀ 2 (connDiffEndo (I := I) (M := M) g₀ g_bg))
    (connDiffLoweredCc (I := I) g₀ g₁) x) ?_
  have hcell : ∀ i' ∈ Finset.range (l + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + i') x
          ((iteratedCovGrad (I := I) g₀ 3 4 i'
            (armSlotEndoCc (I := I) (M := M) g₀ 2
              (connDiffEndo (I := I) (M := M) g₀ g_bg))).toSection x) *
        ∑ l' ∈ Finset.range (l + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
            ((iteratedCovGrad (I := I) g₀ 0 3 l'
              (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) ≤
      (cAS i' * ∑ l' ∈ Finset.range (l + 1 - i'), CA l') *
        Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + i') x
        ((iteratedCovGrad (I := I) g₀ 3 4 i'
          (armSlotEndoCc (I := I) (M := M) g₀ 2
            (connDiffEndo (I := I) (M := M) g₀ g_bg))).toSection x) ≤ cAS i' := hcAS i' x
    have hA2 : (∑ l' ∈ Finset.range (l + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 3 l'
            (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)) ≤
        (∑ l' ∈ Finset.range (l + 1 - i'), CA l') *
          Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun l' hl' => ?_
      rw [Finset.mem_range] at hl'
      rw [bdRfns_iCG_connDiffLoweredCc_eq_connDiffSection (I := I) (M := M) g₀ g₁ l' x]
      refine le_trans (hCA g₁ P htie hδ_le hδ0 hbound l' x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCA_nn l')
      rw [show (∑ k ∈ Finset.range (l' + 2), Combinatorics.antidiagonalTupleGrid b k) =
          Combinatorics.antidiagonalTupleGridWindow b (l' + 2) from rfl]
      exact Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
    have hsum_nn : (0 : ℝ) ≤ ∑ l' ∈ Finset.range (l + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 3 l'
            (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) :=
      Finset.sum_nonneg fun l' _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + l') x _
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 4 i'
              (armSlotEndoCc (I := I) (M := M) g₀ 2
                (connDiffEndo (I := I) (M := M) g₀ g_bg))).toSection x) *
          ∑ l' ∈ Finset.range (l + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 3 l'
                (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
        ≤ cAS i' * ((∑ l' ∈ Finset.range (l + 1 - i'), CA l') *
            Combinatorics.antidiagonalTupleGridWindow b (l + 2)) :=
          mul_le_mul hA1 hA2 hsum_nn (hcAS_nn i')
      _ = (cAS i' * ∑ l' ∈ Finset.range (l + 1 - i'), CA l') *
            Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) l)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]

private theorem bdQuadLow_movingArm_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ l, 0 ≤ C l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C l * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (l + 2) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨cL, hcL_nn, hcL⟩ := bdExists_fixedField_rfns_jet (I := I) (M := M) g₀ 0 3
    (connDiffLoweredCc (I := I) g₀ g_bg)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun l => diagonalGridGrowthFactor (E := E) l *
      ∑ i' ∈ Finset.range (l + 1), (fr ^ 2 * CA i') *
        ∑ l' ∈ Finset.range (l + 1 - i'), cL l',
    fun l => mul_nonneg (appCcGdiag_nonneg (E := E) l)
      (Finset.sum_nonneg fun i' _ => mul_nonneg
        (mul_nonneg (by positivity) (hCA_nn i'))
        (Finset.sum_nonneg fun l' _ => hcL_nn l')), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound l x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (l + 2) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (l + 2)
  rw [connDiffQuadraticLoweredCc]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ l 0 3 4
    (armSlotEndoCc (I := I) (M := M) g₀ 2 (connDiffEndo (I := I) (M := M) g₀ g₁))
    (connDiffLoweredCc (I := I) g₀ g_bg) x) ?_
  have hcell : ∀ i' ∈ Finset.range (l + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + i') x
          ((iteratedCovGrad (I := I) g₀ 3 4 i'
            (armSlotEndoCc (I := I) (M := M) g₀ 2
              (connDiffEndo (I := I) (M := M) g₀ g₁))).toSection x) *
        ∑ l' ∈ Finset.range (l + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
            ((iteratedCovGrad (I := I) g₀ 0 3 l'
              (connDiffLoweredCc (I := I) g₀ g_bg)).toSection x) ≤
      ((fr ^ 2 * CA i') * ∑ l' ∈ Finset.range (l + 1 - i'), cL l') *
        Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + i') x
        ((iteratedCovGrad (I := I) g₀ 3 4 i'
          (armSlotEndoCc (I := I) (M := M) g₀ 2
            (connDiffEndo (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (fr ^ 2 * CA i') * Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by
      refine le_trans (bdArmSlot2_rfns_le (I := I) (M := M) g₀ g₁ i' x) ?_
      rw [← hfr_def]
      have h2 := hCA g₁ P htie hδ_le hδ0 hbound i' x
      calc fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
            ((iteratedCovGrad (I := I) g₀ 1 2 i'
              (connDiffSection (I := I) g₁ g₀)).toSection x)
          ≤ fr ^ 2 * (CA i' * ∑ k ∈ Finset.range (i' + 2),
              Combinatorics.antidiagonalTupleGrid b k) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (fr ^ 2 * CA i') * Combinatorics.antidiagonalTupleGridWindow b (i' + 2) := by
            rw [show (∑ k ∈ Finset.range (i' + 2),
                Combinatorics.antidiagonalTupleGrid b k) =
                Combinatorics.antidiagonalTupleGridWindow b (i' + 2) from rfl]
            ring
        _ ≤ (fr ^ 2 * CA i') * Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by
            refine mul_le_mul_of_nonneg_left ?_
              (mul_nonneg (by positivity) (hCA_nn i'))
            exact Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
    have hA2 : (∑ l' ∈ Finset.range (l + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 3 l'
            (connDiffLoweredCc (I := I) g₀ g_bg)).toSection x)) ≤
        ∑ l' ∈ Finset.range (l + 1 - i'), cL l' :=
      Finset.sum_le_sum fun l' _ => hcL l' x
    have hsum_nn : (0 : ℝ) ≤ ∑ l' ∈ Finset.range (l + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 3 l'
            (connDiffLoweredCc (I := I) g₀ g_bg)).toSection x) :=
      Finset.sum_nonneg fun l' _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + l') x _
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 4 i'
              (armSlotEndoCc (I := I) (M := M) g₀ 2
                (connDiffEndo (I := I) (M := M) g₀ g₁))).toSection x) *
          ∑ l' ∈ Finset.range (l + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 3 l'
                (connDiffLoweredCc (I := I) g₀ g_bg)).toSection x)
        ≤ ((fr ^ 2 * CA i') * Combinatorics.antidiagonalTupleGridWindow b (l + 2)) *
            ∑ l' ∈ Finset.range (l + 1 - i'), cL l' :=
          mul_le_mul hA1 hA2 hsum_nn
            (mul_nonneg (mul_nonneg (by positivity) (hCA_nn i')) hW_nn)
      _ = ((fr ^ 2 * CA i') * ∑ l' ∈ Finset.range (l + 1 - i'), cL l') *
            Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) l)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]

private theorem bdLow0_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ l, 0 ≤ C l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (dLaCovKernelDiffLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C l * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (l + 2) := by
  classical
  obtain ⟨cF, hcF_nn, hcF⟩ := bdExists_fixedField_rfns_jet (I := I) (M := M) g₀ 0 4
    (bdFixLoweredCc (I := I) (M := M) g₀ g_bg g₀)
  obtain ⟨cQ, hcQ_nn, hcQ⟩ := bdExists_fixedField_rfns_jet (I := I) (M := M) g₀ 0 4
    (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ g_bg g_bg)
  obtain ⟨CE, hCE_nn, hCE⟩ := bdQuadLow_movingOuter_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨CF, hCF_nn, hCF⟩ := bdQuadLow_movingArm_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨fun l => 64 * cF l + 64 * cQ l + 32 * cQ l + 16 * cQ l + 8 * CE l +
      4 * CF l + 2 * CF l,
    fun l => by
      have h1 := hcF_nn l; have h2 := hcQ_nn l; have h3 := hCE_nn l; have h4 := hCF_nn l
      linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound l x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set W : ℝ := Combinatorics.antidiagonalTupleGridWindow b (l + 2) with hW_def
  have hW1 : (1 : ℝ) ≤ W :=
    Combinatorics.one_le_antidiagonalTupleGridWindow b hb (by omega)
  have hW_nn : (0 : ℝ) ≤ W := by linarith
  set A := (-1 : ℝ) • bdFixLoweredCc (I := I) (M := M) g₀ g_bg g₀ with hA_def
  set B := domDomCongrSection (I := I) g₀ bdSigma2
    (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ g_bg g_bg) with hB_def
  set Cc := domDomCongrSection (I := I) g₀ bdSigma3
    (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ g_bg g_bg) with hC_def
  set Dd := domDomCongrSection (I := I) g₀ bdSigma4
    (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ g_bg g_bg) with hD_def
  set Ee := domDomCongrSection (I := I) g₀ bdSigma2
    (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ g_bg g₁) with hE_def
  set Ff := domDomCongrSection (I := I) g₀ bdSigma3
    (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ g₁ g_bg) with hF_def
  set Gg := domDomCongrSection (I := I) g₀ bdSigma4
    (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ g₁ g_bg) with hG_def
  have hlow : dLaCovKernelDiffLoweredCc (I := I) (M := M) g₀ g₁ g_bg = ((((A + B) - Cc) - Dd) - Ee) + Ff + Gg := by
    rw [dLaCovKernelDiffLoweredCc, hA_def, hB_def, hC_def, hD_def, hE_def, hF_def, hG_def]
  have hrfns : ∀ (Z : SmoothCcTensor g₀ 0 4), (0 : ℝ) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l Z).toSection x) :=
    fun Z => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _
  have hA' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 4 l A).toSection x) ≤ cF l * W := by
    rw [hA_def, iteratedCovGrad_smul_real]
    rw [show (((-1 : ℝ) • iteratedCovGrad (I := I) g₀ 0 4 l
        (bdFixLoweredCc (I := I) (M := M) g₀ g_bg g₀)).toSection x) =
        (-1 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 4 l
          (bdFixLoweredCc (I := I) (M := M) g₀ g_bg g₀)).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [riemannianFiberNormSq_smul]
    have h := hcF l x
    nlinarith [hcF_nn l, hW1]
  have hddc : ∀ (σ : Equiv.Perm (Fin 4)) (Q : SmoothCcTensor g₀ 0 4),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (domDomCongrSection (I := I) g₀ σ Q)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l Q).toSection x) :=
    fun σ Q => riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g₀ σ Q l x
  have hQfix : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 4 l
        (connDiffQuadraticLoweredCc (I := I) (M := M) g₀ g_bg g_bg)).toSection x) ≤ cQ l * W := by
    have h := hcQ l x
    nlinarith [hcQ_nn l, hW1]
  have hB' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 4 l B).toSection x) ≤ cQ l * W := by
    rw [hB_def, hddc]; exact hQfix
  have hC' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 4 l Cc).toSection x) ≤ cQ l * W := by
    rw [hC_def, hddc]; exact hQfix
  have hD' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 4 l Dd).toSection x) ≤ cQ l * W := by
    rw [hD_def, hddc]; exact hQfix
  have hE' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 4 l Ee).toSection x) ≤ CE l * W := by
    rw [hE_def, hddc]
    exact hCE g₁ P htie hδ_le hδ0 hbound l x
  have hF' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 4 l Ff).toSection x) ≤ CF l * W := by
    rw [hF_def, hddc]
    exact hCF g₁ P htie hδ_le hδ0 hbound l x
  have hG' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 4 l Gg).toSection x) ≤ CF l * W := by
    rw [hG_def, hddc]
    exact hCF g₁ P htie hδ_le hδ0 hbound l x
  rw [hlow]
  have h1 := bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 l
    (((((A + B) - Cc) - Dd) - Ee) + Ff) Gg x
  have h2 := bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 l ((((A + B) - Cc) - Dd) - Ee) Ff x
  have h3 := bdRfns_iCG_sub_le (I := I) (M := M) g₀ 0 4 l (((A + B) - Cc) - Dd) Ee x
  have h4 := bdRfns_iCG_sub_le (I := I) (M := M) g₀ 0 4 l ((A + B) - Cc) Dd x
  have h5 := bdRfns_iCG_sub_le (I := I) (M := M) g₀ 0 4 l (A + B) Cc x
  have h6 := bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 l A B x
  linarith [h1, h2, h3, h4, h5, h6, hA', hB', hC', hD', hE', hF', hG',
    hrfns (((((A + B) - Cc) - Dd) - Ee) + Ff), hrfns ((((A + B) - Cc) - Dd) - Ee),
    hrfns (((A + B) - Cc) - Dd), hrfns ((A + B) - Cc), hrfns (A + B),
    hrfns A, hrfns B, hrfns Cc, hrfns Dd, hrfns Ee, hrfns Ff, hrfns Gg]

private theorem bdXd_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ l, 0 ≤ C l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C l * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (l + 2) := by
  classical
  obtain ⟨CΛ, hCΛ_nn, hCΛ⟩ := bdLambdaSlotInsert3_gridWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨CL, hCL_nn, hCL⟩ := bdLow0_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨fun l => 4 * (diagonalGridGrowthFactor (E := E) l *
      ∑ i' ∈ Finset.range (l + 1), CΛ i' * ∑ l' ∈ Finset.range (l + 1 - i'),
        CL l' * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1)),
    fun l => by
      have h : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) l *
          ∑ i' ∈ Finset.range (l + 1), CΛ i' * ∑ l' ∈ Finset.range (l + 1 - i'),
            CL l' * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1) :=
        mul_nonneg (appCcGdiag_nonneg (E := E) l)
          (Finset.sum_nonneg fun i' _ => mul_nonneg (hCΛ_nn i')
            (Finset.sum_nonneg fun l' _ => mul_nonneg (hCL_nn l')
              (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _)))
      linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound l x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set W : ℝ := Combinatorics.antidiagonalTupleGridWindow b (l + 2) with hW_def
  have hW_nn : (0 : ℝ) ≤ W := Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (l + 2)
  have hhalf : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 4 l
        (deTurckArmCoeffDiffHalfCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
      (diagonalGridGrowthFactor (E := E) l *
        ∑ i' ∈ Finset.range (l + 1), CΛ i' * ∑ l' ∈ Finset.range (l + 1 - i'),
          CL l' * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1)) * W := by
    rw [deTurckArmCoeffDiffHalfCc]
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ l 0 4 4
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
        (fullRaisedEndoField (I := I) (M := M) g₁ g₀))
      (dLaCovKernelDiffLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x) ?_
    have hcell : ∀ i' ∈ Finset.range (l + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
            ((iteratedCovGrad (I := I) g₀ 4 4 i'
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
                (fullRaisedEndoField (I := I) (M := M) g₁ g₀))).toSection x) *
          ∑ l' ∈ Finset.range (l + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 4 l'
                (dLaCovKernelDiffLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        (CΛ i' * ∑ l' ∈ Finset.range (l + 1 - i'),
          CL l' * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1)) * W := by
      intro i' hi'
      rw [Finset.mem_range] at hi'
      have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
          ((iteratedCovGrad (I := I) g₀ 4 4 i'
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
              (fullRaisedEndoField (I := I) (M := M) g₁ g₀))).toSection x) ≤
          CΛ i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 1) :=
        hCΛ g₁ P htie hδ_le hδ0 hbound i' x
      have hA2 : (∑ l' ∈ Finset.range (l + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l') x
            ((iteratedCovGrad (I := I) g₀ 0 4 l'
              (dLaCovKernelDiffLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) ≤
          ∑ l' ∈ Finset.range (l + 1 - i'),
            CL l' * Combinatorics.antidiagonalTupleGridWindow b (l' + 2) :=
        Finset.sum_le_sum fun l' _ => hCL g₁ P htie hδ_le hδ0 hbound l' x
      have hsum_nn : (0 : ℝ) ≤ ∑ l' ∈ Finset.range (l + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l') x
            ((iteratedCovGrad (I := I) g₀ 0 4 l'
              (dLaCovKernelDiffLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) :=
        Finset.sum_nonneg fun l' _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l') x _
      have hA1_rhs_nn : (0 : ℝ) ≤ CΛ i' *
          Combinatorics.antidiagonalTupleGridWindow b (i' + 1) :=
        mul_nonneg (hCΛ_nn i')
          (Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i' + 1))
      refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
      rw [Finset.mul_sum]
      rw [show (CΛ i' * ∑ l' ∈ Finset.range (l + 1 - i'),
          CL l' * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1)) * W =
          ∑ l' ∈ Finset.range (l + 1 - i'),
            (CΛ i' * (CL l' *
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
      calc CΛ i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
            (CL l' * Combinatorics.antidiagonalTupleGridWindow b (l' + 2))
          = (CΛ i' * CL l') * (Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
              Combinatorics.antidiagonalTupleGridWindow b (l' + 1 + 1)) := by
            rw [show l' + 2 = l' + 1 + 1 from rfl]
            ring
        _ ≤ (CΛ i' * CL l') *
              (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1) *
                Combinatorics.antidiagonalTupleGridWindow b (i' + (l' + 1) + 1)) := by
            refine mul_le_mul_of_nonneg_left hpair ?_
            exact mul_nonneg (hCΛ_nn i') (hCL_nn l')
        _ ≤ (CΛ i' * CL l') *
              (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1) * W) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCΛ_nn i') (hCL_nn l'))
            exact mul_le_mul_of_nonneg_left hmono
              (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _)
        _ = (CΛ i' * (CL l' *
              Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1))) * W := by
            ring
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
      (appCcGdiag_nonneg (E := E) l)) ?_
    rw [← Finset.sum_mul, ← mul_assoc]
  rw [deTurckArmCoeffDiffCc]
  refine le_trans (bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 l
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (deTurckArmCoeffDiffHalfCc (I := I) (M := M) g₀ g₁ g_bg))
    (deTurckArmCoeffDiffHalfCc (I := I) (M := M) g₀ g₁ g_bg) x) ?_
  have hswap : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 4 l
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (deTurckArmCoeffDiffHalfCc (I := I) (M := M) g₀ g₁ g_bg))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (deTurckArmCoeffDiffHalfCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 1) (deTurckArmCoeffDiffHalfCc (I := I) (M := M) g₀ g₁ g_bg) l x
  rw [hswap]
  linarith [hhalf]

private theorem bdCovDerivArmDiff_pointwise_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg -
                deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2) := by
  classical
  obtain ⟨CP, hCP_nn, hCP⟩ := bdPairTraceOp_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨CX, hCX_nn, hCX⟩ := bdXd_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      ∑ i' ∈ Finset.range (i + 1), CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * CX l)) * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1),
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hCP_nn i')
        (Finset.sum_nonneg fun l _ => mul_nonneg
          (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCX_nn l)))
          (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set W : ℝ := Combinatorics.antidiagonalTupleGridWindow b (i + 2) with hW_def
  have hW_nn : (0 : ℝ) ≤ W := Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i + 2)
  have hWtower : ∀ l, l ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg)))).toSection x) ≤
      (fr * (fr * CX l)) * Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by
    intro l hl
    have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg)))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg))).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg)))
        (fun y d => by
          rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) l x
    rw [hperm]
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg))).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 5 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 1
              (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg))).toSection x) :=
      rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1
          (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg)) l x
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 5 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 1
            (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg))).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) :=
      rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg) l x
    have h3 := hCX g₁ P htie hδ_le hδ0 hbound l x
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg))).toSection x)
        ≤ fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 5 l
              (slotExtendIter (I := I) (M := M) g₀ 0 4 1
                (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg))).toSection x) := h1
      _ ≤ fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) :=
          mul_le_mul_of_nonneg_left h2 hfr_nn
      _ ≤ fr * (fr * (CX l * Combinatorics.antidiagonalTupleGridWindow b (l + 2))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hfr_nn) hfr_nn
      _ = (fr * (fr * CX l)) * Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by
          ring
  have hlift : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg -
          deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g₀)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg))))).toSection x) := by
    rw [bdCovDerivArmDiff_eq_pairTrace (I := I) (M := M) g₀ g_bg g₁]
    rw [iteratedCovGrad_smul_real]
    rw [show (((-1 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg))))).toSection x) =
        (-1 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg))))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [riemannianFiberNormSq_smul]
    norm_num
  rw [hlift]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ i 2 6 2
    (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg))) x) ?_
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 6 2 i'
            (armPairTraceOpCc (I := I) (M := M) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg)))).toSection x) ≤
      (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * CX l)) *
          Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) * W := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 6 2 i'
          (armPairTraceOpCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CP i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 1) :=
      hCP g₁ P htie hδ_le hδ0 hbound i' x
    have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg)))).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - i'),
          (fr * (fr * CX l)) * Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by
      refine Finset.sum_le_sum fun l hl => ?_
      rw [Finset.mem_range] at hl
      exact hWtower l (by omega)
    have hsum_nn : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (deTurckArmCoeffDiffCc (I := I) (M := M) g₀ g₁ g_bg)))).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _
    have hA1_rhs_nn : (0 : ℝ) ≤ CP i' *
        Combinatorics.antidiagonalTupleGridWindow b (i' + 1) :=
      mul_nonneg (hCP_nn i')
        (Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i' + 1))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * CX l)) *
          Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) * W =
        ∑ l ∈ Finset.range (i + 1 - i'),
          (CP i' * ((fr * (fr * CX l)) *
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
    calc CP i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
          ((fr * (fr * CX l)) * Combinatorics.antidiagonalTupleGridWindow b (l + 2))
        = (CP i' * (fr * (fr * CX l))) *
            (Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
              Combinatorics.antidiagonalTupleGridWindow b (l + 1 + 1)) := by
          rw [show l + 2 = l + 1 + 1 from rfl]
          ring
      _ ≤ (CP i' * (fr * (fr * CX l))) *
            (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) *
              Combinatorics.antidiagonalTupleGridWindow b (i' + (l + 1) + 1)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (hCP_nn i')
            (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCX_nn l)))
      _ ≤ (CP i' * (fr * (fr * CX l))) *
            (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) * W) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (hCP_nn i')
              (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCX_nn l))))
          exact mul_le_mul_of_nonneg_left hmono
            (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _)
      _ = (CP i' * ((fr * (fr * CX l)) *
            Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1))) * W := by
          ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]


theorem exists_deTurckLieCovDerivArm_backgroundDifference_perOrder_l2_tameEnvelope_generic
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieCovDerivArmField (I := I) (M := M) g₀ g₁ g_bg -
                deTurckLieCovDerivArmField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨C, hC_nn, hpt⟩ := bdCovDerivArmDiff_pointwise_gridWindow (I := I) (M := M)
    g₀ g_bg hδ₁_lt
  obtain ⟨Kg, hKg_nn, hKg⟩ := bdL2_tameEnvelope_of_gridWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 2), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg fun k _ => hKg_nn k), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hwin_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by positivity
  have hsubj : deTurckLieCovDerivArmField (I := I) (M := M) g₀ g₁ g_bg -
      deTurckLieCovDerivArmField (I := I) (M := M) g₀ g₁ g₀ =
      deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g₀ := by
    rw [covDerivArmField_eq_dLaCoeffField, covDerivArmField_eq_dLaCoeffField]
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := bdDelta_nonneg (I := I) (M := M) g₀ x₀ P hδ
    have hδ_le' : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    rw [hsubj]
    exact hKg P hPball i (C i) (hC_nn i)
      (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g₀)
      (fun x => hpt g₁ P htie hδ_le' hδ0 hδ i x)
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieCovDerivArmField (I := I) (M := M) g₀ g₁ g_bg -
          deTurckLieCovDerivArmField (I := I) (M := M) g₀ g₁ g₀)‖ = 0 :=
      bdNorm_zero_of_isEmpty (I := I) (M := M) g₀ 2 (2 + i) _
    rw [hz]
    have hK_nn : 0 ≤ C i * ∑ k ∈ Finset.range (i + 2), Kg k :=
      mul_nonneg (hC_nn i) (Finset.sum_nonneg fun k _ => hKg_nn k)
    nlinarith [hwin_nn, hK_nn]


theorem exists_deTurckLieCovDerivArm_backgroundDifference_l2JetWindow
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
              - deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨K, hK_nn, hK⟩ :=
    exists_deTurckLieCovDerivArm_backgroundDifference_perOrder_l2_tameEnvelope_generic
      (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨K, hK_nn, ?_⟩
  intro T δ hδ_le hδ hδZ hball i s hs
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
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T 0 s)‖ ≤ R := by
    intro j hj
    rw [hcP, iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs]
    calc |s| * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤
        1 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
          mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ = ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := one_mul _
      _ ≤ R := hball j hj
  refine le_trans (hK (realizedFam (I := I) g₀ T 0 hδ hδZ s)
    (convexPerturbation (I := I) g₀ T 0 s) hδ_le hδP htie hPball i) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hK_nn i)
  refine add_le_add le_rfl ?_
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [hcP, iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs, mul_pow]
  have h1 : |s| ^ 2 ≤ 1 := by nlinarith [abs_nonneg s]
  nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖, h1,
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j T)]

def deTurckLieCovDerivRefoldPairTraceFamily (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ) (s : ℝ) : SmoothCcTensor g₀ 2 2 :=
  s • ∑ i : Fin 3, ε i • ((1 / 2 : ℝ) •
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (domDomCongrSection (I := I) g₀
              ((q i).trans (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
              (iteratedCovGrad (I := I) g₀ 0 2 2 T))))
      + ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (domDomCongrSection (I := I) g₀
              (((q i).trans (Equiv.swap (0 : Fin 4) 1)).trans
                (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
              (iteratedCovGrad (I := I) g₀ 0 2 2 T))))))

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
