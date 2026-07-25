import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldInputSlotSymmetrization
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.FlatArmCoeffConnectionDifferenceBridge
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindowGInvQuadResidual


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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section bgrConversion

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable (g₀ g₁ : SmoothRiemannianMetric I M)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma unitModel_add_pt (s : ℕ) (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A + B) x =
      unitModel (I := I) (M := M) g₀ s A x + unitModel (I := I) (M := M) g₀ s B x := by
  rw [unitModel, unitModel, unitModel,
    show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (A + B).toSection x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x) from by
      rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_smul_pt (s : ℕ) (c : ℝ) (A : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (c • A) x =
      c • unitModel (I := I) (M := M) g₀ s A x := by
  have h : ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (c • A).toSection x)
      (unitTensor (I := I) (M := M) x)) =
      c • ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
        (unitTensor (I := I) (M := M) x)) := by
    rw [show ((c • A).toSection x) = c • (A.toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl
  rw [unitModel, unitModel, h, Tensor0SSpace.toModel_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma unitModel_sub_pt (s : ℕ) (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A - B) x =
      unitModel (I := I) (M := M) g₀ s A x - unitModel (I := I) (M := M) g₀ s B x := by
  have h : ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (A - B).toSection x)
      (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) := by
    rw [show ((A - B).toSection x) = A.toSection x - B.toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rfl
  rw [unitModel, unitModel, unitModel, h, Tensor0SSpace.toModel_sub]

omit [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_cons_sum_smul (_x : M) {n : ℕ}
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
lemma toModel_cons_cons_sum_smul (_x : M) {n : ℕ}
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma unitModel_eq_ccTensorBilin_pt (S : SmoothCcTensor g₀ 0 2) (b : M)
    (u w : TangentSpace I b) :
    unitModel (I := I) (M := M) g₀ 2 S b ![u, w] = smoothCcTensorBilinForm (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply (I := I) g₀ S b u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma reindexCoeffGen_one_eq (r s : ℕ) (R : SmoothCcTensor g₀ r s) :
    reindexCoeffGen (I := I) (M := M) g₀ r s R 1 = R := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((reindexCoeffGen (I := I) (M := M) g₀ r s R 1).toSection x) D =
      reindexCoeffFibGen (I := I) r s 1 x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) D from rfl]
  rw [reindexCoeffFibGen_apply]
  refine congrArg _ ?_
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  rfl

lemma riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq (r s : ℕ) (σ : Equiv.Perm (Fin s))
    (R : SmoothCcTensor g₀ r s) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i
          (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ R)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i R).toSection x) := by
  have h := rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ r s
    (1 : Equiv.Perm (Fin r)) σ R i x
  rw [reindexCoeffGen_one_eq (I := I) (M := M) g₀ r s
    (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ R)] at h
  exact h

def ricciFoldRemainderSlotPerm : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![1, 3, 4, 5, 0, 2] : Fin 6 → Fin 6) i,
   fun i => (![4, 0, 5, 1, 2, 3] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

def ricciFoldWeightBPerm : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 0, 2, 1, 4, 3] : Fin 6 → Fin 6) i,
   fun i => (![1, 3, 2, 5, 4, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

def tauM1 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 2, 0, 3, 4, 1] : Fin 6 → Fin 6) i,
   fun i => (![2, 5, 1, 3, 4, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

def tauM2 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 2, 0, 1, 4, 3] : Fin 6 → Fin 6) i,
   fun i => (![2, 3, 1, 5, 4, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

def tauM3 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 4, 0, 3, 2, 1] : Fin 6 → Fin 6) i,
   fun i => (![2, 5, 4, 3, 1, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

def tauM4 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 4, 0, 1, 2, 3] : Fin 6 → Fin 6) i,
   fun i => (![2, 3, 4, 5, 1, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma mvOrthoFrame_center_repr (g : SmoothRiemannianMetric I M) (x : M)
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

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma slotExtend_toModel_cons (r s : ℕ) (Φ : SmoothCcTensor g₀ r s) (x : M)
    (D : Tensor0SSpace (r + 1) I x) (v0 : TangentSpace I x) (vs : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (slotExtend (I := I) (M := M) g₀ r s Φ).toSection x) D)
        (Fin.cons (show E from v0) vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D v0)) vs := by
  rw [show ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (slotExtend (I := I) (M := M) g₀ r s Φ).toSection x) D) =
      slotExtendPointwise (I := I) (M := M) g₀ r s x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x) D from rfl]
  exact slotExtendFib_apply_eval (I := I) (M := M) g₀ r s x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x) D
    (show E from v0) vs

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma slotExtendIter_two_toModel (X : SmoothCcTensor g₀ 0 4) (x : M)
    (D : Tensor0SSpace 2 I x) (u : Fin 6 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1] *
        unitModel (I := I) (M := M) g₀ 4 X x (fun k : Fin 4 => u (Fin.natAdd 2 k)) := by
  have hu : (fun k : Fin 6 => (u k : E)) =
      Fin.cons (show E from u 0)
        (Fin.cons (show E from u 1) (fun k : Fin 4 => (u (Fin.natAdd 2 k) : E))) := by
    funext k
    refine Fin.cases rfl (fun k1 => ?_) k
    refine Fin.cases rfl (fun k2 => ?_) k1
    change (u (Fin.succ (Fin.succ k2)) : E) = (u (Fin.natAdd 2 k2) : E)
    congr 1
    exact Fin.ext (by simp [Fin.succ, Fin.natAdd]; omega)
  rw [show (Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) u) =
      (Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtend (I := I) (M := M) g₀ 1 5
            (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X)).toSection x) D)
        (fun k : Fin 6 => (u k : E))) from rfl]
  rw [hu]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 1 5
    (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X) x D (u 0)]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0))) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtend (I := I) (M := M) g₀ 0 4 X).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0))) from rfl]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 0 4 X x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1)]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1) with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![u 0, u 1] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (v0 := (u 1 : E))
      (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D) (v0 := (u 0 : E)) (vs := Fin.cons (show E from u 1) (fun i : Fin 0 => i.elim0))
    rw [h2]
    refine congrArg _ ?_
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    refine Fin.cases rfl (fun i2 => i2.elim0) i
  have hdecomp := tensor0S_rank0_eq_smul_unit (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma slotExtendIter_three_toModel (X : SmoothCcTensor g₀ 0 3) (x : M)
    (D : Tensor0SSpace 3 I x) (u : Fin 6 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 X).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1, u 2] *
        unitModel (I := I) (M := M) g₀ 3 X x (fun k : Fin 3 => u (Fin.natAdd 3 k)) := by
  have hu : (fun k : Fin 6 => (u k : E)) =
      Fin.cons (show E from u 0)
        (Fin.cons (show E from u 1)
          (Fin.cons (show E from u 2) (fun k : Fin 3 => (u (Fin.natAdd 3 k) : E)))) := by
    funext k
    refine Fin.cases rfl (fun k1 => ?_) k
    refine Fin.cases rfl (fun k2 => ?_) k1
    refine Fin.cases rfl (fun k3 => ?_) k2
    change (u (Fin.succ (Fin.succ (Fin.succ k3))) : E) = (u (Fin.natAdd 3 k3) : E)
    congr 1
    exact Fin.ext (by simp [Fin.succ, Fin.natAdd]; omega)
  rw [show (Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 X).toSection x) D) u) =
      (Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtend (I := I) (M := M) g₀ 2 5
            (slotExtendIter (I := I) (M := M) g₀ 0 3 2 X)).toSection x) D)
        (fun k : Fin 6 => (u k : E))) from rfl]
  rw [hu]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 2 5
    (slotExtendIter (I := I) (M := M) g₀ 0 3 2 X) x D (u 0)]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2 X).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0))) =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtend (I := I) (M := M) g₀ 1 4
          (slotExtendIter (I := I) (M := M) g₀ 0 3 1 X)).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0))) from rfl]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 1 4
    (slotExtendIter (I := I) (M := M) g₀ 0 3 1 X) x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 1 X).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1))) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtend (I := I) (M := M) g₀ 0 3 X).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1))) from rfl]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 0 3 X x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)) (u 2)]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)) (u 2) with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![u 0, u 1, u 2] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)) (v0 := (u 2 : E))
      (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (v0 := (u 1 : E))
      (vs := Fin.cons (show E from u 2) (fun i : Fin 0 => i.elim0))
    rw [h2]
    have h3 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2)
      (T := D) (v0 := (u 0 : E))
      (vs := Fin.cons (show E from u 1)
        (Fin.cons (show E from u 2) (fun i : Fin 0 => i.elim0)))
    rw [h3]
    refine congrArg _ ?_
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    refine Fin.cases rfl (fun i2 => ?_) i
    refine Fin.cases rfl (fun i3 => i3.elim0) i2
  have hdecomp := tensor0S_rank0_eq_smul_unit (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma metricCcTensor_unitModel_apply (g : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2 (metricCcTensor (I := I) (M := M) g₀ g) x m =
      g.inner x (m 0) (m 1) := by
  have hbase : unitModel (I := I) (M := M) g₀ 2 (metricCcTensor (I := I) (M := M) g₀ g) x =
      Tensor0SSpace.toModel (metricCcTensorFib (I := I) g x) := by
    rw [unitModel]
    change Tensor0SSpace.toModel
        ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricCcTensorFib (I := I) g x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
            (1 : ℝ))) =
      Tensor0SSpace.toModel (metricCcTensorFib (I := I) g x)
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [hbase]
  rfl

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma tensorBilinearPairing_expand_left (S : SmoothCcTensor g₀ 0 2) (x : M)
    (u w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g₀ S x u w =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x u (smoothOrthoFrame (I := I) g₀ x e x) *
          smoothCcTensorBilinForm (I := I) g₀ S x (smoothOrthoFrame (I := I) g₀ x e x) w := by
  conv_lhs => rw [orthoFrame_expansion_at_center (I := I) (M := M) g₀ x u]
  rw [map_sum (smoothCcTensorBilinForm (I := I) g₀ S x) _ Finset.univ, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul (smoothCcTensorBilinForm (I := I) g₀ S x), ContinuousLinearMap.smul_apply, smul_eq_mul]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma tensorBilinearPairing_expand_right (S : SmoothCcTensor g₀ 0 2) (x : M)
    (u w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g₀ S x u w =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x w (smoothOrthoFrame (I := I) g₀ x e x) *
          smoothCcTensorBilinForm (I := I) g₀ S x u (smoothOrthoFrame (I := I) g₀ x e x) := by
  conv_lhs => rw [orthoFrame_expansion_at_center (I := I) (M := M) g₀ x w]
  rw [map_sum (smoothCcTensorBilinForm (I := I) g₀ S x u) _ Finset.univ]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul (smoothCcTensorBilinForm (I := I) g₀ S x u), smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_vec3_slot0_sum_smul (_x : M)
    (Zm : Tensor0SModel 3 ℝ E) (d : ℕ) (t : Fin d → ℝ) (u : Fin d → E) (a b : E) :
    Zm ![∑ c, t c • u c, a, b] = ∑ c, t c * Zm ![u c, a, b] := by
  classical
  have h1 : ∀ v : E, (![v, a, b] : Fin 3 → E) = Function.update ![(0 : E), a, b] 0 v := by
    intro v
    funext k
    fin_cases k <;> simp [Function.update]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update ![(0 : E), a, b] 0 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update ![(0 : E), a, b] 0 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a' ss ha ih =>
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
lemma toModel_vec3_slot2_sum_smul (_x : M)
    (Zm : Tensor0SModel 3 ℝ E) (d : ℕ) (t : Fin d → ℝ) (u : Fin d → E) (a b : E) :
    Zm ![a, b, ∑ c, t c • u c] = ∑ c, t c * Zm ![a, b, u c] := by
  classical
  have h1 : ∀ v : E, (![a, b, v] : Fin 3 → E) = Function.update ![a, b, (0 : E)] 2 v := by
    intro v
    funext k
    fin_cases k <;> simp [Function.update]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update ![a, b, (0 : E)] 2 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update ![a, b, (0 : E)] 2 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a' ss ha ih =>
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

end bgrConversion

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
