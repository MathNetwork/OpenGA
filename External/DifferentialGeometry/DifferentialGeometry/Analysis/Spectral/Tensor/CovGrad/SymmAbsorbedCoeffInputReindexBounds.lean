import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open TensorRSNabla

section NormedReindexing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma ofModel_domDomCongr_toModel_eq {r : ℕ} {x : M} (σ' : Equiv.Perm (Fin r))
    (d : Tensor0SSpace r I x) :
    (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ'
        (Tensor0SSpace.toModel d)) : Tensor0SSpace r I x) =
      ContinuousMultilinearMap.domDomCongr σ'
        (show ContinuousMultilinearMap ℝ (fun _ : Fin r => TangentSpace I x) ℝ from d) := by
  have h : ContinuousMultilinearMap.domDomCongr σ' (Tensor0SSpace.toModel d) =
      Tensor0SSpace.toModel (ContinuousMultilinearMap.domDomCongr σ'
        (show ContinuousMultilinearMap ℝ (fun _ : Fin r => TangentSpace I x) ℝ from d)) := rfl
  rw [h, Tensor0SSpace.ofModel_toModel]

private lemma domDomCongr_perm_fin0_apply {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (σ : Equiv.Perm (Fin 0)) (f : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => A) ℝ) :
    ContinuousMultilinearMap.domDomCongr σ f = f := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  exact k.elim0

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma reindexCoeffFibGen_fin0 {s : ℕ} {x : M} (σ' : Equiv.Perm (Fin 0))
    (A : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) :
    reindexCoeffFibGen (I := I) 0 s σ' x A = A := by
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoeffFibGen_apply]
  congr 1
  rw [domDomCongr_perm_fin0_apply, Tensor0SSpace.ofModel_toModel]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma reindexCoeffGen_fin0 (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (R : SmoothCcTensor g₀ 0 s) (σ' : Equiv.Perm (Fin 0)) :
    reindexCoeffGen (I := I) (M := M) g₀ 0 s R σ' = R := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [reindexCoeffGen_toSection]
  exact reindexCoeffFibGen_fin0 (I := I) σ' (R.toSection x)

private def reindexInputSection {r : ℕ} (σ' : Equiv.Perm (Fin r))
    (w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯) :
    Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯ :=
  ContMDiffSection.mk
    (fun y => Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr σ' (Tensor0SSpace.toModel (w y))))
    (by
      refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
        (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
        (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr σ'
              (Tensor0SBundle.Tensor0SSpace.toModel (w x))) :
              Tensor0SBundle.Tensor0SSpace r I x))).mpr ?_
      have hYcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
        (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
        (fun x => w x)).mp w.contMDiff
      intro τ x₀
      refine (hYcoord (τ ∘ σ') x₀).congr_of_eventuallyEq ?_
      filter_upwards [Filter.univ_mem] with x _
      rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
      change (ContinuousMultilinearMap.domDomCongr σ'
          (Tensor0SBundle.Tensor0SSpace.toModel (w x)))
          (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
            ((Module.finBasis ℝ E) (τ j))) = _
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      rfl)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma reindexInputSection_apply {r : ℕ} (σ' : Equiv.Perm (Fin r))
    (w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯) (y : M) :
    (reindexInputSection (I := I) (M := M) σ' w) y =
      Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr σ' (Tensor0SSpace.toModel (w y))) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma section_tensorSectionMDiffAt {n : ℕ}
    (w : Cₛ^∞⟮I; Tensor0SModel n ℝ E, (fun y : M => Tensor0SSpace n I y)⟯) (x : M) :
    DifferentialGeometry.Integral.Connection.TensorSectionMDiffAt (I := I) n (fun y => w y) x :=
  (w.contMDiff.contMDiffAt).mdifferentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDerivAt_reindexCoeffGen (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g r s) (σ' : Equiv.Perm (Fin r)) (x : M) (v0 : E) :
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g r s
          (reindexCoeffGen (I := I) (M := M) g r s R σ') x v0) =
      reindexCoeffFibGen (I := I) r s σ' x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s R x v0) := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoeffFibGen_apply]
  rcases r with _ | r'
  · rw [reindexCoeffGen_fin0 (I := I) (M := M) g s R σ']
    congr 1
    rw [domDomCongr_perm_fin0_apply, Tensor0SSpace.ofModel_toModel]
  · obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := Tensor0SModel (r' + 1) ℝ E) (V := fun y : M => Tensor0SSpace (r' + 1) I y)
      (n := (⊤ : ℕ∞)) x D
    set ŵ := reindexInputSection (I := I) (M := M) σ' w with hŵ_def
    have hŵ_apply : ∀ y : M, ŵ y =
        Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ' (Tensor0SSpace.toModel (w y))) := by
      intro y; rw [hŵ_def, reindexInputSection_apply]
    have hŵx : ŵ x = Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr σ' (Tensor0SSpace.toModel (w x))) := hŵ_apply x
    have hL1 := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) (r' + 1) s
      (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
      (reindexCoeffGen (I := I) (M := M) g (r' + 1) s R σ').toSection w x v0
    have hL2 := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) (r' + 1) s
      (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
      R.toSection ŵ x v0
    have hF : (fun y : M =>
          (show Tensor0SSpace (r' + 1) I y →L[ℝ] Tensor0SSpace s I y from
            (reindexCoeffGen (I := I) (M := M) g (r' + 1) s R σ').toSection y) (w y)) =
        (fun y : M =>
          (show Tensor0SSpace (r' + 1) I y →L[ℝ] Tensor0SSpace s I y from R.toSection y) (ŵ y)) := by
      funext y
      rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply, hŵ_apply]
    have hcomm : Tensor0SNabla.tensor0SCovariantDerivative I M (r' + 1)
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (fun y => ŵ y) x v0 =
        Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ'
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M (r' + 1)
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
              (fun y => w y) x v0))) := by
      have hrel : ∀ y : M, (fun z => ŵ z) y =
          ContinuousMultilinearMap.domDomCongr σ'
            (show ContinuousMultilinearMap ℝ (fun _ : Fin (r' + 1) => TangentSpace I y) ℝ from
              (fun z => w z) y) := by
        intro y
        change ŵ y = ContinuousMultilinearMap.domDomCongr σ'
          (show ContinuousMultilinearMap ℝ (fun _ : Fin (r' + 1) => TangentSpace I y) ℝ from w y)
        rw [hŵ_apply]
        exact ofModel_domDomCongr_toModel_eq (I := I) σ' (w y)
      have hd := tensor0SCovariantDerivative_succ_domDomCongr (I := I) (M := M) r' g σ'
        (fun y => w y) (fun y => ŵ y) x v0
        (section_tensorSectionMDiffAt (I := I) (M := M) w x)
        (section_tensorSectionMDiffAt (I := I) (M := M) ŵ x)
        hrel
      exact hd.trans (ofModel_domDomCongr_toModel_eq (I := I) σ'
        (Tensor0SNabla.tensor0SCovariantDerivative I M (r' + 1)
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
          (fun y => w y) x v0)).symm
    rw [← hw, ← hŵx]
    change (show Tensor0SSpace (r' + 1) I x →L[ℝ] Tensor0SSpace s I x from
          TensorRSNabla.tensorRSCovariantDerivative I M (r' + 1) s
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
            (reindexCoeffGen (I := I) (M := M) g (r' + 1) s R σ').toSection x v0) (w x) =
        (show Tensor0SSpace (r' + 1) I x →L[ℝ] Tensor0SSpace s I x from
          TensorRSNabla.tensorRSCovariantDerivative I M (r' + 1) s
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
            R.toSection x v0) (ŵ x)
    rw [hL1, hL2, hF]
    congr 1
    rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply]
    congr 1
    exact hcomm.symm

omit [NeZero (Module.finrank ℝ E)] in
lemma covGrad_reindexCoeffGen (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g r s) (σ' : Equiv.Perm (Fin r)) :
    covGrad (I := I) (M := M) g r s (reindexCoeffGen (I := I) (M := M) g r s R σ') =
      reindexCoeffGen (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s R) σ' := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [covGrad_toSection_apply_eval, reindexCoeffGen_toSection, reindexCoeffFibGen_apply,
    covGrad_toSection_apply_eval]
  have hop := tensorCovDerivAt_reindexCoeffGen (I := I) (M := M) g r s R σ' x (v 0)
  have hopD := DFunLike.congr_fun hop D
  rw [reindexCoeffFibGen_apply] at hopD
  rw [hopD]

omit [NeZero (Module.finrank ℝ E)] in
lemma iteratedCovGrad_reindexCoeffGen (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g r s) (σ' : Equiv.Perm (Fin r)) (k : ℕ) :
    iteratedCovGrad (I := I) g r s k (reindexCoeffGen (I := I) (M := M) g r s R σ') =
      reindexCoeffGen (I := I) (M := M) g r (s + k)
        (iteratedCovGrad (I := I) g r s k R) σ' := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedCovGrad_succ, ih, covGrad_reindexCoeffGen]
    rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma domDomCongr_compMkPiAlgebra_eq (g : SmoothRiemannianMetric I M) (r : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin r → Fin n) (σ' : Equiv.Perm (Fin r)) :
    ContinuousMultilinearMap.domDomCongr σ'
        (show ContinuousMultilinearMap ℝ (fun _ : Fin r => TangentSpace I x) ℝ from
          ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
            (fun k => g.inner x (e (K k))))) =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin r => TangentSpace I x) ℝ from
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K (σ'.symm k)))))) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  rw [← Equiv.prod_comp σ' (fun j => g.inner x (e (K (σ'.symm j))) (v j))]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Equiv.symm_apply_apply]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_reindexCoeffFibGen (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) (σ' : Equiv.Perm (Fin r))
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x r s
        (show TensorRSSpace r s I x from reindexCoeffFibGen (I := I) r s σ' x A) n e K J =
      fiberNormSqComponent (I := I) (M := M) g x r s
        (show TensorRSSpace r s I x from A) n e (fun k => K (σ'.symm k)) J := by
  classical
  rw [fiberNormSqComponent, fiberNormSqComponent]
  rw [reindexCoeffFibGen_apply]
  congr 1
  rw [ofModel_domDomCongr_toModel_eq (I := I) σ']
  rw [domDomCongr_compMkPiAlgebra_eq (I := I) (M := M) g r x e K σ']

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_reindexCoeffFibGen (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (σ' : Equiv.Perm (Fin r)) (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x
        (show TensorRSSpace r s I x from reindexCoeffFibGen (I := I) r s σ' x A) =
      riemannianFiberNormSq (I := I) (M := M) g r s x
        (show TensorRSSpace r s I x from A) := by
  classical
  obtain ⟨n, e, _hn, _horth, _hpars, hsum⟩ :=
    exists_orthonormal_frame_riemannianFiberNormSq (I := I) (M := M) g r s x
  rw [hsum (show TensorRSSpace r s I x from reindexCoeffFibGen (I := I) r s σ' x A),
    hsum (show TensorRSSpace r s I x from A)]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ' (Equiv.refl (Fin n)))
    (fun K => ∑ J : Fin s → Fin n,
      fiberNormSqSummand (I := I) (M := M) g x r s
        (show TensorRSSpace r s I x from reindexCoeffFibGen (I := I) r s σ' x A) n e K J)
    (fun K => ∑ J : Fin s → Fin n,
      fiberNormSqSummand (I := I) (M := M) g x r s
        (show TensorRSSpace r s I x from A) n e K J)
    (fun K => ?_)
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [fiberNormSqSummand_eq_component_sq, fiberNormSqSummand_eq_component_sq]
  rw [fiberNormSqComponent_reindexCoeffFibGen (I := I) (M := M) g r s x A σ' e K J]
  have hev : (Equiv.arrowCongr σ' (Equiv.refl (Fin n))) K = (fun k => K (σ'.symm k)) := by
    funext a; simp [Equiv.arrowCongr]
  rw [hev]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
lemma norm_reindexCoeffGen_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor g r s) (σ' : Equiv.Perm (Fin r)) :
    ‖reindexCoeffGen (I := I) (M := M) g r s W σ'‖ = ‖W‖ := by
  classical
  have hpt : ∀ x : M,
      tensorInnerPointwise (I := I) (M := M) g r s x
          ((reindexCoeffGen (I := I) (M := M) g r s W σ').toFun x)
          ((reindexCoeffGen (I := I) (M := M) g r s W σ').toFun x) =
        tensorInnerPointwise (I := I) (M := M) g r s x (W.toFun x) (W.toFun x) := by
    intro x
    rw [SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply,
      ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x
        ((reindexCoeffGen (I := I) (M := M) g r s W σ').toSection x),
      ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (W.toSection x),
      reindexCoeffGen_toSection]
    exact riemannianFiberNormSq_reindexCoeffFibGen (I := I) (M := M) g r s x σ' (W.toSection x)
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def]
  unfold tensorL2Norm tensorL2Inner
  simp_rw [hpt]

end NormedReindexing

section RiemannianBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma iteratedCovGrad_smul_aux (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem symmAbsorbedCoeff_riemannianFiberNormSq_le (g₀ : SmoothRiemannianMetric I M) (i : ℕ)
    (R : SmoothCcTensor g₀ (2 + i) 2) (σ' : Equiv.Perm (Fin (2 + i))) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ (2 + i) 2 x
        ((symmAbsorbedCoeff (I := I) (M := M) g₀ i R σ').toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ (2 + i) 2 x (R.toSection x) := by
  classical
  set Rm : TensorRSModel (2 + i) 2 ℝ E :=
    TensorRSSpace.toModel (R.toSection x) with hRm
  set Pm : TensorRSModel (2 + i) 2 ℝ E :=
    TensorRSSpace.toModel
      ((reindexCoeffGen (I := I) (M := M) g₀ (2 + i) 2 R σ').toSection x) with hPm
  have htoModel : TensorRSSpace.toModel
      ((symmAbsorbedCoeff (I := I) (M := M) g₀ i R σ').toSection x) =
      (1 / 2 : ℝ) • Rm + (1 / 2 : ℝ) • Pm := by
    have hsec : (symmAbsorbedCoeff (I := I) (M := M) g₀ i R σ').toSection x =
        (1 / 2 : ℝ) • (R.toSection x) +
          (1 / 2 : ℝ) • ((reindexCoeffGen (I := I) (M := M) g₀ (2 + i) 2 R σ').toSection x) := rfl
    rw [hsec, TensorRSSpace.toModel_add, TensorRSSpace.toModel_smul, TensorRSSpace.toModel_smul,
      ← hRm, ← hPm]
  have hBA : tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x Pm Pm =
      tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x Rm Rm := by
    rw [hPm, hRm,
      ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x
        ((reindexCoeffGen (I := I) (M := M) g₀ (2 + i) 2 R σ').toSection x),
      ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x
        (R.toSection x),
      reindexCoeffGen_toSection]
    exact riemannianFiberNormSq_reindexCoeffFibGen (I := I) (M := M) g₀ (2 + i) 2 x σ'
      (R.toSection x)
  have hA_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x Rm Rm := by
    rw [hRm, ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x
      (R.toSection x)]
    exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (2 + i) 2 x (R.toSection x)
  have hCS : tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x Rm Pm ^ 2 ≤
      tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x Rm Rm *
        tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x Pm Pm :=
    tensorInnerPointwise_sq_le_mul (I := I) (M := M) g₀ (2 + i) 2 x Rm Pm
  have hCA : tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x Rm Pm ≤
      tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x Rm Rm := by
    nlinarith [hCS, hA_nn, hBA,
      sq_nonneg (tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x Rm Pm -
        tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x Rm Rm),
      sq_nonneg (tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x Rm Pm +
        tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x Rm Rm)]
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x
      ((symmAbsorbedCoeff (I := I) (M := M) g₀ i R σ').toSection x),
    htoModel,
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ (2 + i) 2 x (R.toSection x),
    ← hRm]
  simp only [tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  rw [tensorInnerPointwise_symm (I := I) (M := M) g₀ (2 + i) 2 x Pm Rm]
  nlinarith [hCA, hBA]

omit [NeZero (Module.finrank ℝ E)] in
theorem symmAbsorbedCoeff_jet_le (g₀ : SmoothRiemannianMetric I M) (i n : ℕ)
    (R : SmoothCcTensor g₀ (2 + i) 2) (σ' : Equiv.Perm (Fin (2 + i))) :
    (∑ k ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g₀ (2 + i) 2 k (symmAbsorbedCoeff (I := I) (M := M) g₀ i R σ')‖ ^ 2) ≤
      ∑ k ∈ Finset.range n, ‖iteratedCovGrad (I := I) g₀ (2 + i) 2 k R‖ ^ 2 := by
  classical
  refine Finset.sum_le_sum (fun k _ => ?_)
  set X : SmoothCcTensor g₀ (2 + i) (2 + k) :=
    iteratedCovGrad (I := I) g₀ (2 + i) 2 k R with hX
  set Y : SmoothCcTensor g₀ (2 + i) (2 + k) :=
    iteratedCovGrad (I := I) g₀ (2 + i) 2 k
      (reindexCoeffGen (I := I) (M := M) g₀ (2 + i) 2 R σ') with hY
  have hsymm : iteratedCovGrad (I := I) g₀ (2 + i) 2 k
      (symmAbsorbedCoeff (I := I) (M := M) g₀ i R σ') = (1 / 2 : ℝ) • X + (1 / 2 : ℝ) • Y := by
    rw [hX, hY, symmAbsorbedCoeff, iteratedCovGrad_add, iteratedCovGrad_smul_aux,
      iteratedCovGrad_smul_aux]
  have hY_norm : ‖Y‖ = ‖X‖ := by
    rw [hY, iteratedCovGrad_reindexCoeffGen, ← hX]
    exact norm_reindexCoeffGen_eq (I := I) (M := M) g₀ (2 + i) (2 + k) X σ'
  have htri : ‖(1 / 2 : ℝ) • X + (1 / 2 : ℝ) • Y‖ ≤ ‖X‖ := by
    calc ‖(1 / 2 : ℝ) • X + (1 / 2 : ℝ) • Y‖
        ≤ ‖(1 / 2 : ℝ) • X‖ + ‖(1 / 2 : ℝ) • Y‖ := norm_add_le _ _
      _ = (1 / 2 : ℝ) * ‖X‖ + (1 / 2 : ℝ) * ‖Y‖ := by
          rw [norm_smul, norm_smul]; norm_num
      _ = (1 / 2 : ℝ) * ‖X‖ + (1 / 2 : ℝ) * ‖X‖ := by rw [hY_norm]
      _ = ‖X‖ := by ring
  rw [hsymm]
  exact pow_le_pow_left₀ (norm_nonneg _) htri 2

end RiemannianBounds

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
