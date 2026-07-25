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

theorem exists_fn_of_forall_exists_bounded (N : ℕ) (Q : ℕ → ℝ → Prop)
    (h : ∀ k, k ≤ N → ∃ c : ℝ, 0 ≤ c ∧ Q k c) :
    ∃ f : ℕ → ℝ, (∀ k, 0 ≤ f k) ∧ ∀ k, k ≤ N → Q k (f k) := by
  induction N with
  | zero =>
    obtain ⟨c, hc0, hc⟩ := h 0 le_rfl
    refine ⟨fun _ => c, fun _ => hc0, ?_⟩
    intro k hk
    rw [Nat.le_zero.mp hk]
    exact hc
  | succ N ih =>
    obtain ⟨f, hf0, hf⟩ := ih (fun k hk => h k (le_trans hk (Nat.le_succ N)))
    obtain ⟨c, hc0, hc⟩ := h (N + 1) le_rfl
    refine ⟨Function.update f (N + 1) c, ?_, ?_⟩
    · intro k
      by_cases hk : k = N + 1
      · rw [hk, Function.update_self]; exact hc0
      · rw [Function.update_of_ne hk]; exact hf0 k
    · intro k hk
      by_cases hkN : k = N + 1
      · rw [hkN, Function.update_self]; exact hc
      · rw [Function.update_of_ne hkN]
        exact hf k (by omega)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianMetric_inner_left_injective (g : SmoothRiemannianMetric I M) (x : M)
    {v w : TangentSpace I x} (h : ∀ u : TangentSpace I x, g.inner x v u = g.inner x w u) :
    v = w := by
  by_contra hne
  have hvw : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g.pos x (v - w) hvw
  have hzero : g.inner x (v - w) (v - w) = 0 := by
    have h' := h (v - w)
    rw [show (g.inner x) (v - w) = (g.inner x) v - (g.inner x) w from
        map_sub (g.inner x) v w,
      ContinuousLinearMap.sub_apply, h', sub_self]
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

private def lieArm1SharpModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (k : Fin (Module.finrank ℝ E)) : TangentSpace I x :=
  cometricLmodel (I := I) g₁ x
    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) ((Module.finBasis ℝ E).cDualBasis k))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem lieArm1_cometric_collapse (g₁ : SmoothRiemannianMetric I M) (x : M)
    (w : TangentSpace I x) :
    ∑ k : Fin (Module.finrank ℝ E),
        g₁.inner x w ((Module.finBasis ℝ E) k) • lieArm1SharpModel (I := I) g₁ x k = w := by
  classical
  refine riemannianMetric_inner_left_injective (I := I) g₁ x (fun u => ?_)
  rw [show g₁.inner x (∑ k : Fin (Module.finrank ℝ E),
        g₁.inner x w ((Module.finBasis ℝ E) k) • lieArm1SharpModel (I := I) g₁ x k) u =
      ∑ k : Fin (Module.finrank ℝ E), g₁.inner x w ((Module.finBasis ℝ E) k) *
        g₁.inner x (lieArm1SharpModel (I := I) g₁ x k) u from by
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    rfl]
  have hdual : ∀ k : Fin (Module.finrank ℝ E),
      g₁.inner x (lieArm1SharpModel (I := I) g₁ x k) u =
        ((Module.finBasis ℝ E).cDualBasis k) (u : E) := fun k =>
    cometricLmodel_covectorOfCLM_inner (I := I) g₁ x ((Module.finBasis ℝ E).cDualBasis k) u
  rw [Finset.sum_congr rfl fun k _ => by rw [hdual k]]
  have hcd : ∀ k : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).cDualBasis k) (u : E) =
        (Module.finBasis ℝ E).repr (u : E) k := by
    intro k
    rw [show ((Module.finBasis ℝ E).cDualBasis k : E →L[ℝ] ℝ)
        = LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).dualBasis k) from rfl,
      LinearMap.coe_toContinuousLinearMap']
    exact Module.Basis.dualBasis_apply (Module.finBasis ℝ E) k (u : E)
  rw [Finset.sum_congr rfl fun k _ => by rw [hcd k]]
  have hrepr : (u : TangentSpace I x) = ∑ k : Fin (Module.finrank ℝ E),
      (Module.finBasis ℝ E).repr (u : E) k • ((Module.finBasis ℝ E) k : TangentSpace I x) := by
    exact_mod_cast ((Module.finBasis ℝ E).sum_repr (u : E)).symm
  conv_rhs => rw [hrepr]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rw [smul_eq_mul, mul_comm]

def deTurckLieTraceCoeffPiece (g₀ g₁ : SmoothRiemannianMetric I M) (σ' : Equiv.Perm (Fin 4))
    (ρ : Equiv.Perm (Fin 3)) (Ψ : SmoothCcTensor g₀ 1 2) : SmoothCcTensor g₀ 3 2 :=
  reindexCoeffGen (I := I) (M := M) g₀ 3 2
    (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
      (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)))
    ρ

private def lieArm1TraceArg (g₁ : SmoothRiemannianMetric I M) (σ' : Equiv.Perm (Fin 4)) (x : M)
    (m : Fin 2 → TangentSpace I x) (k : Fin (Module.finrank ℝ E)) : Fin 4 → E :=
  (Fin.cons ((lieArm1SharpModel (I := I) g₁ x k : TangentSpace I x) : E)
    (Fin.cons (((Module.finBasis ℝ E) k : E)) (fun j : Fin 2 => ((m j : TangentSpace I x) : E)))) ∘ σ'

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem lieArm1Piece_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (Ψ : SmoothCcTensor g₀ 1 2)
    (K : ∀ y : M, TangentSpace I y → TangentSpace I y → TangentSpace I y) (x : M)
    (hΨ : ∀ (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x),
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x) om) YZ =
        om (fun _ : Fin 1 => K x (YZ 0) (YZ 1)))
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ Ψ).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ((Fin.cons (lieArm1TraceArg (I := I) g₁ σ' x m k 0)
            (Fin.cons (lieArm1TraceArg (I := I) g₁ σ' x m k 1)
              (fun _ : Fin 1 =>
                ((K x ((lieArm1TraceArg (I := I) g₁ σ' x m k 2 : E) : TangentSpace I x)
                    ((lieArm1TraceArg (I := I) g₁ σ' x m k 3 : E) : TangentSpace I x) :
                  TangentSpace I x) : E)))) ∘ ρ) := by
  classical
  set D' : Tensor0SSpace 3 I x :=
    Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
      (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel D))
    with hD'
  have happ : (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ Ψ).toSection x) D =
      deTurckLieTraceFib (I := I) g₁ σ' x
        (slotExtendPointwise (I := I) (M := M) g₀ 2 3 x
          (slotExtendPointwise (I := I) (M := M) g₀ 1 2 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x)) D') := by
    rw [deTurckLieTraceCoeffPiece, reindexCoeffGen_toSection]
    rw [reindexCoeffFibGen_apply (I := I) 3 2 ρ x
      (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
          (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection x)
      D]
    rw [appCcRS_toSection]
    rw [ContinuousLinearMap.comp_apply]
    rw [deTurckLieTraceCoeff_toSection]
    rfl
  rw [happ]
  set U : Tensor0SSpace 4 I x :=
    slotExtendPointwise (I := I) (M := M) g₀ 2 3 x
      (slotExtendPointwise (I := I) (M := M) g₀ 1 2 x
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x)) D' with hU
  have htr : Tensor0SSpace.toModel (deTurckLieTraceFib (I := I) g₁ σ' x U)
      (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel U (lieArm1TraceArg (I := I) g₁ σ' x m k) := by
    rw [show deTurckLieTraceFib (I := I) g₁ σ' x U =
        cometricDoubleTraceFib (I := I) g₁ 2 x (domDomCongrFibPerm (I := I) σ' x U) from rfl]
    rw [cometricDoubleTraceFib_toModel]
    rw [domDomCongrFibPerm_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    rw [modelDoubleTrace_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  rw [htr]
  refine Finset.sum_congr rfl fun k _ => ?_
  set w : Fin 4 → E := lieArm1TraceArg (I := I) g₁ σ' x m k with hw
  set D₂ : Tensor0SSpace 2 I x :=
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x) D' (w 0) with hD₂
  set om : Tensor0SSpace 1 I x :=
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) D₂ (w 1) with hom
  set kE : E := ((K x ((w 2 : E) : TangentSpace I x) ((w 3 : E) : TangentSpace I x) :
    TangentSpace I x) : E) with hkE
  calc Tensor0SSpace.toModel U w
      = Tensor0SSpace.toModel U (Fin.cons (w 0) (Matrix.vecTail w)) :=
        congrArg (Tensor0SSpace.toModel U) (Fin.cons_self_tail w).symm
    _ = Tensor0SSpace.toModel
          (slotExtendPointwise (I := I) (M := M) g₀ 1 2 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x) D₂)
          (Matrix.vecTail w) := by
        rw [hU]
        exact slotExtendFib_apply_eval (I := I) (M := M) g₀ 2 3 x _ D' (w 0) (Matrix.vecTail w)
    _ = Tensor0SSpace.toModel
          (slotExtendPointwise (I := I) (M := M) g₀ 1 2 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x) D₂)
          (Fin.cons (Matrix.vecTail w 0) (Matrix.vecTail (Matrix.vecTail w))) :=
        congrArg (Tensor0SSpace.toModel _) (Fin.cons_self_tail (Matrix.vecTail w)).symm
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x) om)
          (Matrix.vecTail (Matrix.vecTail w)) := by
        exact slotExtendFib_apply_eval (I := I) (M := M) g₀ 1 2 x _ D₂ (Matrix.vecTail w 0)
          (Matrix.vecTail (Matrix.vecTail w))
    _ = om (fun _ : Fin 1 =>
          K x ((w 2 : E) : TangentSpace I x) ((w 3 : E) : TangentSpace I x)) :=
        hΨ om (fun j : Fin 2 => ((Matrix.vecTail (Matrix.vecTail w) j : E) : TangentSpace I x))
    _ = Tensor0SSpace.toModel om (fun _ : Fin 1 => kE) := rfl
    _ = Tensor0SSpace.toModel D₂ (Fin.cons (w 1) (fun _ : Fin 1 => kE)) := by
        rw [hom]
        exact tensor0S_curry_apply_eval (I := I) (M := M) (n := 1) D₂ (w 1) (fun _ : Fin 1 => kE)
    _ = Tensor0SSpace.toModel D' (Fin.cons (w 0) (Fin.cons (w 1) (fun _ : Fin 1 => kE))) := by
        rw [hD₂]
        exact tensor0S_curry_apply_eval (I := I) (M := M) (n := 2) D' (w 0)
          (Fin.cons (w 1) (fun _ : Fin 1 => kE))
    _ = Tensor0SSpace.toModel D
          ((Fin.cons (w 0) (Fin.cons (w 1) (fun _ : Fin 1 => kE))) ∘ ρ) := by
        rw [hD', Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
          ContinuousMultilinearMap.domDomCongr_apply]
        rfl
    _ = Tensor0SSpace.toModel D
          ((Fin.cons (lieArm1TraceArg (I := I) g₁ σ' x m k 0)
            (Fin.cons (lieArm1TraceArg (I := I) g₁ σ' x m k 1)
              (fun _ : Fin 1 =>
                ((K x ((lieArm1TraceArg (I := I) g₁ σ' x m k 2 : E) : TangentSpace I x)
                    ((lieArm1TraceArg (I := I) g₁ σ' x m k 3 : E) : TangentSpace I x) :
                  TangentSpace I x) : E)))) ∘ ρ) := rfl

def lieArm1ConnDiffBgCc (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection := (connDiffSection (I := I) g₁ g_bg).toSection
  hasCompactSupport := (connDiffSection (I := I) g₁ g_bg).hasCompactSupport

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem lieArm1ConnDiffBgCc_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      connDiffFib (I := I) g₁ g_bg x := rfl

def lieArm1LoweredBgKappa (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection := (connDiffLoweredCc (I := I) g₁ g_bg).toSection
  hasCompactSupport := (connDiffLoweredCc (I := I) g₁ g_bg).hasCompactSupport

def lieArm1PsiB (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2
    (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
      (domDomCongrSection (I := I) g₀ (⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩ :
        Equiv.Perm (Fin 3))
        (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))
    (sharpFlatEndoCc (I := I) g₀ g₁)

def lieArm1RhoSlot0 : Equiv.Perm (Fin 3) := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

def lieArm1RhoSlot1 : Equiv.Perm (Fin 3) := ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩

def lieArm1SigmaA : Equiv.Perm (Fin 4) := ⟨![2, 0, 3, 1], ![1, 3, 0, 2], by decide, by decide⟩

def lieArm1SigmaASwap : Equiv.Perm (Fin 4) := ⟨![3, 0, 2, 1], ![1, 3, 2, 0], by decide, by decide⟩

def lieArm1SigmaC : Equiv.Perm (Fin 4) := ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

def lieArm1SigmaCSwap : Equiv.Perm (Fin 4) := ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

def lieArm1SigmaD : Equiv.Perm (Fin 4) := ⟨![3, 0, 2, 1], ![1, 3, 2, 0], by decide, by decide⟩

def lieArm1SigmaDSwap : Equiv.Perm (Fin 4) := ⟨![2, 0, 3, 1], ![1, 3, 0, 2], by decide, by decide⟩

def lieArm1SigmaESwap : Equiv.Perm (Fin 4) := ⟨![0, 1, 3, 2], ![0, 1, 3, 2], by decide, by decide⟩

def lieArm1SigmaF : Equiv.Perm (Fin 4) := ⟨![0, 3, 2, 1], ![0, 3, 2, 1], by decide, by decide⟩

def lieArm1SigmaFSwap : Equiv.Perm (Fin 4) := ⟨![0, 2, 3, 1], ![0, 3, 1, 2], by decide, by decide⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem lieArm1_normSq_eq_integral (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor g r s) :
    ‖W‖ ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (W.toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [SmoothCcTensor.norm_def (I := I) (M := M) W,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r s W]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lieArm1_icg_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

omit [NeZero (Module.finrank ℝ E)] in
private theorem lieArm1_normSq_icg_reindex_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor g r s) (ρ : Equiv.Perm (Fin r)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g r s i (reindexCoeffGen (I := I) (M := M) g r s W ρ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s i W‖ ^ 2 := by
  rw [lieArm1_normSq_eq_integral, lieArm1_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g r s W ρ i x

omit [NeZero (Module.finrank ℝ E)] in
private theorem lieArm1_normSq_icg_domDom_eq (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g 0 s i (domDomCongrSection (I := I) g σ S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g 0 s i S‖ ^ 2 := by
  rw [lieArm1_normSq_eq_integral, lieArm1_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g σ S i x

omit [NeZero (Module.finrank ℝ E)] in
theorem lieArm1_normSq_icg_raise_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 (s + 2)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g 1 (s + 1) i
        (cometricRaiseSlot0Field (I := I) (M := M) g s W)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g 0 (s + 2) i W‖ ^ 2 := by
  rw [lieArm1_normSq_eq_integral, lieArm1_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g s W i x

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem lieArm1_norm_isEmpty (hM : IsEmpty M) (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (W : SmoothCcTensor g r s) : ‖W‖ = 0 := by
  haveI := hM
  rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
    MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]

private theorem lieArm1_traceHessianSlotPerm_inv_mul_apply (σ : Equiv.Perm (Fin 4)) (j : Fin 4) :
    traceHessianSlotPerm ((traceHessianSlotPerm⁻¹ * σ) j) = σ j := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem lieArm1_dLTC_eq_reindex_traceHessian
    (g₀ g₁ : SmoothRiemannianMetric I M) (σ ρ : Equiv.Perm (Fin 4))
    (hcomp : ∀ j : Fin 4, traceHessianSlotPerm (ρ j) = σ j) :
    deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (traceHessianCoeff (I := I) (M := M) g₀ g₁) ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieTraceCoeff_toSection, reindexCoeffGen_toSection, traceHessianCoeff_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoeffFibGen_apply, deTurckLieTraceFib, traceHessianFib,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFibPerm_apply, domDomCongrFib_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  have harg : ContinuousMultilinearMap.domDomCongr σ
      (Tensor0SBundle.Tensor0SSpace.toModel D) =
      ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
    refine congrArg _ (funext fun j => ?_)
    rw [hcomp j]
  rw [harg]

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem lieArm1_rfns_dLTC_toSection_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ' : Equiv.Perm (Fin 4)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ').toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x) := by
  rw [lieArm1_dLTC_eq_reindex_traceHessian (I := I) (M := M) g₀ g₁ σ'
      (traceHessianSlotPerm⁻¹ * σ') (lieArm1_traceHessianSlotPerm_inv_mul_apply σ'),
    reindexCoeffGen_toSection]
  exact riemannianFiberNormSq_reindexCoeffFibGen (I := I) (M := M) g₀ 4 2 x
    (traceHessianSlotPerm⁻¹ * σ')
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x)

omit [NeZero (Module.finrank ℝ E)] in
theorem lieArm1_normSq_icg_dLTC_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ' : Equiv.Perm (Fin 4)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 i (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 4 2 i (traceHessianCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 := by
  rw [lieArm1_dLTC_eq_reindex_traceHessian (I := I) (M := M) g₀ g₁ σ'
      (traceHessianSlotPerm⁻¹ * σ') (lieArm1_traceHessianSlotPerm_inv_mul_apply σ')]
  exact lieArm1_normSq_icg_reindex_eq (I := I) (M := M) g₀ 4 2
    (traceHessianCoeff (I := I) (M := M) g₀ g₁) (traceHessianSlotPerm⁻¹ * σ') i

omit [FiniteDimensional ℝ E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem lieArm1_gFibreOpBound_nonneg [Nonempty M] (g₀ : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ) : 0 ≤ δ := by
  obtain ⟨x₀⟩ := ‹Nonempty M›
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
  have habs_nn : 0 ≤ |h x₀ v v| := abs_nonneg _
  by_contra hδc
  have hδc' : δ < 0 := lt_of_not_ge hδc
  have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
    have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
    exact mul_neg_of_neg_of_pos h1 hsqrt_pos
  linarith [le_trans habs_nn hbound]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lieArm1_convexPerturbation_ball (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) {R : ℝ} (a : ℕ)
    (hTball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R)
    (hT'ball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
  intro j hj
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
  have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
      = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
        + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
    rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
      iteratedCovGrad_add, lieArm1_icg_smul, lieArm1_icg_smul]
  rw [heq]
  calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
      ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
          + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
    _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
          + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg h1ms, abs_of_nonneg hs0]
    _ ≤ (1 - s) * R + s * R :=
        add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
          (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
    _ = R := by ring

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
theorem lieArm1_realizedFam_pack (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_le : δ ≤ δ₀)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
          g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w) ∧
      metricCauchySchwarzBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
        ((1 - s) * δ' + s * δ) ∧
      (1 - s) * δ' + s * δ ≤ δ₀ := by
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  refine ⟨fun y v w =>
      realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
        (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w,
    convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1, ?_⟩
  have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
  have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
  have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
  linarith [e1, e2, e3]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm1_toModel_om_single (x : M) (om : Tensor0SSpace 1 I x)
    (m : Fin 1 → TangentSpace I x) :
    Tensor0SSpace.toModel om (fun k => (m k : E)) =
      cotangentToDual (I := I) (x := x) om (m 0) := by
  rw [show (fun k : Fin 1 => (m k : E)) = (fun _ : Fin 1 => (m 0 : E)) from by
    funext k; fin_cases k; rfl]
  rw [cotangentToDual_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm1_g1_inner_gInvRaisedEndo_left (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g₁.inner x (metricComparisonEndo (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
  rw [gInvRaisedEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
  rw [show cotangentToDualLinear (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w from rfl]
  rw [cotangentToDual_g0FlatCLM]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm1_g0_inner_inverseMetricSharp_mixed (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (om : Tensor0SSpace 1 I x) (v : TangentSpace I x) :
    g₀.inner x (inverseMetricSharpFib (I := I) g₁ x om) v =
      cotangentToDual (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) := by
  rw [show cotangentToDual (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) =
      cotangentToDualLinear (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) from rfl]
  rw [← inverseMetricSharpFib_inner (I := I) g₁ x om (metricComparisonEndo (I := I) g₀ g₁ x v)]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om) (metricComparisonEndo (I := I) g₀ g₁ x v)]
  rw [lieArm1_g1_inner_gInvRaisedEndo_left (I := I) (M := M) g₀ g₁ x v
    (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [g₀.symm x v (inverseMetricSharpFib (I := I) g₁ x om)]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma lieArm1_sharpFlat_eq_slotInsert_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om) =
      (g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) om) =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) om from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [lieArm1_toModel_om_single (I := I) (M := M) x om
    (Function.update m 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x (m 0)))]
  rw [Function.update_self]
  rw [lieArm1_toModel_om_single (I := I) (M := M) x
    ((g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om)) m]
  rw [cotangentToDual_g0FlatCLM]
  rw [lieArm1_g0_inner_inverseMetricSharp_mixed (I := I) (M := M) g₀ g₁ x om (m 0)]
  rw [fullRaisedEndoField_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma lieArm1_fullRaised_diff_split (g₀ g₁ : SmoothRiemannianMetric I M) :
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
  rw [show (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) = metricComparisonDiffEndo (I := I) g₀ g₁ x
    from rfl]
  rw [fullRaisedEndoField_apply]
  rw [gInvRaisedEndo_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show metricComparisonEndo (I := I) g₀ g₀ x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma lieArm1_slotInsert_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
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

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem lieArm1_sharpFlat_decomp (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁) +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀) := by
  rw [lieArm1_sharpFlat_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁,
    lieArm1_fullRaised_diff_split (I := I) (M := M) g₀ g₁,
    lieArm1_slotInsert_add (I := I) (M := M) g₀ 0]

theorem lieArm1_sharpFlat_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
            ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Km, hKm_nn, hKm⟩ :=
    diagonalProductGrid_riemannianFiberNormSq_integral_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  set IdIns : SmoothCcTensor g₀ 1 1 :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀) with hIdIns_def
  obtain ⟨S0, hS0_nn, hS0⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 1 IdIns
  refine ⟨2 * Cb 0 + 2 * S0,
    fun i => ∑ q ∈ Finset.range (i + 1),
      (2 * (Cb q * Km q) + 2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2),
    by have := hCb_nn 0; linarith,
    fun i => Finset.sum_nonneg fun q _ => add_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (hCb_nn q) (hKm_nn q)))
      (mul_nonneg (by norm_num) (sq_nonneg _)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  set DiffIns : SmoothCcTensor g₀ 1 1 :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁)
    with hDiffIns_def
  have hdecomp : sharpFlatEndoCc (I := I) g₀ g₁ = DiffIns + IdIns :=
    lieArm1_sharpFlat_decomp (I := I) (M := M) g₀ g₁
  refine ⟨?_, ?_⟩
  · intro x
    have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (DiffIns.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (IdIns.toSection x) := by
      rw [hdecomp]
      rw [show ((DiffIns + IdIns).toSection x) = DiffIns.toSection x + IdIns.toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 1 x _ _
    have hD0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (DiffIns.toSection x) ≤ Cb 0 := by
      have h2 := hCb g₁ P htie hδ_le hδ0 hδ 0 x
      simp only [iteratedCovGrad_zero] at h2
      have hgrid0 : (∑ n ∈ Finset.range (0 + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n 0,
          ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = 1 := by
        simp
      rw [hgrid0, mul_one] at h2
      exact h2
    linarith [hsplit, hD0, hS0 x]
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
    obtain ⟨hgi, hgb⟩ := hKm P hPball q hq_le
    have hDq : ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ ^ 2 ≤ Cb q * Km q := by
      have hint : MeasureTheory.Integrable
          (fun x => Cb q *
            (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
              ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
        1 (1 + q) (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns) _ hint
        (fun x => hCb g₁ P htie hδ_le hδ0 hδ q x)
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul]
      exact mul_le_mul_of_nonneg_left hgb (hCb_nn q)
    have htri : ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ +
          ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ := by
      rw [hdecomp, iteratedCovGrad_add]
      exact norm_add_le _ _
    nlinarith [htri, hDq,
      norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q IdIns),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)),
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ -
        ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖)]

theorem lieArm1_connDiff_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
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
            ((connDiffSection (I := I) g₁ g₀).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 q (connDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨ΛK, FK, hΛK_nn, hFK_nn, hK⟩ :=
    raisedKoszul_order0sup_jetL2_ballUniform_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λsf, Fsf, hΛsf_nn, hFsf_nn, hsf⟩ :=
    lieArm1_sharpFlat_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  have h2A : ∀ k : ℕ, k ≤ a → ∃ c : ℝ, 0 ≤ c ∧
      ∀ (S : SmoothCcTensor g₀ 1 2) (T : SmoothCcTensor g₀ 1 1)
        (ΛS' ΛT' : ℝ), 0 ≤ ΛS' → 0 ≤ ΛT' →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (S.toSection x) ≤ ΛS' ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (T.toSection x) ≤ ΛT' ^ 2) →
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
            c * (ΛT' ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 2 n S‖ ^ 2
                + ΛS' ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 1 l T‖ ^ 2) := by
    intro k _
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 1 1 2 1 k
    exact ⟨C, hC_nn, fun S T ΛS' ΛT' h1 h2 h3 h4 => hC S T ΛS' ΛT' h1 h2 h3 h4⟩
  obtain ⟨C2, hC2_nn, hC2⟩ := exists_fn_of_forall_exists_bounded a _ h2A
  refine ⟨ΛK ^ 2 * Λsf,
    fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * (Λsf * FK q + ΛK ^ 2 * Fsf q)),
    mul_nonneg (sq_nonneg _) hΛsf_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2_nn q) (add_nonneg (mul_nonneg hΛsf_nn (hFK_nn q))
        (mul_nonneg (sq_nonneg _) (hFsf_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hKsup, hKsum⟩ := hK g₁ P hδ_le hδ htie hPball
  obtain ⟨hsfsup, hsfsum⟩ := hsf g₁ P htie hδ_le hδ0 hδ hPball
  have hid : connDiffSection (I := I) g₁ g₀ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 (raisedKoszul (I := I) g₀ g₁)
        (sharpFlatEndoCc (I := I) g₀ g₁) :=
    connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀ g₁
  refine ⟨?_, ?_⟩
  · intro x
    rw [hid, appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
      (show TensorRSSpace 1 2 I x from (raisedKoszul (I := I) g₀ g₁).toSection x)
      (show TensorRSSpace 1 1 I x from (sharpFlatEndoCc (I := I) g₀ g₁).toSection x)) ?_
    exact mul_le_mul (hKsup x) (hsfsup x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) (sq_nonneg ΛK)
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
    have hsfsup' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤ (Real.sqrt Λsf) ^ 2 := by
      intro x
      rw [Real.sq_sqrt hΛsf_nn]
      exact hsfsup x
    obtain ⟨hgi, hgb⟩ := hC2 q hq_le (raisedKoszul (I := I) g₀ g₁)
      (sharpFlatEndoCc (I := I) g₀ g₁) ΛK (Real.sqrt Λsf) hΛK_nn (Real.sqrt_nonneg _)
      hKsup hsfsup'
    rw [hid]
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
      1 (2 + q)
      (iteratedCovGrad (I := I) g₀ 1 2 q
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 (raisedKoszul (I := I) g₀ g₁)
          (sharpFlatEndoCc (I := I) g₀ g₁)))
      (fun x => diagonalGridGrowthFactor (E := E) q *
        ∑ n ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
              ((iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)).toSection x)
            * ∑ l ∈ Finset.range (q + 1 - n),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                  ((iteratedCovGrad (I := I) g₀ 1 1 l
                    (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x))
      (hgi.const_mul (diagonalGridGrowthFactor (E := E) q))
      (fun x => riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
        (I := I) (M := M) g₀ q 1 1 2 (raisedKoszul (I := I) g₀ g₁)
        (sharpFlatEndoCc (I := I) g₀ g₁) x)
    refine le_trans hkey ?_
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) q)
    refine le_trans hgb ?_
    refine mul_le_mul_of_nonneg_left ?_ (hC2_nn q)
    rw [Real.sq_sqrt hΛsf_nn]
    have e1 : Λsf * (∑ n ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ^ 2) ≤
        Λsf * FK q := mul_le_mul_of_nonneg_left (hKsum q hq_le) hΛsf_nn
    have e2 : ΛK ^ 2 * (∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2) ≤
        ΛK ^ 2 * Fsf q := mul_le_mul_of_nonneg_left (hsfsum q hq_le) (sq_nonneg ΛK)
    linarith [e1, e2]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm1_cotangentToDual_map_add (x : M) (om : Tensor0SSpace 1 I x)
    (u v : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) om (u + v) =
      cotangentToDual (I := I) (x := x) om u + cotangentToDual (I := I) (x := x) om v := by
  simp only [show ∀ w : TangentSpace I x, cotangentToDual (I := I) (x := x) om w =
      cotangentToDualLinear (I := I) (x := x) om w from fun w => rfl]
  exact map_add _ u v

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm1_om_add (x : M) (om : Tensor0SSpace 1 I x) (u v : TangentSpace I x) :
    om (fun _ : Fin 1 => u + v) = om (fun _ : Fin 1 => u) + om (fun _ : Fin 1 => v) := by
  rw [← cotangentToDual_apply (I := I) om (u + v), ← cotangentToDual_apply (I := I) om u,
    ← cotangentToDual_apply (I := I) om v]
  exact lieArm1_cotangentToDual_map_add (I := I) (M := M) x om u v

def lieArm1FixCd (g₀ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection := (connDiffSection (I := I) g₀ g_bg).toSection
  hasCompactSupport := (connDiffSection (I := I) g₀ g_bg).hasCompactSupport

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieArm1_connDiffBg_decomp (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg =
      connDiffSection (I := I) g₁ g₀ + lieArm1FixCd (I := I) (M := M) g₀ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show (connDiffSection (I := I) g₁ g₀ + lieArm1FixCd (I := I) (M := M) g₀ g_bg).toSection x =
      (connDiffSection (I := I) g₁ g₀).toSection x +
        (lieArm1FixCd (I := I) (M := M) g₀ g_bg).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [lieArm1ConnDiffBgCc_toSection, connDiffSection_toSection,
    show (lieArm1FixCd (I := I) (M := M) g₀ g_bg).toSection x =
      connDiffFib (I := I) g₀ g_bg x from rfl]
  refine tensorRSSpace_ext 1 2 x (fun om => ?_)
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      (connDiffFib (I := I) g₁ g₀ x + connDiffFib (I := I) g₀ g_bg x : TensorRSSpace 1 2 I x)) om) =
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om +
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₀ g_bg x) om from rfl]
  apply ContinuousMultilinearMap.ext
  intro YZ
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om +
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₀ g_bg x) om) YZ =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om) YZ +
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₀ g_bg x) om) YZ from rfl]
  rw [connDiffFib_apply_eval, connDiffFib_apply_eval, connDiffFib_apply_eval]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g_bg x (YZ 0) (YZ 1) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1) +
        PDE.DeTurck.connDiff (I := I) g₀ g_bg x (YZ 0) (YZ 1) from
    PDE.DeTurck.connDiff_cocycle (I := I) g₀ g₁ g_bg x (YZ 0) (YZ 1)]
  exact lieArm1_om_add (I := I) (M := M) x om _ _

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lieArm1_rfns_toSection_add_le (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s x ((A + B).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x (A.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x (B.toSection x) := by
  rw [show (A + B).toSection x = A.toSection x + B.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g r s x _ _

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lieArm1_normSq_icg_add_le (g : SmoothRiemannianMetric I M) (r s q : ℕ)
    (A B : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r s q (A + B)‖ ^ 2 ≤
      2 * ‖iteratedCovGrad (I := I) g r s q A‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g r s q B‖ ^ 2 := by
  have htri : ‖iteratedCovGrad (I := I) g r s q (A + B)‖ ≤
      ‖iteratedCovGrad (I := I) g r s q A‖ + ‖iteratedCovGrad (I := I) g r s q B‖ := by
    rw [iteratedCovGrad_add]
    exact norm_add_le _ _
  nlinarith [htri, norm_nonneg (iteratedCovGrad (I := I) g r s q (A + B)),
    norm_nonneg (iteratedCovGrad (I := I) g r s q A),
    norm_nonneg (iteratedCovGrad (I := I) g r s q B),
    sq_nonneg (‖iteratedCovGrad (I := I) g r s q A‖ - ‖iteratedCovGrad (I := I) g r s q B‖)]

private theorem lieArm1_rfns_icg_sE2_le (g₀ : SmoothRiemannianMetric I M)
    (Ψ : SmoothCcTensor g₀ 1 2) (l : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 3 4 l
          (slotExtend (I := I) (M := M) g₀ 2 3
            (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l Ψ).toSection x) := by
  have houter := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 3
    (slotExtend (I := I) (M := M) g₀ 1 2 Ψ) l x
  have hinner := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2 Ψ l x
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 3 4 l
          (slotExtend (I := I) (M := M) g₀ 2 3
            (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection x)
      ≤ (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 3 l
              (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)).toSection x) := houter
    _ ≤ (Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 2 l Ψ).toSection x)) :=
        mul_le_mul_of_nonneg_left hinner hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l Ψ).toSection x) := by ring

theorem lieArm1_rfns_sE2_zero_le (g₀ : SmoothRiemannianMetric I M)
    (Ψ : SmoothCcTensor g₀ 1 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
        ((slotExtend (I := I) (M := M) g₀ 2 3
          (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (Ψ.toSection x) := by
  have h := lieArm1_rfns_icg_sE2_le (I := I) (M := M) g₀ Ψ 0 x
  simpa only [iteratedCovGrad_zero] using h

theorem lieArm1_normSq_icg_sE2_le (g₀ : SmoothRiemannianMetric I M)
    (Ψ : SmoothCcTensor g₀ 1 2) (l : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 3 4 l
        (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l Ψ‖ ^ 2 := by
  rw [lieArm1_normSq_eq_integral, lieArm1_normSq_eq_integral]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono ?_ ?_ (fun x => lieArm1_rfns_icg_sE2_le
    (I := I) (M := M) g₀ Ψ l x)
  · exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 3 (4 + l)
      (iteratedCovGrad (I := I) g₀ 3 4 l
        (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)))
  · exact (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 1 (2 + l)
      (iteratedCovGrad (I := I) g₀ 1 2 l Ψ)).const_mul _

theorem lieArm1_piece_rfns_le (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (Ψ : SmoothCcTensor g₀ 1 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        ((deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ Ψ).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ').toSection x) *
        ((Module.finrank ℝ E : ℝ) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (Ψ.toSection x)) := by
  have hdef : deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ Ψ =
      reindexCoeffGen (I := I) (M := M) g₀ 3 2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
          (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)))
        ρ := rfl
  rw [hdef, reindexCoeffGen_toSection]
  rw [riemannianFiberNormSq_reindexCoeffFibGen (I := I) (M := M) g₀ 3 2 x ρ
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
        (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection x)]
  rw [appCcRS_toSection]
  refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 3 4 2 x
    (show TensorRSSpace 4 2 I x from
      (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ').toSection x)
    (show TensorRSSpace 3 4 I x from
      (slotExtend (I := I) (M := M) g₀ 2 3
        (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)).toSection x)) ?_
  refine mul_le_mul_of_nonneg_left ?_ (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 2 x _)
  exact lieArm1_rfns_sE2_zero_le (I := I) (M := M) g₀ Ψ x

theorem lieArm1_piece_normSq_le (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (Ψ : SmoothCcTensor g₀ 1 2)
    (i : ℕ) (C2i ΛS ΛT FSi FTi : ℝ) (hC2i : 0 ≤ C2i)
    (hFS : ∑ n ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 4 2 n
        (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')‖ ^ 2 ≤ FSi)
    (hFT : ∑ l ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 3 4 l
        (slotExtend (I := I) (M := M) g₀ 2 3
          (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))‖ ^ 2 ≤ FTi)
    (htwo : MeasureTheory.Integrable
        (fun x => ∑ n ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
              ((iteratedCovGrad (I := I) g₀ 4 2 n
                (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')).toSection x)
            * ∑ l ∈ Finset.range (i + 1 - n),
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 3 4 l
                    (slotExtend (I := I) (M := M) g₀ 2 3
                      (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, (∑ n ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
              ((iteratedCovGrad (I := I) g₀ 4 2 n
                (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')).toSection x)
            * ∑ l ∈ Finset.range (i + 1 - n),
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 3 4 l
                    (slotExtend (I := I) (M := M) g₀ 2 3
                      (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        C2i * (ΛT ^ 2 * ∑ n ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 n
                (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')‖ ^ 2
            + ΛS ^ 2 * ∑ l ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 3 4 l
                (slotExtend (I := I) (M := M) g₀ 2 3
                  (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))‖ ^ 2)) :
    ‖iteratedCovGrad (I := I) g₀ 3 2 i (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ Ψ)‖ ^ 2 ≤
      diagonalGridGrowthFactor (E := E) i * (C2i * (ΛT ^ 2 * FSi + ΛS ^ 2 * FTi)) := by
  obtain ⟨hgi, hgb⟩ := htwo
  have hdef : deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ Ψ =
      reindexCoeffGen (I := I) (M := M) g₀ 3 2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
          (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)))
        ρ := rfl
  rw [hdef, lieArm1_normSq_icg_reindex_eq]
  have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (2 + i)
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
        (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))))
    (fun x => diagonalGridGrowthFactor (E := E) i *
      ∑ n ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 4 2 n
              (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')).toSection x)
          * ∑ l ∈ Finset.range (i + 1 - n),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 3 4 l
                  (slotExtend (I := I) (M := M) g₀ 2 3
                    (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection x))
    (hgi.const_mul (diagonalGridGrowthFactor (E := E) i))
    (fun x => riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ i 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
      (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)) x)
  refine le_trans hkey ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
  refine le_trans hgb ?_
  refine mul_le_mul_of_nonneg_left ?_ hC2i
  have e1 := mul_le_mul_of_nonneg_left hFS (sq_nonneg ΛT)
  have e2 := mul_le_mul_of_nonneg_left hFT (sq_nonneg ΛS)
  linarith [e1, e2]

theorem lieArm1_twoArm_top_fn (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C2 : ℕ → ℝ, (∀ k, 0 ≤ C2 k) ∧ ∀ k, k ≤ a →
      ∀ (S : SmoothCcTensor g₀ 4 2) (T : SmoothCcTensor g₀ 3 4)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C2 k * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 4 2 n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 3 4 l T‖ ^ 2) := by
  have h2A : ∀ k : ℕ, k ≤ a → ∃ c : ℝ, 0 ≤ c ∧
      ∀ (S : SmoothCcTensor g₀ 4 2) (T : SmoothCcTensor g₀ 3 4)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            c * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 4 2 n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 3 4 l T‖ ^ 2) := by
    intro k _
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 4 3 2 4 k
    exact ⟨C, hC_nn, fun S T ΛS ΛT h1 h2 h3 h4 => hC S T ΛS ΛT h1 h2 h3 h4⟩
  obtain ⟨C2, hC2_nn, hC2⟩ := exists_fn_of_forall_exists_bounded a _ h2A
  exact ⟨C2, hC2_nn, hC2⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem lieArm1_rfns_neg (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem lieArm1_rfns_smul (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm1_rfns_icg_symmS_le (g₀ : SmoothRiemannianMetric I M)
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
  rw [lieArm1_rfns_smul (I := I) (M := M) g₀ 0 (2 + j) x,
    lieArm1_rfns_smul (I := I) (M := M) g₀ 0 (2 + j) x]
  have hperm := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) T j x
  rw [hperm]
  ring_nf
  nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)]

omit [NeZero (Module.finrank ℝ E)] in
lemma lieArm1_normSq_icg_symmS_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (j : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by
  rw [lieArm1_normSq_eq_integral, lieArm1_normSq_eq_integral]
  refine MeasureTheory.integral_mono ?_ ?_
    (fun x => lieArm1_rfns_icg_symmS_le (I := I) (M := M) g₀ T j x)
  · exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + j)
      (iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T))
  · exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + j)
      (iteratedCovGrad (I := I) g₀ 0 2 j T)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma lieArm1_rfns_symmS_zero_le (g₀ : SmoothRiemannianMetric I M)
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
      rw [show unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ T) x
            ![e (J 0), e (J 1)] =
          smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T) x (e (J 0)) (e (J 1)) from
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
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
        have hc0 : (Fintype.card (Fin 0 → Fin n) : ℝ) = 1 := by simp
        have hc2 : (Fintype.card (Fin 2 → Fin n) : ℝ) = (n : ℝ) ^ 2 := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring
        rw [hc0, hc2, one_mul, hnE]

end DifferentialGeometry.Integral.Connection

end
