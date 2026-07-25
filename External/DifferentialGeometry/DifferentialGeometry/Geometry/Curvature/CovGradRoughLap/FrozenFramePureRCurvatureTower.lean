import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedDiffOpProportionalBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformProportionalCurvatureSup
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Slot0SliceFiberNormDomination
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldDifferentiatedTowerNormalForm


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private def pureRFrozenDirLMSummand
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →ₗ[ℝ] TensorRSSpace 0 m I x where
  toFun v := riemannOp (tensorCov (I := I) g 0 m) x (B i x) v
    ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W x) (B i x))
  map_add' v v' := by
    rw [map_add (riemannOp (tensorCov (I := I) g 0 m) x (B i x)) v v']
    rfl
  map_smul' c v := by
    rw [map_smul (riemannOp (tensorCov (I := I) g 0 m) x (B i x)) c v]
    rfl

private noncomputable def pureRFrozenDirCLMSummand
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 m I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (pureRFrozenDirLMSummand (I := I) (M := M) g m B W x i)

private noncomputable def pureRFrozenDirCLM
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (x : M) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 m I x :=
  ∑ i : Fin (Module.finrank ℝ E), pureRFrozenDirCLMSummand (I := I) (M := M) g m B W x i

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRFrozenDirCLM_apply
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (x : M) (v : TangentSpace I x) :
    pureRFrozenDirCLM (I := I) (M := M) g m B W x v =
      ∑ i : Fin (Module.finrank ℝ E),
        riemannOp (tensorCov (I := I) g 0 m) x (B i x) v
          ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W x) (B i x)) := by
  classical
  rw [pureRFrozenDirCLM, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pureRFrozenDirCLMSummand, LinearMap.coe_toContinuousLinearMap', pureRFrozenDirLMSummand,
    LinearMap.coe_mk, AddHom.coe_mk]

private noncomputable def pureRFrozenEndoFib
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    TensorRSSpace 0 (m + 1) I x :=
  covGradBundleEquiv (I := I) (M := M) 0 m x
    (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem pureRFrozenSlot0Sec_contMDiff
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 m ℝ E)
        (E := fun z : M => TensorRSSpace 0 m I z) x
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W.toSection x) (B i x))) := by
  classical
  have hHom : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel 0 m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 m ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace 0 m I z) x
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W.toSection x))) := by
    have hWtot : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
          (E := fun z : M => TensorRSSpace 0 (m + 1) I z) x (W.toSection x)) :=
      W.toSection.contMDiff_toFun
    exact (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) 0 m).comp hWtot
  exact ContMDiff.clm_bundle_apply (b := fun x : M => x)
    (ϕ := fun x => (covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W.toSection x))
    (v := fun x => B i x) hHom (hB i)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem pureRFrozenDirCLM_homSection_contMDiff
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel 0 m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 m ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace 0 m I y) x
        (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x)) := by
  classical
  refine cotangentCov_clmSection_smooth_aux
    (φ := fun x : M => pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x)
    (fun Y => ?_)
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => (Y : Π b : M, TangentSpace I b) b)) :=
    Y.contMDiff

  have hsum : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 m ℝ E)
        (E := fun z : M => TensorRSSpace 0 m I z) x
        (∑ i : Fin (Module.finrank ℝ E),
          riemannSec (tensorCov (I := I) g 0 m) (B i) (fun b : M => Y b)
            (fun y : M => (covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W.toSection y) (B i y))
            x)) := by
    refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
    exact riemannSec_contMDiff (cov := tensorCov (I := I) g 0 m) (hB i) hY
      (pureRFrozenSlot0Sec_contMDiff (I := I) (M := M) g m hB W i)
  refine hsum.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel 0 m ℝ E)
    (E := fun z : M => TensorRSSpace 0 m I z) x) ?_
  rw [pureRFrozenDirCLM_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 m) (X := B i) (Y := fun b : M => Y b)
    (Z := fun y : M => (covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W.toSection y) (B i y))
    (x := x) (hB i) hY (pureRFrozenSlot0Sec_contMDiff (I := I) (M := M) g m hB W i)).symm ▸ rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem pureRFrozenEndoFib_contMDiff
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (m + 1) I z) x
        (pureRFrozenEndoFib (I := I) (M := M) g m B W x)) := by
  classical
  have hcomp :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
        ((covGradBundleSmoothEquiv (I := I) (M := M) 0 m).toDiffeomorph ∘
          (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 m ℝ E)
            (E := fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace 0 m I y) x
            (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) 0 m).toDiffeomorph.contMDiff.comp
      (pureRFrozenDirCLM_homSection_contMDiff (I := I) (M := M) g m hB W)
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply]
  exact covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) 0 m x
    (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x)

private noncomputable def pureRFrozenEndoSucc
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) :
    SmoothCcTensor g 0 (m + 1) where
  toSection :=
    { toFun := fun x : M => pureRFrozenEndoFib (I := I) (M := M) g m B W x
      contMDiff_toFun := pureRFrozenEndoFib_contMDiff (I := I) (M := M) g m hB W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma pureRFrozenEndoSucc_toSection
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    (pureRFrozenEndoSucc (I := I) (M := M) g m B hB W).toSection x =
      pureRFrozenEndoFib (I := I) (M := M) g m B W x := rfl

private noncomputable def pureRFrozenEndo0
    (g : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ∀ (r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 r
  | 0 => fun _ => 0
  | (m + 1) => fun W => pureRFrozenEndoSucc (I := I) (M := M) g m B hB W

private noncomputable def pureRFrozenDiffOp
    (g : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)
  | 0, r => fun W => pureRFrozenEndo0 (I := I) (M := M) g B hB r W
  | (p + 1), r => fun W =>
      covGrad (I := I) (M := M) g 0 (r + p)
          (pureRFrozenDiffOp g B hB p r W) -
        castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
          (pureRFrozenDiffOp g B hB p (r + 1) (covGrad (I := I) (M := M) g 0 r W))

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rfns_eq_sum_fiberNormSqSummand_of_orthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (S : TensorRSSpace 0 s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
      ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J := by
  classical
  subst hn
  haveI : Nonempty (Fin (Module.finrank ℝ (TangentSpace I x))) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (e k)).map_smul (c j) (e j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ (TangentSpace I x))) =
      Module.finrank ℝ (TangentSpace I x) := Fintype.card_fin _
  set bse : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse_eq : ∀ i, bse i = e i := by
    intro i; rw [hbse_def]; exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i
  have hbse_orth : ∀ i j, g.inner x (bse i) (bse j) = if i = j then (1 : ℝ) else 0 := by
    intro i j; rw [hbse_eq i, hbse_eq j]; exact horth i j

  have hstep : riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
      ∑ ψ : Fin s → Fin (Module.finrank ℝ (TangentSpace I x)),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S)
              (unitZeroSec (I := I) (M := M) x))
            (fun k => e (ψ k)) ^ 2 := by
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 s x S]
    rw [show tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel S) (TensorRSSpace.toModel S) =
        covariantTensorInnerPointwise (I := I) (M := M) (0 + s) g x
          (lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel S))
          (lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel S)) from rfl]
    rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (0 + s)
      bse hbse_orth _ _]
    have hkey : ∀ ξ : Fin (0 + s) → Fin (Module.finrank ℝ (TangentSpace I x)),
        lowerAllUpperIndices (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel S) (fun k => bse (ξ k)) =
          Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S)
                (unitZeroSec (I := I) (M := M) x))
              (fun j : Fin s => bse (ξ (Fin.natAdd 0 j))) := by
      intro ξ
      rw [lowerAllUpperIndices_apply (I := I) (M := M) g 0 s x (TensorRSSpace.toModel S)
        (fun k => bse (ξ k))]
      rw [toModel_tensorRS_apply (I := I) (M := M) 0 s x S (unitZeroSec (I := I) (M := M) x)]
      rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel]
      rw [separableFormAt_zero (I := I) (M := M) g x
        (fun i : Fin 0 => (fun k => bse (ξ k)) (Fin.castAdd s i))]
    have hstep2 : ∀ ξ : Fin (0 + s) → Fin (Module.finrank ℝ (TangentSpace I x)),
        lowerAllUpperIndices (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel S) (fun k => bse (ξ k)) *
            lowerAllUpperIndices (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel S) (fun k => bse (ξ k)) =
          Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S)
                (unitZeroSec (I := I) (M := M) x))
              (fun k => e (ξ (Fin.natAdd 0 k))) ^ 2 := by
      intro ξ
      rw [hkey ξ, ← pow_two]
      congr 2
      funext k
      rw [hbse_eq]
    refine Eq.trans (Finset.sum_congr rfl (fun ξ _ => hstep2 ξ)) ?_
    refine Fintype.sum_bijective
      (fun ξ : Fin (0 + s) → Fin (Module.finrank ℝ (TangentSpace I x)) =>
        fun k : Fin s => ξ (Fin.natAdd 0 k))
      ?_ _ _ (fun ξ => rfl)
    refine ⟨fun ξ₁ ξ₂ h => ?_, fun φ => ⟨fun k => φ (Fin.cast (Nat.zero_add s) k), ?_⟩⟩
    · funext k
      have hk : k = Fin.natAdd 0 (Fin.cast (Nat.zero_add s) k) := by ext; simp
      rw [hk]; exact congrFun h (Fin.cast (Nat.zero_add s) k)
    · funext k
      change φ (Fin.cast (Nat.zero_add s) (Fin.natAdd 0 k)) = φ k
      have : Fin.cast (Nat.zero_add s) (Fin.natAdd 0 k) = k := by ext; simp
      rw [this]
  rw [hstep]

  rw [Finset.sum_eq_single (fun k : Fin 0 => k.elim0)]
  · refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [fiberNormSqSummand_eq_component_sq]

    have hweight : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e ((fun k : Fin 0 => k.elim0) k))) : Tensor0SSpace 0 I x) =
        unitZeroSec (I := I) (M := M) x := by
      have hcf : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e ((fun k : Fin 0 => k.elim0) k))) : Tensor0SSpace 0 I x) =
          coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0) := rfl
      rw [hcf]
      apply Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro mm
      have hL : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x 0 e
          (fun k : Fin 0 => k.elim0)) mm = 1 := by
        have h1 : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x 0 e
            (fun k : Fin 0 => k.elim0)) mm =
            coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)
              (fun k : Fin 0 => k.elim0) := by
          apply congrArg; funext k; exact k.elim0
        rw [h1, coframeS_apply (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)
          (fun k : Fin 0 => k.elim0)]
        simp
      have hR : Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) mm = 1 := by
        rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
          ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hL, hR]
    rw [fiberNormSqComponent, hweight]
    rfl
  · intro K _ hK; exact absurd (Subsingleton.elim K (fun k : Fin 0 => k.elim0)) hK
  · intro h; exact absurd (Finset.mem_univ (fun k : Fin 0 => k.elim0)) h

private lemma exists_uniform_riemannOp_tensorCov_proportional
    (g : SmoothRiemannianMetric I M) (m : ℕ) :
    ∃ Csup : ℝ, 0 ≤ Csup ∧
      ∀ (x : M) (v w : TangentSpace I x) (T : TensorRSSpace 0 m I x),
        riemannianFiberNormSq (I := I) (M := M) g 0 m x
            (riemannOp (tensorCov (I := I) g 0 m) x v w T) ≤
          Csup * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x T := by
  classical
  obtain ⟨Ccurv, hCcurv_cont, hCcurv_nonneg, hCcurv_bound⟩ :=
    exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional (I := I) (M := M) g m
  have hCpt := (isCompact_univ (X := M)).image hCcurv_cont
  obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x v w T => ?_⟩
  have hCcurv_le : Ccurv x ≤ max C₀ 0 :=
    le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
  have hvv_nonneg : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0]; simp
    · exact (g.pos x v hv0).le
  have hww_nonneg : 0 ≤ g.inner x w w := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · rw [hw0]; simp
    · exact (g.pos x w hw0).le
  have hfactor_nonneg :
      0 ≤ g.inner x v v * g.inner x w w *
        riemannianFiberNormSq (I := I) (M := M) g 0 m x T :=
    mul_nonneg (mul_nonneg hvv_nonneg hww_nonneg)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m x T)
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 m x
        (riemannOp (tensorCov (I := I) g 0 m) x v w T)
        ≤ Ccurv x * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x T :=
          hCcurv_bound x v w T
    _ = Ccurv x * (g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x T) := by ring
    _ ≤ max C₀ 0 * (g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x T) :=
          mul_le_mul_of_nonneg_right hCcurv_le hfactor_nonneg
    _ = max C₀ 0 * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x T := by ring

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRFrozenEndoFib_slot0Curry_rfns_eq
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : SmoothCcTensor g 0 (m + 1)) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hreprS : ∀ S : TensorRSSpace 0 m I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 m x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin m → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 m S n e K J)
    (a : Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g 0 m x
        (slot0Curry (I := I) (M := M) g x m e K₀
          (pureRFrozenEndoFib (I := I) (M := M) g m B W x) a) =
      riemannianFiberNormSq (I := I) (M := M) g 0 m x
        (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x (e a)) := by
  classical
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x m e hreprS _ K₀,
    riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x m e hreprS _ K₀]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  congr 1

  unfold fiberNormSqComponent
  set ωK : Tensor0SSpace 0 I x :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
      (fun k => g.inner x (e (K₀ k))) with hωK

  have hslot : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
          slot0Curry (I := I) (M := M) g x m e K₀
            (pureRFrozenEndoFib (I := I) (M := M) g m B W x) a) ωK =
        tensor0S_curry (I := I) (M := M) m x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
            pureRFrozenEndoFib (I := I) (M := M) g m B W x) ωK) (e a) := by
    rw [slot0Curry_apply (I := I) (M := M) g x m e K₀
      (pureRFrozenEndoFib (I := I) (M := M) g m B W x) a ωK]
    have hscalar : tensor00Scalar (I := I) (M := M) x ωK = 1 := by
      rw [hωK,
        show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
          coframeS (I := I) (M := M) g x 0 e K₀ from rfl,
        tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
        coframeS_apply (I := I) (M := M) g x 0 e K₀]
      simp
    rw [hscalar, one_smul]
  rw [hslot]

  rw [show (tensor0S_curry (I := I) (M := M) m x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          pureRFrozenEndoFib (I := I) (M := M) g m B W x) ωK) (e a)
        (fun k => e (J k)) : ℝ) =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) m x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
            pureRFrozenEndoFib (I := I) (M := M) g m B W x) ωK) (e a))
        (fun k => e (J k)) from rfl]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
      pureRFrozenEndoFib (I := I) (M := M) g m B W x) ωK) (v0 := e a) (vs := fun k => e (J k))]

  rw [pureRFrozenEndoFib]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) 0 m x
    (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x) ωK
    (Fin.cons (e a) (fun k => e (J k)))]
  rw [Fin.cons_zero]
  congr 1

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma covGradBundleEquiv_symm_reading_rfns_le
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M)
    (T : TensorRSSpace 0 (m + 1) I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hreprS : ∀ S : TensorRSSpace 0 m I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 m x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin m → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 m S n e K J)
    (hreprSucc : ∀ S : TensorRSSpace 0 (m + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (m + 1) → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 (m + 1) S n e K J)
    (a : Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g 0 m x
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm T (e a)) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x T := by
  classical
  have heq : riemannianFiberNormSq (I := I) (M := M) g 0 m x
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm T (e a)) =
      riemannianFiberNormSq (I := I) (M := M) g 0 m x
        (slot0Curry (I := I) (M := M) g x m e K₀ T a) := by
    rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x m e hreprS _ K₀,
      riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x m e hreprS _ K₀]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    congr 1
    unfold fiberNormSqComponent
    set ωK : Tensor0SSpace 0 I x :=
      (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K₀ k))) with hωK

    have hslot : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
            slot0Curry (I := I) (M := M) g x m e K₀ T a) ωK =
          tensor0S_curry (I := I) (M := M) m x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from T) ωK) (e a) := by
      rw [slot0Curry_apply (I := I) (M := M) g x m e K₀ T a ωK]
      have hscalar : tensor00Scalar (I := I) (M := M) x ωK = 1 := by
        rw [hωK,
          show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
              (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
            coframeS (I := I) (M := M) g x 0 e K₀ from rfl,
          tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
          coframeS_apply (I := I) (M := M) g x 0 e K₀]
        simp
      rw [hscalar, one_smul]

    rw [show ((((covGradBundleEquiv (I := I) (M := M) 0 m x).symm T (e a)) ωK)
          (fun k => e (J k)) : ℝ) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
            (covGradBundleEquiv (I := I) (M := M) 0 m x).symm T (e a)) ωK)
          (fun k => e (J k)) from rfl]
    rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) 0 m x T (e a) ωK (fun k => e (J k))]

    rw [hslot]
    rw [show ((tensor0S_curry (I := I) (M := M) m x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from T) ωK) (e a))
          (fun k => e (J k)) : ℝ) =
        Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) m x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from T) ωK) (e a))
          (fun k => e (J k)) from rfl]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from T) ωK)
      (v0 := e a) (vs := fun k => e (J k))]
  rw [heq]
  exact riemannianFiberNormSq_slot0Curry_le_of_frame (I := I) (M := M) g m x e K₀
    hreprS hreprSucc T a

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma covGradBundleEquiv_symm_reading_rfns_le_centreFrame
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x₀ : M)
    (T : TensorRSSpace 0 (m + 1) I x₀)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hBorth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x₀ (B i x₀) (B j x₀) = if i = j then (1 : ℝ) else 0)
    (i : Fin (Module.finrank ℝ E)) :
    riemannianFiberNormSq (I := I) (M := M) g 0 m x₀
        ((covGradBundleEquiv (I := I) (M := M) 0 m x₀).symm T (B i x₀)) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x₀ T := by
  classical
  set eC : Fin (Module.finrank ℝ E) → TangentSpace I x₀ := fun j => B j x₀ with heC_def
  have hnC : Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I x₀) := rfl
  have horthC : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x₀ (eC a) (eC b) = if a = b then (1 : ℝ) else 0 := fun a b => hBorth a b
  set K₀ : Fin 0 → Fin (Module.finrank ℝ E) := fun k => k.elim0 with hK₀
  have hreprS : ∀ S : TensorRSSpace 0 m I x₀,
      riemannianFiberNormSq (I := I) (M := M) g 0 m x₀ S =
        ∑ K : Fin 0 → Fin (Module.finrank ℝ E), ∑ J : Fin m → Fin (Module.finrank ℝ E),
          fiberNormSqSummand (I := I) (M := M) g x₀ 0 m S (Module.finrank ℝ E) eC K J :=
    fun S => rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g m x₀ S eC hnC horthC
  have hreprSucc : ∀ S : TensorRSSpace 0 (m + 1) I x₀,
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x₀ S =
        ∑ K : Fin 0 → Fin (Module.finrank ℝ E), ∑ J : Fin (m + 1) → Fin (Module.finrank ℝ E),
          fiberNormSqSummand (I := I) (M := M) g x₀ 0 (m + 1) S (Module.finrank ℝ E) eC K J :=
    fun S => rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g (m + 1) x₀ S eC hnC
      horthC
  have h := covGradBundleEquiv_symm_reading_rfns_le (I := I) (M := M) g m x₀ T eC K₀
    hreprS hreprSucc i
  rwa [heC_def] at h

theorem exists_proportional_pureRFrozenFrameDiffOp_orderZero
    (g : SmoothRiemannianMetric I M) :
    ∃ kappa0 : ℕ → ℝ, (∀ r, 0 ≤ kappa0 r) ∧
      ∀ (r : ℕ) (W : SmoothCcTensor g 0 r) (x₀ : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + 0) x₀
            ((pureRFrozenDiffOp (I := I) (M := M) g (smoothOrthoFrame (I := I) g x₀)
              (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) 0 r W).toSection x₀) ≤
          kappa0 r * riemannianFiberNormSq (I := I) (M := M) g 0 r x₀ (W.toSection x₀) := by
  classical
  set N : ℝ := (Module.finrank ℝ E : ℝ) with hN_def

  choose Csup hCsup_nonneg hCsup using fun m =>
    exists_uniform_riemannOp_tensorCov_proportional (I := I) (M := M) g m
  refine ⟨fun r => match r with | 0 => 0 | (m + 1) => N ^ 3 * Csup m,
    fun r => ?_, fun r W x₀ => ?_⟩
  · cases r with
    | zero => exact le_refl 0
    | succ m => exact mul_nonneg (by positivity) (hCsup_nonneg m)

  rw [show (pureRFrozenDiffOp (I := I) (M := M) g (smoothOrthoFrame (I := I) g x₀)
        (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) 0 r W) =
      pureRFrozenEndo0 (I := I) (M := M) g (smoothOrthoFrame (I := I) g x₀)
        (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) r W from rfl]
  cases r with
  | zero =>

      rw [show ((pureRFrozenEndo0 (I := I) (M := M) g (smoothOrthoFrame (I := I) g x₀)
            (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) 0 W).toSection x₀ :
            TensorRSSpace 0 (0 + 0) I x₀) = (0 : TensorRSSpace 0 (0 + 0) I x₀) from rfl]
      rw [riemannianFiberNormSq_zero]
      have hrhs0 : (fun r => match r with
          | 0 => (0 : ℝ) | (m + 1) => N ^ 3 * Csup m) 0 = 0 := rfl
      rw [hrhs0, zero_mul]
  | succ m =>

      set B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b := smoothOrthoFrame (I := I) g x₀
        with hB_def
      have hBorth : ∀ i j : Fin (Module.finrank ℝ E),
          g.inner x₀ (B i x₀) (B j x₀) = if i = j then (1 : ℝ) else 0 := by
        intro i j; rw [hB_def]; exact smoothOrthoFrame_orthonormal_at_center (I := I) g x₀ i j

      obtain ⟨n, e, _bse, hn, _hbse_eq, horth, _hpars, _hexp, _hreprm1⟩ :=
        tangent_orthonormalBasisS_witness (I := I) (M := M) g (m + 1) x₀
      set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀

      have hreprS : ∀ S : TensorRSSpace 0 m I x₀,
          riemannianFiberNormSq (I := I) (M := M) g 0 m x₀ S =
            ∑ K : Fin 0 → Fin n, ∑ J : Fin m → Fin n,
              fiberNormSqSummand (I := I) (M := M) g x₀ 0 m S n e K J :=
        fun S => rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g m x₀ S e
          (by rw [hn]) horth
      have hreprSucc : ∀ S : TensorRSSpace 0 (m + 1) I x₀,
          riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x₀ S =
            ∑ K : Fin 0 → Fin n, ∑ J : Fin (m + 1) → Fin n,
              fiberNormSqSummand (I := I) (M := M) g x₀ 0 (m + 1) S n e K J :=
        fun S => rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g (m + 1) x₀ S e
          (by rw [hn]) horth

      rw [show (pureRFrozenEndo0 (I := I) (M := M) g B
            (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) (m + 1) W).toSection x₀ =
          pureRFrozenEndoFib (I := I) (M := M) g m B W x₀ from rfl]

      rw [riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame (I := I) (M := M) g m x₀ e K₀
        hreprS hreprSucc (pureRFrozenEndoFib (I := I) (M := M) g m B W x₀)]

      have hslice : ∀ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 m x₀
              (slot0Curry (I := I) (M := M) g x₀ m e K₀
                (pureRFrozenEndoFib (I := I) (M := M) g m B W x₀) a) =
            riemannianFiberNormSq (I := I) (M := M) g 0 m x₀
              (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x₀ (e a)) :=
        fun a => pureRFrozenEndoFib_slot0Curry_rfns_eq (I := I) (M := M) g m B W x₀ e K₀ hreprS a
      rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hslice a)]

      set Csm : ℝ := Csup m with hCsm_def
      have hper : ∀ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 m x₀
              (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x₀ (e a)) ≤
            (n : ℝ) * ((n : ℝ) * (Csm *
              riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x₀ (W.toSection x₀))) := by
        intro a
        rw [pureRFrozenDirCLM_apply (I := I) (M := M) g m B (fun y : M => W.toSection y) x₀ (e a)]

        refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 m x₀
          (Finset.univ : Finset (Fin (Module.finrank ℝ E))) _) ?_
        rw [Finset.card_univ, Fintype.card_fin]

        have hcard_le : (Module.finrank ℝ E : ℝ) = (n : ℝ) := by rw [hn]; rfl
        rw [hcard_le]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)

        have hsummand : ∀ i : Fin (Module.finrank ℝ E),
            riemannianFiberNormSq (I := I) (M := M) g 0 m x₀
                (riemannOp (tensorCov (I := I) g 0 m) x₀ (B i x₀) (e a)
                  ((covGradBundleEquiv (I := I) (M := M) 0 m x₀).symm (W.toSection x₀) (B i x₀))) ≤
              Csm * riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x₀ (W.toSection x₀) := by
          intro i
          have hgB : g.inner x₀ (B i x₀) (B i x₀) = 1 := by
            have := hBorth i i; rwa [if_pos rfl] at this
          have hge : g.inner x₀ (e a) (e a) = 1 := by
            have := horth a a; rwa [if_pos rfl] at this
          have hbound := hCsup m x₀ (B i x₀) (e a)
            ((covGradBundleEquiv (I := I) (M := M) 0 m x₀).symm (W.toSection x₀) (B i x₀))
          rw [hgB, hge, mul_one, mul_one, ← hCsm_def] at hbound
          refine le_trans hbound ?_
          refine mul_le_mul_of_nonneg_left ?_ (by rw [hCsm_def]; exact hCsup_nonneg m)

          exact covGradBundleEquiv_symm_reading_rfns_le_centreFrame (I := I) (M := M) g m x₀
            (W.toSection x₀) B hBorth i
        refine le_trans (Finset.sum_le_sum (fun i _ => hsummand i)) ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcard_le]

      refine le_trans (Finset.sum_le_sum (fun a _ => hper a)) ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hn_eq : (n : ℝ) = N := by rw [hn, hN_def]; rfl
      have hrhs : (fun r => match r with
          | 0 => (0 : ℝ) | (m' + 1) => N ^ 3 * Csup m') (m + 1) = N ^ 3 * Csup m := rfl
      rw [hn_eq, hCsm_def, hrhs]
      exact le_of_eq (by ring)

private noncomputable def pureRSlot0BilinAt
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (y : M) (v : TangentSpace I y) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TensorRSSpace 0 m I y :=
  haveI : T2Space (TangentSpace I y) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => (riemannOp (tensorCov (I := I) g 0 m) y X v).comp
        ((covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W y))
      map_add' := fun X X' => by
        ext Y
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (riemannOp (tensorCov (I := I) g 0 m) y).map_add X X']
      map_smul' := fun c X => by
        ext Y
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (riemannOp (tensorCov (I := I) g 0 m) y).map_smul c X] }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRSlot0BilinAt_apply
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (y : M) (v X Y : TangentSpace I y) :
    pureRSlot0BilinAt (I := I) (M := M) g m W y v X Y =
      riemannOp (tensorCov (I := I) g 0 m) y X v
        ((covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W y) Y) := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRSlot0BilinAt_frame_summand
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W : SmoothCcTensor g 0 (m + 1))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (i : Fin (Module.finrank ℝ E)) (y : M) (v : TangentSpace I y) :
    riemannOp (tensorCov (I := I) g 0 m) y (B i y) v
        ((covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W.toSection y) (B i y)) =
      pureRSlot0BilinAt (I := I) (M := M) g m (fun b : M => W.toSection b) y v (B i y) (B i y) := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem pureRFrozenDirCLM_frame_independent
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1))
    {B C : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b} (y : M)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (B i y) (B j y) = if i = j then (1 : ℝ) else 0)
    (hC_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (C i y) (C j y) = if i = j then (1 : ℝ) else 0) :
    pureRFrozenDirCLM (I := I) (M := M) g m B (fun b : M => W.toSection b) y =
      pureRFrozenDirCLM (I := I) (M := M) g m C (fun b : M => W.toSection b) y := by
  classical
  haveI : T2Space (TangentSpace I y) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  refine ContinuousLinearMap.ext (fun v => ?_)
  refine ContinuousLinearMap.ext (fun D => ?_)
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro mtail
  haveI : T2Space (TensorRSSpace 0 m I y) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y))
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 m I y) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y))

  set scalarize : TensorRSSpace 0 m I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun T => Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from T) D) mtail
        map_add' := fun T T' => by
          change Tensor0SSpace.toModel ((T + T') D) mtail =
            Tensor0SSpace.toModel (T D) mtail + Tensor0SSpace.toModel (T' D) mtail
          rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
            ContinuousMultilinearMap.add_apply]
        map_smul' := fun c T => by
          change Tensor0SSpace.toModel ((c • T) D) mtail = c • Tensor0SSpace.toModel (T D) mtail
          rw [ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
            ContinuousMultilinearMap.smul_apply] }
    with hscalarize_def
  have hscalarize_apply : ∀ T : TensorRSSpace 0 m I y,
      scalarize T = Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from T) D) mtail := by
    intro T
    rw [hscalarize_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

  set Hb : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X => scalarize.comp
          (pureRSlot0BilinAt (I := I) (M := M) g m (fun b : M => W.toSection b) y v X)
        map_add' := fun X X' => by
          ext Y
          change scalarize (pureRSlot0BilinAt (I := I) (M := M) g m
              (fun b : M => W.toSection b) y v (X + X') Y) =
            scalarize (pureRSlot0BilinAt (I := I) (M := M) g m
                (fun b : M => W.toSection b) y v X Y) +
              scalarize (pureRSlot0BilinAt (I := I) (M := M) g m
                (fun b : M => W.toSection b) y v X' Y)
          rw [map_add (pureRSlot0BilinAt (I := I) (M := M) g m
            (fun b : M => W.toSection b) y v) X X',
            ContinuousLinearMap.add_apply, map_add scalarize]
        map_smul' := fun c X => by
          ext Y
          change scalarize (pureRSlot0BilinAt (I := I) (M := M) g m
              (fun b : M => W.toSection b) y v (c • X) Y) =
            c • scalarize (pureRSlot0BilinAt (I := I) (M := M) g m
              (fun b : M => W.toSection b) y v X Y)
          rw [map_smul (pureRSlot0BilinAt (I := I) (M := M) g m
            (fun b : M => W.toSection b) y v) c X,
            ContinuousLinearMap.smul_apply, map_smul scalarize] }
    with hHb_def
  have hHb_apply : ∀ X Y : TangentSpace I y,
      Hb X Y = Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from
          pureRSlot0BilinAt (I := I) (M := M) g m (fun b : M => W.toSection b) y v X Y) D) mtail := by
    intro X Y
    rw [hHb_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      ContinuousLinearMap.comp_apply, hscalarize_apply]

  have hframe : ∀ (F : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from
          pureRFrozenDirCLM (I := I) (M := M) g m F (fun b : M => W.toSection b) y v) D) mtail =
      ∑ i : Fin (Module.finrank ℝ E), Hb (F i y) (F i y) := by
    intro F
    have hsum_apply :
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from
          pureRFrozenDirCLM (I := I) (M := M) g m F (fun b : M => W.toSection b) y v) D =
        ∑ i : Fin (Module.finrank ℝ E),
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from
            riemannOp (tensorCov (I := I) g 0 m) y (F i y) v
              ((covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W.toSection y) (F i y))) D := by
      rw [pureRFrozenDirCLM_apply, ContinuousLinearMap.sum_apply]
    rw [hsum_apply, ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Tensor0SSpace.toModelL_apply, hHb_apply (F i y) (F i y),
      pureRSlot0BilinAt_frame_summand (I := I) (M := M) g m W F i y v]
  rw [hframe B, hframe C]
  rw [orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => B i y) hB_orth,
    orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => C i y) hC_orth]

private noncomputable def pureRGenuineEndoFib
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    TensorRSSpace 0 (m + 1) I x :=
  pureRFrozenEndoFib (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) W x

omit [CompactSpace M] [I.Boundaryless] in
private lemma pureRGenuineEndoFib_eq_frozen_on_nbhd
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W : SmoothCcTensor g 0 (m + 1)) (x₀ : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    pureRGenuineEndoFib (I := I) (M := M) g m W y =
      pureRFrozenEndoFib (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x₀) W y := by
  rw [pureRGenuineEndoFib, pureRFrozenEndoFib, pureRFrozenEndoFib]
  refine congrArg (covGradBundleEquiv (I := I) (M := M) 0 m y) ?_
  exact pureRFrozenDirCLM_frame_independent (I := I) (M := M) g m W y
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hy i j)

omit [CompactSpace M] [I.Boundaryless] in
private theorem pureRGenuineEndoFib_contMDiff
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (m + 1) I z) x
        (pureRGenuineEndoFib (I := I) (M := M) g m W x)) := by
  classical
  intro x₀
  have h_fixed_at : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (m + 1) I z) y
        (pureRFrozenEndoFib (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x₀) W y)) x₀ :=
    pureRFrozenEndoFib_contMDiff (I := I) (M := M) g m
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) W x₀
  refine h_fixed_at.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
    (E := fun z : M => TensorRSSpace 0 (m + 1) I z) y)
    (pureRGenuineEndoFib_eq_frozen_on_nbhd (I := I) (M := M) g m W x₀ hy)

private noncomputable def pureRGenuineEndoSucc
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1)) :
    SmoothCcTensor g 0 (m + 1) where
  toSection :=
    { toFun := fun x : M => pureRGenuineEndoFib (I := I) (M := M) g m W x
      contMDiff_toFun := pureRGenuineEndoFib_contMDiff (I := I) (M := M) g m W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
@[simp] private lemma pureRGenuineEndoSucc_toSection
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    (pureRGenuineEndoSucc (I := I) (M := M) g m W).toSection x =
      pureRGenuineEndoFib (I := I) (M := M) g m W x := rfl

private noncomputable def pureRGenuineEndo0
    (g : SmoothRiemannianMetric I M) :
    ∀ (r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 r
  | 0 => fun _ => 0
  | (m + 1) => fun W => pureRGenuineEndoSucc (I := I) (M := M) g m W

noncomputable def pureRGenuineDiffOp
    (g : SmoothRiemannianMetric I M) :
    ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)
  | 0, r => fun W => pureRGenuineEndo0 (I := I) (M := M) g r W
  | (p + 1), r => fun W =>
      covGrad (I := I) (M := M) g 0 (r + p)
          (pureRGenuineDiffOp g p r W) -
        castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
          (pureRGenuineDiffOp g p (r + 1) (covGrad (I := I) (M := M) g 0 r W))

private theorem covGrad_pureRGenuineDiffOp_eq
    (g : SmoothRiemannianMetric I M) (p r : ℕ) (W : SmoothCcTensor g 0 r) :
    covGrad (I := I) (M := M) g 0 (r + p) (pureRGenuineDiffOp (I := I) (M := M) g p r W) =
      pureRGenuineDiffOp (I := I) (M := M) g (p + 1) r W +
        castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
          (pureRGenuineDiffOp (I := I) (M := M) g p (r + 1)
            (covGrad (I := I) (M := M) g 0 r W)) := by
  change _ = (covGrad (I := I) (M := M) g 0 (r + p)
      (pureRGenuineDiffOp (I := I) (M := M) g p r W) -
      castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
        (pureRGenuineDiffOp (I := I) (M := M) g p (r + 1)
          (covGrad (I := I) (M := M) g 0 r W))) + _
  rw [sub_add_cancel]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRGenuineEndoFib_linear
    (g : SmoothRiemannianMetric I M) (m : ℕ) (c₁ c₂ : ℝ)
    (W₁ W₂ : SmoothCcTensor g 0 (m + 1)) (x : M) :
    pureRGenuineEndoFib (I := I) (M := M) g m
        (c₁ • W₁ + c₂ • W₂) x =
      c₁ • pureRGenuineEndoFib (I := I) (M := M) g m W₁ x +
        c₂ • pureRGenuineEndoFib (I := I) (M := M) g m W₂ x := by
  classical
  rw [pureRGenuineEndoFib, pureRGenuineEndoFib, pureRGenuineEndoFib]
  rw [pureRFrozenEndoFib, pureRFrozenEndoFib, pureRFrozenEndoFib]
  rw [← map_smul (covGradBundleEquiv (I := I) (M := M) 0 m x) c₁,
    ← map_smul (covGradBundleEquiv (I := I) (M := M) 0 m x) c₂,
    ← map_add (covGradBundleEquiv (I := I) (M := M) 0 m x)]
  refine congrArg (covGradBundleEquiv (I := I) (M := M) 0 m x) ?_
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply,
    pureRFrozenDirCLM_apply, pureRFrozenDirCLM_apply, pureRFrozenDirCLM_apply,
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hval : (c₁ • W₁ + c₂ • W₂).toSection x =
      c₁ • W₁.toSection x + c₂ • W₂.toSection x := by
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [hval, map_add, map_smul, map_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, map_add, map_smul, map_smul]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRGenuineEndoFib_local
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W₁ W₂ : SmoothCcTensor g 0 (m + 1)) (x : M)
    (hx : W₁.toSection x = W₂.toSection x) :
    pureRGenuineEndoFib (I := I) (M := M) g m W₁ x =
      pureRGenuineEndoFib (I := I) (M := M) g m W₂ x := by
  classical
  rw [pureRGenuineEndoFib, pureRGenuineEndoFib, pureRFrozenEndoFib, pureRFrozenEndoFib]
  refine congrArg (covGradBundleEquiv (I := I) (M := M) 0 m x) ?_
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [pureRFrozenDirCLM_apply, pureRFrozenDirCLM_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hx]

private theorem pureRGenuineDiffOp_isOrderZeroCurvFactor (g : SmoothRiemannianMetric I M) :
    IsPointwiseLinearLocalOperator (I := I) (M := M) g (pureRGenuineDiffOp (I := I) (M := M) g) where
  linear := by
    intro r c₁ c₂ W₁ W₂ x
    cases r with
    | zero =>
        have h0 : ∀ W : SmoothCcTensor g 0 0,
            (pureRGenuineDiffOp (I := I) (M := M) g 0 0 W).toSection x =
              (0 : TensorRSSpace 0 (0 + 0) I x) := by
          intro W
          change (pureRGenuineEndo0 (I := I) (M := M) g 0 W).toSection x =
            (0 : TensorRSSpace 0 (0 + 0) I x)
          rw [show pureRGenuineEndo0 (I := I) (M := M) g 0 W = 0 from rfl,
            SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]
          rfl
        rw [h0, h0, h0]
        simp
    | succ m =>
        rw [show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) (c₁ • W₁ + c₂ • W₂)).toSection x =
              pureRGenuineEndoFib (I := I) (M := M) g m (c₁ • W₁ + c₂ • W₂) x from rfl,
          show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W₁).toSection x =
              pureRGenuineEndoFib (I := I) (M := M) g m W₁ x from rfl,
          show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W₂).toSection x =
              pureRGenuineEndoFib (I := I) (M := M) g m W₂ x from rfl,
          pureRGenuineEndoFib_linear (I := I) (M := M) g m c₁ c₂ W₁ W₂ x]
  local' := by
    intro r W₁ W₂ x hx
    cases r with
    | zero =>
        have h0 : ∀ W : SmoothCcTensor g 0 0,
            (pureRGenuineDiffOp (I := I) (M := M) g 0 0 W).toSection x =
              (0 : TensorRSSpace 0 (0 + 0) I x) := by
          intro W
          change (pureRGenuineEndo0 (I := I) (M := M) g 0 W).toSection x =
            (0 : TensorRSSpace 0 (0 + 0) I x)
          rw [show pureRGenuineEndo0 (I := I) (M := M) g 0 W = 0 from rfl,
            SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]
          rfl
        rw [h0, h0]
    | succ m =>
        rw [show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W₁).toSection x =
              pureRGenuineEndoFib (I := I) (M := M) g m W₁ x from rfl,
          show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W₂).toSection x =
              pureRGenuineEndoFib (I := I) (M := M) g m W₂ x from rfl,
          pureRGenuineEndoFib_local (I := I) (M := M) g m W₁ W₂ x hx]

private noncomputable def pureRDirCLMTensor
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (τ : TensorRSSpace 0 (m + 1) I x) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 m I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    (haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
     haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
     LinearMap.toContinuousLinearMap
      { toFun := fun v => riemannOp (tensorCov (I := I) g 0 m) x (B i x) v
          ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ (B i x))
        map_add' := fun v v' => by
          rw [map_add (riemannOp (tensorCov (I := I) g 0 m) x (B i x)) v v']; rfl
        map_smul' := fun c v => by
          rw [map_smul (riemannOp (tensorCov (I := I) g 0 m) x (B i x)) c v]; rfl })


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRDirCLMTensor_apply
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (τ : TensorRSSpace 0 (m + 1) I x) (v : TangentSpace I x) :
    pureRDirCLMTensor (I := I) (M := M) g m B x τ v =
      ∑ i : Fin (Module.finrank ℝ E),
        riemannOp (tensorCov (I := I) g 0 m) x (B i x) v
          ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ (B i x)) := by
  classical
  rw [pureRDirCLMTensor, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRFrozenDirCLM_eq_pureRDirCLMTensor
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x =
      pureRDirCLMTensor (I := I) (M := M) g m B x (W.toSection x) := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [pureRFrozenDirCLM_apply, pureRDirCLMTensor_apply]


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem riemannOp_tensorCov_homNatural
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M) (v w : TangentSpace I x)
    (Ξ : TensorRSSpace 0 m I x) (d : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        riemannOp (tensorCov (I := I) g 0 m) x v w Ξ) d =
      riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) x v w
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from Ξ) d) := by
  classical
  set X : Π y : M, TangentSpace I y := smoothExtensionTangent (I := I) x v with hX_def
  set Wfield : Π y : M, TangentSpace I y := smoothExtensionTangent (I := I) x w with hW_def
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) :=
    smoothExtensionTangent_contMDiff (I := I) x v
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Wfield) :=
    smoothExtensionTangent_contMDiff (I := I) x w
  have hXx : X x = v := smoothExtensionTangent_eq (I := I) x v
  have hWx : Wfield x = w := smoothExtensionTangent_eq (I := I) x w
  obtain ⟨Ξsec, hΞx⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := TensorRSModel 0 m ℝ E) (V := fun y : M => TensorRSSpace 0 m I y) (n := (⊤ : ℕ∞)) x Ξ
  obtain ⟨dSec, hdSec⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 0 ℝ E) (V := fun y : M => Tensor0SSpace 0 I y) (n := (⊤ : ℕ∞)) x d
  have hΞd_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel m ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel m ℝ E)
        (E := fun z : M => Tensor0SSpace m I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from Ξsec y) (dSec y))) :=
    ContMDiff.clm_bundle_apply (b := id) Ξsec.contMDiff dSec.contMDiff
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        riemannOp (tensorCov (I := I) g 0 m) x v w Ξ) d =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        riemannSec (tensorCov (I := I) g 0 m) (fun b => X b) (fun b => Wfield b)
          (fun b => Ξsec b) x) (dSec x) from by
    rw [← hXx, ← hWx, ← hΞx,
      riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 m) hX hW Ξsec.contMDiff]
    rw [show d = dSec x from hdSec.symm]]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        riemannSec (tensorCov (I := I) g 0 m) (fun b => X b) (fun b => Wfield b)
          (fun b => Ξsec b) x) (dSec x) =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g))
          (fun b => X b) (fun b => Wfield b)
          (HomConnectionGen.pairedSection (M := M) (U := fun z : M => Tensor0SSpace 0 I z)
            (V := fun z : M => Tensor0SSpace m I z)
            (fun b => Ξsec b) (fun b => dSec b)) x -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from Ξsec x)
          (riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
            (fun b => X b) (fun b => Wfield b) (fun b => dSec b) x) from
    HomConnectionGen.riemannSec_homBundleGen_apply_eq I M
      (Tensor0SModel 0 ℝ E) (fun z : M => Tensor0SSpace 0 I z)
      (Tensor0SModel m ℝ E) (fun z : M => Tensor0SSpace m I z)
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
      (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g))
      ⟨fun b => X b, hX⟩ ⟨fun b => Wfield b, hW⟩ Ξsec dSec x]
  rw [show riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
        (fun b => X b) (fun b => Wfield b) (fun b => dSec b) x = 0 from
    riemannSec_tensor0SCov_zero_eq_zero (I := I) (M := M) g ⟨fun b => X b, hX⟩
      ⟨fun b => Wfield b, hW⟩ (fun b => dSec b) dSec.contMDiff x]
  rw [map_zero, sub_zero]
  rw [show riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) x v w
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from Ξ) d) =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g))
          (fun b => X b) (fun b => Wfield b)
          (HomConnectionGen.pairedSection (M := M) (U := fun z : M => Tensor0SSpace 0 I z)
            (V := fun z : M => Tensor0SSpace m I z)
            (fun b => Ξsec b) (fun b => dSec b)) x from by
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from Ξ) d =
        HomConnectionGen.pairedSection (M := M) (U := fun z : M => Tensor0SSpace 0 I z)
          (V := fun z : M => Tensor0SSpace m I z)
          (fun b => Ξsec b) (fun b => dSec b) x from by
      rw [HomConnectionGen.pairedSection_apply, show d = dSec x from hdSec.symm, hΞx]]
    rw [← hXx, ← hWx]
    exact riemannOp_apply_smooth
      (cov := Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) hX hW
      hΞd_smooth]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma covGradBundleEquiv_symm_apply_eq_curry
    (m : ℕ) (x : M)
    (τ : TensorRSSpace 0 (m + 1) I x) (w : TangentSpace I x) (d : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
      ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ) w) d =
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from τ) d) w := by
  apply tensor0SSpace_ext (𝕜 := ℝ) m x
  intro v'
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ) w) d v' =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
          ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ) w) d) v' from rfl]
  rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) 0 m x τ w d v']
  rw [show tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from τ) d) w v' =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from τ) d) w) v' from rfl]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from τ) d) w v']


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRDirCLMTensor_covGradEquiv_eval
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (τ : TensorRSSpace 0 (m + 1) I x) (d : Tensor0SSpace 0 I x)
    (v : Fin (m + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 m x
            (pureRDirCLMTensor (I := I) (M := M) g m B x τ)) d) v =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) x
            (B i x) (v 0)
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from τ) d) (B i x)))
          (Matrix.vecTail v) := by
  classical
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) 0 m x
    (pureRDirCLMTensor (I := I) (M := M) g m B x τ) d v]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        pureRDirCLMTensor (I := I) (M := M) g m B x τ (v 0)) d =
      (∑ i : Fin (Module.finrank ℝ E),
        riemannOp (tensorCov (I := I) g 0 m) x (B i x) (v 0)
          ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ (B i x))) d from by
    rw [pureRDirCLMTensor_apply (I := I) (M := M) g m B x τ (v 0)]]
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Tensor0SSpace.toModelL_apply]
  rw [riemannOp_tensorCov_homNatural (I := I) (M := M) g m x (B i x) (v 0)
    ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ (B i x)) d]
  rw [covGradBundleEquiv_symm_apply_eq_curry (I := I) (M := M) m x τ (B i x) d]


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureREndoOpFibVal_eval
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (S : Tensor0SSpace (m + 1) I x) (v : Fin (m + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 m x
            (pureRDirCLMTensor (I := I) (M := M) g m B x
              (unitScalarRSLift (I := I) (M := M) x S)))
          (unitZeroSec (I := I) (M := M) x)) v =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) x
            (B i x) (v 0)
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x S (B i x)))
          (Matrix.vecTail v) := by
  rw [pureRDirCLMTensor_covGradEquiv_eval (I := I) (M := M) g m B x
    (unitScalarRSLift (I := I) (M := M) x S) (unitZeroSec (I := I) (M := M) x) v]
  rw [unitScalarRSLift_apply_unit (I := I) (M := M) x S]


private noncomputable def pureREndoOpFib
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace (m + 1) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (m + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun S =>
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 m x
            (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
              (unitScalarRSLift (I := I) (M := M) x S)))
          (unitZeroSec (I := I) (M := M) x)
      map_add' := fun S S' => by
        apply tensor0SSpace_ext (𝕜 := ℝ) (m + 1) x
        intro v
        rw [show (show Tensor0SSpace (m + 1) I x from
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                  covGradBundleEquiv (I := I) (M := M) 0 m x
                    (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                      (unitScalarRSLift (I := I) (M := M) x (S + S'))))
                  (unitZeroSec (I := I) (M := M) x)) v =
              Tensor0SSpace.toModel
                ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                  covGradBundleEquiv (I := I) (M := M) 0 m x
                    (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                      (unitScalarRSLift (I := I) (M := M) x (S + S'))))
                  (unitZeroSec (I := I) (M := M) x)) v from rfl,
          show (show Tensor0SSpace (m + 1) I x from
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                  covGradBundleEquiv (I := I) (M := M) 0 m x
                    (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                      (unitScalarRSLift (I := I) (M := M) x S)))
                  (unitZeroSec (I := I) (M := M) x) +
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                  covGradBundleEquiv (I := I) (M := M) 0 m x
                    (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                      (unitScalarRSLift (I := I) (M := M) x S')))
                  (unitZeroSec (I := I) (M := M) x)) v =
              Tensor0SSpace.toModel
                  ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                    covGradBundleEquiv (I := I) (M := M) 0 m x
                      (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                        (unitScalarRSLift (I := I) (M := M) x S)))
                    (unitZeroSec (I := I) (M := M) x)) v +
                Tensor0SSpace.toModel
                  ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                    covGradBundleEquiv (I := I) (M := M) 0 m x
                      (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                        (unitScalarRSLift (I := I) (M := M) x S')))
                    (unitZeroSec (I := I) (M := M) x)) v from rfl]
        rw [pureREndoOpFibVal_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x (S + S') v,
          pureREndoOpFibVal_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x S v,
          pureREndoOpFibVal_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x S' v,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [show tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x (S + S')
                (smoothOrthoFrame (I := I) g x i x) =
              tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x S (smoothOrthoFrame (I := I) g x i x) +
                tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x S'
                  (smoothOrthoFrame (I := I) g x i x) from by
          rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x),
            ContinuousLinearMap.add_apply]]
        rw [map_add (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g))
          x (smoothOrthoFrame (I := I) g x i x) (v 0)), Tensor0SSpace.toModel_add,
          ContinuousMultilinearMap.add_apply]
      map_smul' := fun c S => by
        apply tensor0SSpace_ext (𝕜 := ℝ) (m + 1) x
        intro v
        rw [show (show Tensor0SSpace (m + 1) I x from
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                  covGradBundleEquiv (I := I) (M := M) 0 m x
                    (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                      (unitScalarRSLift (I := I) (M := M) x (c • S))))
                  (unitZeroSec (I := I) (M := M) x)) v =
              Tensor0SSpace.toModel
                ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                  covGradBundleEquiv (I := I) (M := M) 0 m x
                    (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                      (unitScalarRSLift (I := I) (M := M) x (c • S))))
                  (unitZeroSec (I := I) (M := M) x)) v from rfl,
          show (show Tensor0SSpace (m + 1) I x from
                (RingHom.id ℝ) c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                  covGradBundleEquiv (I := I) (M := M) 0 m x
                    (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                      (unitScalarRSLift (I := I) (M := M) x S)))
                  (unitZeroSec (I := I) (M := M) x)) v =
              c • Tensor0SSpace.toModel
                  ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                    covGradBundleEquiv (I := I) (M := M) 0 m x
                      (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                        (unitScalarRSLift (I := I) (M := M) x S)))
                    (unitZeroSec (I := I) (M := M) x)) v from rfl]
        rw [pureREndoOpFibVal_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x (c • S) v,
          pureREndoOpFibVal_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x S v,
          Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [show tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x (c • S)
                (smoothOrthoFrame (I := I) g x i x) =
              c • tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x S
                (smoothOrthoFrame (I := I) g x i x) from by
          rw [map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x),
            ContinuousLinearMap.smul_apply]]
        rw [map_smul (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g))
          x (smoothOrthoFrame (I := I) g x i x) (v 0)), Tensor0SSpace.toModel_smul,
          ContinuousMultilinearMap.smul_apply] }


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureREndoOpFib_apply
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M) (S : Tensor0SSpace (m + 1) I x) :
    pureREndoOpFib (I := I) (M := M) g m x S =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        covGradBundleEquiv (I := I) (M := M) 0 m x
          (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
            (unitScalarRSLift (I := I) (M := M) x S)))
        (unitZeroSec (I := I) (M := M) x) := by
  rw [pureREndoOpFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRGenuineEndoFib_eq_comp
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    pureRGenuineEndoFib (I := I) (M := M) g m W x =
      TensorRSSpace.ofCLM
        ((pureREndoOpFib (I := I) (M := M) g m x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x)) := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 (m + 1) x
  intro d
  apply tensor0SSpace_ext (𝕜 := ℝ) (m + 1) x
  intro v

  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        pureRGenuineEndoFib (I := I) (M := M) g m W x) d v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 m x
            (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
              (W.toSection x))) d) v from by
    rw [pureRGenuineEndoFib, pureRFrozenEndoFib,
      pureRFrozenDirCLM_eq_pureRDirCLMTensor (I := I) (M := M) g m
        (smoothOrthoFrame (I := I) g x) W x]
    rfl]
  rw [pureRDirCLMTensor_covGradEquiv_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
    (W.toSection x) d v]

  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        TensorRSSpace.ofCLM
          ((pureREndoOpFib (I := I) (M := M) g m x).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x))) d v =
      Tensor0SSpace.toModel
        (pureREndoOpFib (I := I) (M := M) g m x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x) d)) v from rfl]
  rw [pureREndoOpFib_apply (I := I) (M := M) g m x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x) d)]
  rw [pureRDirCLMTensor_covGradEquiv_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
    (unitScalarRSLift (I := I) (M := M) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x) d))
    (unitZeroSec (I := I) (M := M) x) v]
  rw [unitScalarRSLift_apply_unit (I := I) (M := M) x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x) d)]


theorem pureRGenuineDiffOp_zero_succ_toSection_unit_eval
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1)) (x : M)
    (v : Fin (m + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W).toSection x)
          (unitZeroSec (I := I) (M := M) x)) v =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) x
            (smoothOrthoFrame (I := I) g x i x) (v 0)
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x)
                (unitZeroSec (I := I) (M := M) x))
              (smoothOrthoFrame (I := I) g x i x)))
          (Matrix.vecTail v) := by
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W).toSection x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        covGradBundleEquiv (I := I) (M := M) 0 m x
          (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
            (W.toSection x))) from by
    change (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        pureRGenuineEndoFib (I := I) (M := M) g m W x) = _
    rw [pureRGenuineEndoFib, pureRFrozenEndoFib,
      pureRFrozenDirCLM_eq_pureRDirCLMTensor (I := I) (M := M) g m
        (smoothOrthoFrame (I := I) g x) W x]]
  rw [pureRDirCLMTensor_covGradEquiv_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
    (W.toSection x) (unitZeroSec (I := I) (M := M) x) v]


private theorem pureREndoOp_contMDiff (g : SmoothRiemannianMetric I M) (m : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel (m + 1) (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel (m + 1) (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace (m + 1) (m + 1) I z)
        x (TensorRSSpace.ofCLM (pureREndoOpFib (I := I) (M := M) g m x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel (m + 1) ℝ E) (V₁ := fun x : M => Tensor0SSpace (m + 1) I x)
    (F₂ := Tensor0SModel (m + 1) ℝ E) (V₂ := fun x : M => Tensor0SSpace (m + 1) I x)
    (φ := fun x => (show Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace (m + 1) I x from
      pureREndoOpFib (I := I) (M := M) g m x))
  intro Z
  set Wσ : SmoothCcTensor g 0 (m + 1) :=
    ⟨unitScalarRSLiftCₛ (I := I) (M := M) Z, HasCompactSupport.of_compactSpace _⟩ with hWσ_def

  have hpt : ∀ x : M, pureREndoOpFib (I := I) (M := M) g m x (Z x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        pureRGenuineEndoFib (I := I) (M := M) g m Wσ x) (unitZeroSec (I := I) (M := M) x) := by
    intro x
    rw [pureREndoOpFib_apply (I := I) (M := M) g m x (Z x)]
    rw [pureRGenuineEndoFib, pureRFrozenEndoFib,
      pureRFrozenDirCLM_eq_pureRDirCLMTensor (I := I) (M := M) g m
        (smoothOrthoFrame (I := I) g x) Wσ x]
    rfl
  have hWσ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (m + 1) I z) x
        (pureRGenuineEndoFib (I := I) (M := M) g m Wσ x)) :=
    pureRGenuineEndoFib_contMDiff (I := I) (M := M) g m Wσ
  have heval : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (m + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (m + 1) I z) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          pureRGenuineEndoFib (I := I) (M := M) g m Wσ x)
          (unitZeroSec (I := I) (M := M) x))) :=
    ContMDiff.clm_bundle_apply (b := id) hWσ (unitZeroSec (I := I) (M := M)).contMDiff
  refine heval.congr ?_
  intro x
  exact (congrArg (TotalSpace.mk' (Tensor0SModel (m + 1) ℝ E)
    (E := fun z : M => Tensor0SSpace (m + 1) I z) x) (hpt x)).symm ▸ rfl

theorem exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (g : SmoothRiemannianMetric I M) :
    ∃ Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0),
      ∀ (r : ℕ) (W : SmoothCcTensor g 0 r),
        pureRGenuineDiffOp (I := I) (M := M) g 0 r W =
          operatorFieldApply (I := I) (M := M) g (r + 0) (r + 0) (Φ₀ r) W := by
  classical

  refine ⟨fun r => match r with
    | 0 => 0
    | (m + 1) =>
        { toSection :=
            { toFun := fun x : M => TensorRSSpace.ofCLM (pureREndoOpFib (I := I) (M := M) g m x)
              contMDiff_toFun := pureREndoOp_contMDiff (I := I) (M := M) g m }
          hasCompactSupport := HasCompactSupport.of_compactSpace _ }, ?_⟩
  intro r W
  cases r with
  | zero =>

      apply SmoothCcTensor.ext
      apply ContMDiffSection.ext
      intro x
      rw [show (pureRGenuineDiffOp (I := I) (M := M) g 0 0 W).toSection x =
            (pureRGenuineEndo0 (I := I) (M := M) g 0 W).toSection x from rfl,
        show pureRGenuineEndo0 (I := I) (M := M) g 0 W = 0 from rfl,
        SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]
      rw [appCc_toSection (I := I) (M := M) g 0 0 0 W]
      rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 0 I x from
            (0 : SmoothCcTensor g 0 0).toSection x) = 0 from by
        rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl]
      rw [ContinuousLinearMap.zero_comp]
      rfl
  | succ m =>

      apply SmoothCcTensor.ext
      apply ContMDiffSection.ext
      intro x
      rw [show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W).toSection x =
            pureRGenuineEndoFib (I := I) (M := M) g m W x from rfl]
      rw [appCc_toSection (I := I) (M := M) g (m + 1) (m + 1) _ W]
      rw [pureRGenuineEndoFib_eq_comp (I := I) (M := M) g m W x]
      rfl

theorem exists_proportional_pureRGenuineDiffOp_highOrder (g : SmoothRiemannianMetric I M) :
    ∃ kappaHigh : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kappaHigh p r) ∧
      ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + (p + 1)) x
            ((pureRGenuineDiffOp (I := I) (M := M) g (p + 1) r W).toSection x) ≤
          kappaHigh p r * ∑ q ∈ Finset.range (p + 2),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  classical

  obtain ⟨Φ₀, hΦ₀⟩ := exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (I := I) (M := M) g

  have hNF : ∀ (p r : ℕ),
      IsIteratedCovGradNormalForm (I := I) (M := M) g (pureRGenuineDiffOp (I := I) (M := M) g) p r :=
    fun p => normalForm_of_base (I := I) (M := M) g
      (pureRGenuineDiffOp (I := I) (M := M) g)
      (covGrad_pureRGenuineDiffOp_eq (I := I) (M := M) g) Φ₀ hΦ₀ p

  choose kap hkap_nn hkap using fun p r =>
    exists_jet_bound_of_normalForm (I := I) (M := M) g
      (pureRGenuineDiffOp (I := I) (M := M) g) p r (hNF p r)
  refine ⟨fun p r => kap (p + 1) r, fun p r => hkap_nn (p + 1) r, fun p r W x => ?_⟩

  have h := hkap (p + 1) r W x
  rw [show (p + 1) + 1 = p + 2 from rfl] at h
  exact h

theorem exists_proportional_pureRGenuineDiffOp (g : SmoothRiemannianMetric I M) :
    ∃ kappa : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kappa p r) ∧
      ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x
            ((pureRGenuineDiffOp (I := I) (M := M) g p r W).toSection x) ≤
          kappa p r * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  classical

  obtain ⟨kappa0, hkappa0_nn, hkappa0⟩ :=
    exists_proportional_pureRFrozenFrameDiffOp_orderZero (I := I) (M := M) g
  obtain ⟨kappaHigh, hkappaHigh_nn, hkappaHigh⟩ :=
    exists_proportional_pureRGenuineDiffOp_highOrder (I := I) (M := M) g
  refine ⟨fun p r => match p with | 0 => kappa0 r | (p' + 1) => kappaHigh p' r,
    fun p r => ?_, fun p r W x => ?_⟩
  · cases p with
    | zero => exact hkappa0_nn r
    | succ p' => exact hkappaHigh_nn p' r
  · cases p with
    | zero =>

        have h := hkappa0 r W x
        rw [show (fun p r => match p with
            | 0 => kappa0 r | (p' + 1) => kappaHigh p' r) 0 r = kappa0 r from rfl]
        have hsec : (pureRGenuineDiffOp (I := I) (M := M) g 0 r W).toSection x =
            (pureRFrozenDiffOp (I := I) (M := M) g (smoothOrthoFrame (I := I) g x)
              (fun i => smoothOrthoFrame_smooth (I := I) g x i) 0 r W).toSection x := by
          cases r with
          | zero => rfl
          | succ m => rfl
        rw [hsec, Finset.sum_range_one]

        exact h
    | succ p' =>
        have h := hkappaHigh p' r W x
        rw [show (fun p r => match p with
            | 0 => kappa0 r | (p'' + 1) => kappaHigh p'' r) (p' + 1) r = kappaHigh p' r from rfl]

        rw [show (p' + 1) + 1 = p' + 2 from rfl]
        exact h

omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRFrozenSlot0_covGrad_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    (covGradBundleEquiv (I := I) (M := M) 0 s x).symm
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) (B i x) =
      covApply (tensorCov (I := I) g 0 s) (B i) (fun y : M => S.toSection y) x := by
  rw [covGrad_toSection_apply (I := I) (M := M) g 0 s S x,
    ContinuousLinearEquiv.symm_apply_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRFrozenDiffOp0_eq_fixedFramePureRSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    pureRFrozenDiffOp (I := I) (M := M) g B hB 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S) =
      fixedFramePureRSection (I := I) (M := M) g s S B hB := by
  classical

  refine SmoothCcTensor.ext (DFunLike.ext _ _ (fun x => ?_))

  change pureRFrozenEndoFib (I := I) (M := M) g s B (covGrad (I := I) (M := M) g 0 s S) x =
    (fixedFramePureRSection (I := I) (M := M) g s S B hB).toSection x
  rw [fixedFramePureRSection_toSection, pureRFrozenEndoFib, genuineCurvPureRFibFixedFrame]

  refine congrArg (covGradBundleEquiv (I := I) (M := M) 0 s x) ?_
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [pureRFrozenDirCLM_apply, pureRDirCLMFixedFrame, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pureRDirCLMSummandFixedFrame, LinearMap.coe_toContinuousLinearMap', pureRDirLMSummandFixedFrame,
    LinearMap.coe_mk, AddHom.coe_mk, pureRFrozenSlot0_covGrad_eq (I := I) (M := M) g s S B x i]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covGrad_heq_congr_tw (g : SmoothRiemannianMetric I M) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g 0 a} {Z : SmoothCcTensor g 0 b} (hYZ : HEq Y Z) :
    HEq (covGrad (I := I) (M := M) g 0 a Y) (covGrad (I := I) (M := M) g 0 b Z) := by
  subst h
  rw [eq_of_heq hYZ]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_covGrad_comm_heq_tw (g : SmoothRiemannianMetric I M)
    (s q : ℕ) (X : SmoothCcTensor g 0 s) :
    HEq (iteratedCovGrad g 0 (s + 1) q (covGrad (I := I) (M := M) g 0 s X))
      (iteratedCovGrad g 0 s (q + 1) X) := by
  induction q with
  | zero =>
      rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := 0) (s := s + 1) (j := k)
        (covGrad (I := I) (M := M) g 0 s X)]
      rw [iteratedCovGrad_succ (g := g) (r := 0) (s := s) (j := k + 1) X]
      exact covGrad_heq_congr_tw g (by omega : (s + 1) + k = s + (k + 1)) ih

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem rfns_toSection_heq_congr_tw (g : SmoothRiemannianMetric I M)
    {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g 0 a} {Z : SmoothCcTensor g 0 b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 b x (Z.toSection x) := by
  subst h
  rw [eq_of_heq hYZ]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem riemannianFiberNormSq_toSection_iteratedCovGrad_covGrad_comm (g : SmoothRiemannianMetric I M)
    (s q : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + q) x
        ((iteratedCovGrad g 0 (s + 1) q (covGrad (I := I) (M := M) g 0 s S)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + (q + 1)) x
        ((iteratedCovGrad g 0 s (q + 1) S).toSection x) :=
  rfns_toSection_heq_congr_tw g (by omega : (s + 1) + q = s + (q + 1))
    (iteratedCovGrad_covGrad_comm_heq_tw (I := I) (M := M) g s q S) x

lemma pureRGenuineDiffOp0_eq_GcurvSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s) :
    pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s T) =
      genuineCurvatureOnlySection (I := I) (M := M) g s T := by
  classical
  refine SmoothCcTensor.ext (DFunLike.ext _ _ (fun x => ?_))

  change pureRGenuineEndoFib (I := I) (M := M) g s (covGrad (I := I) (M := M) g 0 s T) x =
    (genuineCurvatureOnlySection (I := I) (M := M) g s T).toSection x
  rw [pureRGenuineEndoFib]
  set hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    fun i => smoothOrthoFrame_smooth (I := I) g x i with hB_def

  have hfrozen := pureRFrozenDiffOp0_eq_fixedFramePureRSection (I := I) (M := M) g s T
    (smoothOrthoFrame (I := I) g x) hB
  have hfib : pureRFrozenEndoFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x)
        (covGrad (I := I) (M := M) g 0 s T) x =
      (fixedFramePureRSection (I := I) (M := M) g s T
        (smoothOrthoFrame (I := I) g x) hB).toSection x := by
    have := congrArg (fun (Z : SmoothCcTensor g 0 (s + 1)) => Z.toSection x) hfrozen
    simpa [pureRFrozenDiffOp, pureRFrozenEndo0, pureRFrozenEndoSucc_toSection] using this
  rw [hfib]

  exact ((GcurvSection_toSection_eventuallyEq_fixedFramePureRSection
    (I := I) (M := M) g s T x hB).self_of_nhds).symm

theorem exists_GcurvSection_iteratedCovGrad_grid_bound (g : SmoothRiemannianMetric I M) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (k : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + k) x
            ((iteratedCovGrad g 0 (s + 1) k
              (genuineCurvatureOnlySection (I := I) (M := M) g s S)).toSection x) ≤
          (c s k) ^ 2 * ∑ i ∈ Finset.range (1 + k),
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + 1)) x
              ((iteratedCovGrad g 0 s (i + 1) S).toSection x) := by
  classical
  obtain ⟨kappa, hkappa_nn, hkappa⟩ := exists_proportional_pureRGenuineDiffOp (I := I) (M := M) g

  refine ⟨fun s' k => Real.sqrt ((4 : ℝ) ^ k * gridWindowSum kappa 0 (s' + 1) k),
    fun _ k => Real.sqrt_nonneg _, fun s S k x => ?_⟩
  have hcsq : (Real.sqrt ((4 : ℝ) ^ k * gridWindowSum kappa 0 (s + 1) k)) ^ 2 =
      (4 : ℝ) ^ k * gridWindowSum kappa 0 (s + 1) k := by
    rw [Real.sq_sqrt]
    exact mul_nonneg (by positivity) (gridWindowSum_nonneg hkappa_nn 0 (s + 1) k)
  rw [hcsq]

  have hgrid := DifferentialGeometry.Integral.Connection.DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le_at
    (g := g)
    (op := fun p r W => pureRGenuineDiffOp (I := I) (M := M) g p r W)
    (fun p r W => covGrad_pureRGenuineDiffOp_eq (I := I) (M := M) g p r W)
    kappa hkappa_nn x
    (fun p r W => hkappa p r W x)
    (s + 1) (covGrad (I := I) (M := M) g 0 s S) k

  rw [pureRGenuineDiffOp0_eq_GcurvSection (I := I) (M := M) g s S] at hgrid
  refine hgrid.trans (le_of_eq ?_)

  refine congrArg (fun t => ((4 : ℝ) ^ k * gridWindowSum kappa 0 (s + 1) k) * t) ?_
  rw [Nat.add_comm 1 k]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact riemannianFiberNormSq_toSection_iteratedCovGrad_covGrad_comm (I := I) (M := M) g s q S x

noncomputable def curvOpField (g : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g (s + 0) (s + 0) :=
  (Classical.choose (exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (I := I) (M := M) g)) s

theorem curvOpField_apply_eq_pureRGenuineDiffOp
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
  (Classical.choose_spec (exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (I := I) (M := M) g) s S).symm

noncomputable def genuineDiffCurvSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1)
    (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S

@[simp] lemma genuineDiffCurvSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (genuineDiffCurvSection (I := I) (M := M) g s S).toSection x =
      (show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
        (covGrad (I := I) (M := M) g (s + 0) (s + 0)
          (curvOpField (I := I) (M := M) g s)).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from S.toSection x) := by
  rw [genuineDiffCurvSection,
    appCc_toSection (I := I) (M := M) g (s + 0) (s + 0 + 1)
      (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S x]
  rfl

theorem genuineDiffCurvSection_eq_covGrad_sub_slotExtend
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    genuineDiffCurvSection (I := I) (M := M) g s S =
      covGrad (I := I) (M := M) g 0 (s + 0)
          (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) -
        operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
          (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
            (curvOpField (I := I) (M := M) g s))
          (covGrad (I := I) (M := M) g 0 (s + 0) S) := by
  classical
  have hbase : operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
    (Classical.choose_spec (exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (I := I) (M := M) g) s S).symm
  have hB := covGrad_operatorFieldApply_eq (I := I) (M := M) g (s + 0) (s + 0)
    (curvOpField (I := I) (M := M) g s) S
  have hgds : operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S =
      genuineDiffCurvSection (I := I) (M := M) g s S := rfl
  rw [hgds] at hB
  have hB' := eq_sub_of_add_eq (hB.symm)
  rw [hB', hbase]

theorem appCc_slotExtend_curvOpField_covGrad_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
          (operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x) d)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
          (curvOpField (I := I) (M := M) g s).toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
        vs := by
  classical
  rw [appCc_toSection (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
      (slotExtend (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))
      (covGrad (I := I) (M := M) g 0 (s + 0) S) x,
    ContinuousLinearMap.comp_apply,
    slotExtend_toSection (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) x]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g (s + 0) (s + 0) x
    (show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
      (curvOpField (I := I) (M := M) g s).toSection x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
      (covGrad (I := I) (M := M) g 0 (s + 0) S).toSection x) d) v0 vs]
  rw [tensor0S_curry_covGrad_appCc_eq (I := I) (M := M) g (s + 0) S x d v0]

set_option maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in

theorem covGrad_pureRGenuineDiffOp_unit_eval_eq_genuineDiffCurv_add_spectator
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
          tensorCovDerivAt (I := I) (M := M) g 0 (s + 0)
            (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) x v0) d)
        vs =
      Tensor0SSpace.toModel
          ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x d)
          (Fin.cons v0 vs) +
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            (curvOpField (I := I) (M := M) g s).toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
          vs := by
  classical
  have hbase : operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
    (Classical.choose_spec (exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (I := I) (M := M) g) s S).symm
  have hB := covGrad_operatorFieldApply_eq (I := I) (M := M) g (s + 0) (s + 0)
    (curvOpField (I := I) (M := M) g s) S
  rw [hbase] at hB
  have hsec := congrArg (fun T : SmoothCcTensor g 0 (s + 0 + 1) => T.toSection x) hB
  simp only at hsec
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply] at hsec
  have happ :
      (covGrad (I := I) (M := M) g 0 (s + 0)
          (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toSection x d =
        (genuineDiffCurvSection (I := I) (M := M) g s S).toSection x d +
          (operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x d := by
    rw [hsec, ContinuousLinearMap.add_apply]
    rfl
  have hlhs :
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0)
              (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) x v0) d)
          vs =
        Tensor0SSpace.toModel
          ((covGrad (I := I) (M := M) g 0 (s + 0)
            (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toSection x d)
          (Fin.cons v0 vs) := by
    have h := covGrad_toSection_apply_eval (I := I) (M := M) g 0 (s + 0)
      (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) x d (Fin.cons v0 vs)
    refine Eq.symm (h.trans ?_)
    have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (s + 0 + 1) → E) = vs := by
      funext j; simp [Matrix.vecTail, Fin.cons_succ]
    have hhead : (Fin.cons v0 vs : Fin (s + 0 + 1) → E) 0 = v0 := by simp [Fin.cons_zero]
    rw [htail, hhead]
  have hterm2 :
      Tensor0SSpace.toModel
          ((operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x d)
          (Fin.cons v0 vs) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            (curvOpField (I := I) (M := M) g s).toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
          vs :=
    appCc_slotExtend_curvOpField_covGrad_unit_eval (I := I) (M := M) g s S x d v0 vs
  rw [hlhs, happ, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, hterm2]

theorem appCc_covGrad_covGrad_curvOpField_eq_covGrad_genuineDiffCurv_sub_slotExtend
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0 + 1)
          (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))) S =
      covGrad (I := I) (M := M) g 0 (s + 0 + 1)
          (genuineDiffCurvSection (I := I) (M := M) g s S) -
        operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1 + 1)
          (slotExtend (I := I) (M := M) g (s + 0) (s + 0 + 1)
            (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)))
          (covGrad (I := I) (M := M) g 0 (s + 0) S) := by
  classical
  have hB := covGrad_operatorFieldApply_eq (I := I) (M := M) g (s + 0) (s + 0 + 1)
    (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S
  have hgds : operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S =
      genuineDiffCurvSection (I := I) (M := M) g s S := rfl
  rw [hgds] at hB
  exact (eq_sub_of_add_eq hB.symm)

theorem appCc_slotExtend_covGrad_curvOpField_covGrad_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0 + 1) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1 + 1) I x from
          (operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0 + 1)
              (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x) d)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
          (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)).toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
        vs := by
  classical
  rw [appCc_toSection (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1 + 1)
      (slotExtend (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)))
      (covGrad (I := I) (M := M) g 0 (s + 0) S) x,
    ContinuousLinearMap.comp_apply,
    slotExtend_toSection (I := I) (M := M) g (s + 0) (s + 0 + 1)
      (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) x]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g (s + 0) (s + 0 + 1) x
    (show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
      (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)).toSection x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
      (covGrad (I := I) (M := M) g 0 (s + 0) S).toSection x) d) v0 vs]
  rw [tensor0S_curry_covGrad_appCc_eq (I := I) (M := M) g (s + 0) S x d v0]

theorem appCc_covGrad_covGrad_curvOpField_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0 + 1) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1 + 1) I x from
          (operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1 + 1)
            (covGrad (I := I) (M := M) g (s + 0) (s + 0 + 1)
              (covGrad (I := I) (M := M) g (s + 0) (s + 0)
                (curvOpField (I := I) (M := M) g s))) S).toSection x) d)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0 + 1)
              (genuineDiffCurvSection (I := I) (M := M) g s S) x v0) d)
          vs -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
            (covGrad (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s)).toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
          vs := by
  classical
  have hsec := appCc_covGrad_covGrad_curvOpField_eq_covGrad_genuineDiffCurv_sub_slotExtend
    (I := I) (M := M) g s S
  have happ :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1 + 1) I x from
          (operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1 + 1)
            (covGrad (I := I) (M := M) g (s + 0) (s + 0 + 1)
              (covGrad (I := I) (M := M) g (s + 0) (s + 0)
                (curvOpField (I := I) (M := M) g s))) S).toSection x) d =
        (covGrad (I := I) (M := M) g 0 (s + 0 + 1)
            (genuineDiffCurvSection (I := I) (M := M) g s S)).toSection x d -
          (operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0 + 1)
              (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x d := by
    rw [hsec]
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      ContinuousLinearMap.sub_apply]
  rw [happ, Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  have hT1 :
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1 + 1) I x from
            (covGrad (I := I) (M := M) g 0 (s + 0 + 1)
              (genuineDiffCurvSection (I := I) (M := M) g s S)).toSection x) d)
          (Fin.cons v0 vs) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0 + 1)
              (genuineDiffCurvSection (I := I) (M := M) g s S) x v0) d)
          vs := by
    rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 (s + 0 + 1)
      (genuineDiffCurvSection (I := I) (M := M) g s S) x d (Fin.cons v0 vs)]
    have hhead : (Fin.cons v0 vs : Fin (s + 0 + 1 + 1) → E) 0 = v0 := by
      simp [Fin.cons_zero]
    have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (s + 0 + 1 + 1) → E) =
        (vs : Fin (s + 0 + 1) → E) := by
      funext j; simp [Matrix.vecTail, Fin.cons_succ]
    rw [hhead, htail]
  have hT2 := appCc_slotExtend_covGrad_curvOpField_covGrad_unit_eval
    (I := I) (M := M) g s S x d v0 vs
  rw [hT1, hT2]

end Connection
end Integral
end DifferentialGeometry

end
