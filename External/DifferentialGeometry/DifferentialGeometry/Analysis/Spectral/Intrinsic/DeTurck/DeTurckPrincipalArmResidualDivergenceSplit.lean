import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricDifferenceSlotPairing
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.OperatorFieldPairingIBP
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.EigenBasis
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.DirichletSpectralBochnerGap
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedAppCcLeibniz
import DifferentialGeometry.Geometry.Connection.TensorNabla.EndoCovariantDerivativeSelfAdjoint
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SlotInsertSelfAdjointPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HomFieldActionL2JetBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.CovDivergenceRoughLaplacianCommutation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SlotSwapPairingCalculus
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.HomFieldCurvatureJetDecomposition


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private lemma armResidual_vecTail_cons {α : Type*} {n : ℕ} (a : α) (w : Fin n → α) :
    Matrix.vecTail (Fin.cons a w) = w := by
  funext j
  simp [Matrix.vecTail, Fin.cons_succ]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma armResidual_toModel_sum {s : ℕ} (b : M) {ι : Type*} (fs : Finset ι)
    (f : ι → Tensor0SSpace s I b) :
    Tensor0SSpace.toModel (∑ i ∈ fs, f i) = ∑ i ∈ fs, Tensor0SSpace.toModel (f i) :=
  map_sum (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) s b) f fs

omit [NeZero (Module.finrank ℝ E)] in
private lemma armResidual_model_slot0_linear {s : ℕ} {ι : Type*} (fs : Finset ι)
    (T : Tensor0SBundle.Tensor0SModel (s + 1) ℝ E) (c : ι → ℝ) (f : ι → E)
    (rest : Fin s → E) :
    T (Fin.cons (∑ j ∈ fs, c j • f j) rest) = ∑ j ∈ fs, c j * T (Fin.cons (f j) rest) := by
  have h : ∀ u : E, T (Fin.cons u rest) =
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1) => E) ℝ) T u) rest := by
    intro u
    rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [h, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul, ← h]

omit [NeZero (Module.finrank ℝ E)] in
private lemma armResidual_model_slot1_linear {s : ℕ} {ι : Type*} (fs : Finset ι)
    (T : Tensor0SBundle.Tensor0SModel (s + 1 + 1) ℝ E) (a : E) (c : ι → ℝ) (f : ι → E)
    (rest : Fin s → E) :
    T (Fin.cons a (Fin.cons (∑ j ∈ fs, c j • f j) rest)) =
      ∑ j ∈ fs, c j * T (Fin.cons a (Fin.cons (f j) rest)) := by
  have hcur : ∀ w : Fin (s + 1) → E,
      T (Fin.cons a w) =
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1 + 1) => E) ℝ) T a) w := by
    intro w
    rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [hcur,
    armResidual_model_slot0_linear (E := E) fs
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1 + 1) => E) ℝ) T a)
      c f rest]
  exact Finset.sum_congr rfl fun j _ => by rw [hcur]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma armResidual_orthoFrame_expansion (g₀ : SmoothRiemannianMetric I M) (b : M)
    (u : TangentSpace I b) :
    u = ∑ i : Fin (Module.finrank ℝ E),
      g₀.inner b u (smoothOrthoFrame (I := I) g₀ b i b) •
        smoothOrthoFrame (I := I) g₀ b i b := by
  classical
  have horth : ∀ a c : Fin (Module.finrank ℝ E),
      g₀.inner b (smoothOrthoFrame (I := I) g₀ b a b)
        (smoothOrthoFrame (I := I) g₀ b c b) = if a = c then 1 else 0 :=
    fun a c => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ b a c
  have he_li : LinearIndependent ℝ (fun i => smoothOrthoFrame (I := I) g₀ b i b) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g₀.inner b (smoothOrthoFrame (I := I) g₀ b k b)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g₀ b j b) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g₀.inner b (smoothOrthoFrame (I := I) g₀ b k b)
        (c j • smoothOrthoFrame (I := I) g₀ b j b) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g₀.inner b (smoothOrthoFrame (I := I) g₀ b k b)).map_smul (c j),
        smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E :=
    Fintype.card_fin _
  set bse := basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse : ∀ i, bse i = smoothOrthoFrame (I := I) g₀ b i b :=
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i
  have hcoeff : ∀ j : Fin (Module.finrank ℝ E),
      g₀.inner b u (smoothOrthoFrame (I := I) g₀ b j b) = bse.repr u j := by
    intro j
    rw [g₀.symm b u (smoothOrthoFrame (I := I) g₀ b j b)]
    conv_lhs => rw [← bse.sum_repr u]
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [(g₀.inner b (smoothOrthoFrame (I := I) g₀ b j b)).map_smul (bse.repr u i),
        smul_eq_mul, hbse i, horth j i])]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [if_pos rfl, mul_one]
    · intro i _ hij
      rw [if_neg (fun h => hij h.symm), mul_zero]
  calc u = ∑ i : Fin (Module.finrank ℝ E), bse.repr u i • bse i := (bse.sum_repr u).symm
    _ = ∑ i : Fin (Module.finrank ℝ E),
        g₀.inner b u (smoothOrthoFrame (I := I) g₀ b i b) •
          smoothOrthoFrame (I := I) g₀ b i b := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoeff i, hbse i]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma armResidual_toModel_contract_covariant (s : ℕ) (b : M) (v : TangentSpace I b)
    (A : TensorRSSpace 0 (s + 1) I b) (D : Tensor0SSpace 0 I b) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from
          Tensor0SBundle.contract_covariant 0 s b v A) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from A) D)
        (Fin.cons ((v : TangentSpace I b) : E) m) :=
  rfl

private lemma armResidual_covDivergence_toSection (g₀ : SmoothRiemannianMetric I M)
    (s : ℕ) (V : SmoothCcTensor g₀ 0 (s + 1)) (b : M) :
    ((covDivergence (I := I) (M := M) g₀ s V).toSection b : TensorRSSpace 0 s I b) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.contract_covariant 0 s b (smoothOrthoFrame (I := I) g₀ b i b)
          (tensorCovDerivAt (I := I) (M := M) g₀ 0 (s + 1) V b
            (smoothOrthoFrame (I := I) g₀ b i b)) := by
  classical
  rw [covDivergence_toSection_apply (I := I) (M := M) g₀ s V b]
  rw [covDivergenceRaw]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
        (smoothOrthoFrame (I := I) g₀ b i z)) b :=
    (smoothOrthoFrame_smooth (I := I) g₀ b i).contMDiffAt.mdifferentiableAt (by simp)
  rw [codiffPsi_apply (I := I) (M := M) g₀ s V b hSmooth_at hSmooth_at]
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 0 (s + 1) V b
    (smoothOrthoFrame (I := I) g₀ b i b)]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma armResidual_toModel_doubleTraceFib (g₀ : SmoothRiemannianMetric I M) (b : M)
    (W : Tensor0SSpace (2 + 2) I b) (m : Fin 2 → E) :
    Tensor0SSpace.toModel (DeTurck.cometricDoubleTraceFib (I := I) g₀ 2 b W) m =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel W
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m)) := by
  classical
  rw [DeTurck.cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g₀ 2 b
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) b) W]
  rw [armResidual_toModel_sum (I := I) (M := M) b Finset.univ
    (fun i => Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 b
      (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (2 + 1) b W
        (smoothOrthoFrame (I := I) g₀ b i b))
      (smoothOrthoFrame (I := I) g₀ b i b))]
  rw [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (2 + 1) b W
      (smoothOrthoFrame (I := I) g₀ b i b))
    (v0 := ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)) (vs := m)]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (T := W)
    (v0 := ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E))
    (vs := Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m)]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma armResidual_slot01_transpose (g₀ g₁ : SmoothRiemannianMetric I M) (b : M)
    (T : Tensor0SBundle.Tensor0SModel (2 + 1 + 1) ℝ E) (m : Fin 2 → E) :
    (∑ i : Fin (Module.finrank ℝ E),
        T (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
            (Fin.cons ((metricComparisonDiffEndo (I := I) g₀ g₁ b
                (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E) m))) =
      ∑ i : Fin (Module.finrank ℝ E),
        T (Fin.cons ((metricComparisonDiffEndo (I := I) g₀ g₁ b
              (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m)) := by
  classical
  set e : Fin (Module.finrank ℝ E) → TangentSpace I b :=
    fun i => smoothOrthoFrame (I := I) g₀ b i b with he
  set Λ : TangentSpace I b →L[ℝ] TangentSpace I b :=
    metricComparisonDiffEndo (I := I) g₀ g₁ b with hΛ
  have hadj : ∀ a c : TangentSpace I b, g₀.inner b (Λ a) c = g₀.inner b a (Λ c) :=
    fun a c => gInvDiffRaisedEndo_g0_self_adjoint (I := I) g₀ g₁ b a c
  have hexp : ∀ v : TangentSpace I b,
      v = ∑ j : Fin (Module.finrank ℝ E), g₀.inner b v (e j) • e j :=
    fun v => armResidual_orthoFrame_expansion (I := I) (M := M) g₀ b v
  have hL : ∀ i : Fin (Module.finrank ℝ E),
      T (Fin.cons ((e i : TangentSpace I b) : E)
          (Fin.cons ((Λ (e i) : TangentSpace I b) : E) m)) =
        ∑ j : Fin (Module.finrank ℝ E), g₀.inner b (Λ (e i)) (e j) *
          T (Fin.cons ((e i : TangentSpace I b) : E)
              (Fin.cons ((e j : TangentSpace I b) : E) m)) := by
    intro i
    conv_lhs => rw [hexp (Λ (e i))]
    exact armResidual_model_slot1_linear (E := E) Finset.univ T ((e i : TangentSpace I b) : E)
      (fun j => g₀.inner b (Λ (e i)) (e j)) (fun j => ((e j : TangentSpace I b) : E)) m
  have hR : ∀ i : Fin (Module.finrank ℝ E),
      T (Fin.cons ((Λ (e i) : TangentSpace I b) : E)
          (Fin.cons ((e i : TangentSpace I b) : E) m)) =
        ∑ j : Fin (Module.finrank ℝ E), g₀.inner b (Λ (e i)) (e j) *
          T (Fin.cons ((e j : TangentSpace I b) : E)
              (Fin.cons ((e i : TangentSpace I b) : E) m)) := by
    intro i
    conv_lhs => rw [hexp (Λ (e i))]
    exact armResidual_model_slot0_linear (E := E) Finset.univ T
      (fun j => g₀.inner b (Λ (e i)) (e j)) (fun j => ((e j : TangentSpace I b) : E))
      (Fin.cons ((e i : TangentSpace I b) : E) m)
  rw [Finset.sum_congr rfl (fun i _ => hL i), Finset.sum_congr rfl (fun i _ => hR i)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hco : g₀.inner b (Λ (e j)) (e i) = g₀.inner b (Λ (e i)) (e j) := by
    rw [hadj (e j) (e i), g₀.symm b (e j) (Λ (e i))]
  rw [hco]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma armResidual_covGrad_eval (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g₀ 0 s) (b : M) (D : Tensor0SSpace 0 I b)
    (v0 : E) (vs : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from
          (covGrad (I := I) (M := M) g₀ 0 s W).toSection b) D) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from
          tensorCovDerivAt (I := I) (M := M) g₀ 0 s W b v0) D) vs := by
  have h := covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 s W b D (Fin.cons v0 vs)
  have ht : Matrix.vecTail (Fin.cons v0 vs : Fin (s + 1) → TangentSpace I b) = vs := by
    funext j
    rfl
  exact h.trans (congrArg (fun w : Fin s → E =>
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from
        tensorCovDerivAt (I := I) (M := M) g₀ 0 s W b v0) D) w) ht)

omit [NeZero (Module.finrank ℝ E)] in
private lemma armResidual_contract_term_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (u₀ : SmoothCcTensor g₀ 0 2) (b : M) (D : Tensor0SSpace 0 I b) (m : Fin 2 → E)
    (i : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
          Tensor0SBundle.contract_covariant 0 2 b (smoothOrthoFrame (I := I) g₀ b i b)
            (tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))
                (covGrad (I := I) (M := M) g₀ 0 2 u₀)) b
              (smoothOrthoFrame (I := I) g₀ b i b))) D) m =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)
          (Fin.cons
            ((((endoCovariantDerivative (I := I) (M := M) g₀)
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
                  (smoothOrthoFrame (I := I) g₀ b i b))
                (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E) m) +
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toSection b) D)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
            (Fin.cons ((metricComparisonDiffEndo (I := I) g₀ g₁ b
                (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E) m)) := by
  classical
  set ei : TangentSpace I b := smoothOrthoFrame (I := I) g₀ b i b with hei
  set Du : SmoothCcTensor g₀ 0 (2 + 1) := covGrad (I := I) (M := M) g₀ 0 2 u₀ with hDu
  set Λf := gInvDiffRaisedEndoField (I := I) g₀ g₁ with hΛf
  rw [armResidual_toModel_contract_covariant (I := I) (M := M) 2 b ei _ D m]
  have hderiv := tensorCovDerivAt_appCc_eq (I := I) (M := M) g₀ (2 + 1) (2 + 1)
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 Λf) Du b ((ei : TangentSpace I b) : E)
  rw [hderiv]
  rw [show ((((show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          tensorCovDerivAt (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 Λf) b ((ei : TangentSpace I b) : E)).comp
          (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from Du.toSection b) +
        (show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 Λf).toSection b).comp
          (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) Du b
              ((ei : TangentSpace I b) : E))) : TensorRSSpace 0 (2 + 1) I b)) D =
      (show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          tensorCovDerivAt (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 Λf) b ((ei : TangentSpace I b) : E))
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from Du.toSection b) D) +
      (show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 Λf).toSection b)
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) Du b
            ((ei : TangentSpace I b) : E)) D) from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  congr 1
  · rw [tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g₀ 2 Λf b
      ((ei : TangentSpace I b) : E)]
    rw [slotInsertEndoFib_apply_eval (I := I) (M := M) (2 + 1) 0 b
      ((endoCovariantDerivative (I := I) (M := M) g₀) Λf b ((ei : TangentSpace I b) : E))
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from Du.toSection b) D)
      (Fin.cons ((ei : TangentSpace I b) : E) m)]
    rw [Fin.cons_zero, Fin.update_cons_zero]
  · rw [slotInsertEndoCc_toSection (I := I) (M := M) g₀ 2 Λf b]
    rw [slotInsertEndoFib_apply_eval (I := I) (M := M) (2 + 1) 0 b (Λf b)
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
        tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) Du b
          ((ei : TangentSpace I b) : E)) D)
      (Fin.cons ((ei : TangentSpace I b) : E) m)]
    rw [Fin.cons_zero, Fin.update_cons_zero]
    exact (armResidual_covGrad_eval (I := I) (M := M) g₀ (2 + 1) Du b D
      ((ei : TangentSpace I b) : E)
      (Fin.cons ((Λf b (ei : TangentSpace I b) : TangentSpace I b) : E) m)).symm

omit [BoundarylessManifold I M] in
private lemma armResidual_arm_toModel_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (u₀ : SmoothCcTensor g₀ 0 2) (b : M) (D : Tensor0SSpace 0 I b) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toSection b) D) m =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toSection b) D)
          (Fin.cons ((metricComparisonDiffEndo (I := I) g₀ g₁ b
              (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m)) := by
  classical
  rw [deTurckPrincipalCometricArm,
    deTurckPrincipalCometricCoeff_eq_appCcRS_doubleTrace_slotInsertEndo (I := I) (M := M) g₀ g₁]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (DifferentialGeometry.Integral.Connection.ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2
            (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (DifferentialGeometry.Integral.Connection.endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
          (iteratedCovGrad (I := I) g₀ 0 2 2 u₀)).toSection b) D) m =
    Tensor0SSpace.toModel
      (DeTurck.cometricDoubleTraceFib (I := I) g₀ 2 b
        (slotInsertEndoFib (I := I) (M := M) (3 + 1) 0 b
          (gInvDiffRaisedEndoField (I := I) g₀ g₁ b)
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 4 I b from
            (iteratedCovGrad (I := I) g₀ 0 2 2 u₀).toSection b) D))) m from rfl]
  rw [armResidual_toModel_doubleTraceFib (I := I) (M := M) g₀ b
    (slotInsertEndoFib (I := I) (M := M) (3 + 1) 0 b
      (gInvDiffRaisedEndoField (I := I) g₀ g₁ b)
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 4 I b from
        (iteratedCovGrad (I := I) g₀ 0 2 2 u₀).toSection b) D)) m]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) (3 + 1) 0 b
    (gInvDiffRaisedEndoField (I := I) g₀ g₁ b)
    ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 4 I b from
      (iteratedCovGrad (I := I) g₀ 0 2 2 u₀).toSection b) D)
    (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
      (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m))]
  rw [Fin.cons_zero, Fin.update_cons_zero]
  rfl

private lemma armResidual_gTerm_toModel_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (u₀ : SmoothCcTensor g₀ 0 2) (b : M) (D : Tensor0SSpace 0 I b) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0)
            (ccOperatorFieldComp (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))))
            (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toSection b) D) m =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)
          (Fin.cons
            ((((endoCovariantDerivative (I := I) (M := M) g₀)
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
                  (smoothOrthoFrame (I := I) g₀ b i b))
                (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E) m) := by
  classical
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0)
          (ccOperatorFieldComp (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
            (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toSection b) D) m =
    Tensor0SSpace.toModel
      (DeTurck.cometricDoubleTraceFib (I := I) g₀ 2 b
        ((show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
          (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection b)
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D))) m from rfl]
  rw [armResidual_toModel_doubleTraceFib (I := I) (M := M) g₀ b
    ((show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection b)
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
        (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)) m]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hstep : Tensor0SSpace.toModel
      ((show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
        (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection b)
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D))
      (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m)) =
      Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (2 + 1) 0 b
          ((endoCovariantDerivative (I := I) (M := M) g₀)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
            (smoothOrthoFrame (I := I) g₀ b i b))
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D))
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m) := by
    have h := covGrad_slotInsertEndoCc_toSection_eq (I := I) (M := M) g₀ 2
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
        (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)
      (Fin.cons (smoothOrthoFrame (I := I) g₀ b i b)
        (Fin.cons (smoothOrthoFrame (I := I) g₀ b i b) m))
    have ht : Matrix.vecTail (Fin.cons (smoothOrthoFrame (I := I) g₀ b i b)
        (Fin.cons (smoothOrthoFrame (I := I) g₀ b i b) m) :
          Fin (2 + 1 + 1) → TangentSpace I b) =
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m :
          Fin (2 + 1) → E) := by
      funext j
      refine Fin.cases ?_ (fun j' => ?_) j
      · rfl
      · rfl
    exact h.trans (congrArg (fun w : Fin (2 + 1) → E =>
      Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (2 + 1) 0 b
          ((endoCovariantDerivative (I := I) (M := M) g₀)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
            (smoothOrthoFrame (I := I) g₀ b i b))
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)) w) ht)
  rw [hstep]
  have happ : Tensor0SSpace.toModel
      (slotInsertEndoFib (I := I) (M := M) (2 + 1) 0 b
        ((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
          (smoothOrthoFrame (I := I) g₀ b i b))
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D))
      (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)
        (Function.update
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m) 0
          (((endoCovariantDerivative (I := I) (M := M) g₀)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
              (smoothOrthoFrame (I := I) g₀ b i b))
            ((Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m :
              Fin (2 + 1) → E) 0))) :=
    slotInsertEndoFib_apply_eval (I := I) (M := M) (2 + 1) 0 b _ _ _
  rw [happ]
  rw [show ((Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m :
      Fin (2 + 1) → E) 0) = ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
    from rfl]
  rw [Fin.update_cons_zero]

set_option backward.isDefEq.respectTransparency false in
theorem armResidual_covDivergence_split (g₀ g₁ : SmoothRiemannianMetric I M)
    (u₀ : SmoothCcTensor g₀ 0 2) :
    covDivergence (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀)) =
      deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀ +
        operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0)
          (ccOperatorFieldComp (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
            (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro b
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun m => ?_
  beta_reduce
  set P : SmoothCcTensor g₀ 0 (2 + 1) :=
    operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁))
      (covGrad (I := I) (M := M) g₀ 0 2 u₀) with hP
  set Garm : SmoothCcTensor g₀ 0 (2 + 0) :=
    operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 0)
      (ccOperatorFieldComp (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
        (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
        (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))))
      (covGrad (I := I) (M := M) g₀ 0 2 u₀) with hGarm
  rw [show ((deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀ + Garm).toSection b :
      TensorRSSpace 0 2 I b) =
    ((deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toSection b :
      TensorRSSpace 0 2 I b) + (Garm.toSection b : TensorRSSpace 0 2 I b) from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((((deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toSection b :
        TensorRSSpace 0 2 I b) + (Garm.toSection b : TensorRSSpace 0 2 I b) :
        TensorRSSpace 0 2 I b)) D =
    (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toSection b) D +
    (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from Garm.toSection b) D from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [armResidual_covDivergence_toSection (I := I) (M := M) g₀ 2 P b]
  rw [show ((∑ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.contract_covariant 0 2 b (smoothOrthoFrame (I := I) g₀ b i b)
        (tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) P b
          (smoothOrthoFrame (I := I) g₀ b i b)) : TensorRSSpace 0 2 I b)) D =
    ∑ i : Fin (Module.finrank ℝ E),
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
        Tensor0SBundle.contract_covariant 0 2 b (smoothOrthoFrame (I := I) g₀ b i b)
          (tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) P b
            (smoothOrthoFrame (I := I) g₀ b i b))) D from by
    exact ContinuousLinearMap.sum_apply _ _ _]
  rw [armResidual_toModel_sum (I := I) (M := M) b Finset.univ
    (fun i => (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
      Tensor0SBundle.contract_covariant 0 2 b (smoothOrthoFrame (I := I) g₀ b i b)
        (tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) P b
          (smoothOrthoFrame (I := I) g₀ b i b))) D)]
  rw [ContinuousMultilinearMap.sum_apply]
  rw [hP]
  rw [Finset.sum_congr rfl (fun i _ =>
    armResidual_contract_term_eq (I := I) (M := M) g₀ g₁ u₀ b D m i)]
  rw [Finset.sum_add_distrib]
  rw [armResidual_arm_toModel_eq (I := I) (M := M) g₀ g₁ u₀ b D m]
  rw [hGarm]
  rw [armResidual_gTerm_toModel_eq (I := I) (M := M) g₀ g₁ u₀ b D m]
  rw [armResidual_slot01_transpose (I := I) (M := M) g₀ g₁ b
    (Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
        (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
          (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toSection b) D)) m]
  exact add_comm _ _

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
