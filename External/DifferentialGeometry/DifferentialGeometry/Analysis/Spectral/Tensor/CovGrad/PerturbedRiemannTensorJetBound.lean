import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PerturbedCurvatureFrameComponentBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem exists_orthoFrame_basis_local (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
      (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x)),
      (∀ i : Fin (Module.finrank ℝ E), bse i = e i) ∧
      (∀ a b : Fin (Module.finrank ℝ E),
        g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) := by
  classical
  obtain ⟨n, e0, hn, horth0, _hpars, _hrepr⟩ :=
    exists_orthonormal_frame_riemannianFiberNormSq (I := I) (M := M) g 0 0 x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  subst hnE
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x := e0 with he_def
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := horth0
  haveI : Nonempty (Fin (Module.finrank ℝ (TangentSpace I x))) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hcard : Fintype.card (Fin (Module.finrank ℝ (TangentSpace I x))) =
      Module.finrank ℝ (TangentSpace I x) := Fintype.card_fin _
  refine ⟨e, basisOfLinearIndependentOfCardEqFinrank he_li hcard, fun i => ?_, horth⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem riemannianFiberNormSq_le_of_componentSq_sum_le
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (S : TensorRSSpace r s I x)
    (C : ℝ)
    (hKsum : ∀ (e : Fin (Module.finrank ℝ E) → TangentSpace I x),
      (∀ a b : Fin (Module.finrank ℝ E),
        g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) →
      ∀ (K : Fin r → Fin (Module.finrank ℝ E)),
        (∑ J : Fin s → Fin (Module.finrank ℝ E),
          (fiberNormSqComponent (I := I) (M := M) g₀ x r s S (Module.finrank ℝ E) e K J) ^ 2)
          ≤ C ^ 2) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x S
      ≤ ((Module.finrank ℝ E : ℝ) ^ r) * C ^ 2 := by
  classical
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis_local (I := I) (M := M) g₀ x
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ r s x S e bse rfl hbse horth]
  calc (∑ K : Fin r → Fin (Module.finrank ℝ E), ∑ J : Fin s → Fin (Module.finrank ℝ E),
          (fiberNormSqComponent (I := I) (M := M) g₀ x r s S (Module.finrank ℝ E) e K J) ^ 2)
      ≤ ∑ _K : Fin r → Fin (Module.finrank ℝ E), C ^ 2 :=
        Finset.sum_le_sum (fun K _ => hKsum e horth K)
    _ = ((Module.finrank ℝ E : ℝ) ^ r) * C ^ 2 := by
        rw [Finset.sum_const]
        simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_pow]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_riemannBiContrFib_perturbed_rfns_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ max δ₀ 0)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w +
            ccTensorBilinSymm (I := I) g₀ P x v w)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              (show TensorRSSpace 2 2 I x from
                TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) ≤ Λ := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_riemannBiContrFib_perturbed_frameComponent_sum_sq_le_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨((Module.finrank ℝ E : ℝ) ^ 2) * C ^ 2, by positivity, ?_⟩
  intro g₁ P δ hδ_le hδ htie x henv
  exact riemannianFiberNormSq_le_of_componentSq_sum_le (I := I) (M := M) g₀ 2 2 x
    (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) C
    (fun e horth K => hC g₁ P hδ_le hδ htie x henv e horth K)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_ricciArmOrder0CurvCoeffFib_perturbed_rfns_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ max δ₀ 0)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w +
            ccTensorBilinSymm (I := I) g₀ P x v w)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              (show TensorRSSpace 2 2 I x from
                TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x)) ≤ Λ := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_ricciArmOrder0CurvCoeffFib_perturbed_frameComponent_sum_sq_le_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨((Module.finrank ℝ E : ℝ) ^ 2) * C ^ 2, by positivity, ?_⟩
  intro g₁ P δ hδ_le hδ htie x henv
  exact riemannianFiberNormSq_le_of_componentSq_sum_le (I := I) (M := M) g₀ 2 2 x
    (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x)) C
    (fun e horth K => hC g₁ P hδ_le hδ htie x henv e horth K)

end Curvature
end Geometry
end DifferentialGeometry

end
