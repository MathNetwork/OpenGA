import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricDiffCovGradKoszul
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferenceKoszulSecondCovGrad
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferencePrincipalEndomorphismTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferenceSymmetrizedReindexedCoeff
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferenceReindexingArmSplitting


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
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

section NormedRiemannCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def riemannKernelBilin (g₁ : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => (g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q))
      map_add' := fun v0 v0' => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_add v0 v0',
          ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, map_add]
      map_smul' := fun c v0 => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_smul c v0,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul,
          RingHom.id_apply] }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem riemannKernelBilin_apply (g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    riemannKernelBilin (I := I) g₁ x p q v0 v1 =
      g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [riemannKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

def riemannSummandFib (g₁ : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (riemannKernelBilin (I := I) g₁ x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem riemannSummandFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannSummandFib (I := I) g₁ x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) p q) (v 1) := by
  rw [riemannSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, Tensor0SSpace.toModel_ofModel,
    bilinFormToModel_apply, smul_eq_mul]
  rfl

def riemannBiContrFibFixedFrame (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    riemannSummandFib (I := I) g₁ x (B a x) (B b x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem riemannBiContrFibFixedFrame_toModel (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannBiContrFibFixedFrame (I := I) g₁ B x D) v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) (B a x) (B b x)) (v 1) *
          Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)] := by
  classical
  rw [riemannBiContrFibFixedFrame, ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  apply congrArg (fun z : ℝ => 2 * z)
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, riemannSummandFib_toModel]
  ring

def innerPairBilin (x : M) (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X : TangentSpace I x) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => (K X Y) • (Dd X)
      map_add' := fun Y Y' => by rw [map_add, add_smul]
      map_smul' := fun c Y => by rw [map_smul, smul_eq_mul, RingHom.id_apply, mul_smul] }

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem innerPairBilin_apply (x : M) (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X Y Y' : TangentSpace I x) :
    innerPairBilin (I := I) x K Dd X Y Y' = K X Y * Dd X Y' := by
  rw [innerPairBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

def outerPairBilin (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (chartInvGramMatrix (I := I) g x x k l * K X (chartModelBasis E k)) •
          (ContinuousLinearMap.flip Dd (chartModelBasis E l))
      map_add' := fun X X' => by
        ext Y'
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_add, smul_eq_mul]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring
      map_smul' := fun c X => by
        ext Y'
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem outerPairBilin_apply (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (X X' : TangentSpace I x) :
    outerPairBilin (I := I) g x K Dd X X' =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          (K X (chartModelBasis E k) * Dd X' (chartModelBasis E l)) := by
  rw [outerPairBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.flip_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem double_frame_bilin_trace_eq_fixed
    (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1:ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g x x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g x x k l *
          (K (chartModelBasis E m) (chartModelBasis E k) *
            Dd (chartModelBasis E n) (chartModelBasis E l))) := by
  classical

  have hinner : ∀ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      outerPairBilin (I := I) g x K Dd (B a) (B a) := by
    intro a
    rw [outerPairBilin_apply]
    have h := orthonormal_basis_bilin_trace (I := I) (M := M) g (x := x)
      (innerPairBilin (I := I) x K Dd (B a)) B hB
    simp only [innerPairBilin_apply] at h
    rw [h]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]

  have hout := orthonormal_basis_bilin_trace (I := I) (M := M) g (x := x)
    (outerPairBilin (I := I) g x K Dd) B hB
  rw [hout]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [outerPairBilin_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem double_frame_bilin_trace_indep
    (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B C : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1:ℝ) else 0)
    (hC : ∀ i j, g.inner x (C i) (C j) = if i = j then (1:ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      ∑ a, ∑ b, K (C a) (C b) * Dd (C a) (C b) := by
  rw [double_frame_bilin_trace_eq_fixed (I := I) g x K Dd B hB,
    double_frame_bilin_trace_eq_fixed (I := I) g x K Dd C hC]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem contMDiff_bilinSection_of_chartScalar
    (Hb : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hscalar : ∀ (x₀ : M) (σ : Fin 2 → Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Hb x (chartFrameVec (I := I) x₀ (σ 0) x) (chartFrameVec (I := I) x₀ (σ 1) x))
        (chartAt H x₀).source) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (Tensor0SSpace.ofModel (I := I) (x := x)
          (bilinFormToModel (TangentSpace I x) (Hb x)))) := by
  classical
  let d := Module.finrank ℝ E
  let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b
    (fun x => Tensor0SSpace.ofModel (I := I) (x := x)
      (bilinFormToModel (TangentSpace I x) (Hb x)))).mpr fun σ x₀ => ?_
  have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => Hb x (chartFrameVec (I := I) x₀ (σ 0) x) (chartFrameVec (I := I) x₀ (σ 1) x))
      (chartAt H x₀).source := hscalar x₀ σ
  have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have h_src_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
    (chartAt H x₀).open_source.mem_nhds hx₀_src
  refine ((hcomp x₀ hx₀_src).contMDiffAt h_src_nhd).congr_of_eventuallyEq ?_
  have h_base_nhd : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
  filter_upwards [h_base_nhd] with x hx
  rw [continuousMultilinearMap_basis_repr]
  change Tensor0SSpace.toModel
      (Tensor0SSpace.ofModel (I := I) (x := x) (bilinFormToModel (TangentSpace I x) (Hb x)))
      (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
  rw [Tensor0SSpace.toModel_ofModel]
  exact bilinFormToModel_apply (TangentSpace I x) (Hb x)
    (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j)))

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem kernelScalar_global (g₁ : SmoothRiemannianMetric I M)
    {Y W p q : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) := by
  classical
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => riemannSec (LeviCivita (I := I) g₁) Y p q b)) :=
    riemannSec_contMDiff (cov := LeviCivita (I := I) g₁) hY hp hq
  have hcongr : (fun x : M => g₁.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) =
      (fun x : M => g₁.inner x (riemannSec (LeviCivita (I := I) g₁) Y p q x) (W x)) := by
    funext x
    rw [riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁) hY hp hq]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₁
    ⟨fun b => riemannSec (LeviCivita (I := I) g₁) Y p q b, hRsec⟩ ⟨fun b => W b, hW⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannKernelBilin_homSection_contMDiff (g₁ : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (riemannKernelBilin (I := I) g₁ x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => riemannKernelBilin (I := I) g₁ x (p x) (q x))
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => riemannKernelBilin (I := I) g₁ x (p x) (q x) (Y x))
  intro W
  have h_scalar := kernelScalar_global (I := I) g₁ Y.contMDiff W.contMDiff hp hq
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change riemannKernelBilin (I := I) g₁ y (p y) (q y) (Y y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [riemannKernelBilin_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem contMDiff_bilinSection_of_homSection
    (Hb : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hHb : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x (Hb x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (Tensor0SSpace.ofModel (I := I) (x := x)
          (bilinFormToModel (TangentSpace I x) (Hb x)))) := by
  classical
  refine contMDiff_bilinSection_of_chartScalar (I := I) Hb (fun x₀ σ => ?_)
  have hcf_0 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => chartFrameVec (I := I) x₀ (σ 0) b))
      (trivializationAt E (TangentSpace I) x₀).baseSet := fun x hx =>
    chartBasisVec_contMDiffOn (I := I) x₀ (σ 0) x hx
  have hcf_1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => chartFrameVec (I := I) x₀ (σ 1) b))
      (trivializationAt E (TangentSpace I) x₀).baseSet := fun x hx =>
    chartBasisVec_contMDiffOn (I := I) x₀ (σ 1) x hx
  have happ1 := ContMDiffOn.clm_bundle_apply (F₁ := E) (F₂ := E →L[ℝ] ℝ)
    (E₁ := fun z : M => TangentSpace I z) (E₂ := fun z : M => TangentSpace I z →L[ℝ] ℝ)
    (b := id) hHb.contMDiffOn hcf_0
  have happ := ContMDiffOn.clm_bundle_apply (F₁ := E) (F₂ := ℝ)
    (E₁ := fun z : M => TangentSpace I z) (E₂ := fun _ : M => ℝ)
    (b := id) happ1 hcf_1
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannBiContrFibFixedFrame_apply_section_contMDiff (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (riemannBiContrFibFixedFrame (I := I) g₁ B x (Y x))) := by
  classical

  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (riemannSummandFib (I := I) g₁ x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => riemannKernelBilin (I := I) g₁ x (B a x) (B b x))
      (riemannKernelBilin_homSection_contMDiff (I := I) g₁ (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (bilinFormToModel (TangentSpace I x) (riemannKernelBilin (I := I) g₁ x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl

  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => riemannSummandFib (I := I) g₁ x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [riemannBiContrFibFixedFrame, hStot_def, ContMDiffSection.coe_smul, Pi.smul_apply]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannBiContrFibFixedFrame_contMDiff (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannBiContrFibFixedFrame (I := I) g₁ B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => riemannBiContrFibFixedFrame (I := I) g₁ B x)
  intro Y
  exact riemannBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₁ B hB Y

def frameRiemannKernel (g₁ : SmoothRiemannianMetric I M) (x : M) (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (g₁.inner x).flip v1 |>.comp
        ((riemannOp (LeviCivita (I := I) g₁) x v0 p))
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (riemannOp (LeviCivita (I := I) g₁) x v0).map_add p p', map_add]
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (riemannOp (LeviCivita (I := I) g₁) x v0).map_smul c p, map_smul] }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem frameRiemannKernel_apply (g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameRiemannKernel (I := I) g₁ x v0 v1 p q =
      g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [frameRiemannKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

def riemannBiContrFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  riemannBiContrFibFixedFrame (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x) x

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem riemannBiContrFibFixedFrame_eq_of_orthonormal
    (g₁ : SmoothRiemannianMetric I M) (y : M)
    (B C : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i j, g₁.inner y (B i y) (B j y) = if i = j then (1 : ℝ) else 0)
    (hC : ∀ i j, g₁.inner y (C i y) (C j y) = if i = j then (1 : ℝ) else 0) :
    riemannBiContrFibFixedFrame (I := I) g₁ B y =
      riemannBiContrFibFixedFrame (I := I) g₁ C y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [riemannBiContrFibFixedFrame_toModel, riemannBiContrFibFixedFrame_toModel]
  apply congrArg (fun z : ℝ => 2 * z)
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner y (riemannOp (LeviCivita (I := I) g₁) y (v 0) (Bf a) (Bf b)) (v 1) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameRiemannKernel (I := I) g₁ y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameRiemannKernel_apply (I := I) g₁ y (v 0) (v 1) (Bf a) (Bf b),
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => B a y), hrewrite (fun a => C a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameRiemannKernel (I := I) g₁ y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => B a y) (fun a => C a y) hB hC

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem riemannBiContrFib_eq_fixedFrame_on_nbhd (g₁ : SmoothRiemannianMetric I M) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    riemannBiContrFib (I := I) g₁ y =
      riemannBiContrFibFixedFrame (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x₀) y := by
  rw [riemannBiContrFib]
  exact riemannBiContrFibFixedFrame_eq_of_orthonormal (I := I) g₁ y
    (smoothOrthoFrame (I := I) g₁ y) (smoothOrthoFrame (I := I) g₁ x₀)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

omit [CompactSpace M] [I.Boundaryless] in
theorem riemannBiContrFib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannBiContrFibFixedFrame (I := I) g₁
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    riemannBiContrFibFixedFrame_contMDiff (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (riemannBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₁ x₀ hy))

def ricciArmOrder0RiemannCoeffField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))
      contMDiff_toFun := riemannBiContrFib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
@[simp] theorem ricciArmOrder0RiemannCoeffField_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) :
    (ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) :=
  rfl

omit [I.Boundaryless] in
theorem exists_ricciArmOrder0RiemannCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∃ R_Rm : SmoothCcTensor g₀ 2 2,
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
        unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 R_Rm W) x v =
          2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            g₁.inner x
                (riemannOp (LeviCivita (I := I) g₁) x (v 0)
                  (smoothOrthoFrame (I := I) g₁ x a x)
                  (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) *
              unitModel (I := I) (M := M) g₀ 2 W x
                (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                  else smoothOrthoFrame (I := I) g₁ x b x) :=
  by
  classical
  refine ⟨ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁, fun W x v => ?_⟩
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0RiemannCoeffField_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      riemannBiContrFib (I := I) g₁ x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [riemannBiContrFib, riemannBiContrFibFixedFrame_toModel]
  refine congrArg (fun t => (2 : ℝ) * t) ?_
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp

noncomputable def ricciArmOrder0RiemannCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁

omit [I.Boundaryless] in
@[simp] theorem ricciArmOrder0RiemannCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) :=
  rfl


omit [I.Boundaryless] in
theorem ricciArmOrder0RiemannCoeff_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2 (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁) W) x v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x
            (riemannOp (LeviCivita (I := I) g₁) x (v 0)
              (smoothOrthoFrame (I := I) g₁ x a x)
              (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) *
          unitModel (I := I) (M := M) g₀ 2 W x
            (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
              else smoothOrthoFrame (I := I) g₁ x b x) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0RiemannCoeff_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      riemannBiContrFib (I := I) g₁ x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [riemannBiContrFib, riemannBiContrFibFixedFrame_toModel]
  refine congrArg (fun t => (2 : ℝ) * t) ?_
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp

end NormedRiemannCoefficients

section InnerProductSpaceSymmetrization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def symmAbsorbedPrincipalCoeffPure (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 4 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 2
    (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 2))


omit [NeZero (Module.finrank ℝ E)] in
theorem symmAbsorbedPrincipalCoeffPure_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2 (symmAbsorbedPrincipalCoeffPure (I := I) (M := M) g₀ g₁ S)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 2 S
    (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 2))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 2)) x v

noncomputable def symmAbsorbedOrder0CurvCoeff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 0
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))


omit [NeZero (Module.finrank ℝ E)] in
theorem symmAbsorbedOrder0CurvCoeff_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2 (symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀ g₁ S)
          (iteratedCovGrad (I := I) g₀ 0 2 0 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2 (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 S
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0)) x v

noncomputable def symmAbsorbedOrder0RiemannCoeff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 0
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))


theorem symmAbsorbedOrder0RiemannCoeff_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2 (symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ S)
          (iteratedCovGrad (I := I) g₀ 0 2 0 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2 (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 S
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0)) x v

end InnerProductSpaceSymmetrization

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
