import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CorrFieldChristoffelCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovDerivConnDiffQuadraticBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseMetricPerturbationFibreBound
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Geometry.Metric.MetricBounds
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffUniformBoundsSlotPermutations


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators Matrix Interval

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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section UniformBound


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma flat_toModel_apply (g₀ : SmoothRiemannianMetric I M) (x : M)
    (uu : TangentSpace I x) (v : Fin 1 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x uu) v =
      g₀.inner x uu ((v 0 : E) : TangentSpace I x) := by
  have h1 : Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x uu) v =
      (g0FlatCLM (I := I) g₀ x uu) (fun j : Fin 1 => ((v j : E) : TangentSpace I x)) := rfl
  rw [h1]
  have h2 : (fun j : Fin 1 => ((v j : E) : TangentSpace I x)) =
      (fun _ : Fin 1 => ((v 0 : E) : TangentSpace I x)) := by
    funext j
    fin_cases j
    rfl
  rw [h2]
  rw [show (g0FlatCLM (I := I) g₀ x uu) (fun _ : Fin 1 => ((v 0 : E) : TangentSpace I x)) =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x uu) ((v 0 : E) : TangentSpace I x)
    from (cotangentToDual_apply (I := I) (x := x) _ _).symm]
  rw [cotangentToDual_g0FlatCLM]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma dualPair_sum_swap (g₀ : SmoothRiemannianMetric I M) (x : M)
    (F : Tensor0SBundle.Tensor0SModel 1 ℝ E → E → ℝ)
    (hFβ : ∀ z : E, IsLinearMap ℝ (fun β => F β z))
    (hFz : ∀ β, IsLinearMap ℝ (fun z : E => F β z))
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (_horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (hrepr : ∀ v : TangentSpace I x, v = ∑ a : Fin n, g₀.inner x (e a) v • e a) :
    (∑ i : Fin (Module.finrank ℝ E),
        F (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i)) ((Module.finBasis ℝ E) i)) =
      ∑ a : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E)) := by
  classical
  have hcdual : ∀ i : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).cDualBasis i) =
        LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i) := by
    intro i
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    congr 1
    exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) i
  have hexp : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis i) =
        ∑ a : Fin n, ((Module.finBasis ℝ E).coord i ((e a : E))) •
          Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a)) := by
    intro i
    apply ContinuousMultilinearMap.ext
    intro v
    rw [Tensor0SBundle.model_covectorOfCLM_apply, hcdual i]
    have hRHS : (∑ a : Fin n, ((Module.finBasis ℝ E).coord i ((e a : E))) •
          Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) v =
        ∑ a : Fin n, ((Module.finBasis ℝ E).coord i ((e a : E))) *
          g₀.inner x (e a) ((v 0 : E) : TangentSpace I x) := by
      rw [ContinuousMultilinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [ContinuousMultilinearMap.smul_apply, flat_toModel_apply, smul_eq_mul]
    rw [hRHS]
    have hv0 : ((v 0 : E) : TangentSpace I x) =
        ∑ a : Fin n, g₀.inner x (e a) ((v 0 : E) : TangentSpace I x) • e a :=
      hrepr ((v 0 : E) : TangentSpace I x)
    calc LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i) (v 0)
        = (Module.finBasis ℝ E).coord i (v 0) := rfl
      _ = (Module.finBasis ℝ E).coord i
            (∑ a : Fin n, g₀.inner x (e a) ((v 0 : E) : TangentSpace I x) • ((e a : E))) := by
          exact congrArg ((Module.finBasis ℝ E).coord i) hv0
      _ = ∑ a : Fin n, g₀.inner x (e a) ((v 0 : E) : TangentSpace I x) *
            (Module.finBasis ℝ E).coord i ((e a : E)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [map_smul, smul_eq_mul]
      _ = ∑ a : Fin n, (Module.finBasis ℝ E).coord i ((e a : E)) *
            g₀.inner x (e a) ((v 0 : E) : TangentSpace I x) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          ring
  calc (∑ i : Fin (Module.finrank ℝ E),
        F (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i)) ((Module.finBasis ℝ E) i))
      = ∑ i : Fin (Module.finrank ℝ E), ∑ a : Fin n,
          ((Module.finBasis ℝ E).coord i ((e a : E))) *
            F (Tensor0SBundle.Tensor0SSpace.toModel
                (g0FlatCLM (I := I) g₀ x (e a))) ((Module.finBasis ℝ E) i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hexp i]
        set ℓ := IsLinearMap.mk' (fun β => F β ((Module.finBasis ℝ E) i))
          (hFβ ((Module.finBasis ℝ E) i)) with hℓ
        have hFℓ : ∀ β, F β ((Module.finBasis ℝ E) i) = ℓ β := fun β => rfl
        rw [hFℓ, map_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [map_smul, smul_eq_mul, ← hFℓ]
    _ = ∑ a : Fin n, ∑ i : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).coord i ((e a : E))) *
            F (Tensor0SBundle.Tensor0SSpace.toModel
                (g0FlatCLM (I := I) g₀ x (e a))) ((Module.finBasis ℝ E) i) :=
        Finset.sum_comm
    _ = ∑ a : Fin n,
          F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E)) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        set ℓ := IsLinearMap.mk'
          (fun z : E => F (Tensor0SBundle.Tensor0SSpace.toModel
            (g0FlatCLM (I := I) g₀ x (e a))) z)
          (hFz (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a)))) with hℓ
        have hFℓ : ∀ z, F (Tensor0SBundle.Tensor0SSpace.toModel
            (g0FlatCLM (I := I) g₀ x (e a))) z = ℓ z := fun z => rfl
        calc (∑ i : Fin (Module.finrank ℝ E),
              ((Module.finBasis ℝ E).coord i ((e a : E))) *
                F (Tensor0SBundle.Tensor0SSpace.toModel
                    (g0FlatCLM (I := I) g₀ x (e a))) ((Module.finBasis ℝ E) i))
            = ∑ i : Fin (Module.finrank ℝ E),
                ℓ (((Module.finBasis ℝ E).coord i ((e a : E))) • (Module.finBasis ℝ E) i) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [map_smul, smul_eq_mul, ← hFℓ]
          _ = ℓ (∑ i : Fin (Module.finrank ℝ E),
                ((Module.finBasis ℝ E).coord i ((e a : E))) • (Module.finBasis ℝ E) i) :=
              (map_sum ℓ _ _).symm
          _ = F (Tensor0SBundle.Tensor0SSpace.toModel
                (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E)) := by
              rw [← hFℓ]
              congr 1
              have hbe := (Module.finBasis ℝ E).sum_repr ((e a : E))
              calc (∑ i : Fin (Module.finrank ℝ E),
                    ((Module.finBasis ℝ E).coord i ((e a : E))) • (Module.finBasis ℝ E) i)
                  = ∑ i : Fin (Module.finrank ℝ E),
                      ((Module.finBasis ℝ E).repr ((e a : E)) i) • (Module.finBasis ℝ E) i := by
                    refine Finset.sum_congr rfl (fun i _ => ?_)
                    rw [Module.Basis.coord_apply]
                _ = (e a : E) := hbe

def fibPointwiseBound (g₀ : SmoothRiemannianMetric I M) (x : M) (d : ℕ) (c : ℝ)
    (Z : Tensor0SBundle.Tensor0SSpace d I x) : Prop :=
  0 ≤ c ∧ ∀ w : Fin d → TangentSpace I x,
    |Tensor0SBundle.Tensor0SSpace.toModel Z (fun j => (w j : E))| ≤
      c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j))


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] in
lemma fibPointwiseBound_coframe (g₀ : SmoothRiemannianMetric I M) (x : M) (d : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin d → Fin n) :
    fibPointwiseBound (I := I) g₀ x d 1 (coframeS (I := I) (M := M) g₀ x d e K) := by
  refine ⟨zero_le_one, ?_⟩
  intro w
  have hval : Tensor0SBundle.Tensor0SSpace.toModel
      (coframeS (I := I) (M := M) g₀ x d e K) (fun j => (w j : E)) =
      coframeS (I := I) (M := M) g₀ x d e K (fun j => w j) := rfl
  rw [hval, coframeS_apply, one_mul, Finset.abs_prod]
  refine Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => ?_)
  have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e (K j)) (w j)
  have h1 : g₀.inner x (e (K j)) (e (K j)) = 1 := by rw [horth (K j) (K j)]; simp
  rw [h1, Real.sqrt_one, one_mul] at hcs
  exact hcs


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fibPointwiseBound_slotPerm (g₀ : SmoothRiemannianMetric I M) (x : M) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) {c : ℝ} {Z : Tensor0SBundle.Tensor0SSpace d I x}
    (hZ : fibPointwiseBound (I := I) g₀ x d c Z) :
    fibPointwiseBound (I := I) g₀ x d c (slotPermCLM (I := I) ρ x Z) := by
  refine ⟨hZ.1, ?_⟩
  intro w
  have hsp : Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) ρ x Z)
      (fun j => (w j : E)) =
      (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Z))
        (fun j => (w j : E)) := by
    rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [hsp, ContinuousMultilinearMap.domDomCongr_apply]
  have hb := hZ.2 (fun j => w (ρ j))
  refine le_trans hb (le_of_eq ?_)
  congr 1
  exact Equiv.prod_comp ρ (fun j => Real.sqrt (g₀.inner x (w j) (w j)))


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fibPointwiseBound_prod_nonneg (g₀ : SmoothRiemannianMetric I M) (x : M) {d : ℕ}
    (w : Fin d → TangentSpace I x) :
    0 ≤ ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) :=
  Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
lemma connDiff_flat_factor_bound (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    {CA : ℝ}
    (hpwA : ∀ v w : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w)) ≤
        CA * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w))
    (a : Fin n) (v : Fin 2 → TangentSpace I x) :
    |(Tensor0SBundle.TensorRSSpace.toModel (connDiffFib (I := I) g₁ g₀ x)
        (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
        (fun j => (v j : E))| ≤
      CA * (Real.sqrt (g₀.inner x (v 0) (v 0)) * Real.sqrt (g₀.inner x (v 1) (v 1))) := by
  have h1 : Tensor0SBundle.TensorRSSpace.toModel (connDiffFib (I := I) g₁ g₀ x)
      (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          connDiffFib (I := I) g₁ g₀ x) (g0FlatCLM (I := I) g₀ x (e a))) :=
    (toModel_tensorRS_apply (I := I) 1 2 x (connDiffFib (I := I) g₁ g₀ x)
      (g0FlatCLM (I := I) g₀ x (e a))).symm
  rw [h1]
  have h2 : Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) (g0FlatCLM (I := I) g₀ x (e a)))
      (fun j => (v j : E)) =
      ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) (g0FlatCLM (I := I) g₀ x (e a))) (fun j => v j) := rfl
  rw [h2, connDiffFib_apply_eval]
  rw [show (g0FlatCLM (I := I) g₀ x (e a))
      (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) (v 1)) =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x (e a))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) (v 1)) from
    (cotangentToDual_apply (I := I) (x := x) _ _).symm]
  rw [cotangentToDual_g0FlatCLM]
  have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e a)
    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) (v 1))
  have h1a : g₀.inner x (e a) (e a) = 1 := by rw [horth a a]; simp
  rw [h1a, Real.sqrt_one, one_mul] at hcs
  refine le_trans hcs (le_trans (hpwA (v 0) (v 1)) (le_of_eq ?_))
  ring


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fibPointwiseBound_connContr21 (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (hrepr : ∀ v : TangentSpace I x, v = ∑ a : Fin n, g₀.inner x (e a) v • e a)
    (B : Tensor0SBundle.TensorRSSpace 1 2 I x) {CB : ℝ} (hCB : 0 ≤ CB)
    (hB : ∀ (a : Fin n) (v : Fin 2 → TangentSpace I x),
      |(Tensor0SBundle.TensorRSSpace.toModel B
          (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
          (fun j => (v j : E))| ≤
        CB * (Real.sqrt (g₀.inner x (v 0) (v 0)) * Real.sqrt (g₀.inner x (v 1) (v 1))))
    {c : ℝ} {D : Tensor0SBundle.Tensor0SSpace 3 I x}
    (hD : fibPointwiseBound (I := I) g₀ x 3 c D) :
    fibPointwiseBound (I := I) g₀ x 4 ((n : ℝ) * CB * c) (connContrCLM (I := I) 2 1 x B D) := by
  refine ⟨mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hCB) hD.1, ?_⟩
  intro w
  rw [connContrCLM_toModel_apply (I := I) 2 1 x B D (fun j => (w j : E))]
  have hfirst : ∀ z : E,
      (Fin.cons z (fun j => (w j : E)) ∘ Fin.castAdd 2 : Fin 3 → E) =
        ![z, (w 0 : E), (w 1 : E)] := by
    intro z
    funext j
    fin_cases j <;> rfl
  have hlast : ∀ z : E,
      (Fin.cons z (fun j => (w j : E)) ∘ Fin.natAdd 3 : Fin 2 → E) =
        ![(w 2 : E), (w 3 : E)] := by
    intro z
    funext j
    fin_cases j <;> rfl
  simp only [hfirst, hlast]
  set F : Tensor0SBundle.Tensor0SModel 1 ℝ E → E → ℝ := fun β z =>
    Tensor0SBundle.Tensor0SSpace.toModel D ![z, (w 0 : E), (w 1 : E)] *
      (Tensor0SBundle.TensorRSSpace.toModel B β) ![(w 2 : E), (w 3 : E)] with hF
  have hFβ : ∀ z : E, IsLinearMap ℝ (fun β => F β z) := by
    intro z
    constructor
    · intro β₁ β₂
      rw [hF]
      simp only [map_add, ContinuousMultilinearMap.add_apply, mul_add]
    · intro cc β
      rw [hF]
      simp only [map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring
  have hFz : ∀ β, IsLinearMap ℝ (fun z : E => F β z) := by
    intro β
    constructor
    · intro z₁ z₂
      rw [hF]
      simp only
      rw [show (![z₁ + z₂, (w 0 : E), (w 1 : E)] : Fin 3 → E) =
          Fin.cons (z₁ + z₂) ![(w 0 : E), (w 1 : E)] from rfl]
      rw [show (![z₁, (w 0 : E), (w 1 : E)] : Fin 3 → E) =
          Fin.cons z₁ ![(w 0 : E), (w 1 : E)] from rfl]
      rw [show (![z₂, (w 0 : E), (w 1 : E)] : Fin 3 → E) =
          Fin.cons z₂ ![(w 0 : E), (w 1 : E)] from rfl]
      rw [show Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons (z₁ + z₂) ![(w 0 : E), (w 1 : E)]) =
          Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z₁ ![(w 0 : E), (w 1 : E)]) +
            Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z₂ ![(w 0 : E), (w 1 : E)]) from
        (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.cons_add _ z₁ z₂]
      ring
    · intro cc z
      rw [hF]
      simp only
      rw [show (![cc • z, (w 0 : E), (w 1 : E)] : Fin 3 → E) =
          Fin.cons (cc • z) ![(w 0 : E), (w 1 : E)] from rfl]
      rw [show (![z, (w 0 : E), (w 1 : E)] : Fin 3 → E) =
          Fin.cons z ![(w 0 : E), (w 1 : E)] from rfl]
      rw [show Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons (cc • z) ![(w 0 : E), (w 1 : E)]) =
          cc • Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z ![(w 0 : E), (w 1 : E)]) from
        (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.cons_smul _ cc z]
      rw [smul_eq_mul, smul_eq_mul]
      ring
  rw [show (∑ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel D ![((Module.finBasis ℝ E) i), (w 0 : E), (w 1 : E)] *
        (Tensor0SBundle.TensorRSSpace.toModel B
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis i)))
          ![(w 2 : E), (w 3 : E)]) =
      ∑ a : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E)) from
    dualPair_sum_swap (I := I) g₀ x F hFβ hFz e horth hrepr]
  have hterm : ∀ a : Fin n,
      |F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))| ≤
        CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
    intro a
    rw [hF]
    simp only
    rw [abs_mul]
    have hDterm : |Tensor0SBundle.Tensor0SSpace.toModel D ![((e a : E)), (w 0 : E), (w 1 : E)]| ≤
        c * (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))) := by
      have harg : (![((e a : E)), (w 0 : E), (w 1 : E)] : Fin 3 → E) =
          (fun j => ((![e a, w 0, w 1] : Fin 3 → TangentSpace I x) j : E)) := by
        funext j
        fin_cases j <;> rfl
      rw [harg]
      have hb := hD.2 ![e a, w 0, w 1]
      have hprod : (∏ j, Real.sqrt (g₀.inner x ((![e a, w 0, w 1] : Fin 3 → TangentSpace I x) j)
          ((![e a, w 0, w 1] : Fin 3 → TangentSpace I x) j))) =
          Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1)) := by
        rw [Fin.prod_univ_three]
        have h1a : g₀.inner x (e a) (e a) = 1 := by rw [horth a a]; simp
        rw [show ((![e a, w 0, w 1] : Fin 3 → TangentSpace I x) 0) = e a from rfl,
          show ((![e a, w 0, w 1] : Fin 3 → TangentSpace I x) 1) = w 0 from rfl,
          show ((![e a, w 0, w 1] : Fin 3 → TangentSpace I x) 2) = w 1 from rfl,
          h1a, Real.sqrt_one, one_mul]
      rw [hprod] at hb
      exact hb
    have hBterm : |(Tensor0SBundle.TensorRSSpace.toModel B
        (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
        ![(w 2 : E), (w 3 : E)]| ≤
        CB * (Real.sqrt (g₀.inner x (w 2) (w 2)) * Real.sqrt (g₀.inner x (w 3) (w 3))) := by
      have harg : (![(w 2 : E), (w 3 : E)] : Fin 2 → E) =
          (fun j => ((![w 2, w 3] : Fin 2 → TangentSpace I x) j : E)) := by
        funext j
        fin_cases j <;> rfl
      rw [harg]
      exact hB a ![w 2, w 3]
    calc |Tensor0SBundle.Tensor0SSpace.toModel D ![((e a : E)), (w 0 : E), (w 1 : E)]| *
          |(Tensor0SBundle.TensorRSSpace.toModel B
              (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
              ![(w 2 : E), (w 3 : E)]|
        ≤ (c * (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1)))) *
            (CB * (Real.sqrt (g₀.inner x (w 2) (w 2)) * Real.sqrt (g₀.inner x (w 3) (w 3)))) :=
          mul_le_mul hDterm hBterm (abs_nonneg _)
            (mul_nonneg hD.1 (by positivity))
      _ = CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
          rw [Fin.prod_univ_four]
          ring
  calc |∑ a : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))|
      ≤ ∑ a : Fin n,
          |F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin n, CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) :=
        Finset.sum_le_sum (fun a _ => hterm a)
    _ = (n : ℝ) * CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fibPointwiseBound_connContr11 (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (hrepr : ∀ v : TangentSpace I x, v = ∑ a : Fin n, g₀.inner x (e a) v • e a)
    (B : Tensor0SBundle.TensorRSSpace 1 2 I x) {CB : ℝ} (hCB : 0 ≤ CB)
    (hB : ∀ (a : Fin n) (v : Fin 2 → TangentSpace I x),
      |(Tensor0SBundle.TensorRSSpace.toModel B
          (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
          (fun j => (v j : E))| ≤
        CB * (Real.sqrt (g₀.inner x (v 0) (v 0)) * Real.sqrt (g₀.inner x (v 1) (v 1))))
    {c : ℝ} {D : Tensor0SBundle.Tensor0SSpace 2 I x}
    (hD : fibPointwiseBound (I := I) g₀ x 2 c D) :
    fibPointwiseBound (I := I) g₀ x 3 ((n : ℝ) * CB * c) (connContrCLM (I := I) 1 1 x B D) := by
  refine ⟨mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hCB) hD.1, ?_⟩
  intro w
  rw [connContrCLM_toModel_apply (I := I) 1 1 x B D (fun j => (w j : E))]
  have hfirst : ∀ z : E,
      (Fin.cons z (fun j => (w j : E)) ∘ Fin.castAdd 2 : Fin 2 → E) = ![z, (w 0 : E)] := by
    intro z
    funext j
    fin_cases j <;> rfl
  have hlast : ∀ z : E,
      (Fin.cons z (fun j => (w j : E)) ∘ Fin.natAdd 2 : Fin 2 → E) =
        ![(w 1 : E), (w 2 : E)] := by
    intro z
    funext j
    fin_cases j <;> rfl
  simp only [hfirst, hlast]
  set F : Tensor0SBundle.Tensor0SModel 1 ℝ E → E → ℝ := fun β z =>
    Tensor0SBundle.Tensor0SSpace.toModel D ![z, (w 0 : E)] *
      (Tensor0SBundle.TensorRSSpace.toModel B β) ![(w 1 : E), (w 2 : E)] with hF
  have hFβ : ∀ z : E, IsLinearMap ℝ (fun β => F β z) := by
    intro z
    constructor
    · intro β₁ β₂
      rw [hF]
      simp only [map_add, ContinuousMultilinearMap.add_apply, mul_add]
    · intro cc β
      rw [hF]
      simp only [map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring
  have hFz : ∀ β, IsLinearMap ℝ (fun z : E => F β z) := by
    intro β
    constructor
    · intro z₁ z₂
      rw [hF]
      simp only
      rw [show (![z₁ + z₂, (w 0 : E)] : Fin 2 → E) = Fin.cons (z₁ + z₂) ![(w 0 : E)] from rfl,
        show (![z₁, (w 0 : E)] : Fin 2 → E) = Fin.cons z₁ ![(w 0 : E)] from rfl,
        show (![z₂, (w 0 : E)] : Fin 2 → E) = Fin.cons z₂ ![(w 0 : E)] from rfl]
      rw [show Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons (z₁ + z₂) ![(w 0 : E)]) =
          Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z₁ ![(w 0 : E)]) +
            Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z₂ ![(w 0 : E)]) from
        (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.cons_add _ z₁ z₂]
      ring
    · intro cc z
      rw [hF]
      simp only
      rw [show (![cc • z, (w 0 : E)] : Fin 2 → E) = Fin.cons (cc • z) ![(w 0 : E)] from rfl,
        show (![z, (w 0 : E)] : Fin 2 → E) = Fin.cons z ![(w 0 : E)] from rfl]
      rw [show Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons (cc • z) ![(w 0 : E)]) =
          cc • Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z ![(w 0 : E)]) from
        (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.cons_smul _ cc z]
      rw [smul_eq_mul, smul_eq_mul]
      ring
  rw [show (∑ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel D ![((Module.finBasis ℝ E) i), (w 0 : E)] *
        (Tensor0SBundle.TensorRSSpace.toModel B
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis i)))
          ![(w 1 : E), (w 2 : E)]) =
      ∑ a : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E)) from
    dualPair_sum_swap (I := I) g₀ x F hFβ hFz e horth hrepr]
  have hterm : ∀ a : Fin n,
      |F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))| ≤
        CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
    intro a
    rw [hF]
    simp only
    rw [abs_mul]
    have hDterm : |Tensor0SBundle.Tensor0SSpace.toModel D ![((e a : E)), (w 0 : E)]| ≤
        c * Real.sqrt (g₀.inner x (w 0) (w 0)) := by
      have harg : (![((e a : E)), (w 0 : E)] : Fin 2 → E) =
          (fun j => ((![e a, w 0] : Fin 2 → TangentSpace I x) j : E)) := by
        funext j
        fin_cases j <;> rfl
      rw [harg]
      have hb := hD.2 ![e a, w 0]
      have hprod : (∏ j, Real.sqrt (g₀.inner x ((![e a, w 0] : Fin 2 → TangentSpace I x) j)
          ((![e a, w 0] : Fin 2 → TangentSpace I x) j))) =
          Real.sqrt (g₀.inner x (w 0) (w 0)) := by
        rw [Fin.prod_univ_two]
        have h1a : g₀.inner x (e a) (e a) = 1 := by rw [horth a a]; simp
        rw [show ((![e a, w 0] : Fin 2 → TangentSpace I x) 0) = e a from rfl,
          show ((![e a, w 0] : Fin 2 → TangentSpace I x) 1) = w 0 from rfl,
          h1a, Real.sqrt_one, one_mul]
      rw [hprod] at hb
      exact hb
    have hBterm : |(Tensor0SBundle.TensorRSSpace.toModel B
        (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
        ![(w 1 : E), (w 2 : E)]| ≤
        CB * (Real.sqrt (g₀.inner x (w 1) (w 1)) * Real.sqrt (g₀.inner x (w 2) (w 2))) := by
      have harg : (![(w 1 : E), (w 2 : E)] : Fin 2 → E) =
          (fun j => ((![w 1, w 2] : Fin 2 → TangentSpace I x) j : E)) := by
        funext j
        fin_cases j <;> rfl
      rw [harg]
      exact hB a ![w 1, w 2]
    calc |Tensor0SBundle.Tensor0SSpace.toModel D ![((e a : E)), (w 0 : E)]| *
          |(Tensor0SBundle.TensorRSSpace.toModel B
              (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
              ![(w 1 : E), (w 2 : E)]|
        ≤ (c * Real.sqrt (g₀.inner x (w 0) (w 0))) *
            (CB * (Real.sqrt (g₀.inner x (w 1) (w 1)) * Real.sqrt (g₀.inner x (w 2) (w 2)))) :=
          mul_le_mul hDterm hBterm (abs_nonneg _)
            (mul_nonneg hD.1 (by positivity))
      _ = CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
          rw [Fin.prod_univ_three]
          ring
  calc |∑ a : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))|
      ≤ ∑ a : Fin n,
          |F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin n, CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) :=
        Finset.sum_le_sum (fun a _ => hterm a)
    _ = (n : ℝ) * CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fibPointwiseBound_connContr12 (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (hrepr : ∀ v : TangentSpace I x, v = ∑ a : Fin n, g₀.inner x (e a) v • e a)
    (B : Tensor0SBundle.TensorRSSpace 1 3 I x) {CB : ℝ} (hCB : 0 ≤ CB)
    (hB : ∀ (a : Fin n) (v : Fin 3 → TangentSpace I x),
      |(Tensor0SBundle.TensorRSSpace.toModel B
          (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
          (fun j => (v j : E))| ≤
        CB * (Real.sqrt (g₀.inner x (v 0) (v 0)) * Real.sqrt (g₀.inner x (v 1) (v 1)) *
          Real.sqrt (g₀.inner x (v 2) (v 2))))
    {c : ℝ} {D : Tensor0SBundle.Tensor0SSpace 2 I x}
    (hD : fibPointwiseBound (I := I) g₀ x 2 c D) :
    fibPointwiseBound (I := I) g₀ x 4 ((n : ℝ) * CB * c) (connContrCLM (I := I) 1 2 x B D) := by
  refine ⟨mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hCB) hD.1, ?_⟩
  intro w
  rw [connContrCLM_toModel_apply (I := I) 1 2 x B D (fun j => (w j : E))]
  have hfirst : ∀ z : E,
      (Fin.cons z (fun j => (w j : E)) ∘ Fin.castAdd 3 : Fin 2 → E) = ![z, (w 0 : E)] := by
    intro z
    funext j
    fin_cases j <;> rfl
  have hlast : ∀ z : E,
      (Fin.cons z (fun j => (w j : E)) ∘ Fin.natAdd 2 : Fin 3 → E) =
        ![(w 1 : E), (w 2 : E), (w 3 : E)] := by
    intro z
    funext j
    fin_cases j <;> rfl
  simp only [hfirst, hlast]
  set F : Tensor0SBundle.Tensor0SModel 1 ℝ E → E → ℝ := fun β z =>
    Tensor0SBundle.Tensor0SSpace.toModel D ![z, (w 0 : E)] *
      (Tensor0SBundle.TensorRSSpace.toModel B β) ![(w 1 : E), (w 2 : E), (w 3 : E)] with hF
  have hFβ : ∀ z : E, IsLinearMap ℝ (fun β => F β z) := by
    intro z
    constructor
    · intro β₁ β₂
      rw [hF]
      simp only [map_add, ContinuousMultilinearMap.add_apply, mul_add]
    · intro cc β
      rw [hF]
      simp only [map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring
  have hFz : ∀ β, IsLinearMap ℝ (fun z : E => F β z) := by
    intro β
    constructor
    · intro z₁ z₂
      rw [hF]
      simp only
      rw [show (![z₁ + z₂, (w 0 : E)] : Fin 2 → E) = Fin.cons (z₁ + z₂) ![(w 0 : E)] from rfl,
        show (![z₁, (w 0 : E)] : Fin 2 → E) = Fin.cons z₁ ![(w 0 : E)] from rfl,
        show (![z₂, (w 0 : E)] : Fin 2 → E) = Fin.cons z₂ ![(w 0 : E)] from rfl]
      rw [show Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons (z₁ + z₂) ![(w 0 : E)]) =
          Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z₁ ![(w 0 : E)]) +
            Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z₂ ![(w 0 : E)]) from
        (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.cons_add _ z₁ z₂]
      ring
    · intro cc z
      rw [hF]
      simp only
      rw [show (![cc • z, (w 0 : E)] : Fin 2 → E) = Fin.cons (cc • z) ![(w 0 : E)] from rfl,
        show (![z, (w 0 : E)] : Fin 2 → E) = Fin.cons z ![(w 0 : E)] from rfl]
      rw [show Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons (cc • z) ![(w 0 : E)]) =
          cc • Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons z ![(w 0 : E)]) from
        (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.cons_smul _ cc z]
      rw [smul_eq_mul, smul_eq_mul]
      ring
  rw [show (∑ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel D ![((Module.finBasis ℝ E) i), (w 0 : E)] *
        (Tensor0SBundle.TensorRSSpace.toModel B
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis i)))
          ![(w 1 : E), (w 2 : E), (w 3 : E)]) =
      ∑ a : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E)) from
    dualPair_sum_swap (I := I) g₀ x F hFβ hFz e horth hrepr]
  have hterm : ∀ a : Fin n,
      |F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))| ≤
        CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
    intro a
    rw [hF]
    simp only
    rw [abs_mul]
    have hDterm : |Tensor0SBundle.Tensor0SSpace.toModel D ![((e a : E)), (w 0 : E)]| ≤
        c * Real.sqrt (g₀.inner x (w 0) (w 0)) := by
      have harg : (![((e a : E)), (w 0 : E)] : Fin 2 → E) =
          (fun j => ((![e a, w 0] : Fin 2 → TangentSpace I x) j : E)) := by
        funext j
        fin_cases j <;> rfl
      rw [harg]
      have hb := hD.2 ![e a, w 0]
      have hprod : (∏ j, Real.sqrt (g₀.inner x ((![e a, w 0] : Fin 2 → TangentSpace I x) j)
          ((![e a, w 0] : Fin 2 → TangentSpace I x) j))) =
          Real.sqrt (g₀.inner x (w 0) (w 0)) := by
        rw [Fin.prod_univ_two]
        have h1a : g₀.inner x (e a) (e a) = 1 := by rw [horth a a]; simp
        rw [show ((![e a, w 0] : Fin 2 → TangentSpace I x) 0) = e a from rfl,
          show ((![e a, w 0] : Fin 2 → TangentSpace I x) 1) = w 0 from rfl,
          h1a, Real.sqrt_one, one_mul]
      rw [hprod] at hb
      exact hb
    have hBterm : |(Tensor0SBundle.TensorRSSpace.toModel B
        (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
        ![(w 1 : E), (w 2 : E), (w 3 : E)]| ≤
        CB * (Real.sqrt (g₀.inner x (w 1) (w 1)) * Real.sqrt (g₀.inner x (w 2) (w 2)) *
          Real.sqrt (g₀.inner x (w 3) (w 3))) := by
      have harg : (![(w 1 : E), (w 2 : E), (w 3 : E)] : Fin 3 → E) =
          (fun j => ((![w 1, w 2, w 3] : Fin 3 → TangentSpace I x) j : E)) := by
        funext j
        fin_cases j <;> rfl
      rw [harg]
      exact hB a ![w 1, w 2, w 3]
    calc |Tensor0SBundle.Tensor0SSpace.toModel D ![((e a : E)), (w 0 : E)]| *
          |(Tensor0SBundle.TensorRSSpace.toModel B
              (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
              ![(w 1 : E), (w 2 : E), (w 3 : E)]|
        ≤ (c * Real.sqrt (g₀.inner x (w 0) (w 0))) *
            (CB * (Real.sqrt (g₀.inner x (w 1) (w 1)) * Real.sqrt (g₀.inner x (w 2) (w 2)) *
              Real.sqrt (g₀.inner x (w 3) (w 3)))) :=
          mul_le_mul hDterm hBterm (abs_nonneg _)
            (mul_nonneg hD.1 (by positivity))
      _ = CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
          rw [Fin.prod_univ_four]
          ring
  calc |∑ a : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))|
      ≤ ∑ a : Fin n,
          |F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))) ((e a : E))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin n, CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) :=
        Finset.sum_le_sum (fun a _ => hterm a)
    _ = (n : ℝ) * CB * c * ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma cometricDoubleTrace_toModel_bound (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (hrepr : ∀ v : TangentSpace I x, v = ∑ a : Fin n, g₀.inner x (e a) v • e a)
    {q : ℝ} (_hq : 0 ≤ q)
    (hqb : ∀ b : Fin n,
      Real.sqrt (g₀.inner x
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)))
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)))) ≤ q)
    {c : ℝ} {Z : Tensor0SBundle.Tensor0SSpace 4 I x}
    (hZ : fibPointwiseBound (I := I) g₀ x 4 c Z)
    (w : Fin 2 → TangentSpace I x) :
    |Tensor0SBundle.Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₁ 2 x Z)
        (fun j => (w j : E))| ≤
      (n : ℝ) * q * c *
        (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))) := by
  rw [cometricDoubleTraceFib_toModel, modelDoubleTrace_apply]
  set F : Tensor0SBundle.Tensor0SModel 1 ℝ E → E → ℝ := fun β z =>
    Tensor0SBundle.Tensor0SSpace.toModel Z
      (Fin.cons (cometricLmodel (I := I) g₁ x β)
        (Fin.cons z ![(w 0 : E), (w 1 : E)])) with hF
  have hFβ : ∀ z : E, IsLinearMap ℝ (fun β => F β z) := by
    intro z
    constructor
    · intro β₁ β₂
      rw [hF]
      simp only [map_add]
      exact (Tensor0SBundle.Tensor0SSpace.toModel Z).toMultilinearMap.cons_add _ _ _
    · intro cc β
      rw [hF]
      simp only [map_smul]
      exact (Tensor0SBundle.Tensor0SSpace.toModel Z).toMultilinearMap.cons_smul _ _ _
  have hFz : ∀ β, IsLinearMap ℝ (fun z : E => F β z) := by
    intro β
    have hupd : ∀ z : E,
        (Fin.cons (cometricLmodel (I := I) g₁ x β)
          (Fin.cons z ![(w 0 : E), (w 1 : E)]) : Fin 4 → E) =
        Function.update (Fin.cons (cometricLmodel (I := I) g₁ x β)
          (Fin.cons (0 : E) ![(w 0 : E), (w 1 : E)])) 1 z := by
      intro z
      funext j
      fin_cases j <;> rfl
    constructor
    · intro z₁ z₂
      rw [hF]
      simp only
      rw [hupd (z₁ + z₂), hupd z₁, hupd z₂]
      exact (Tensor0SBundle.Tensor0SSpace.toModel Z).map_update_add _ 1 z₁ z₂
    · intro cc z
      rw [hF]
      simp only
      rw [hupd (cc • z), hupd z, smul_eq_mul]
      have := (Tensor0SBundle.Tensor0SSpace.toModel Z).map_update_smul
        (Fin.cons (cometricLmodel (I := I) g₁ x β)
          (Fin.cons (0 : E) ![(w 0 : E), (w 1 : E)])) 1 cc z
      rw [this, smul_eq_mul]
  have hswap : (∑ k : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel Z
        (Fin.cons (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) (fun j => (w j : E))))) =
      ∑ b : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e b))) ((e b : E)) := by
    have hargs : ∀ (z : E) (β : Tensor0SBundle.Tensor0SModel 1 ℝ E),
        (Fin.cons (cometricLmodel (I := I) g₁ x β) (Fin.cons z (fun j => (w j : E))) :
          Fin 4 → E) =
        Fin.cons (cometricLmodel (I := I) g₁ x β) (Fin.cons z ![(w 0 : E), (w 1 : E)]) := by
      intro z β
      funext j
      fin_cases j <;> rfl
    have hpre : (∑ k : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel Z
          (Fin.cons (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) (fun j => (w j : E))))) =
        ∑ k : Fin (Module.finrank ℝ E),
          F (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) ((Module.finBasis ℝ E) k) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hF]
      simp only
      rw [hargs]
    rw [hpre]
    exact dualPair_sum_swap (I := I) g₀ x F hFβ hFz e horth hrepr
  rw [hswap]
  have hterm : ∀ b : Fin n,
      |F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e b))) ((e b : E))| ≤
        q * c * (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))) := by
    intro b
    rw [hF]
    simp only
    have hcml : cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e b))) =
        inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)) := by
      exact congrArg (inverseMetricSharpFib (I := I) g₁ x)
        (Tensor0SBundle.Tensor0SSpace.ofModel_toModel (g0FlatCLM (I := I) g₀ x (e b)))
    rw [hcml]
    set qb : TangentSpace I x :=
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)) with hqbdef
    have harg : (Fin.cons ((qb : TangentSpace I x) : E)
        (Fin.cons ((e b : E)) ![(w 0 : E), (w 1 : E)]) : Fin 4 → E) =
        (fun j => ((![qb, e b, w 0, w 1] : Fin 4 → TangentSpace I x) j : E)) := by
      funext j
      fin_cases j <;> rfl
    rw [harg]
    have hb := hZ.2 ![qb, e b, w 0, w 1]
    have hprod : (∏ j, Real.sqrt (g₀.inner x ((![qb, e b, w 0, w 1] : Fin 4 → TangentSpace I x) j)
        ((![qb, e b, w 0, w 1] : Fin 4 → TangentSpace I x) j))) =
        Real.sqrt (g₀.inner x qb qb) *
          (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))) := by
      rw [Fin.prod_univ_four]
      have h1b : g₀.inner x (e b) (e b) = 1 := by rw [horth b b]; simp
      rw [show ((![qb, e b, w 0, w 1] : Fin 4 → TangentSpace I x) 0) = qb from rfl,
        show ((![qb, e b, w 0, w 1] : Fin 4 → TangentSpace I x) 1) = e b from rfl,
        show ((![qb, e b, w 0, w 1] : Fin 4 → TangentSpace I x) 2) = w 0 from rfl,
        show ((![qb, e b, w 0, w 1] : Fin 4 → TangentSpace I x) 3) = w 1 from rfl,
        h1b, Real.sqrt_one]
      ring
    rw [hprod] at hb
    refine le_trans hb ?_
    have hqb_le := hqb b
    rw [← hqbdef] at hqb_le
    have hwprod : 0 ≤ Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc c * (Real.sqrt (g₀.inner x qb qb) *
          (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))))
        ≤ c * (q * (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hZ.1
          exact mul_le_mul_of_nonneg_right hqb_le hwprod
      _ = q * c * (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))) := by
          ring
  calc |∑ b : Fin n,
        F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e b))) ((e b : E))|
      ≤ ∑ b : Fin n,
          |F (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e b))) ((e b : E))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : Fin n, q * c *
          (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))) :=
        Finset.sum_le_sum (fun b _ => hterm b)
    _ = (n : ℝ) * q * c *
          (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma fourTrace_toModel_bound (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (hrepr : ∀ v : TangentSpace I x, v = ∑ a : Fin n, g₀.inner x (e a) v • e a)
    {q : ℝ} (hq : 0 ≤ q)
    (hqb : ∀ b : Fin n,
      Real.sqrt (g₀.inner x
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)))
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)))) ≤ q)
    {c : ℝ} {Z : Tensor0SBundle.Tensor0SSpace 4 I x}
    (hZ : fibPointwiseBound (I := I) g₀ x 4 c Z)
    (w : Fin 2 → TangentSpace I x) :
    |Tensor0SBundle.Tensor0SSpace.toModel
        (ricciCometricFourTraceCLM (I := I) g₁ x Z) (fun j => (w j : E))| ≤
      2 * (n : ℝ) * q * c *
        (Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1))) := by
  have hexpand : ricciCometricFourTraceCLM (I := I) g₁ x Z =
      ((1 : ℝ) / 2) •
        (cometricDoubleTraceFib (I := I) g₁ 2 x (slotPermCLM (I := I) cdPerm4_0231 x Z)
          + cometricDoubleTraceFib (I := I) g₁ 2 x (slotPermCLM (I := I) cdPerm4_0321 x Z)
          - cometricDoubleTraceFib (I := I) g₁ 2 x Z
          - cometricDoubleTraceFib (I := I) g₁ 2 x (slotPermCLM (I := I) cdPerm4_2301 x Z)) := rfl
  rw [hexpand, Tensor0SBundle.Tensor0SSpace.toModel_smul,
    Tensor0SBundle.Tensor0SSpace.toModel_sub, Tensor0SBundle.Tensor0SSpace.toModel_sub,
    Tensor0SBundle.Tensor0SSpace.toModel_add]
  rw [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.add_apply]
  set t₁ := Tensor0SBundle.Tensor0SSpace.toModel
    (cometricDoubleTraceFib (I := I) g₁ 2 x (slotPermCLM (I := I) cdPerm4_0231 x Z))
    (fun j => (w j : E)) with ht₁
  set t₂ := Tensor0SBundle.Tensor0SSpace.toModel
    (cometricDoubleTraceFib (I := I) g₁ 2 x (slotPermCLM (I := I) cdPerm4_0321 x Z))
    (fun j => (w j : E)) with ht₂
  set t₃ := Tensor0SBundle.Tensor0SSpace.toModel
    (cometricDoubleTraceFib (I := I) g₁ 2 x Z) (fun j => (w j : E)) with ht₃
  set t₄ := Tensor0SBundle.Tensor0SSpace.toModel
    (cometricDoubleTraceFib (I := I) g₁ 2 x (slotPermCLM (I := I) cdPerm4_2301 x Z))
    (fun j => (w j : E)) with ht₄
  set W : ℝ := Real.sqrt (g₀.inner x (w 0) (w 0)) * Real.sqrt (g₀.inner x (w 1) (w 1)) with hW
  have hW_nn : 0 ≤ W := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hb₁ : |t₁| ≤ (n : ℝ) * q * c * W :=
    cometricDoubleTrace_toModel_bound (I := I) g₀ g₁ x e horth hrepr hq hqb
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_0231 hZ) w
  have hb₂ : |t₂| ≤ (n : ℝ) * q * c * W :=
    cometricDoubleTrace_toModel_bound (I := I) g₀ g₁ x e horth hrepr hq hqb
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_0321 hZ) w
  have hb₃ : |t₃| ≤ (n : ℝ) * q * c * W :=
    cometricDoubleTrace_toModel_bound (I := I) g₀ g₁ x e horth hrepr hq hqb hZ w
  have hb₄ : |t₄| ≤ (n : ℝ) * q * c * W :=
    cometricDoubleTrace_toModel_bound (I := I) g₀ g₁ x e horth hrepr hq hqb
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_2301 hZ) w
  have htotal : |t₁ + t₂ - t₃ - t₄| ≤ 4 * ((n : ℝ) * q * c * W) := by
    have h12 : |t₁ + t₂| ≤ |t₁| + |t₂| := abs_add_le t₁ t₂
    have h123 : |t₁ + t₂ - t₃| ≤ |t₁ + t₂| + |t₃| := by
      rw [sub_eq_add_neg]
      refine le_trans (abs_add_le _ _) (le_of_eq ?_)
      rw [abs_neg]
    have h1234 : |t₁ + t₂ - t₃ - t₄| ≤ |t₁ + t₂ - t₃| + |t₄| := by
      rw [sub_eq_add_neg (t₁ + t₂ - t₃) t₄]
      refine le_trans (abs_add_le _ _) (le_of_eq ?_)
      rw [abs_neg]
    linarith
  rw [smul_eq_mul, abs_mul, show |(1 : ℝ) / 2| = 1 / 2 from by norm_num]
  calc (1 / 2 : ℝ) * |t₁ + t₂ - t₃ - t₄| ≤ (1 / 2 : ℝ) * (4 * ((n : ℝ) * q * c * W)) :=
        mul_le_mul_of_nonneg_left htotal (by norm_num)
    _ = 2 * (n : ℝ) * q * c * W := by ring


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma fibPointwiseBound_order1CLM (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (hrepr : ∀ v : TangentSpace I x, v = ∑ a : Fin n, g₀.inner x (e a) v • e a)
    (A : Tensor0SBundle.TensorRSSpace 1 2 I x) {CA : ℝ} (hCA : 0 ≤ CA)
    (hAf : ∀ (a : Fin n) (v : Fin 2 → TangentSpace I x),
      |(Tensor0SBundle.TensorRSSpace.toModel A
          (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
          (fun j => (v j : E))| ≤
        CA * (Real.sqrt (g₀.inner x (v 0) (v 0)) * Real.sqrt (g₀.inner x (v 1) (v 1))))
    {c : ℝ} {D : Tensor0SBundle.Tensor0SSpace 3 I x}
    (hD : fibPointwiseBound (I := I) g₀ x 3 c D) :
    fibPointwiseBound (I := I) g₀ x 4 (5 * ((n : ℝ) * CA * c))
      (linearizedRicciConnDiffOrder1CLM (I := I) x A D) := by
  have h₁ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_0312
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm3_102 hD))
  have h₂ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_0213
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm3_120 hD))
  have h₃ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_2301
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf hD)
  have h₄ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_1302
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm3_102 hD))
  have h₅ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_1203
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm3_120 hD))
  have hval : linearizedRicciConnDiffOrder1CLM (I := I) x A D =
      -(slotPermCLM (I := I) cdPerm4_0312 x
          (connContrCLM (I := I) 2 1 x A (slotPermCLM (I := I) cdPerm3_102 x D))
        + slotPermCLM (I := I) cdPerm4_0213 x
          (connContrCLM (I := I) 2 1 x A (slotPermCLM (I := I) cdPerm3_120 x D))
        + slotPermCLM (I := I) cdPerm4_2301 x (connContrCLM (I := I) 2 1 x A D)
        + slotPermCLM (I := I) cdPerm4_1302 x
          (connContrCLM (I := I) 2 1 x A (slotPermCLM (I := I) cdPerm3_102 x D))
        + slotPermCLM (I := I) cdPerm4_1203 x
          (connContrCLM (I := I) 2 1 x A (slotPermCLM (I := I) cdPerm3_120 x D))) := rfl
  refine ⟨mul_nonneg (by norm_num)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hCA) hD.1), ?_⟩
  intro w
  rw [hval, Tensor0SBundle.Tensor0SSpace.toModel_neg, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_add, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_add]
  rw [ContinuousMultilinearMap.neg_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, abs_neg]
  set P4 : ℝ := ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) with hP4
  have hP4nn : 0 ≤ P4 := fibPointwiseBound_prod_nonneg (I := I) g₀ x w
  have b₁ := h₁.2 w
  have b₂ := h₂.2 w
  have b₃ := h₃.2 w
  have b₄ := h₄.2 w
  have b₅ := h₅.2 w
  rw [← hP4] at b₁ b₂ b₃ b₄ b₅
  set v₁ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_0312 x
      (connContrCLM (I := I) 2 1 x A (slotPermCLM (I := I) cdPerm3_102 x D)))
    (fun j => (w j : E)) with hv₁
  set v₂ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_0213 x
      (connContrCLM (I := I) 2 1 x A (slotPermCLM (I := I) cdPerm3_120 x D)))
    (fun j => (w j : E)) with hv₂
  set v₃ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_2301 x (connContrCLM (I := I) 2 1 x A D))
    (fun j => (w j : E)) with hv₃
  set v₄ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_1302 x
      (connContrCLM (I := I) 2 1 x A (slotPermCLM (I := I) cdPerm3_102 x D)))
    (fun j => (w j : E)) with hv₄
  set v₅ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_1203 x
      (connContrCLM (I := I) 2 1 x A (slotPermCLM (I := I) cdPerm3_120 x D)))
    (fun j => (w j : E)) with hv₅
  have habs : |v₁ + v₂ + v₃ + v₄ + v₅| ≤ |v₁| + |v₂| + |v₃| + |v₄| + |v₅| := by
    have i1 : |v₁ + v₂| ≤ |v₁| + |v₂| := abs_add_le _ _
    have i2 : |v₁ + v₂ + v₃| ≤ |v₁ + v₂| + |v₃| := abs_add_le _ _
    have i3 : |v₁ + v₂ + v₃ + v₄| ≤ |v₁ + v₂ + v₃| + |v₄| := abs_add_le _ _
    have i4 : |v₁ + v₂ + v₃ + v₄ + v₅| ≤ |v₁ + v₂ + v₃ + v₄| + |v₅| := abs_add_le _ _
    linarith
  calc |v₁ + v₂ + v₃ + v₄ + v₅| ≤ |v₁| + |v₂| + |v₃| + |v₄| + |v₅| := habs
    _ ≤ 5 * ((n : ℝ) * CA * c) * P4 := by linarith


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma fibPointwiseBound_order0CLM (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (hrepr : ∀ v : TangentSpace I x, v = ∑ a : Fin n, g₀.inner x (e a) v • e a)
    (A : Tensor0SBundle.TensorRSSpace 1 2 I x) {CA : ℝ} (hCA : 0 ≤ CA)
    (hAf : ∀ (a : Fin n) (v : Fin 2 → TangentSpace I x),
      |(Tensor0SBundle.TensorRSSpace.toModel A
          (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
          (fun j => (v j : E))| ≤
        CA * (Real.sqrt (g₀.inner x (v 0) (v 0)) * Real.sqrt (g₀.inner x (v 1) (v 1))))
    (DA : Tensor0SBundle.TensorRSSpace 1 3 I x) {CDA : ℝ} (hCDA : 0 ≤ CDA)
    (hDAf : ∀ (a : Fin n) (v : Fin 3 → TangentSpace I x),
      |(Tensor0SBundle.TensorRSSpace.toModel DA
          (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
          (fun j => (v j : E))| ≤
        CDA * (Real.sqrt (g₀.inner x (v 0) (v 0)) * Real.sqrt (g₀.inner x (v 1) (v 1)) *
          Real.sqrt (g₀.inner x (v 2) (v 2))))
    {c : ℝ} {D : Tensor0SBundle.Tensor0SSpace 2 I x}
    (hD : fibPointwiseBound (I := I) g₀ x 2 c D) :
    fibPointwiseBound (I := I) g₀ x 4
      (6 * ((n : ℝ) * CA * ((n : ℝ) * CA * c)) + 2 * ((n : ℝ) * CDA * c))
      (linearizedRicciConnDiffOrder0CLM (I := I) x A DA D) := by
  have hDswap := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm2_10 hD
  have hinn := fibPointwiseBound_connContr11 (I := I) g₀ x e horth hrepr A hCA hAf hD
  have hinn' := fibPointwiseBound_connContr11 (I := I) g₀ x e horth hrepr A hCA hAf hDswap
  have hu₃ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_3201
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm3_102 hinn))
  have hu₄ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_2301
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm3_102 hinn'))
  have hu₅ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_3102
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm3_120 hinn))
  have hu₆ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_1302
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf hinn')
  have hu₇ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_1203
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf hinn)
  have hu₈ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_2103
    (fibPointwiseBound_connContr21 (I := I) g₀ x e horth hrepr A hCA hAf
      (fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm3_120 hinn'))
  have hu₁ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_3012
    (fibPointwiseBound_connContr12 (I := I) g₀ x e horth hrepr DA hCDA hDAf hD)
  have hu₂ := fibPointwiseBound_slotPerm (I := I) g₀ x cdPerm4_2013
    (fibPointwiseBound_connContr12 (I := I) g₀ x e horth hrepr DA hCDA hDAf hDswap)
  have hval : linearizedRicciConnDiffOrder0CLM (I := I) x A DA D =
      (slotPermCLM (I := I) cdPerm4_3201 x
          (connContrCLM (I := I) 2 1 x A
            (slotPermCLM (I := I) cdPerm3_102 x (connContrCLM (I := I) 1 1 x A D)))
        + slotPermCLM (I := I) cdPerm4_2301 x
          (connContrCLM (I := I) 2 1 x A
            (slotPermCLM (I := I) cdPerm3_102 x
              (connContrCLM (I := I) 1 1 x A (slotPermCLM (I := I) cdPerm2_10 x D))))
        + slotPermCLM (I := I) cdPerm4_3102 x
          (connContrCLM (I := I) 2 1 x A
            (slotPermCLM (I := I) cdPerm3_120 x (connContrCLM (I := I) 1 1 x A D)))
        + slotPermCLM (I := I) cdPerm4_1302 x
          (connContrCLM (I := I) 2 1 x A
            (connContrCLM (I := I) 1 1 x A (slotPermCLM (I := I) cdPerm2_10 x D)))
        + slotPermCLM (I := I) cdPerm4_1203 x
          (connContrCLM (I := I) 2 1 x A (connContrCLM (I := I) 1 1 x A D))
        + slotPermCLM (I := I) cdPerm4_2103 x
          (connContrCLM (I := I) 2 1 x A
            (slotPermCLM (I := I) cdPerm3_120 x
              (connContrCLM (I := I) 1 1 x A (slotPermCLM (I := I) cdPerm2_10 x D)))))
      - slotPermCLM (I := I) cdPerm4_3012 x (connContrCLM (I := I) 1 2 x DA D)
      - slotPermCLM (I := I) cdPerm4_2013 x
          (connContrCLM (I := I) 1 2 x DA (slotPermCLM (I := I) cdPerm2_10 x D)) := rfl
  refine ⟨add_nonneg
    (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hCA)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hCA) hD.1)))
    (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hCDA) hD.1)), ?_⟩
  intro w
  rw [hval, Tensor0SBundle.Tensor0SSpace.toModel_sub, Tensor0SBundle.Tensor0SSpace.toModel_sub,
    Tensor0SBundle.Tensor0SSpace.toModel_add, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_add, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_add]
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply]
  set P4 : ℝ := ∏ j, Real.sqrt (g₀.inner x (w j) (w j)) with hP4
  have hP4nn : 0 ≤ P4 := fibPointwiseBound_prod_nonneg (I := I) g₀ x w
  have b₃ := hu₃.2 w
  have b₄ := hu₄.2 w
  have b₅ := hu₅.2 w
  have b₆ := hu₆.2 w
  have b₇ := hu₇.2 w
  have b₈ := hu₈.2 w
  have b₁ := hu₁.2 w
  have b₂ := hu₂.2 w
  rw [← hP4] at b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
  set y₃ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_3201 x
      (connContrCLM (I := I) 2 1 x A
        (slotPermCLM (I := I) cdPerm3_102 x (connContrCLM (I := I) 1 1 x A D))))
    (fun j => (w j : E)) with hy₃
  set y₄ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_2301 x
      (connContrCLM (I := I) 2 1 x A
        (slotPermCLM (I := I) cdPerm3_102 x
          (connContrCLM (I := I) 1 1 x A (slotPermCLM (I := I) cdPerm2_10 x D)))))
    (fun j => (w j : E)) with hy₄
  set y₅ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_3102 x
      (connContrCLM (I := I) 2 1 x A
        (slotPermCLM (I := I) cdPerm3_120 x (connContrCLM (I := I) 1 1 x A D))))
    (fun j => (w j : E)) with hy₅
  set y₆ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_1302 x
      (connContrCLM (I := I) 2 1 x A
        (connContrCLM (I := I) 1 1 x A (slotPermCLM (I := I) cdPerm2_10 x D))))
    (fun j => (w j : E)) with hy₆
  set y₇ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_1203 x
      (connContrCLM (I := I) 2 1 x A (connContrCLM (I := I) 1 1 x A D)))
    (fun j => (w j : E)) with hy₇
  set y₈ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_2103 x
      (connContrCLM (I := I) 2 1 x A
        (slotPermCLM (I := I) cdPerm3_120 x
          (connContrCLM (I := I) 1 1 x A (slotPermCLM (I := I) cdPerm2_10 x D)))))
    (fun j => (w j : E)) with hy₈
  set y₁ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_3012 x (connContrCLM (I := I) 1 2 x DA D))
    (fun j => (w j : E)) with hy₁
  set y₂ := Tensor0SBundle.Tensor0SSpace.toModel
    (slotPermCLM (I := I) cdPerm4_2013 x
      (connContrCLM (I := I) 1 2 x DA (slotPermCLM (I := I) cdPerm2_10 x D)))
    (fun j => (w j : E)) with hy₂
  have habs : |y₃ + y₄ + y₅ + y₆ + y₇ + y₈ - y₁ - y₂| ≤
      |y₃| + |y₄| + |y₅| + |y₆| + |y₇| + |y₈| + |y₁| + |y₂| := by
    have i1 : |y₃ + y₄| ≤ |y₃| + |y₄| := abs_add_le _ _
    have i2 : |y₃ + y₄ + y₅| ≤ |y₃ + y₄| + |y₅| := abs_add_le _ _
    have i3 : |y₃ + y₄ + y₅ + y₆| ≤ |y₃ + y₄ + y₅| + |y₆| := abs_add_le _ _
    have i4 : |y₃ + y₄ + y₅ + y₆ + y₇| ≤ |y₃ + y₄ + y₅ + y₆| + |y₇| := abs_add_le _ _
    have i5 : |y₃ + y₄ + y₅ + y₆ + y₇ + y₈| ≤ |y₃ + y₄ + y₅ + y₆ + y₇| + |y₈| := abs_add_le _ _
    have i6 : |y₃ + y₄ + y₅ + y₆ + y₇ + y₈ - y₁| ≤ |y₃ + y₄ + y₅ + y₆ + y₇ + y₈| + |y₁| := by
      rw [sub_eq_add_neg]
      refine le_trans (abs_add_le _ _) (le_of_eq ?_)
      rw [abs_neg]
    have i7 : |y₃ + y₄ + y₅ + y₆ + y₇ + y₈ - y₁ - y₂| ≤
        |y₃ + y₄ + y₅ + y₆ + y₇ + y₈ - y₁| + |y₂| := by
      rw [sub_eq_add_neg (y₃ + y₄ + y₅ + y₆ + y₇ + y₈ - y₁) y₂]
      refine le_trans (abs_add_le _ _) (le_of_eq ?_)
      rw [abs_neg]
    linarith
  calc |y₃ + y₄ + y₅ + y₆ + y₇ + y₈ - y₁ - y₂|
      ≤ |y₃| + |y₄| + |y₅| + |y₆| + |y₇| + |y₈| + |y₁| + |y₂| := habs
    _ ≤ (6 * ((n : ℝ) * CA * ((n : ℝ) * CA * c)) + 2 * ((n : ℝ) * CDA * c)) * P4 := by
        have e1 : (6 * ((n : ℝ) * CA * ((n : ℝ) * CA * c)) + 2 * ((n : ℝ) * CDA * c)) * P4 =
            ((n : ℝ) * CA * ((n : ℝ) * CA * c) * P4) * 6 + ((n : ℝ) * CDA * c * P4) * 2 := by
          ring
        rw [e1]
        linarith

end UniformBound

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
