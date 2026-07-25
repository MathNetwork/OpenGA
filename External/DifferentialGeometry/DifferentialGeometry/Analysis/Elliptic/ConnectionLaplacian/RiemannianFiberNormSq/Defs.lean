import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.VectorBundle.Riemannian


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def fiberNormSqSummand
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (T : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) : ℝ :=
  ((T : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
        (fun k => g.inner b (e (K k))))
      (fun k => e (J k))) ^ 2

omit [FiniteDimensional ℝ E] in
lemma fiberNormSqSummand_nonneg
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (T : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    0 ≤ fiberNormSqSummand (I := I) (M := M) g b r s T n e K J := by
  unfold fiberNormSqSummand
  exact sq_nonneg _

omit [FiniteDimensional ℝ E] in
private lemma fiberNormSqSummand_zero
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqSummand (I := I) (M := M) g b r s
      (0 : TensorRSSpace r s I b) n e K J = 0 := by
  unfold fiberNormSqSummand
  have h_inner : ((0 : TensorRSSpace r s I b)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
        (fun k => g.inner b (e (K k)))) :
      Tensor0SSpace s I b) = 0 := rfl
  rw [show (((0 : TensorRSSpace r s I b)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
        (fun k => g.inner b (e (K k)))))
      (fun k => e (J k)) : ℝ) = 0 from by rw [h_inner]; rfl]
  norm_num

noncomputable def riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) : ℝ := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I b) := g.toRiemannianMetric.toCore b
  have hc : ContinuousAt (fun v : TangentSpace I b => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt b
  have hb : Bornology.IsVonNBounded ℝ {v : TangentSpace I b |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded b
  letI : NormedAddCommGroup (TangentSpace I b) := cd.toNormedAddCommGroupOfTopology hc hb
  letI : InnerProductSpace ℝ (TangentSpace I b) :=
    InnerProductSpace.ofCoreOfTopology cd hc hb
  let n : ℕ := Module.finrank ℝ (TangentSpace I b)
  let e : OrthonormalBasis (Fin n) ℝ (TangentSpace I b) := stdOrthonormalBasis ℝ _
  exact ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
    fiberNormSqSummand (I := I) (M := M) g b r s T n (fun i => e i) K J

theorem riemannianFiberNormSq_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    0 ≤ riemannianFiberNormSq (I := I) (M := M) g r s b T := by
  classical
  unfold riemannianFiberNormSq
  refine Finset.sum_nonneg (fun K _ => ?_)
  refine Finset.sum_nonneg (fun J _ => ?_)
  exact fiberNormSqSummand_nonneg (I := I) (M := M) g b r s T _ _ K J

theorem riemannianFiberNormSq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s b (0 : TensorRSSpace r s I b) = 0 := by
  classical
  unfold riemannianFiberNormSq
  refine Finset.sum_eq_zero (fun K _ => ?_)
  refine Finset.sum_eq_zero (fun J _ => ?_)
  exact fiberNormSqSummand_zero (I := I) (M := M) g b r s _ _ K J

end Connection
end Integral
end DifferentialGeometry
