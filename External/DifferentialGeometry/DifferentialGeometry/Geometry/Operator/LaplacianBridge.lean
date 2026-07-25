import DifferentialGeometry.Geometry.Connection.LeviCivita.DivergenceFrameInvariance
import DifferentialGeometry.Geometry.Operator.Laplacian

set_option autoImplicit false








noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Integral.DivergenceTheorem
open Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
variable [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank Real E)] in


omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem divergence_levi_eq
    (g : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergence (I := I) (LeviCivita (I := I) g) Z.toFun x =
      divergence_g (I := I) g Z x := by
  classical
  by_cases hdim : Module.finrank Real E = 0
  · have htang : Module.finrank Real (TangentSpace I x) = 0 := hdim
    letI : Subsingleton (TangentSpace I x) :=
      Module.finrank_zero_iff.mp htang
    rw [divergence_eq]
    rw [Subsingleton.elim (LeviCivita (I := I) g Z.toFun x).toLinearMap 0]
    simp only [map_zero, divergence_g_def, localDivergence_def]
    change 0 = (∑ _i : Fin (Module.finrank Real E), _) / _
    have huniv : (Finset.univ : Finset (Fin (Module.finrank Real E))) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i _
      have hi0 : i.val < 0 := by
        simpa only [hdim] using i.isLt
      exact (Nat.not_lt_zero _ hi0).elim
    rw [huniv]
    simp
  letI : NeZero (Module.finrank Real E) := ⟨hdim⟩
  let D := (tangentMetricData_gen (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  let basis := ob.toBasis
  have hON : ∀ i j, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0 := by
    intro i j
    have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
      MetricFiberData.toCore_inner D (ob i) (ob j)
    have hob := ob.inner_eq_ite i j
    change g.inner x (ob.toBasis i) (ob.toBasis j) =
      if i = j then (1 : Real) else 0
    rw [← TangentMetricData_gen.inner_eq_gen (tangentMetricData_gen (I := I) g x)
      (ob.toBasis i) (ob.toBasis j)]
    change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
    rw [← hinner]
    exact hob
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (fun i j => if i = j then (1 : Real) else 0) := by
    intro i j
    constructor <;> simp [hON]
  rw [divergence_eq]
  rw [linearMap_trace_eq_sum_inv_inner_apply (I := I) g x basis
    (fun i j => if i = j then 1 else 0) hinv]
  rw [← metricTracePair0SAt_nablaCov_eq_divergence (I := I) g Z x]
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
    (fun i j => if i = j then 1 else 0) hinv]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [nablaCovTensor_apply]
  simp only [vec2]
  norm_num

omit [NeZero (Module.finrank Real E)] in


omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem laplacian_levi_eq
    (g : SmoothRiemannianMetric I M) {f : M → Real}
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f) (x : M) :
    laplacian (I := I) (LeviCivita (I := I) g) g f x =
      Δ_g (I := I) g hf x := by
  have hdiv := divergence_levi_eq (I := I) g (grad_g (I := I) g hf) x
  simpa only [laplacian_eq, grad_g_apply, Δ_g_def] using hdiv

omit [NeZero (Module.finrank Real E)] in


omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem laplacianAt_eq_delta
    (G : RealizedMetricFamily (I := I) (M := M) Real) (t : Real)
    {f : M → Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (hconn : G.connection t = LeviCivita (I := I) (G.metric t)) (x : M) :
    laplacianAt (I := I) G t f x = Δ_g (I := I) (G.metric t) hf x := by
  unfold laplacianAt
  rw [hconn]
  exact laplacian_levi_eq (I := I) (G.metric t) hf x

end DifferentialGeometry.Integral.Connection

end
