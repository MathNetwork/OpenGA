import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.WindowPreconv

set_option autoImplicit false
set_option linter.style.longLine false




























noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology
open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]






omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem evolNorm_bound_of_ricBound
    [Module.Finite ℝ E]
    {K U : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {N : Nat}
    (hKc : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hN : 1 ≤ N)
    (B : Real -> Real)
    (hequiv : MetricUniformEquivalentOnWindow (I := I) U β ψ gRef gSeq B)
    (Bmax : Real) (hBmax1 : 1 ≤ Bmax) (hBmax : ∀ t ∈ Set.Icc β ψ, B t ≤ Bmax)
    (Cg : Nat -> Real)
    (hBprev : forall r : Nat, 1 <= r -> r < N ->
      MetricCovDerivOrderBoundOnWindow (I := I) U β ψ gSeq gRef r (Cg r))
    (KShi : Real) (hKShi0 : 0 ≤ KShi)
    (hShi : MovingShiBoundOn (I := I) U β ψ gSeq N KShi)
    (CN : Real) (hCN0 : 0 ≤ CN)
    (hboundN : MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef N CN) :
    ∃ L : Real, 0 ≤ L ∧
      ∀ i : Nat, ∀ x ∈ K, ∀ s : Real, s ∈ Set.Icc β ψ ->
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (N + 2)
          (((-2 : Real) • nablaRicReal (I := I) gSeq gRef N i s x))) ≤ L := by
  obtain ⟨Cpp, Cppp, hpp0, hppp0, hb⟩ := ric_bound_field (I := I) hKc hU hKU
    N hN B hequiv Bmax hBmax1 hBmax Cg hBprev KShi hKShi0 hShi
  refine ⟨2 * (Cpp * CN + Cppp), by positivity, fun i x hx s hs => ?_⟩
  rw [sqrt_normSq0S_smul]
  have hsqrt := hb i s hs x hx
  have hmcd := hboundN i s hs x hx
  have habs : |(-2 : Real)| = 2 := by norm_num
  rw [habs]
  calc 2 * Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (N + 2)
          (nablaRicReal (I := I) gSeq gRef N i s x))
      ≤ 2 * (Cpp * metricCovDerivNorm (I := I) N (gSeq i s) gRef x + Cppp) :=
        mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ ≤ 2 * (Cpp * CN + Cppp) := by
        have : Cpp * metricCovDerivNorm (I := I) N (gSeq i s) gRef x ≤ Cpp * CN :=
          mul_le_mul_of_nonneg_left hmcd hpp0
        linarith









omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem hgLip_orderN_of_solutions
    [Module.Finite ℝ E]
    {K U : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {N : Nat}
    (hKc : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hN : 1 ≤ N)
    (B : Real -> Real)
    (hequiv : MetricUniformEquivalentOnWindow (I := I) U β ψ gRef gSeq B)
    (Bmax : Real) (hBmax1 : 1 ≤ Bmax) (hBmax : ∀ t ∈ Set.Icc β ψ, B t ≤ Bmax)
    (Cg : Nat -> Real)
    (hBprev : forall r : Nat, 1 <= r -> r < N ->
      MetricCovDerivOrderBoundOnWindow (I := I) U β ψ gSeq gRef r (Cg r))
    (KShi : Real) (hKShi0 : 0 ≤ KShi)
    (hShi : MovingShiBoundOn (I := I) U β ψ gSeq N KShi)
    (CN : Real) (hCN0 : 0 ≤ CN)
    (hboundN : MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef N CN)
    (D : Nat -> RealTimeInterval)
    (S : (i : Nat) -> SolutionOn (I := I) (M := M) (D i))
    (hS : ∀ i : Nat, IsSolutionOn (I := I) (S i))
    (hmet : ∀ (i : Nat) (r : Real), (S i).family.metric r = gSeq i r)
    (hreg : ∀ i : Nat, Set.Icc β ψ ⊆ (D i).regular)
    (hswap : ∀ i : Nat, ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) (D i).carrier (D i).regular
        ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (solnMetricField (I := I) (S i) r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (solnEvolField (I := I) (S i) r) p) p'
          (fun a : Fin (p + 2) => V a p'))) :
    ∃ L : Real, 0 ≤ L ∧
      ∀ i : Nat, ∀ s : Real, s ∈ Set.Icc β ψ -> ∀ t : Real, t ∈ Set.Icc β ψ ->
        ∀ x : M, x ∈ K ->
          metricDerivNorm (I := I) N (gSeq i s) (gSeq i t) gRef x ≤ L * |s - t| := by
  obtain ⟨L, hL0, hLbound⟩ := evolNorm_bound_of_ricBound (I := I) hKc hU hKU hN
    B hequiv Bmax hBmax1 hBmax Cg hBprev KShi hKShi0 hShi CN hCN0 hboundN
  have hev := hevComp_of_solutions (I := I) (K := K) (β := β) (ψ := ψ)
    (gSeq := gSeq) (gRef := gRef) (N := N) D S hS hmet hreg hswap
  refine ⟨L, hL0, fun i s hs t ht x hx => ?_⟩
  exact timeLipschitz_of_hasDerivAt (I := I) gRef N (gSeq i)
    (fun s' x' => (-2 : Real) • nablaRicReal (I := I) gSeq gRef N i s' x')
    K β ψ L
    (fun x' hx' s' hs' v => hev i x' hx' s' hs' v)
    (fun x' hx' s' hs' => hLbound i x' hx' s' hs')
    s hs t ht x hx

end HCGCompactness
end DifferentialGeometry
