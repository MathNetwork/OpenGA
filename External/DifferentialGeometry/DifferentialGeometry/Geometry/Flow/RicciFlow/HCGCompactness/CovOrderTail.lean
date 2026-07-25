import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivContinuity

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

section ZeroOrder

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]

omit [Module.Finite ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [IsManifold I 2 M] in
private theorem metricField_zero
    [Module.Finite ℝ E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.metricTensorField (I := I) g x = metricTensor0S (I := I) g x := by
  ext v
  rw [Tensor0SBundle.metricTensorField_apply, metricTensor0S_apply]

omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem covOrder_zero_point
    [Module.Finite ℝ E]
    (g gRef : SmoothRiemannianMetric I M) (x : M) {C : Real} (hC1 : 1 ≤ C)
    (hpair : ∀ v : TangentSpace I x,
      C⁻¹ * g.inner x v v ≤ gRef.inner x v v ∧
        gRef.inner x v v ≤ C * g.inner x v v) :
    metricCovDerivNorm (I := I) 0 g gRef x ≤
      C * Real.sqrt (Module.finrank Real E : Real) := by
  classical
  have hcomp := sqrt_normSq0S_le_of_metric_equiv
    (I := I) (g := g) (h := gRef) x 2 hC1 hpair (metricTensor0S (I := I) g x)
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) g x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro a b
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h' a b
  have hself :
      Tensor0SBundle.normSq0S (I := I) g x 2 (metricTensor0S (I := I) g x) =
        (Module.finrank Real E : Real) := by
    have hcard := normSq0S_metricTensor0S_eq_card (I := I) g basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) hinv
    simpa using hcard
  have hcov :
      metricCovDerivNorm (I := I) 0 g gRef x =
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x 2
          (metricTensor0S (I := I) g x)) := by
    simp only [metricCovDerivNorm, metricCovDeriv_eq_covDerivOfField]
    change Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x 2
        (Tensor0SBundle.metricTensorField (I := I) g x)) =
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x 2
        (metricTensor0S (I := I) g x))
    rw [metricField_zero]
  have hC0 : (0 : Real) ≤ C := le_trans zero_le_one hC1
  have hsq : Real.sqrt (C ^ 2) = C := by
    rw [Real.sqrt_sq hC0]
  rw [hcov]
  calc
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x 2
        (metricTensor0S (I := I) g x)) ≤
      Real.sqrt (C ^ 2) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2
        (metricTensor0S (I := I) g x)) := hcomp
    _ = C * Real.sqrt (Module.finrank Real E : Real) := by rw [hsq, hself]



omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem covOrder_zero_le
    [Module.Finite ℝ E]
    {K : Set M} (g gRef : SmoothRiemannianMetric I M) {C : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K gRef g C) :
    MetricCovDerivOrderBoundOn (I := I) K 0 g gRef
      (C * Real.sqrt (Module.finrank Real E : Real)) := by
  intro x hx
  have hsymm := metricUniformEquivalentOn_symm (I := I) hEq
  exact covOrder_zero_point (I := I) g gRef x hEq.1 (hsymm.2 x hx)

end ZeroOrder

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]



omit [Module.Finite ℝ E] [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem exists_initC
    [Module.Finite ℝ E]
    [CompactSpace M]
    (g gRef : SmoothRiemannianMetric I M) :
    ∃ initC : Nat → Real, (∀ r : Nat, 0 ≤ initC r) ∧
      ∀ r : Nat, ∀ x : M,
        metricCovDerivNorm (I := I) r g gRef x ≤ initC r := by
  have hb : ∀ r : Nat, ∃ C : Real, ∀ x : M,
      metricCovDerivNorm (I := I) r g gRef x ≤ C := by
    intro r
    obtain ⟨C, hC⟩ := metricCovDerivNorm_bddOn (I := I) isCompact_univ r g gRef
    exact ⟨C, fun x => hC x (Set.mem_univ x)⟩
  choose C hC using hb
  refine ⟨fun r => max (C r) 0, fun r => le_max_right _ _, ?_⟩
  intro r x
  exact le_trans (hC r x) (le_max_left _ _)





omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem covOrder_stage_const
    [Module.Finite ℝ E]
    {K U : Set M} {gRef : SmoothRiemannianMetric I M}
    (hKc : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (N : Nat) (hN : 1 ≤ N)
    (Bmax : Real) (hBmax1 : 1 ≤ Bmax)
    (Cg : Nat → Real)
    (KShi : Real) (hKShi0 : 0 ≤ KShi)
    (initC : Real) (hinitC0 : 0 ≤ initC)
    (timeRadius : Real) :
    ∃ Cw : Real,
      ∀ {β ψ t0 : Real}
        {gSeq : Nat → Real → SmoothRiemannianMetric I M}
        (B : Real → Real)
        (_hequiv : MetricUniformEquivalentOnWindow (I := I) U β ψ gRef gSeq B)
        (_hBmax : ∀ t ∈ Set.Icc β ψ, B t ≤ Bmax)
        (_hBprev : ∀ r : Nat, 1 ≤ r → r < N →
          MetricCovDerivOrderBoundOnWindow (I := I) U β ψ gSeq gRef r (Cg r))
        (_hShi : MovingShiBoundOn (I := I) U β ψ gSeq N KShi)
        (_ht0 : t0 ∈ Set.Icc β ψ)
        (_hevComp : ∀ i : Nat, ∀ x ∈ K, ∀ s ∈ Set.Icc β ψ,
          ∀ v : Fin (N + 2) → TangentSpace I x,
            HasDerivAt
              (fun r : Real => metricCovDeriv (I := I) (gSeq i r) gRef N x v)
              (((-2 : Real) • nablaRicReal (I := I) gSeq gRef N i s x) v) s)
        (_hinit : ∀ i : Nat, ∀ x : M, x ∈ K →
          metricCovDerivNorm (I := I) N (gSeq i t0) gRef x ≤ initC)
        (_htime : ∀ t : Real, t ∈ Set.Icc β ψ → |t - t0| ≤ timeRadius),
        MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef N Cw := by
  obtain ⟨Cpp, Cppp, hCpp, hCppp, hfield⟩ :=
    ric_bound_const (I := I) hKc hU hKU N hN Bmax hBmax1 Cg KShi hKShi0
  refine ⟨metricCovOrderEvolutionConstant Cpp Cppp timeRadius initC, ?_⟩
  intro β ψ t0 gSeq B hequiv hBmax hBprev hShi ht0 hevComp hinit htime
  exact metricCovOrderWindow_of_evolution (I := I)
    { t0_mem := ht0
      nablaRic := nablaRicReal (I := I) gSeq gRef N
      normsq_evol := normsq_evol_of_comp (I := I) hevComp
      Cpp := Cpp
      Cppp := Cppp
      Cpp_nonneg := hCpp
      Cppp_nonneg := hCppp
      ric_bound := hfield B hequiv hBmax hBprev hShi
      initC := initC
      initC_nonneg := hinitC0
      init_bound := hinit
      timeRadius := timeRadius
      time_abs_le := htime }





omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem covOrder_tower_const
    [Module.Finite ℝ E]
    {K U : Set M} {gRef : SmoothRiemannianMetric I M}
    (hKc : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (N : Nat)
    (Bmax : Real) (hBmax1 : 1 ≤ Bmax)
    (KShi : Real) (hKShi0 : 0 ≤ KShi)
    (initC : Nat → Real) (hinitC0 : ∀ r : Nat, 0 ≤ initC r)
    (timeRadius : Real) :
    ∀ r : Nat, 1 ≤ r → r ≤ N →
      ∃ Cw : Real,
        ∀ {β ψ t0 : Real}
          {gSeq : Nat → Real → SmoothRiemannianMetric I M}
          (B : Real → Real)
          (_hequiv : MetricUniformEquivalentOnWindow (I := I) U β ψ gRef gSeq B)
          (_hBmax : ∀ t ∈ Set.Icc β ψ, B t ≤ Bmax)
          (_hShi : MovingShiBoundOn (I := I) U β ψ gSeq N KShi)
          (_ht0 : t0 ∈ Set.Icc β ψ)
          (_hev : ∀ q : Nat, 1 ≤ q → q ≤ N →
            ∀ i : Nat, ∀ x ∈ U, ∀ s ∈ Set.Icc β ψ,
              ∀ v : Fin (q + 2) → TangentSpace I x,
                HasDerivAt
                  (fun r' : Real => metricCovDeriv (I := I) (gSeq i r') gRef q x v)
                  (((-2 : Real) • nablaRicReal (I := I) gSeq gRef q i s x) v) s)
          (_hinit : ∀ q : Nat, 1 ≤ q → q ≤ N →
            ∀ i : Nat, ∀ x ∈ U,
              metricCovDerivNorm (I := I) q (gSeq i t0) gRef x ≤ initC q)
          (_htime : ∀ t : Real, t ∈ Set.Icc β ψ → |t - t0| ≤ timeRadius),
          MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef r Cw := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let Stable := fun (K' : Set M) (r : Nat) (Cw : Real) =>
    ∀ {β ψ t0 : Real}
      {gSeq : Nat → Real → SmoothRiemannianMetric I M}
      (B : Real → Real)
      (_hequiv : MetricUniformEquivalentOnWindow (I := I) U β ψ gRef gSeq B)
      (_hBmax : ∀ t ∈ Set.Icc β ψ, B t ≤ Bmax)
      (_hShi : MovingShiBoundOn (I := I) U β ψ gSeq N KShi)
      (_ht0 : t0 ∈ Set.Icc β ψ)
      (_hev : ∀ q : Nat, 1 ≤ q → q ≤ N →
        ∀ i : Nat, ∀ x ∈ U, ∀ s ∈ Set.Icc β ψ,
          ∀ v : Fin (q + 2) → TangentSpace I x,
            HasDerivAt
              (fun r' : Real => metricCovDeriv (I := I) (gSeq i r') gRef q x v)
              (((-2 : Real) • nablaRicReal (I := I) gSeq gRef q i s x) v) s)
      (_hinit : ∀ q : Nat, 1 ≤ q → q ≤ N →
        ∀ i : Nat, ∀ x ∈ U,
          metricCovDerivNorm (I := I) q (gSeq i t0) gRef x ≤ initC q)
      (_htime : ∀ t : Real, t ∈ Set.Icc β ψ → |t - t0| ≤ timeRadius),
      MetricCovDerivOrderBoundOnWindow (I := I) K' β ψ gSeq gRef r Cw
  have hmain : ∀ r : Nat, 1 ≤ r → r ≤ N →
      ∀ K' : Set M, IsCompact K' →
        ∀ U' : Set M, IsOpen U' → K' ⊆ U' → U' ⊆ U →
          ∃ Cw : Real, Stable K' r Cw := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ihr =>
      intro h1 hrN K' hK'c U' hU' hK'U' hU'U
      obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK'c hU' hK'U'
      have hLsubU : (interior L : Set M) ⊆ U := fun x hx =>
        hU'U (hLU (interior_subset hx))
      have hex : ∀ q : Nat, ∃ Cq : Real, 1 ≤ q → q < r → Stable L q Cq := by
        intro q
        by_cases hq : 1 ≤ q ∧ q < r
        · obtain ⟨Cq, hCq⟩ := ihr q hq.2 hq.1 (le_trans (le_of_lt hq.2) hrN)
            L hLc U' hU' hLU hU'U
          exact ⟨Cq, fun _ _ => hCq⟩
        · exact ⟨0, fun ha hb => absurd ⟨ha, hb⟩ hq⟩
      choose Cg hCg using hex
      obtain ⟨Cw, hCw⟩ := covOrder_stage_const (I := I) hK'c isOpen_interior hKL
        r h1 Bmax hBmax1 Cg KShi hKShi0 (initC r) (hinitC0 r) timeRadius
      refine ⟨Cw, ?_⟩
      dsimp only [Stable]
      intro β ψ t0 gSeq B hequiv hBmax hShi ht0 hev hinit htime
      exact hCw B
        (metricUniformEquivalentOnWindow_mono (I := I) hLsubU hequiv)
        hBmax
        (fun q hq1 hqr => metricCovOrderWindow_mono (I := I) interior_subset
          (hCg q hq1 hqr B hequiv hBmax hShi ht0 hev hinit htime))
        (fun s hs i t ht x hx => hShi s (le_trans hs hrN) i t ht x (hLsubU hx))
        ht0
        (fun i x hx s hs v => hev r h1 hrN i x (hU'U (hK'U' hx)) s hs v)
        (fun i x hx => hinit r h1 hrN i x (hU'U (hK'U' hx)))
        htime
  intro r h1 hrN
  simpa only [Stable] using hmain r h1 hrN K hKc U hU hKU (subset_refl U)



omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem covOrder_Ico_tail
    [Module.Finite ℝ E]
    {K U : Set M} {t0 omega : Real}
    {gSeq : Nat → Real → SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (hKc : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (N : Nat)
    (Bmax : Real) (hBmax1 : 1 ≤ Bmax)
    (KShi : Real) (hKShi0 : 0 ≤ KShi)
    (initC : Nat → Real) (hinitC0 : ∀ r : Nat, 0 ≤ initC r)
    (timeRadius : Real)
    (B : Real → Real)
    (hequiv : ∀ ψ ∈ Set.Ico t0 omega,
      MetricUniformEquivalentOnWindow (I := I) U t0 ψ gRef gSeq B)
    (hBmax : ∀ t ∈ Set.Ico t0 omega, B t ≤ Bmax)
    (hShi : ∀ ψ ∈ Set.Ico t0 omega,
      MovingShiBoundOn (I := I) U t0 ψ gSeq N KShi)
    (hev : ∀ ψ ∈ Set.Ico t0 omega, ∀ q : Nat, 1 ≤ q → q ≤ N →
      ∀ i : Nat, ∀ x ∈ U, ∀ s ∈ Set.Icc t0 ψ,
        ∀ v : Fin (q + 2) → TangentSpace I x,
          HasDerivAt
            (fun r' : Real => metricCovDeriv (I := I) (gSeq i r') gRef q x v)
            (((-2 : Real) • nablaRicReal (I := I) gSeq gRef q i s x) v) s)
    (hinit : ∀ q : Nat, 1 ≤ q → q ≤ N →
      ∀ i : Nat, ∀ x ∈ U,
        metricCovDerivNorm (I := I) q (gSeq i t0) gRef x ≤ initC q)
    (htime : ∀ t ∈ Set.Ico t0 omega, |t - t0| ≤ timeRadius) :
    ∀ r : Nat, 1 ≤ r → r ≤ N →
      ∃ Cw : Real, ∀ i : Nat, ∀ s ∈ Set.Ico t0 omega,
        MetricCovDerivOrderBoundOn (I := I) K r (gSeq i s) gRef Cw := by
  intro r h1 hrN
  obtain ⟨Cw, hCw⟩ := covOrder_tower_const (I := I) hKc hU hKU N
    Bmax hBmax1 KShi hKShi0 initC hinitC0 timeRadius r h1 hrN
  refine ⟨Cw, ?_⟩
  intro i s hs
  obtain ⟨ψ, hsψ, hψω⟩ := exists_between hs.2
  have hψ : ψ ∈ Set.Ico t0 omega := ⟨le_trans hs.1 hsψ.le, hψω⟩
  have hsIcc : s ∈ Set.Icc t0 ψ := ⟨hs.1, hsψ.le⟩
  have hwindow := hCw B (hequiv ψ hψ)
    (fun t ht => hBmax t ⟨ht.1, lt_of_le_of_lt ht.2 hψω⟩)
    (hShi ψ hψ) ⟨le_rfl, hψ.1⟩ (hev ψ hψ) hinit
    (fun t ht => htime t ⟨ht.1, lt_of_le_of_lt ht.2 hψω⟩)
  exact hwindow i s hsIcc

end HCGCompactness
end DifferentialGeometry
