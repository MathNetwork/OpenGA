import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvDiag
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.WindowPreconv

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false


































noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology
open Bundle Tensor0SBundle TensorLieDeriv
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
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metricDerivNorm_le_compSq_uniform
    [FiniteDimensional Real E]
    (gRef : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    ∃ (basisE : Module.Basis (Fin (Module.finrank Real E)) Real E)
      (u' : Set M) (Cu : Real),
      IsOpen u' ∧ x ∈ u' ∧
      u' ⊆ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet ∧ 1 ≤ Cu ∧
      ∀ (gk gInf : SmoothRiemannianMetric I M),
      ∀ z ∈ u', ∀ hz : z ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet,
        metricDerivNorm (I := I) a gk gInf gRef z ≤
          Cu * Real.sqrt (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
            (Tensor0SBundle.component0S (I := I)
                (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).toBasisAt hz) (metricCovDeriv (I := I) gk gRef a z) I0
              - Tensor0SBundle.component0S (I := I)
                (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).toBasisAt hz) (metricCovDeriv (I := I) gInf gRef a z) I0) ^ 2) := by
  classical
  obtain ⟨basisE, u', ε, hopen, hxu', hsub, hε0, hnε, hgram, hONx, hfwd, hrev⟩ :=
    exists_goodFrame_compBound (I := I) gRef x
  refine ⟨basisE, u', ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2),
    hopen, hxu', hsub, ?_, fun gk gInf z hzu' hz => ?_⟩
  ·
    have hcard : (0 : Real) ≤ (Fintype.card (Fin (Module.finrank Real E)) : Real) :=
      Nat.cast_nonneg _
    exact one_le_pow₀ (by nlinarith)
  ·
    set bz := (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
        I 1 basisE).toBasisAt hz) with hbz
    have hcomp : ∀ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
        Tensor0SBundle.component0S (I := I) bz
            (metricDiffCovDerivAt (I := I) a gk gInf gRef z) I0
          = Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gk gRef a z) I0
            - Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gInf gRef a z) I0 :=
      fun I0 => rfl
    have hsumeq : (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
          Tensor0SBundle.component0S (I := I) bz
            (metricDiffCovDerivAt (I := I) a gk gInf gRef z) I0 ^ 2)
        = ∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
          (Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gk gRef a z) I0
            - Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gInf gRef a z) I0) ^ 2 := by
      refine Finset.sum_congr rfl fun I0 _ => ?_
      rw [hcomp I0]
    have hb := hrev z hz hzu' (a + 2) (metricDiffCovDerivAt (I := I) a gk gInf gRef z)
    have hCge1 : (1 : Real) ≤ (3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1) := by
      have : (0 : Real) ≤ (Fintype.card (Fin (Module.finrank Real E)) : Real) := Nat.cast_nonneg _
      nlinarith
    have hCpow1 : (1 : Real) ≤ ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) :=
      one_le_pow₀ hCge1
    have hsqrtle : Real.sqrt (((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2))
        ≤ ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) := by
      have h2 : ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2)
          ≤ (((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2)) ^ 2 := by
        nlinarith [hCpow1]
      calc Real.sqrt (((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2))
          ≤ Real.sqrt ((((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2)) ^ 2) :=
            Real.sqrt_le_sqrt h2
        _ = ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) :=
            Real.sqrt_sq (by positivity)
    rw [metricDerivNorm]
    calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z (a + 2)
            (metricDiffCovDerivAt (I := I) a gk gInf gRef z))
        ≤ Real.sqrt (((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) *
            ∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
              Tensor0SBundle.component0S (I := I) bz
                (metricDiffCovDerivAt (I := I) a gk gInf gRef z) I0 ^ 2) := Real.sqrt_le_sqrt hb
      _ = Real.sqrt (((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2)) *
            Real.sqrt (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
              Tensor0SBundle.component0S (I := I) bz
                (metricDiffCovDerivAt (I := I) a gk gInf gRef z) I0 ^ 2) :=
          Real.sqrt_mul (by positivity) _
      _ ≤ ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) *
            Real.sqrt (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
              Tensor0SBundle.component0S (I := I) bz
                (metricDiffCovDerivAt (I := I) a gk gInf gRef z) I0 ^ 2) :=
          mul_le_mul_of_nonneg_right hsqrtle (Real.sqrt_nonneg _)
      _ = ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) *
            Real.sqrt (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
              (Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gk gRef a z) I0
                - Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gInf gRef a z) I0) ^ 2) := by
          rw [hsumeq]





omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metricDerivNorm_le_compSq
    [FiniteDimensional Real E]
    (gRef gk gInf : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    ∃ (basisE : Module.Basis (Fin (Module.finrank Real E)) Real E)
      (u' : Set M) (Cu : Real),
      IsOpen u' ∧ x ∈ u' ∧
      u' ⊆ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet ∧ 1 ≤ Cu ∧
      ∀ z ∈ u', ∀ hz : z ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet,
        metricDerivNorm (I := I) a gk gInf gRef z ≤
          Cu * Real.sqrt (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
            (Tensor0SBundle.component0S (I := I)
                (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).toBasisAt hz) (metricCovDeriv (I := I) gk gRef a z) I0
              - Tensor0SBundle.component0S (I := I)
                (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).toBasisAt hz) (metricCovDeriv (I := I) gInf gRef a z) I0) ^ 2) := by
  obtain ⟨basisE, u', Cu, hopen, hxu', hsub, hCu, h⟩ :=
    metricDerivNorm_le_compSq_uniform (I := I) gRef a x
  exact ⟨basisE, u', Cu, hopen, hxu', hsub, hCu, fun z hzu' hz => h gk gInf z hzu' hz⟩








omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricCInfConvOnCompacts_of_normConv
    [FiniteDimensional Real E]
    (gSeq : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hnorm : ∀ (p : ℕ) (K : Set M), IsCompact K → ∀ ε : Real, 0 < ε →
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
        metricDerivNorm (I := I) a (gSeq k) gInf gRef x < ε) :
    MetricCInfConvOnCompacts (I := I) gSeq gInf gRef := by
  intro K hK p ε hε
  obtain ⟨k0, hk0⟩ := hnorm p K hK (ε / 2) (by positivity)
  refine ⟨k0, fun k hk => ?_⟩
  refine lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall (I := I) K p (gSeq k) gInf gRef (ε / 2) (by positivity)
      (fun a hap x hxK => (hk0 k hk a hap x hxK).le)) (by linarith)











omit [Module.Finite ℝ E] [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem exists_subseq_hconv
    [FiniteDimensional Real E]
    (K : Set M) (p : ℕ)
    (gSeq : ℕ → Real → SmoothRiemannianMetric I M)
    (gInf : Real → SmoothRiemannianMetric I M) (gRef : SmoothRiemannianMetric I M)
    (e : ℕ → Real)
    (hstep : ∀ n : ℕ, ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ ε : Real, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
          metricDerivNorm (I := I) a (gSeq ((φ ∘ ψ) k) (e n)) (gInf (e n)) gRef x < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n : ℕ, ∀ ε : Real, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
        metricDerivNorm (I := I) a (gSeq (φ k) (e n)) (gInf (e n)) gRef x < ε := by
  refine exists_diag_subseq
    (fun n φ => ∀ ε : Real, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
      metricDerivNorm (I := I) a (gSeq (φ k) (e n)) (gInf (e n)) gRef x < ε)
    hstep ?_ ?_
  ·
    intro n φ ψ hψ hP ε hε
    obtain ⟨k0, hk0⟩ := hP ε hε
    exact ⟨k0, fun k hk a hap x hxK => hk0 (ψ k) (le_trans hk hψ.le_apply) a hap x hxK⟩
  ·
    intro n φ m hP ε hε
    obtain ⟨k0, hk0⟩ := hP ε hε
    refine ⟨k0 + m, fun k hk a hap x hxK => ?_⟩
    have hval := hk0 (k - m) (by omega) a hap x hxK
    simp only [Nat.sub_add_cancel (show m ≤ k by omega)] at hval
    exact hval










omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem windowPreconv_of_perTime
    [FiniteDimensional Real E]
    (K : Set M) (β ψ : Real) (p : ℕ)
    (gSeq : ℕ → Real → SmoothRiemannianMetric I M)
    (gInf : Real → SmoothRiemannianMetric I M) (gRef : SmoothRiemannianMetric I M)
    (L : Real) (hL : 0 ≤ L)
    (hgLip : ∀ k : ℕ, ∀ s ∈ Set.Icc β ψ, ∀ t ∈ Set.Icc β ψ, ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
      metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x ≤ L * |s - t|)
    (hInfLip : ∀ s ∈ Set.Icc β ψ, ∀ t ∈ Set.Icc β ψ, ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
      metricDerivNorm (I := I) a (gInf s) (gInf t) gRef x ≤ L * |s - t|)
    (e : ℕ → Real) (he : ∀ n : ℕ, e n ∈ Set.Icc β ψ)
    (hdense : ∀ t ∈ Set.Icc β ψ, ∀ δ : Real, 0 < δ → ∃ n : ℕ, |t - e n| < δ)
    (hstep : ∀ n : ℕ, ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ ε : Real, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
          metricDerivNorm (I := I) a (gSeq ((φ ∘ ψ) k) (e n)) (gInf (e n)) gRef x < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε : Real, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ t ∈ Set.Icc β ψ,
        metricDerivNormSupOn (I := I) K p (gSeq (φ k) t) (gInf t) gRef < ε := by
  obtain ⟨φ, hφ, hconv⟩ := exists_subseq_hconv (I := I) K p gSeq gInf gRef e hstep
  refine ⟨φ, hφ, ?_⟩
  refine windowPreconv (I := I) K β ψ p (fun k => gSeq (φ k)) gInf gRef L hL
    (fun k => hgLip (φ k)) hInfLip (Set.range e) ?_ ?_
  · intro t ht δ hδ
    obtain ⟨n, hn⟩ := hdense t ht δ hδ
    exact ⟨e n, ⟨n, rfl⟩, he n, hn⟩
  · rintro τ ⟨n, rfl⟩ _ ε hε
    exact hconv n ε hε

end HCGCompactness
end DifferentialGeometry
