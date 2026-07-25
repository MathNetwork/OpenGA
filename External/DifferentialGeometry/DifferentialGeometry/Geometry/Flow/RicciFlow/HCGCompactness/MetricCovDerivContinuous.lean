import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricDerivNormRestrict
import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame

set_option autoImplicit false
set_option linter.style.longLine false





























noncomputable section

open Set Function
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] [BoundarylessManifold I M]



private noncomputable def orthoFrameBasis
    (gRef : SmoothRiemannianMetric I M) (z₀ : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) z₀) :
    Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I y) :=
  basisOfLinearIndependentOfCardEqFinrank
    (b := fun a : Fin (Module.finrank Real E) =>
      smoothOrthoFrame (I := I) gRef z₀ a y)
    (by
      classical
      rw [Fintype.linearIndependent_iff]
      intro c hc b
      have hON := fun a b' =>
        smoothOrthoFrame_orthonormal (I := I) (M := M) gRef z₀ hy a b'
      have hpair :
          gRef.inner y (∑ a, c a • smoothOrthoFrame (I := I) gRef z₀ a y)
            (smoothOrthoFrame (I := I) gRef z₀ b y) = 0 := by
        rw [hc]; simp
      rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
      rw [Finset.sum_eq_single b] at hpair
      · rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, hON b b,
          if_pos rfl, smul_eq_mul, mul_one] at hpair
        exact hpair
      · intro a _ hab
        rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, hON a b,
          if_neg (by simpa using hab), smul_zero]
      · intro hb
        exact absurd (Finset.mem_univ b) hb)
    (by rw [Fintype.card_fin]; rfl)

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
@[simp]
private lemma orthoFrameBasis_apply
    (gRef : SmoothRiemannianMetric I M) (z₀ : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) z₀)
    (a : Fin (Module.finrank Real E)) :
    orthoFrameBasis (I := I) gRef z₀ hy a =
      smoothOrthoFrame (I := I) gRef z₀ a y := by
  unfold orthoFrameBasis
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]



private noncomputable def orthoFrameSection
    (gRef : SmoothRiemannianMetric I M) (z₀ : M)
    (i : Fin (Module.finrank Real E)) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
  ContMDiffSection.mk (smoothOrthoFrame (I := I) gRef z₀ i)
    (smoothOrthoFrame_smooth (I := I) gRef z₀ i)

omit [CompleteSpace E] [SigmaCompactSpace M] [BoundarylessManifold I M] in
@[simp]
private lemma orthoFrameSection_apply
    (gRef : SmoothRiemannianMetric I M) (z₀ : M)
    (i : Fin (Module.finrank Real E)) (y : M) :
    orthoFrameSection (I := I) gRef z₀ i y = smoothOrthoFrame (I := I) gRef z₀ i y :=
  rfl



omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
private lemma metricCovDerivNorm_eq_sum_sq_on_nbhd
    (q : Nat) (h gRef : SmoothRiemannianMetric I M) (z₀ : M) {z : M}
    (hz : z ∈ smoothOrthoFrameNbhd (I := I) (M := M) z₀) :
    metricCovDerivNorm (I := I) q h gRef z =
      Real.sqrt (∑ slots : Fin (q + 2) -> Fin (Module.finrank Real E),
        (metricCovDeriv (I := I) h gRef q z
            (fun a : Fin (q + 2) =>
              smoothOrthoFrame (I := I) gRef z₀ (slots a) z)) ^ 2) := by
  classical
  have hON : ∀ i j,
      gRef.inner z
          (orthoFrameBasis (I := I) gRef z₀ hz i)
          (orthoFrameBasis (I := I) gRef z₀ hz j) = if i = j then (1 : Real) else 0 := by
    intro i j
    rw [orthoFrameBasis_apply, orthoFrameBasis_apply]
    exact smoothOrthoFrame_orthonormal (I := I) (M := M) gRef z₀ hz i j
  have hinv :
      Tensor0SBundle.MetricInverseInBasis_gen (I := I) (M := M) gRef z
        (orthoFrameBasis (I := I) gRef z₀ hz)
        (Tensor0SBundle.identityInvMetric
          (Idx := Fin (Module.finrank Real E))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I) gRef
      (orthoFrameBasis (I := I) gRef z₀ hz) hON
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric]
      using h'
  rw [metricCovDerivNorm,
    Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) (M := M) gRef z (q + 2)
      (orthoFrameBasis (I := I) gRef z₀ hz) hinv]
  congr 1
  apply Finset.sum_congr rfl
  intro slots _
  congr 1
  rw [Tensor0SBundle.component0S_apply]
  congr 1
  funext a
  rw [orthoFrameBasis_apply]



omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem metricCovDerivNorm_continuousAt
    (q : Nat) (h gRef : SmoothRiemannianMetric I M) (z₀ : M) :
    ContinuousAt (fun z : M => metricCovDerivNorm (I := I) q h gRef z) z₀ := by
  classical


  have hnbhd : smoothOrthoFrameNbhd (I := I) (M := M) z₀ ∈ nhds z₀ :=
    smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) z₀
  have hz₀ : z₀ ∈ smoothOrthoFrameNbhd (I := I) (M := M) z₀ :=
    mem_smoothOrthoFrameNbhd_self (I := I) (M := M) z₀

  set g : M -> Real := fun z =>
    Real.sqrt (∑ slots : Fin (q + 2) -> Fin (Module.finrank Real E),
      (metricCovDeriv (I := I) h gRef q z
          (fun a : Fin (q + 2) =>
            smoothOrthoFrame (I := I) gRef z₀ (slots a) z)) ^ 2) with hg_def

  have hcomp_cont : ∀ slots : Fin (q + 2) -> Fin (Module.finrank Real E),
      Continuous (fun z : M =>
        metricCovDeriv (I := I) h gRef q z
          (fun a : Fin (q + 2) => smoothOrthoFrame (I := I) gRef z₀ (slots a) z)) := by
    intro slots
    have hsmooth : ∀ z : M, ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun z : M => metricCovDeriv (I := I) h gRef q z
          (fun a : Fin (q + 2) => smoothOrthoFrame (I := I) gRef z₀ (slots a) z)) z := by
      intro z
      have hEval := Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s := q + 2)
        (metricCovDeriv (I := I) h gRef q)
        (fun a : Fin (q + 2) => orthoFrameSection (I := I) gRef z₀ (slots a)) z
      simpa only [orthoFrameSection_apply] using hEval
    have : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun z : M => metricCovDeriv (I := I) h gRef q z
          (fun a : Fin (q + 2) => smoothOrthoFrame (I := I) gRef z₀ (slots a) z)) :=
      fun z => hsmooth z
    exact this.continuous

  have hsum_cont : Continuous (fun z : M =>
      ∑ slots : Fin (q + 2) -> Fin (Module.finrank Real E),
        (metricCovDeriv (I := I) h gRef q z
            (fun a : Fin (q + 2) =>
              smoothOrthoFrame (I := I) gRef z₀ (slots a) z)) ^ 2) :=
    continuous_finset_sum _ (fun slots _ => (hcomp_cont slots).pow 2)
  have hg_cont : Continuous g := by
    rw [hg_def]; exact Real.continuous_sqrt.comp hsum_cont

  have heq : (fun z : M => metricCovDerivNorm (I := I) q h gRef z) =ᶠ[nhds z₀] g := by
    filter_upwards [hnbhd] with z hz
    exact metricCovDerivNorm_eq_sum_sq_on_nbhd (I := I) q h gRef z₀ hz
  exact (hg_cont.continuousAt).congr heq.symm




omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem metricCovDerivNorm_continuous
    (q : Nat) (h gRef : SmoothRiemannianMetric I M) :
    Continuous (fun z : M => metricCovDerivNorm (I := I) q h gRef z) :=
  continuous_iff_continuousAt.mpr
    (fun z₀ => metricCovDerivNorm_continuousAt (I := I) q h gRef z₀)





omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem metricCovDerivNorm_bddAbove_of_isCompact
    (q : Nat) (h gRef : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K) :
    BddAbove ((fun z : M => metricCovDerivNorm (I := I) q h gRef z) '' K) :=
  (hK.image (metricCovDerivNorm_continuous (I := I) q h gRef)).bddAbove



omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem metricCovDerivNorm_le_of_isCompact
    (q : Nat) (h gRef : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K) :
    ∃ C : Real, ∀ z : M, z ∈ K -> metricCovDerivNorm (I := I) q h gRef z <= C := by
  obtain ⟨C, hC⟩ := metricCovDerivNorm_bddAbove_of_isCompact (I := I) q h gRef hK
  refine ⟨C, fun z hz => ?_⟩
  exact hC ⟨z, hz, rfl⟩













omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem smoothRiemannianMetric_eq_of_inner
    {h₁ h₂ : SmoothRiemannianMetric I M}
    (hinner : (fun x => h₁.inner x) = fun x => h₂.inner x) :
    h₁ = h₂ := by
  obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := h₁
  obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := h₂
  have : i₁ = i₂ := hinner
  subst this
  rfl



omit [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem restrictOpen_eq_of_eqOn
    (h₁ h₂ : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (hUeq : ∀ x : M, x ∈ U -> ∀ v w : TangentSpace I x,
      h₁.inner x v w = h₂.inner x v w) :
    h₁.restrictOpen (I := I) U = h₂.restrictOpen (I := I) U := by
  apply smoothRiemannianMetric_eq_of_inner (I := I)
  funext x
  ext v w
  rw [SmoothRiemannianMetric.restrictOpen_inner, SmoothRiemannianMetric.restrictOpen_inner]
  exact hUeq (x : M) x.2 v w




omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem metricCovDeriv_eq_of_eqOn
    (h₁ h₂ gRef : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (hUeq : ∀ x : M, x ∈ U -> ∀ v w : TangentSpace I x,
      h₁.inner x v w = h₂.inner x v w)
    (a : Nat) (x : U) (slots : Fin (a + 2) -> TangentSpace I x) :
    metricCovDeriv (I := I) h₁ gRef a (x : M) slots =
      metricCovDeriv (I := I) h₂ gRef a (x : M) slots := by
  rw [← metricCovDeriv_restrictOpen_apply (I := I) h₁ gRef U a x slots,
    ← metricCovDeriv_restrictOpen_apply (I := I) h₂ gRef U a x slots,
    restrictOpen_eq_of_eqOn (I := I) h₁ h₂ U hUeq]




omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem metricCovDerivNorm_eq_of_eqOn
    (h₁ h₂ gRef : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (hUeq : ∀ x : M, x ∈ U -> ∀ v w : TangentSpace I x,
      h₁.inner x v w = h₂.inner x v w)
    (q : Nat) {z : M} (hz : z ∈ U) :
    metricCovDerivNorm (I := I) q h₁ gRef z =
      metricCovDerivNorm (I := I) q h₂ gRef z := by
  have hcov : metricCovDeriv (I := I) h₁ gRef q z = metricCovDeriv (I := I) h₂ gRef q z := by
    ext slots
    exact metricCovDeriv_eq_of_eqOn (I := I) h₁ h₂ gRef U hUeq q ⟨z, hz⟩ slots
  rw [metricCovDerivNorm, metricCovDerivNorm, hcov]

end HCGCompactness
end DifferentialGeometry
