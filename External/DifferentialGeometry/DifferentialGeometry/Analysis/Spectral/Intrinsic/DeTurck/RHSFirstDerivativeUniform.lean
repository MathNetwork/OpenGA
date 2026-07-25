import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSFirstDerivativeLipschitz









namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

set_option maxHeartbeats 800000 in



omit [NeZero (Module.finrank ℝ E)] in
theorem chartRHSD_pou_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q₀ : ℝ) (hQ₀_nn : 0 ≤ Q₀)
    (hQ₀ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ a c : Fin (Module.finrank ℝ E),
          |chartGramOnE (I := I) (gSeq k) α a c (extChartAt I α b)| ≤ Q₀)
    (Q₁ : ℝ) (hQ₁_nn : 0 ≤ Q₁)
    (hQ₁ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α a c)
              (extChartAt I α b)| ≤ Q₁)
    (hQ₁Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) gBase α a c)
              (extChartAt I α b)| ≤ Q₁)
    (Q₂ : ℝ) (hQ₂_nn : 0 ≤ Q₂)
    (hQ₂ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) (gSeq k) α a c)) (extChartAt I α b)| ≤ Q₂)
    (hQ₂Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) gBase α a c)) (extChartAt I α b)| ≤ Q₂)
    (Q₃ : ℝ) (hQ₃_nn : 0 ≤ Q₃)
    (hQ₃ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ e d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) e
            (partialDeriv (E := E) d
              (partialDeriv (E := E) m
                (chartGramOnE (I := I) (gSeq k) α a c))) (extChartAt I α b)| ≤ Q₃)
    (hQ₃Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ e d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) e
            (partialDeriv (E := E) d
              (partialDeriv (E := E) m
                (chartGramOnE (I := I) gBase α a c))) (extChartAt I α b)| ≤ Q₃) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k₁ k₂ : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ d i j : Fin (Module.finrank ℝ E),
            |partialDeriv (E := E) d
                (chartDeTurckRHSComp (I := I) gBase (gSeq k₁) α i j)
                  (extChartAt I α b) -
              partialDeriv (E := E) d
                (chartDeTurckRHSComp (I := I) gBase (gSeq k₂) α i j)
                  (extChartAt I α b)| ≤
              C * metricJet3DiffSup (I := I) (M := M)
                (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
  classical
  let gAll : Option ι → SmoothRiemannianMetric I M := fun k => k.elim gBase gSeq
  have hequivAll : ∀ k : Option ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gAll k).inner b v v ∧
        (gAll k).inner b v v ≤ Λ * gBase.inner b v v := by
    intro k b v
    cases k with
    | none =>
        have hnonneg : 0 ≤ gBase.inner b v v := by
          rcases eq_or_ne v 0 with rfl | hv
          · simp
          · exact (gBase.pos b v hv).le
        have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛ
        constructor
        · simpa [gAll] using mul_le_mul_of_nonneg_right
            ((inv_le_one₀ hΛpos).2 hΛ) hnonneg
        · simpa [gAll] using mul_le_mul_of_nonneg_right hΛ hnonneg
    | some k => simpa [gAll] using hequiv k b v
  have hQ₁All : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : Option ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) (gAll k) α a c)
              (extChartAt I α b)| ≤ Q₁ := by
    intro α hα k b hb m a c
    cases k with
    | none => simpa [gAll] using hQ₁Base α hα b hb m a c
    | some k => simpa [gAll] using hQ₁ α hα k b hb m a c
  have hQ₂All : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : Option ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) (gAll k) α a c)) (extChartAt I α b)| ≤ Q₂ := by
    intro α hα k b hb d m a c
    cases k with
    | none => simpa [gAll] using hQ₂Base α hα b hb d m a c
    | some k => simpa [gAll] using hQ₂ α hα k b hb d m a c
  have hQ₃All : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : Option ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ e d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) e
            (partialDeriv (E := E) d
              (partialDeriv (E := E) m
                (chartGramOnE (I := I) (gAll k) α a c))) (extChartAt I α b)| ≤ Q₃ := by
    intro α hα k b hb e d m a c
    cases k with
    | none => simpa [gAll] using hQ₃Base α hα b hb e d m a c
    | some k => simpa [gAll] using hQ₃ α hα k b hb e d m a c
  obtain ⟨Mb, hMb, hMbAll⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll
  obtain ⟨T, hT, hTAll⟩ :=
    DeTurckCoefficients.invGramD2_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll
      Q₁ Q₂ hQ₁_nn hQ₂_nn hQ₁All hQ₂All
  obtain ⟨CΓ, hCΓ, hΓAll⟩ :=
    DeTurckCoefficients.christoffel_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll Q₁ hQ₁_nn hQ₁All
  obtain ⟨CdΓ, hCdΓ, hΓDAll⟩ :=
    DeTurckCoefficients.christoffelD_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll
      Q₁ hQ₁_nn hQ₁All Q₂ hQ₂_nn hQ₂All
  obtain ⟨Cd2Γ, hCd2Γ, hΓD2All⟩ :=
    DeTurckCoefficients.christD2_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll
      Q₁ Q₂ Q₃ hQ₁_nn hQ₂_nn hQ₃_nn hQ₁All hQ₂All hQ₃All
  obtain ⟨Cinv, hCinv, hInvLip⟩ :=
    DeTurckCoefficients.chartInvGram_pou_lip
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  obtain ⟨CD, hCD, hInvDLip⟩ :=
    DeTurckCoefficients.invGramD_pou_lip
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv Q₁ hQ₁_nn hQ₁
  obtain ⟨CT, hCT, hInvD2Lip⟩ :=
    DeTurckCoefficients.invGramD2_pou_lip
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
      Q₁ Q₂ hQ₁_nn hQ₂_nn hQ₁ hQ₂
  obtain ⟨G₀, hG₀, hΓLip⟩ :=
    DeTurckCoefficients.christoffel_pou_lip
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv Q₁ hQ₁_nn hQ₁
  obtain ⟨G₁, hG₁, hΓDLip⟩ :=
    DeTurckCoefficients.christoffelD_pou_lip
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
      Q₁ hQ₁_nn hQ₁ Q₂ hQ₂_nn hQ₂
  obtain ⟨G₂, hG₂, hΓD2Lip⟩ :=
    DeTurckCoefficients.christD2_pou_lip
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
      Q₁ Q₂ Q₃ hQ₁_nn hQ₂_nn hQ₃_nn hQ₁ hQ₂ hQ₃
  let n : ℝ := Module.finrank ℝ E
  let D : ℝ := n ^ 2 * Mb ^ 2 * Q₁
  let P : ℝ := 2 * CΓ
  let R : ℝ := 2 * CdΓ
  let S : ℝ := 2 * Cd2Γ
  let V : ℝ := n ^ 2 * Mb * P
  let DV : ℝ := n ^ 2 * (D * P + Mb * R)
  let D2V : ℝ := n ^ 2 * (T * P + 2 * D * R + Mb * S)
  let W₀ : ℝ := n ^ 2 * (Cinv * P + Mb * G₀)
  let W₁ : ℝ := n ^ 2 * (CD * P + D * G₀ + Cinv * R + Mb * G₁)
  let W₂ : ℝ := n ^ 2 *
    ((CT * P + T * G₀) + 2 * (CD * R + D * G₁) + (Cinv * S + Mb * G₂))
  let RicL : ℝ := n * (2 * G₂ + 4 * n * (G₁ * CΓ + CdΓ * G₀))
  let LieL : ℝ := n *
    (((W₁ * Q₁ + DV) + (W₀ * Q₂ + V)) +
      2 * ((W₁ * Q₁ + DV) + (W₂ * Q₀ + D2V)))
  let C : ℝ := 2 * RicL + LieL + 1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hDV : 0 ≤ DV := by dsimp [DV]; positivity
  have hD2V : 0 ≤ D2V := by dsimp [D2V]; positivity
  have hW₀ : 0 ≤ W₀ := by dsimp [W₀]; positivity
  have hW₁ : 0 ≤ W₁ := by dsimp [W₁]; positivity
  have hW₂ : 0 ≤ W₂ := by dsimp [W₂]; positivity
  have hRicL : 0 ≤ RicL := by dsimp [RicL]; positivity
  have hLieL : 0 ≤ LieL := by dsimp [LieL]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro α hα k₁ k₂ b hb d i j
  have hbBase : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hbSource : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hbBase
  have hleft : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hbSource
  have hy : extChartAt I α b ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hbSource)
  have hMb₂ : ∀ a c : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) (gSeq k₂) α a c (extChartAt I α b)| ≤ Mb := by
    intro a c
    rw [chartInvGramOnE_def, hleft]
    simpa [gAll] using hMbAll α hα (some k₂) b hb a c
  have hD₂ : ∀ e a c : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (chartInvGramOnE (I := I) (gSeq k₂) α a c) (extChartAt I α b)| ≤ D := by
    intro e a c
    simpa [D, n] using DeTurckCoefficients.invGramD_abs_le
      (I := I) (M := M) (gSeq k₂) α hy hMb.le hMb₂
      (hQ₁ α hα k₂ b hb) e a c
  have hT₂ : ∀ e r a c : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (partialDeriv (E := E) r
          (chartInvGramOnE (I := I) (gSeq k₂) α a c)) (extChartAt I α b)| ≤ T := by
    intro e r a c
    simpa [gAll] using hTAll α hα (some k₂) b hb e r a c
  have hΓ₁ : ∀ a c l : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) (gSeq k₁) α a c l (extChartAt I α b)| ≤ CΓ := by
    intro a c l
    simpa [gAll] using hΓAll α hα (some k₁) b hb a c l
  have hΓ₂ : ∀ a c l : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) (gSeq k₂) α a c l (extChartAt I α b)| ≤ CΓ := by
    intro a c l
    simpa [gAll] using hΓAll α hα (some k₂) b hb a c l
  have hΓBase : ∀ a c l : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) gBase α a c l (extChartAt I α b)| ≤ CΓ := by
    intro a c l
    simpa [gAll] using hΓAll α hα none b hb a c l
  have hΓD₁ : ∀ e a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (chartChristoffel (I := I) (gSeq k₁) α a c l) (extChartAt I α b)| ≤ CdΓ := by
    intro e a c l
    simpa [gAll] using hΓDAll α hα (some k₁) b hb e a c l
  have hΓD₂ : ∀ e a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (chartChristoffel (I := I) (gSeq k₂) α a c l) (extChartAt I α b)| ≤ CdΓ := by
    intro e a c l
    simpa [gAll] using hΓDAll α hα (some k₂) b hb e a c l
  have hΓDBase : ∀ e a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (chartChristoffel (I := I) gBase α a c l) (extChartAt I α b)| ≤ CdΓ := by
    intro e a c l
    simpa [gAll] using hΓDAll α hα none b hb e a c l
  have hΓD2₁ : ∀ e r a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (partialDeriv (E := E) r
          (chartChristoffel (I := I) (gSeq k₁) α a c l)) (extChartAt I α b)| ≤ Cd2Γ := by
    intro e r a c l
    simpa [gAll] using hΓD2All α hα (some k₁) b hb e r a c l
  have hΓD2₂ : ∀ e r a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (partialDeriv (E := E) r
          (chartChristoffel (I := I) (gSeq k₂) α a c l)) (extChartAt I α b)| ≤ Cd2Γ := by
    intro e r a c l
    simpa [gAll] using hΓD2All α hα (some k₂) b hb e r a c l
  have hΓD2Base : ∀ e r a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (partialDeriv (E := E) r
          (chartChristoffel (I := I) gBase α a c l)) (extChartAt I α b)| ≤ Cd2Γ := by
    intro e r a c l
    simpa [gAll] using hΓD2All α hα none b hb e r a c l
  have hΓBg₁ : ∀ a c l : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) (gSeq k₁) α a c l (extChartAt I α b) -
        chartChristoffel (I := I) gBase α a c l (extChartAt I α b)| ≤ P := by
    intro a c l
    calc
      |_ - _| ≤ |_| + |_| := abs_sub _ _
      _ ≤ CΓ + CΓ := add_le_add (hΓ₁ a c l) (hΓBase a c l)
      _ = P := by dsimp [P]; ring
  have hΓBg₂ : ∀ a c l : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) (gSeq k₂) α a c l (extChartAt I α b) -
        chartChristoffel (I := I) gBase α a c l (extChartAt I α b)| ≤ P := by
    intro a c l
    calc
      |_ - _| ≤ |_| + |_| := abs_sub _ _
      _ ≤ CΓ + CΓ := add_le_add (hΓ₂ a c l) (hΓBase a c l)
      _ = P := by dsimp [P]; ring
  have hΓDBg₁ : ∀ e a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
          (chartChristoffel (I := I) (gSeq k₁) α a c l) (extChartAt I α b) -
        partialDeriv (E := E) e
          (chartChristoffel (I := I) gBase α a c l) (extChartAt I α b)| ≤ R := by
    intro e a c l
    calc
      |_ - _| ≤ |_| + |_| := abs_sub _ _
      _ ≤ CdΓ + CdΓ := add_le_add (hΓD₁ e a c l) (hΓDBase e a c l)
      _ = R := by dsimp [R]; ring
  have hΓDBg₂ : ∀ e a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
          (chartChristoffel (I := I) (gSeq k₂) α a c l) (extChartAt I α b) -
        partialDeriv (E := E) e
          (chartChristoffel (I := I) gBase α a c l) (extChartAt I α b)| ≤ R := by
    intro e a c l
    calc
      |_ - _| ≤ |_| + |_| := abs_sub _ _
      _ ≤ CdΓ + CdΓ := add_le_add (hΓD₂ e a c l) (hΓDBase e a c l)
      _ = R := by dsimp [R]; ring
  have hΓD2Bg₁ : ∀ e r a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
          (partialDeriv (E := E) r
            (chartChristoffel (I := I) (gSeq k₁) α a c l)) (extChartAt I α b) -
        partialDeriv (E := E) e
          (partialDeriv (E := E) r
            (chartChristoffel (I := I) gBase α a c l)) (extChartAt I α b)| ≤ S := by
    intro e r a c l
    calc
      |_ - _| ≤ |_| + |_| := abs_sub _ _
      _ ≤ Cd2Γ + Cd2Γ := add_le_add (hΓD2₁ e r a c l) (hΓD2Base e r a c l)
      _ = S := by dsimp [S]; ring
  have hΓD2Bg₂ : ∀ e r a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
          (partialDeriv (E := E) r
            (chartChristoffel (I := I) (gSeq k₂) α a c l)) (extChartAt I α b) -
        partialDeriv (E := E) e
          (partialDeriv (E := E) r
            (chartChristoffel (I := I) gBase α a c l)) (extChartAt I α b)| ≤ S := by
    intro e r a c l
    calc
      |_ - _| ≤ |_| + |_| := abs_sub _ _
      _ ≤ Cd2Γ + Cd2Γ := add_le_add (hΓD2₂ e r a c l) (hΓD2Base e r a c l)
      _ = S := by dsimp [S]; ring
  have hInv : ∀ a c : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) (gSeq k₁) α a c (extChartAt I α b) -
        chartInvGramOnE (I := I) (gSeq k₂) α a c (extChartAt I α b)| ≤
          Cinv * chartGramDiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α ((extChartAt I α).symm (extChartAt I α b)) := by
    intro a c
    rw [chartInvGramOnE_def, chartInvGramOnE_def, hleft]
    exact hInvLip α hα k₁ k₂ b hb a c
  have hInvD : ∀ e a c : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
          (chartInvGramOnE (I := I) (gSeq k₁) α a c) (extChartAt I α b) -
        partialDeriv (E := E) e
          (chartInvGramOnE (I := I) (gSeq k₂) α a c) (extChartAt I α b)| ≤
          CD * chartMetricJet1DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    intro e a c
    exact hInvDLip α hα k₁ k₂ b hb e a c
  have hInvD2 : ∀ e r a c : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
          (partialDeriv (E := E) r
            (chartInvGramOnE (I := I) (gSeq k₁) α a c)) (extChartAt I α b) -
        partialDeriv (E := E) e
          (partialDeriv (E := E) r
            (chartInvGramOnE (I := I) (gSeq k₂) α a c)) (extChartAt I α b)| ≤
          CT * chartMetricJet2DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    intro e r a c
    exact hInvD2Lip α hα k₁ k₂ b hb e r a c
  have hΓ : ∀ a c l : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) (gSeq k₁) α a c l (extChartAt I α b) -
        chartChristoffel (I := I) (gSeq k₂) α a c l (extChartAt I α b)| ≤
          G₀ * chartMetricJet1DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    intro a c l
    exact hΓLip α hα k₁ k₂ b hb a c l
  have hΓD : ∀ e a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
          (chartChristoffel (I := I) (gSeq k₁) α a c l) (extChartAt I α b) -
        partialDeriv (E := E) e
          (chartChristoffel (I := I) (gSeq k₂) α a c l) (extChartAt I α b)| ≤
          G₁ * chartMetricJet2DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    intro e a c l
    exact hΓDLip α hα k₁ k₂ b hb e a c l
  have hΓD2 : ∀ e r a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
          (partialDeriv (E := E) r
            (chartChristoffel (I := I) (gSeq k₁) α a c l)) (extChartAt I α b) -
        partialDeriv (E := E) e
          (partialDeriv (E := E) r
            (chartChristoffel (I := I) (gSeq k₂) α a c l)) (extChartAt I α b)| ≤
          G₂ * metricJet3DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    intro e r a c l
    exact hΓD2Lip α hα k₁ k₂ b hb e r a c l
  have hJ₂_le : chartMetricJet2DiffSup (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b) ≤
        metricJet3DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b) :=
    metricJet2_le_jet3 (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b)
  have hJ₁_le : chartMetricJet1DiffSup (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b) ≤
        metricJet3DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b) :=
    (chartMetricJet1DiffSup_le_jet2 (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b)).trans hJ₂_le
  have hG_le : chartGramDiffSup (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α
        ((extChartAt I α).symm (extChartAt I α b)) ≤
        metricJet3DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    exact (chartGramDiffSup_le_jet1 (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b)).trans hJ₁_le
  have hInv3 : ∀ a c : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) (gSeq k₁) α a c (extChartAt I α b) -
        chartInvGramOnE (I := I) (gSeq k₂) α a c (extChartAt I α b)| ≤
          Cinv * metricJet3DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    intro a c
    exact (hInv a c).trans (mul_le_mul_of_nonneg_left hG_le hCinv.le)
  have hInvD3 : ∀ e a c : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
          (chartInvGramOnE (I := I) (gSeq k₁) α a c) (extChartAt I α b) -
        partialDeriv (E := E) e
          (chartInvGramOnE (I := I) (gSeq k₂) α a c) (extChartAt I α b)| ≤
          CD * metricJet3DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    intro e a c
    exact (hInvD e a c).trans (mul_le_mul_of_nonneg_left hJ₁_le hCD.le)
  have hInvD23 : ∀ e r a c : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
          (partialDeriv (E := E) r
            (chartInvGramOnE (I := I) (gSeq k₁) α a c)) (extChartAt I α b) -
        partialDeriv (E := E) e
          (partialDeriv (E := E) r
            (chartInvGramOnE (I := I) (gSeq k₂) α a c)) (extChartAt I α b)| ≤
          CT * metricJet3DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    intro e r a c
    exact (hInvD2 e r a c).trans (mul_le_mul_of_nonneg_left hJ₂_le hCT.le)
  have hΓ3 : ∀ a c l : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) (gSeq k₁) α a c l (extChartAt I α b) -
        chartChristoffel (I := I) (gSeq k₂) α a c l (extChartAt I α b)| ≤
          G₀ * metricJet3DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    intro a c l
    exact (hΓ a c l).trans (mul_le_mul_of_nonneg_left hJ₁_le hG₀.le)
  have hΓD3 : ∀ e a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
          (chartChristoffel (I := I) (gSeq k₁) α a c l) (extChartAt I α b) -
        partialDeriv (E := E) e
          (chartChristoffel (I := I) (gSeq k₂) α a c l) (extChartAt I α b)| ≤
          G₁ * metricJet3DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    intro e a c l
    exact (hΓD e a c l).trans (mul_le_mul_of_nonneg_left hJ₂_le hG₁.le)
  have hVF₂ : ∀ l : Fin (Module.finrank ℝ E),
      |chartDeTurckVFComp (I := I) (gSeq k₂) gBase α l (extChartAt I α b)| ≤ V := by
    intro l
    simpa [V, n] using DeTurckCoefficients.deTurckVF_abs_le
      (I := I) (M := M) (gSeq k₂) gBase α (extChartAt I α b) l
      hMb.le hMb₂ (fun a c => hΓBg₂ a c l)
  have hVFD₂ : ∀ e l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (chartDeTurckVFComp (I := I) (gSeq k₂) gBase α l) (extChartAt I α b)| ≤ DV := by
    intro e l
    simpa [DV, n] using DeTurckCoefficients.deTurckVFD_abs_le
      (I := I) (M := M) (gSeq k₂) gBase α hy e l hD hMb.le
      (hD₂ e) (fun a c => hΓBg₂ a c l) hMb₂ (fun a c => hΓDBg₂ e a c l)
  have hVFD2₂ : ∀ e r l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (partialDeriv (E := E) r
          (chartDeTurckVFComp (I := I) (gSeq k₂) gBase α l)) (extChartAt I α b)| ≤ D2V := by
    intro e r l
    simpa [D2V, n] using DeTurckCoefficients.deTurckVFD2_le
      (I := I) (M := M) (gSeq k₂) gBase α hy e r l
      hMb.le hD hT hMb₂ hD₂ hT₂
      (fun a c => hΓBg₂ a c l)
      (fun q a c => hΓDBg₂ q a c l)
      (fun q s a c => hΓD2Bg₂ q s a c l)
  have hVFsub : ∀ l : Fin (Module.finrank ℝ E),
      |chartDeTurckVFComp (I := I) (gSeq k₁) gBase α l (extChartAt I α b) -
        chartDeTurckVFComp (I := I) (gSeq k₂) gBase α l (extChartAt I α b)| ≤
          W₀ * metricJet3DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    intro l
    have h := DeTurckCoefficients.chartDeTurckVFComp_sub_abs_le
      (I := I) (M := M) (gSeq k₁) (gSeq k₂) gBase α
      hCinv.le hMb.le hP hΓBg₁ hMb₂ hInv hΓ l
    have h' : |chartDeTurckVFComp (I := I) (gSeq k₁) gBase α l (extChartAt I α b) -
        chartDeTurckVFComp (I := I) (gSeq k₂) gBase α l (extChartAt I α b)| ≤
          W₀ * chartMetricJet1DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
      simpa [W₀, n] using h
    exact h'.trans (mul_le_mul_of_nonneg_left hJ₁_le hW₀)
  have hVFDsub : ∀ e l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
          (chartDeTurckVFComp (I := I) (gSeq k₁) gBase α l) (extChartAt I α b) -
        partialDeriv (E := E) e
          (chartDeTurckVFComp (I := I) (gSeq k₂) gBase α l) (extChartAt I α b)| ≤
          W₁ * metricJet3DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    intro e l
    have h := DeTurckCoefficients.partialDeriv_chartDeTurckVFComp_sub_abs_le
      (I := I) (M := M) (gSeq k₁) (gSeq k₂) gBase α hy
      hCD.le hCinv.le hG₀.le hMb.le hP hD hR e l
      (hInvD e) hInv hΓ (hΓD e) hΓBg₁ hMb₂ (hD₂ e)
      (fun a c q => hΓDBg₁ e a c q)
    have h' : |partialDeriv (E := E) e
          (chartDeTurckVFComp (I := I) (gSeq k₁) gBase α l) (extChartAt I α b) -
        partialDeriv (E := E) e
          (chartDeTurckVFComp (I := I) (gSeq k₂) gBase α l) (extChartAt I α b)| ≤
          W₁ * chartMetricJet2DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
      simpa [W₁, n] using h
    exact h'.trans (mul_le_mul_of_nonneg_left hJ₂_le hW₁)
  have hVFD2sub : ∀ e r l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
          (partialDeriv (E := E) r
            (chartDeTurckVFComp (I := I) (gSeq k₁) gBase α l)) (extChartAt I α b) -
        partialDeriv (E := E) e
          (partialDeriv (E := E) r
            (chartDeTurckVFComp (I := I) (gSeq k₂) gBase α l)) (extChartAt I α b)| ≤
          W₂ * metricJet3DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    intro e r l
    simpa [W₂, n] using DeTurckCoefficients.deTurckVFD2_sub
      (I := I) (M := M) (gSeq k₁) (gSeq k₂) gBase α hy e r l
      hMb.le hD hT hCinv.le hCD.le hCT.le hMb₂ hD₂ hT₂
      (fun a c => hΓBg₁ a c l)
      (fun q a c => hΓDBg₁ q a c l)
      (fun q s a c => hΓD2Bg₁ q s a c l)
      hInv3 hInvD3 hInvD23 hΓ3 hΓD3 hΓD2
  have hRic : |partialDeriv (E := E) d
        (chartRicciTensor (I := I) (gSeq k₁) α i j) (extChartAt I α b) -
      partialDeriv (E := E) d
        (chartRicciTensor (I := I) (gSeq k₂) α i j) (extChartAt I α b)| ≤
        RicL * metricJet3DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    simpa [RicL, n] using DeTurckCoefficients.chartRicciD_sub
      (I := I) (M := M) (gSeq k₁) (gSeq k₂) α hy d i j
      hCdΓ hG₁.le hΓ₁ hΓD₂ hΓ3 hΓD3 hΓD2
  have hLie : |partialDeriv (E := E) d
        (chartLieDeTurckComp (I := I) (gSeq k₁) gBase α i j) (extChartAt I α b) -
      partialDeriv (E := E) d
        (chartLieDeTurckComp (I := I) (gSeq k₂) gBase α i j) (extChartAt I α b)| ≤
        LieL * metricJet3DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
    simpa [LieL, n] using DeTurckCoefficients.chartLieD_sub
      (I := I) (M := M) (gSeq k₁) (gSeq k₂) gBase α hy d i j
      hV hDV hD2V hW₀ hW₁ hW₂
      (hQ₀ α hα k₁ b hb) (hQ₁ α hα k₁ b hb) (hQ₂ α hα k₁ b hb)
      hVF₂ hVFD₂ hVFD2₂ hVFsub hVFDsub hVFD2sub
  rw [partial_chartRHS (I := I) gBase (gSeq k₁) α d i j hy,
    partial_chartRHS (I := I) gBase (gSeq k₂) α d i j hy]
  rw [show ((-2 : ℝ) * partialDeriv (E := E) d
          (chartRicciTensor (I := I) (gSeq k₁) α i j) (extChartAt I α b) +
        partialDeriv (E := E) d
          (chartLieDeTurckComp (I := I) (gSeq k₁) gBase α i j) (extChartAt I α b)) -
      ((-2 : ℝ) * partialDeriv (E := E) d
          (chartRicciTensor (I := I) (gSeq k₂) α i j) (extChartAt I α b) +
        partialDeriv (E := E) d
          (chartLieDeTurckComp (I := I) (gSeq k₂) gBase α i j) (extChartAt I α b)) =
      (-2 : ℝ) * (partialDeriv (E := E) d
          (chartRicciTensor (I := I) (gSeq k₁) α i j) (extChartAt I α b) -
        partialDeriv (E := E) d
          (chartRicciTensor (I := I) (gSeq k₂) α i j) (extChartAt I α b)) +
      (partialDeriv (E := E) d
          (chartLieDeTurckComp (I := I) (gSeq k₁) gBase α i j) (extChartAt I α b) -
        partialDeriv (E := E) d
          (chartLieDeTurckComp (I := I) (gSeq k₂) gBase α i j) (extChartAt I α b)) by ring]
  refine (abs_add_le _ _).trans ?_
  calc
    |(-2 : ℝ) * (_ - _)| + |_ - _| ≤
        2 * (RicL * metricJet3DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b)) +
        LieL * metricJet3DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
      rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
      exact add_le_add (mul_le_mul_of_nonneg_left hRic (by norm_num)) hLie
    _ = (2 * RicL + LieL) * metricJet3DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by ring
    _ ≤ C * metricJet3DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
      exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
        (metricJet3_nonneg (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b))




omit [NeZero (Module.finrank ℝ E)] in
theorem chartRHSD_pou_bnd
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q₀ : ℝ) (hQ₀_nn : 0 ≤ Q₀)
    (hQ₀ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ a c : Fin (Module.finrank ℝ E),
          |chartGramOnE (I := I) (gSeq k) α a c (extChartAt I α b)| ≤ Q₀)
    (Q₁ : ℝ) (hQ₁_nn : 0 ≤ Q₁)
    (hQ₁ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α a c)
              (extChartAt I α b)| ≤ Q₁)
    (hQ₁Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) gBase α a c)
              (extChartAt I α b)| ≤ Q₁)
    (Q₂ : ℝ) (hQ₂_nn : 0 ≤ Q₂)
    (hQ₂ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) (gSeq k) α a c)) (extChartAt I α b)| ≤ Q₂)
    (hQ₂Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) gBase α a c)) (extChartAt I α b)| ≤ Q₂)
    (Q₃ : ℝ) (hQ₃_nn : 0 ≤ Q₃)
    (hQ₃ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ e d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) e
            (partialDeriv (E := E) d
              (partialDeriv (E := E) m
                (chartGramOnE (I := I) (gSeq k) α a c))) (extChartAt I α b)| ≤ Q₃)
    (hQ₃Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ e d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) e
            (partialDeriv (E := E) d
              (partialDeriv (E := E) m
                (chartGramOnE (I := I) gBase α a c))) (extChartAt I α b)| ≤ Q₃) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ d i j : Fin (Module.finrank ℝ E),
            |partialDeriv (E := E) d
              (chartDeTurckRHSComp (I := I) gBase (gSeq k) α i j)
                (extChartAt I α b)| ≤ C := by
  classical
  let gAll : Option ι → SmoothRiemannianMetric I M := fun k => k.elim gBase gSeq
  have hequivAll : ∀ k : Option ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gAll k).inner b v v ∧
        (gAll k).inner b v v ≤ Λ * gBase.inner b v v := by
    intro k b v
    cases k with
    | none =>
        have hnonneg : 0 ≤ gBase.inner b v v := by
          rcases eq_or_ne v 0 with rfl | hv
          · simp
          · exact (gBase.pos b v hv).le
        have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛ
        constructor
        · simpa [gAll] using mul_le_mul_of_nonneg_right
            ((inv_le_one₀ hΛpos).2 hΛ) hnonneg
        · simpa [gAll] using mul_le_mul_of_nonneg_right hΛ hnonneg
    | some k => simpa [gAll] using hequiv k b v
  have hQ₁All : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : Option ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) (gAll k) α a c)
              (extChartAt I α b)| ≤ Q₁ := by
    intro α hα k b hb m a c
    cases k with
    | none => simpa [gAll] using hQ₁Base α hα b hb m a c
    | some k => simpa [gAll] using hQ₁ α hα k b hb m a c
  have hQ₂All : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : Option ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) (gAll k) α a c)) (extChartAt I α b)| ≤ Q₂ := by
    intro α hα k b hb d m a c
    cases k with
    | none => simpa [gAll] using hQ₂Base α hα b hb d m a c
    | some k => simpa [gAll] using hQ₂ α hα k b hb d m a c
  have hQ₃All : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : Option ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ e d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) e
            (partialDeriv (E := E) d
              (partialDeriv (E := E) m
                (chartGramOnE (I := I) (gAll k) α a c))) (extChartAt I α b)| ≤ Q₃ := by
    intro α hα k b hb e d m a c
    cases k with
    | none => simpa [gAll] using hQ₃Base α hα b hb e d m a c
    | some k => simpa [gAll] using hQ₃ α hα k b hb e d m a c
  obtain ⟨Mb, hMb, hMbAll⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll
  obtain ⟨T, hT, hTAll⟩ :=
    DeTurckCoefficients.invGramD2_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll
      Q₁ Q₂ hQ₁_nn hQ₂_nn hQ₁All hQ₂All
  obtain ⟨CΓ, hCΓ, hΓAll⟩ :=
    DeTurckCoefficients.christoffel_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll Q₁ hQ₁_nn hQ₁All
  obtain ⟨CdΓ, hCdΓ, hdΓAll⟩ :=
    DeTurckCoefficients.christoffelD_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll
      Q₁ hQ₁_nn hQ₁All Q₂ hQ₂_nn hQ₂All
  obtain ⟨Cd2Γ, hCd2Γ, hd2ΓAll⟩ :=
    DeTurckCoefficients.christD2_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll
      Q₁ Q₂ Q₃ hQ₁_nn hQ₂_nn hQ₃_nn hQ₁All hQ₂All hQ₃All
  let n : ℝ := Module.finrank ℝ E
  let D : ℝ := n ^ 2 * Mb ^ 2 * Q₁
  let P : ℝ := 2 * CΓ
  let R : ℝ := 2 * CdΓ
  let S : ℝ := 2 * Cd2Γ
  let V : ℝ := n ^ 2 * Mb * P
  let DV : ℝ := n ^ 2 * (D * P + Mb * R)
  let D2V : ℝ := n ^ 2 * (T * P + 2 * D * R + Mb * S)
  let RicD : ℝ := n * (2 * Cd2Γ + 4 * n * (CΓ * CdΓ))
  let LieD : ℝ := n * (3 * DV * Q₁ + V * Q₂ + 2 * Q₀ * D2V)
  let C : ℝ := 2 * RicD + LieD + 1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hDV : 0 ≤ DV := by dsimp [DV]; positivity
  have hD2V : 0 ≤ D2V := by dsimp [D2V]; positivity
  have hRicD : 0 ≤ RicD := by dsimp [RicD]; positivity
  have hLieD : 0 ≤ LieD := by dsimp [LieD]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro α hα k b hb d i j
  have hbBase : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hbSource : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hbBase
  have hleft : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hbSource
  have hy : extChartAt I α b ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hbSource)
  have hMbG : ∀ a c : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) (gSeq k) α a c (extChartAt I α b)| ≤ Mb := by
    intro a c
    rw [chartInvGramOnE_def, hleft]
    simpa [gAll] using hMbAll α hα (some k) b hb a c
  have hDG : ∀ m a c : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m
        (chartInvGramOnE (I := I) (gSeq k) α a c) (extChartAt I α b)| ≤ D := by
    intro m a c
    simpa [D, n] using DeTurckCoefficients.invGramD_abs_le
      (I := I) (M := M) (gSeq k) α hy hMb.le hMbG
      (hQ₁ α hα k b hb) m a c
  have hTG : ∀ e m a c : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (partialDeriv (E := E) m
          (chartInvGramOnE (I := I) (gSeq k) α a c)) (extChartAt I α b)| ≤ T := by
    intro e m a c
    simpa [gAll] using hTAll α hα (some k) b hb e m a c
  have hΓG : ∀ a c l : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) (gSeq k) α a c l (extChartAt I α b)| ≤ CΓ := by
    intro a c l
    simpa [gAll] using hΓAll α hα (some k) b hb a c l
  have hΓBase : ∀ a c l : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) gBase α a c l (extChartAt I α b)| ≤ CΓ := by
    intro a c l
    simpa [gAll] using hΓAll α hα none b hb a c l
  have hdΓG : ∀ m a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m
        (chartChristoffel (I := I) (gSeq k) α a c l) (extChartAt I α b)| ≤ CdΓ := by
    intro m a c l
    simpa [gAll] using hdΓAll α hα (some k) b hb m a c l
  have hdΓBase : ∀ m a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m
        (chartChristoffel (I := I) gBase α a c l) (extChartAt I α b)| ≤ CdΓ := by
    intro m a c l
    simpa [gAll] using hdΓAll α hα none b hb m a c l
  have hd2ΓG : ∀ e m a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (partialDeriv (E := E) m
          (chartChristoffel (I := I) (gSeq k) α a c l)) (extChartAt I α b)| ≤ Cd2Γ := by
    intro e m a c l
    simpa [gAll] using hd2ΓAll α hα (some k) b hb e m a c l
  have hd2ΓBase : ∀ e m a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (partialDeriv (E := E) m
          (chartChristoffel (I := I) gBase α a c l)) (extChartAt I α b)| ≤ Cd2Γ := by
    intro e m a c l
    simpa [gAll] using hd2ΓAll α hα none b hb e m a c l
  have hΓdiff : ∀ a c l : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) (gSeq k) α a c l (extChartAt I α b) -
        chartChristoffel (I := I) gBase α a c l (extChartAt I α b)| ≤ P := by
    intro a c l
    calc
      |_ - _| ≤ |_| + |_| := abs_sub _ _
      _ ≤ CΓ + CΓ := add_le_add (hΓG a c l) (hΓBase a c l)
      _ = P := by dsimp [P]; ring
  have hdΓdiff : ∀ m a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m
          (chartChristoffel (I := I) (gSeq k) α a c l) (extChartAt I α b) -
        partialDeriv (E := E) m
          (chartChristoffel (I := I) gBase α a c l) (extChartAt I α b)| ≤ R := by
    intro m a c l
    calc
      |_ - _| ≤ |_| + |_| := abs_sub _ _
      _ ≤ CdΓ + CdΓ := add_le_add (hdΓG m a c l) (hdΓBase m a c l)
      _ = R := by dsimp [R]; ring
  have hd2Γdiff : ∀ e m a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
          (partialDeriv (E := E) m
            (chartChristoffel (I := I) (gSeq k) α a c l)) (extChartAt I α b) -
        partialDeriv (E := E) e
          (partialDeriv (E := E) m
            (chartChristoffel (I := I) gBase α a c l)) (extChartAt I α b)| ≤ S := by
    intro e m a c l
    calc
      |_ - _| ≤ |_| + |_| := abs_sub _ _
      _ ≤ Cd2Γ + Cd2Γ := add_le_add (hd2ΓG e m a c l) (hd2ΓBase e m a c l)
      _ = S := by dsimp [S]; ring
  have hVF : ∀ l : Fin (Module.finrank ℝ E),
      |chartDeTurckVFComp (I := I) (gSeq k) gBase α l (extChartAt I α b)| ≤ V := by
    intro l
    simpa [V, n] using DeTurckCoefficients.deTurckVF_abs_le
      (I := I) (M := M) (gSeq k) gBase α (extChartAt I α b) l hMb.le hMbG
      (fun a c => hΓdiff a c l)
  have hVFD : ∀ m l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m
        (chartDeTurckVFComp (I := I) (gSeq k) gBase α l) (extChartAt I α b)| ≤ DV := by
    intro m l
    simpa [DV, n] using DeTurckCoefficients.deTurckVFD_abs_le
      (I := I) (M := M) (gSeq k) gBase α hy m l hD hMb.le
      (fun a c => hDG m a c) (fun a c => hΓdiff a c l) hMbG
      (fun a c => hdΓdiff m a c l)
  have hVFD2 : ∀ e m l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (partialDeriv (E := E) m
          (chartDeTurckVFComp (I := I) (gSeq k) gBase α l)) (extChartAt I α b)| ≤ D2V := by
    intro e m l
    simpa [D2V, n] using DeTurckCoefficients.deTurckVFD2_le
      (I := I) (M := M) (gSeq k) gBase α hy e m l hMb.le hD hT
      hMbG hDG hTG (fun a c => hΓdiff a c l)
      (fun r a c => hdΓdiff r a c l) (fun q r a c => hd2Γdiff q r a c l)
  have hRicci :
      |partialDeriv (E := E) d
        (chartRicciTensor (I := I) (gSeq k) α i j) (extChartAt I α b)| ≤ RicD := by
    simpa [RicD, n] using DeTurckCoefficients.chartRicciD_abs_le
      (I := I) (M := M) (gSeq k) α hy d i j hCΓ hCdΓ hΓG hdΓG hd2ΓG
  have hLie :
      |partialDeriv (E := E) d
        (chartLieDeTurckComp (I := I) (gSeq k) gBase α i j) (extChartAt I α b)| ≤ LieD := by
    simpa [LieD, n] using DeTurckCoefficients.chartLieD_abs_le
      (I := I) (M := M) (gSeq k) gBase α hy d i j
      hQ₀_nn hQ₁_nn hV hDV (hQ₀ α hα k b hb) (hQ₁ α hα k b hb)
      (hQ₂ α hα k b hb) hVF hVFD hVFD2
  refine (DeTurckCoefficients.chartRHSD_abs_le
    (I := I) (M := M) gBase (gSeq k) α d i j hy hRicci hLie).trans ?_
  dsimp [C]
  linarith

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
