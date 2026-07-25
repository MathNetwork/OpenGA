import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSAbsoluteBound







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




omit [NeZero (Module.finrank ℝ E)] in
theorem chartRHS_pou_lip
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
        ∀ c m a q : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) c
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) (gSeq k) α a q)) (extChartAt I α b)| ≤ Q₂)
    (hQ₂Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ c m a q : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) c
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) gBase α a q)) (extChartAt I α b)| ≤ Q₂) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k₁ k₂ : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ i j : Fin (Module.finrank ℝ E),
            |chartDeTurckRHSComp (I := I) gBase (gSeq k₁) α i j (extChartAt I α b) -
              chartDeTurckRHSComp (I := I) gBase (gSeq k₂) α i j (extChartAt I α b)| ≤
                C * chartMetricJet2DiffSup (I := I) (M := M)
                  (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
  classical
  obtain ⟨Cric, hCric_pos, hCric⟩ :=
    DeTurckCoefficients.chartRicci_pou_lip
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
      Q₁ hQ₁_nn hQ₁ Q₂ hQ₂_nn hQ₂
  obtain ⟨Clie, hClie_pos, hClie⟩ :=
    DeTurckCoefficients.chartLie_pou_lip
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
      Q₀ hQ₀_nn hQ₀ Q₁ hQ₁_nn hQ₁ hQ₁Base Q₂ hQ₂_nn hQ₂ hQ₂Base
  refine ⟨2 * Cric + Clie, by positivity, ?_⟩
  intro α hα k₁ k₂ b hb i j
  have hsplit :
      chartDeTurckRHSComp (I := I) gBase (gSeq k₁) α i j (extChartAt I α b) -
          chartDeTurckRHSComp (I := I) gBase (gSeq k₂) α i j (extChartAt I α b) =
        (-2 : ℝ) *
            (chartRicciTensor (I := I) (gSeq k₁) α i j (extChartAt I α b) -
              chartRicciTensor (I := I) (gSeq k₂) α i j (extChartAt I α b)) +
          (chartLieDeTurckComp (I := I) (gSeq k₁) gBase α i j (extChartAt I α b) -
            chartLieDeTurckComp (I := I) (gSeq k₂) gBase α i j (extChartAt I α b)) := by
    rw [chartDeTurckRHSComp_def, chartDeTurckRHSComp_def]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have hric := hCric α hα k₁ k₂ b hb i j
  have hlie := hClie α hα k₁ k₂ b hb i j
  calc
    |(-2 : ℝ) *
          (chartRicciTensor (I := I) (gSeq k₁) α i j (extChartAt I α b) -
            chartRicciTensor (I := I) (gSeq k₂) α i j (extChartAt I α b))| +
        |chartLieDeTurckComp (I := I) (gSeq k₁) gBase α i j (extChartAt I α b) -
          chartLieDeTurckComp (I := I) (gSeq k₂) gBase α i j (extChartAt I α b)|
      ≤ 2 * (Cric * chartMetricJet2DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b)) +
        Clie * chartMetricJet2DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
        apply add_le_add
        · rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
          have htwo : (0 : ℝ) ≤ 2 := by norm_num
          exact mul_le_mul_of_nonneg_left hric htwo
        · exact hlie
    _ = (2 * Cric + Clie) * chartMetricJet2DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by ring




omit [NeZero (Module.finrank ℝ E)] in
theorem chartRHS_pou_bnd
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
    (hQ₀Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ a c : Fin (Module.finrank ℝ E),
          |chartGramOnE (I := I) gBase α a c (extChartAt I α b)| ≤ Q₀)
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
        ∀ c m a q : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) c
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) (gSeq k) α a q)) (extChartAt I α b)| ≤ Q₂)
    (hQ₂Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ c m a q : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) c
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) gBase α a q)) (extChartAt I α b)| ≤ Q₂) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ i j : Fin (Module.finrank ℝ E),
            |chartDeTurckRHSComp (I := I) gBase (gSeq k) α i j
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
  have hQ₀All : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : Option ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ a c : Fin (Module.finrank ℝ E),
          |chartGramOnE (I := I) (gAll k) α a c (extChartAt I α b)| ≤ Q₀ := by
    intro α hα k b hb a c
    cases k with
    | none => simpa [gAll] using hQ₀Base α hα b hb a c
    | some k => simpa [gAll] using hQ₀ α hα k b hb a c
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
        ∀ c m a q : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) c
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) (gAll k) α a q)) (extChartAt I α b)| ≤ Q₂ := by
    intro α hα k b hb c m a q
    cases k with
    | none => simpa [gAll] using hQ₂Base α hα b hb c m a q
    | some k => simpa [gAll] using hQ₂ α hα k b hb c m a q
  obtain ⟨Mb, hMb, hMbAll⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll
  obtain ⟨CΓ, hCΓ, hΓAll⟩ :=
    DeTurckCoefficients.christoffel_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll Q₁ hQ₁_nn hQ₁All
  obtain ⟨CdΓ, hCdΓ, hdΓAll⟩ :=
    DeTurckCoefficients.christoffelD_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll
      Q₁ hQ₁_nn hQ₁All Q₂ hQ₂_nn hQ₂All
  let n : ℝ := Module.finrank ℝ E
  let D : ℝ := n ^ 2 * Mb ^ 2 * Q₁
  let P : ℝ := 2 * CΓ
  let R : ℝ := 2 * CdΓ
  let V : ℝ := n ^ 2 * Mb * P
  let DV : ℝ := n ^ 2 * (D * P + Mb * R)
  let RicB : ℝ := n * (2 * CdΓ + 2 * n * CΓ ^ 2)
  let LieB : ℝ := n * (V * Q₁ + 2 * Q₀ * DV)
  let C : ℝ := 2 * RicB + LieB + 1
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hDV : 0 ≤ DV := by dsimp [DV]; positivity
  have hRicB : 0 ≤ RicB := by dsimp [RicB]; positivity
  have hLieB : 0 ≤ LieB := by dsimp [LieB]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro α hα k b hb i j
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
  have hDG : ∀ m a c : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m
        (chartInvGramOnE (I := I) (gSeq k) α a c) (extChartAt I α b)| ≤ D := by
    intro m a c
    simpa [D, n] using DeTurckCoefficients.invGramD_abs_le
      (I := I) (M := M) (gSeq k) α hy hMb.le hMbG
      (fun mm aa cc => hQ₁ α hα k b hb mm aa cc) m a c
  have hΓdiff : ∀ a c l : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) (gSeq k) α a c l (extChartAt I α b) -
        chartChristoffel (I := I) gBase α a c l (extChartAt I α b)| ≤ P := by
    intro a c l
    rw [sub_eq_add_neg]
    calc
      |chartChristoffel (I := I) (gSeq k) α a c l (extChartAt I α b) +
          -chartChristoffel (I := I) gBase α a c l (extChartAt I α b)|
          ≤ |chartChristoffel (I := I) (gSeq k) α a c l (extChartAt I α b)| +
            |-chartChristoffel (I := I) gBase α a c l (extChartAt I α b)| :=
              abs_add_le _ _
      _ = |chartChristoffel (I := I) (gSeq k) α a c l (extChartAt I α b)| +
            |chartChristoffel (I := I) gBase α a c l (extChartAt I α b)| := by
              rw [abs_neg]
      _ ≤ CΓ + CΓ := add_le_add (hΓG a c l) (hΓBase a c l)
      _ = P := by dsimp [P]; ring
  have hdΓdiff : ∀ m a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m
          (chartChristoffel (I := I) (gSeq k) α a c l) (extChartAt I α b) -
        partialDeriv (E := E) m
          (chartChristoffel (I := I) gBase α a c l) (extChartAt I α b)| ≤ R := by
    intro m a c l
    rw [sub_eq_add_neg]
    calc
      |partialDeriv (E := E) m
          (chartChristoffel (I := I) (gSeq k) α a c l) (extChartAt I α b) +
          -partialDeriv (E := E) m
            (chartChristoffel (I := I) gBase α a c l) (extChartAt I α b)|
          ≤ |partialDeriv (E := E) m
              (chartChristoffel (I := I) (gSeq k) α a c l) (extChartAt I α b)| +
            |-partialDeriv (E := E) m
              (chartChristoffel (I := I) gBase α a c l) (extChartAt I α b)| :=
                abs_add_le _ _
      _ = |partialDeriv (E := E) m
              (chartChristoffel (I := I) (gSeq k) α a c l) (extChartAt I α b)| +
            |partialDeriv (E := E) m
              (chartChristoffel (I := I) gBase α a c l) (extChartAt I α b)| := by
                rw [abs_neg]
      _ ≤ CdΓ + CdΓ := add_le_add (hdΓG m a c l) (hdΓBase m a c l)
      _ = R := by dsimp [R]; ring
  have hvf : ∀ l : Fin (Module.finrank ℝ E),
      |chartDeTurckVFComp (I := I) (gSeq k) gBase α l (extChartAt I α b)| ≤ V := by
    intro l
    simpa [V, n] using DeTurckCoefficients.deTurckVF_abs_le
      (I := I) (M := M) (gSeq k) gBase α (extChartAt I α b) l
      hMb.le hMbG (hΓdiff (l := l))
  have hdvf : ∀ m l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m
        (chartDeTurckVFComp (I := I) (gSeq k) gBase α l) (extChartAt I α b)| ≤ DV := by
    intro m l
    simpa [DV, n] using DeTurckCoefficients.deTurckVFD_abs_le
      (I := I) (M := M) (gSeq k) gBase α hy m l hD hMb.le
      (hDG m) (hΓdiff (l := l)) hMbG (hdΓdiff m (l := l))
  have hRic :
      |chartRicciTensor (I := I) (gSeq k) α i j (extChartAt I α b)| ≤ RicB := by
    simpa [RicB, n] using DeTurckCoefficients.chartRicci_abs_le
      (I := I) (M := M) (gSeq k) α i j (extChartAt I α b) hCΓ hΓG hdΓG
  have hLie :
      |chartLieDeTurckComp (I := I) (gSeq k) gBase α i j (extChartAt I α b)| ≤ LieB := by
    simpa [LieB, n] using DeTurckCoefficients.chartLie_abs_le
      (I := I) (M := M) (gSeq k) gBase α i j (extChartAt I α b)
      hQ₀_nn hQ₁_nn hV hDV (hQ₀ α hα k b hb)
      (hQ₁ α hα k b hb) hvf hdvf
  have hRHS := DeTurckCoefficients.chartRHS_abs_le
    (I := I) (M := M) gBase (gSeq k) α i j (extChartAt I α b) hRic hLie
  exact hRHS.trans (by dsimp [C]; linarith)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
