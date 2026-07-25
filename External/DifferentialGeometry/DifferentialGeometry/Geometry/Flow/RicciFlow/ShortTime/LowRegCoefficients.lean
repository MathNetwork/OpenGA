import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSUniformFamily
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSFirstDerivativeUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.GramInvUniformEigenvalueLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconv









namespace DifferentialGeometry.PDE.RicciFlow

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [T2Space M] [SigmaCompactSpace M]



structure LowRegCoeff where
  ellMin : ℝ
  ellMax : ℝ
  gram0 : ℝ
  gram1 : ℝ
  gram2 : ℝ
  gram3 : ℝ
  rhsBound : ℝ
  rhsD1Bound : ℝ
  rhsLip : ℝ
  rhsD1Lip : ℝ





structure IsLowRegCoeff {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M) (D : LowRegCoeff) : Prop where
  ellMin_pos : 0 < D.ellMin
  ellMax_pos : 0 < D.ellMax
  gram0_nonneg : 0 ≤ D.gram0
  gram1_nonneg : 0 ≤ D.gram1
  gram2_nonneg : 0 ≤ D.gram2
  gram3_nonneg : 0 ≤ D.gram3
  rhsBound_pos : 0 < D.rhsBound
  rhsD1Bound_pos : 0 < D.rhsD1Bound
  rhsLip_pos : 0 < D.rhsLip
  rhsD1Lip_pos : 0 < D.rhsD1Lip
  elliptic :
    ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          D.ellMin * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) ≤
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) (gSeq k) α b i j * ξ i * ξ j ∧
            (∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) (gSeq k) α b i j * ξ i * ξ j) ≤
              D.ellMax * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2)
  gram0_bound :
    ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ i j : Fin (Module.finrank ℝ E),
          |chartGramOnE (I := I) (gSeq k) α i j (extChartAt I α b)| ≤ D.gram0
  gram1_bound :
    ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m i j : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α i j)
              (extChartAt I α b)| ≤ D.gram1
  gram2_bound :
    ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ c m i j : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) c
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) (gSeq k) α i j)) (extChartAt I α b)| ≤ D.gram2
  gram3_bound :
    ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ d c m i j : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) c
              (partialDeriv (E := E) m
                (chartGramOnE (I := I) (gSeq k) α i j))) (extChartAt I α b)| ≤ D.gram3
  rhs_bound :
    ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ i j : Fin (Module.finrank ℝ E),
          |chartDeTurckRHSComp (I := I) gBase (gSeq k) α i j
            (extChartAt I α b)| ≤ D.rhsBound
  rhs_d1_bound :
    ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ d i j : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) d
            (chartDeTurckRHSComp (I := I) gBase (gSeq k) α i j)
              (extChartAt I α b)| ≤ D.rhsD1Bound
  rhs_lipschitz :
    ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k₁ k₂ : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ i j : Fin (Module.finrank ℝ E),
          |chartDeTurckRHSComp (I := I) gBase (gSeq k₁) α i j (extChartAt I α b) -
            chartDeTurckRHSComp (I := I) gBase (gSeq k₂) α i j (extChartAt I α b)| ≤
              D.rhsLip * chartMetricJet2DiffSup (I := I) (M := M)
                (gSeq k₁) (gSeq k₂) α (extChartAt I α b)
  rhs_d1_lipschitz :
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
              D.rhsD1Lip * metricJet3DiffSup (I := I) (M := M)
                (gSeq k₁) (gSeq k₂) α (extChartAt I α b)




theorem exists_low_reg_coeff {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (B : ℝ)
    (hbdd : ∀ k : ι, ∀ q : ℕ, q ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gSeq k) gBase B) :
    ∃ D : LowRegCoeff, IsLowRegCoeff (I := I) gBase gSeq D := by
  classical
  obtain ⟨B₀, hB₀⟩ :=
    metricCovDerivNorm_bddOn (I := I) isCompact_univ 0 gBase gBase
  obtain ⟨B₁, hB₁⟩ :=
    metricCovDerivNorm_bddOn (I := I) isCompact_univ 1 gBase gBase
  obtain ⟨B₂, hB₂⟩ :=
    metricCovDerivNorm_bddOn (I := I) isCompact_univ 2 gBase gBase
  obtain ⟨B₃, hB₃⟩ :=
    metricCovDerivNorm_bddOn (I := I) isCompact_univ 3 gBase gBase
  let BBase : ℝ := max (max B₀ B₁) (max B₂ B₃)
  have hbase : ∀ q : ℕ, q ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q gBase gBase BBase := by
    intro q hq x hx
    interval_cases q
    · exact (hB₀ x hx).trans
        ((le_max_left B₀ B₁).trans (le_max_left (max B₀ B₁) (max B₂ B₃)))
    · exact (hB₁ x hx).trans
        ((le_max_right B₀ B₁).trans (le_max_left (max B₀ B₁) (max B₂ B₃)))
    · exact (hB₂ x hx).trans
        ((le_max_left B₂ B₃).trans (le_max_right (max B₀ B₁) (max B₂ B₃)))
    · exact (hB₃ x hx).trans
        ((le_max_right B₂ B₃).trans (le_max_right (max B₀ B₁) (max B₂ B₃)))
  let BAll : ℝ := max B BBase
  let gAll : Option ι → SmoothRiemannianMetric I M := fun k => k.elim gBase gSeq
  have hAllBdd : ∀ k : Option ι, ∀ q : ℕ, q ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gAll k) gBase BAll := by
    intro k q hq
    cases k with
    | none =>
        intro x hx
        exact (hbase q hq x hx).trans (le_max_right B BBase)
    | some k =>
        intro x hx
        exact (hbdd k q hq x hx).trans (le_max_left B BBase)
  obtain ⟨Q₀, hQ₀_nn, hQ₀⟩ :=
    chartGram_pou_bnd (I := I) gBase gAll BAll
      (fun k => hAllBdd k 0 (by omega))
  obtain ⟨Q₁, hQ₁_nn, hQ₁⟩ :=
    chartGram_pou_d1 (I := I) gBase gAll BAll
      (fun k q hq => hAllBdd k q (by omega))
  obtain ⟨Q₂, hQ₂_nn, hQ₂⟩ :=
    chartGram_pou_d2 (I := I) gBase gAll BAll
      (fun k q hq => hAllBdd k q (by omega))
  obtain ⟨Q₃, hQ₃_nn, hQ₃⟩ :=
    chartGram_pou_d3 (I := I) gBase gAll BAll hAllBdd
  have hQ₀Seq : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ i j : Fin (Module.finrank ℝ E),
          |chartGramOnE (I := I) (gSeq k) α i j (extChartAt I α b)| ≤ Q₀ := by
    intro α hα k b hb i j
    simpa [gAll] using hQ₀ α hα (some k) b hb i j
  have hQ₀Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ i j : Fin (Module.finrank ℝ E),
          |chartGramOnE (I := I) gBase α i j (extChartAt I α b)| ≤ Q₀ := by
    intro α hα b hb i j
    simpa [gAll] using hQ₀ α hα none b hb i j
  have hQ₁Seq : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m i j : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α i j)
              (extChartAt I α b)| ≤ Q₁ := by
    intro α hα k b hb m i j
    simpa [gAll] using hQ₁ α hα (some k) b hb m i j
  have hQ₁Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m i j : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) gBase α i j)
              (extChartAt I α b)| ≤ Q₁ := by
    intro α hα b hb m i j
    simpa [gAll] using hQ₁ α hα none b hb m i j
  have hQ₂Seq : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ c m i j : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) c
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) (gSeq k) α i j)) (extChartAt I α b)| ≤ Q₂ := by
    intro α hα k b hb c m i j
    simpa [gAll] using hQ₂ α hα (some k) b hb c m i j
  have hQ₂Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ c m i j : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) c
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) gBase α i j)) (extChartAt I α b)| ≤ Q₂ := by
    intro α hα b hb c m i j
    simpa [gAll] using hQ₂ α hα none b hb c m i j
  have hQ₃Seq : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ d c m i j : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) c
              (partialDeriv (E := E) m
                (chartGramOnE (I := I) (gSeq k) α i j))) (extChartAt I α b)| ≤ Q₃ := by
    intro α hα k b hb d c m i j
    simpa [gAll] using hQ₃ α hα (some k) b hb d c m i j
  have hQ₃Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ d c m i j : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) c
              (partialDeriv (E := E) m
                (chartGramOnE (I := I) gBase α i j))) (extChartAt I α b)| ≤ Q₃ := by
    intro α hα b hb d c m i j
    simpa [gAll] using hQ₃ α hα none b hb d c m i j
  obtain ⟨ellMin, ellMax, hellMin, hellMax, hell⟩ :=
    chartInvGram_pou_eqv (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  obtain ⟨Crhs, hCrhs, hRhs⟩ :=
    chartRHS_pou_lip (I := I) (M := M) gBase gSeq Λ hΛ hequiv
      Q₀ hQ₀_nn hQ₀Seq Q₁ hQ₁_nn hQ₁Seq hQ₁Base
      Q₂ hQ₂_nn hQ₂Seq hQ₂Base
  obtain ⟨CrhsBound, hCrhsBound, hRhsBound⟩ :=
    chartRHS_pou_bnd (I := I) (M := M) gBase gSeq Λ hΛ hequiv
      Q₀ hQ₀_nn hQ₀Seq hQ₀Base Q₁ hQ₁_nn hQ₁Seq hQ₁Base
      Q₂ hQ₂_nn hQ₂Seq hQ₂Base
  obtain ⟨CrhsD1, hCrhsD1, hRhsD1⟩ :=
    chartRHSD_pou_bnd (I := I) (M := M) gBase gSeq Λ hΛ hequiv
      Q₀ hQ₀_nn hQ₀Seq Q₁ hQ₁_nn hQ₁Seq hQ₁Base
      Q₂ hQ₂_nn hQ₂Seq hQ₂Base Q₃ hQ₃_nn hQ₃Seq hQ₃Base
  obtain ⟨CrhsD1Lip, hCrhsD1Lip, hRhsD1Lip⟩ :=
    chartRHSD_pou_lip (I := I) (M := M) gBase gSeq Λ hΛ hequiv
      Q₀ hQ₀_nn hQ₀Seq Q₁ hQ₁_nn hQ₁Seq hQ₁Base
      Q₂ hQ₂_nn hQ₂Seq hQ₂Base Q₃ hQ₃_nn hQ₃Seq hQ₃Base
  let D : LowRegCoeff :=
    { ellMin := ellMin
      ellMax := ellMax
      gram0 := Q₀
      gram1 := Q₁
      gram2 := Q₂
      gram3 := Q₃
      rhsBound := CrhsBound
      rhsD1Bound := CrhsD1
      rhsLip := Crhs
      rhsD1Lip := CrhsD1Lip }
  refine ⟨D, ?_⟩
  exact
    { ellMin_pos := hellMin
      ellMax_pos := hellMax
      gram0_nonneg := hQ₀_nn
      gram1_nonneg := hQ₁_nn
      gram2_nonneg := hQ₂_nn
      gram3_nonneg := hQ₃_nn
      rhsBound_pos := hCrhsBound
      rhsD1Bound_pos := hCrhsD1
      rhsLip_pos := hCrhs
      rhsD1Lip_pos := hCrhsD1Lip
      elliptic := hell
      gram0_bound := hQ₀Seq
      gram1_bound := hQ₁Seq
      gram2_bound := hQ₂Seq
      gram3_bound := hQ₃Seq
      rhs_bound := hRhsBound
      rhs_d1_bound := hRhsD1
      rhs_lipschitz := hRhs
      rhs_d1_lipschitz := hRhsD1Lip }

end DifferentialGeometry.PDE.RicciFlow
