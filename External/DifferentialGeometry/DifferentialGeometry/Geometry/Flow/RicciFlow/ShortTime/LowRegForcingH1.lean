import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegCoefficients
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.UniformL2FromRaw
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSSectionChartComponentIdentity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.MetricJet3Intrinsic
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetInput
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound








noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem rhs_raw_eq
    (gBase g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) gBase 0 2
        (deTurckRHSSectionBg (I := I) gBase g) α Idx Jdx b =
      chartDeTurckRHSComp (I := I) gBase g α (Jdx 0) (Jdx 1)
        (extChartAt I α b) := by
  simpa only [chartDeTurckRHSComp_def] using
    tensorChartComponentRaw_deTurckRHSSectionBg_eq_chartRicciLie
      (I := I) (M := M) gBase g α hb Idx Jdx

omit [NeZero (Module.finrank ℝ E)] in
private theorem rhs_raw_sub_eq
    (gBase g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) gBase 0 2
        (deTurckRHSSectionBg (I := I) gBase g₁ -
          deTurckRHSSectionBg (I := I) gBase g₂) α Idx Jdx b =
      chartDeTurckRHSComp (I := I) gBase g₁ α (Jdx 0) (Jdx 1)
          (extChartAt I α b) -
        chartDeTurckRHSComp (I := I) gBase g₂ α (Jdx 0) (Jdx 1)
          (extChartAt I α b) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ
      (deTurckRHSSectionBg (I := I) gBase g₂),
    tensorChartComponentRaw_add, tensorChartComponentRaw_smul,
    rhs_raw_eq (I := I) (M := M) gBase g₁ α hb,
    rhs_raw_eq (I := I) (M := M) gBase g₂ α hb]
  simp only [smul_eq_mul, neg_one_mul, sub_eq_add_neg]

omit [SigmaCompactSpace M] in
private theorem rhs_pull_eq
    (gBase g : SmoothRiemannianMetric I M) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    Set.EqOn
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) gBase 0 2
          (deTurckRHSSectionBg (I := I) gBase g) α
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx))
      (chartDeTurckRHSComp (I := I) gBase g α (Jdx 0) (Jdx 1) ∘
        (toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  let b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
  have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target
      (I := I) hy
  have hb_src : b ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy_target
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α :=
    (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source
      (I := I) α b).2 hb_src
  have hφ : extChartAt I α b = (toEuclidean (E := E)).symm y :=
    (extChartAt I α).right_inv hy_target
  rw [rhs_raw_eq (I := I) (M := M) gBase g α hb_good]
  simp only [Function.comp_apply, hφ]

omit [SigmaCompactSpace M] in
private theorem rhs_partial_eq
    (gBase g : SmoothRiemannianMetric I M) (α : M)
    (d : Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) d
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) gBase 0 2
            (deTurckRHSSectionBg (I := I) gBase g) α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx)) y =
      partialDeriv (E := E) d
        (chartDeTurckRHSComp (I := I) gBase g α (Jdx 0) (Jdx 1))
        ((toEuclidean (E := E)).symm y) := by
  have hderiv := euclidPartial_congr_of_eqOn_isOpen (E := E) d
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (rhs_pull_eq (I := I) (M := M) gBase g α Jdx) hy
  calc
    euclidPartial (E := E) d
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) gBase 0 2
            (deTurckRHSSectionBg (I := I) gBase g) α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx)) y
        = euclidPartial (E := E) d
            (chartDeTurckRHSComp (I := I) gBase g α (Jdx 0) (Jdx 1) ∘
              (toEuclidean (E := E)).symm) y := hderiv
    _ = ((partialDeriv (E := E) d
          (chartDeTurckRHSComp (I := I) gBase g α (Jdx 0) (Jdx 1))) ∘
            (toEuclidean (E := E)).symm) y :=
      (congrFun (partialDeriv_comp_toEuclidean_symm_eq_euclidPartial
        (E := E) d
        (chartDeTurckRHSComp (I := I) gBase g α (Jdx 0) (Jdx 1))) y).symm
    _ = _ := rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private theorem rawComp_sub
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (b : M) :
    tensorChartComponentRaw (I := I) (M := M) g r s (S₁ - S₂) α Idx Jdx b =
      tensorChartComponentRaw (I := I) (M := M) g r s S₁ α Idx Jdx b -
        tensorChartComponentRaw (I := I) (M := M) g r s S₂ α Idx Jdx b := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ S₂,
    tensorChartComponentRaw_add, tensorChartComponentRaw_smul]
  simp only [smul_eq_mul, neg_one_mul, sub_eq_add_neg]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private theorem lowerTerm_sub
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (y : EuclN) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s (S₁ - S₂) α m Idx Jdx y =
      covDerivLowerOrderTerm (I := I) (M := M) g r s S₁ α m Idx Jdx y -
        covDerivLowerOrderTerm (I := I) (M := M) g r s S₂ α m Idx Jdx y := by
  classical
  rw [covDerivLowerOrderTerm_def, covDerivLowerOrderTerm_def,
    covDerivLowerOrderTerm_def, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [rawComp_sub (I := I) (M := M)]
  ring

private theorem rhs_cov_raw_eq
    (gBase g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb_src : b ∈ (extChartAt I α).source)
    (Kdx : Fin 3 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) gBase 0 3
        (covGrad (I := I) (M := M) gBase 0 2
          (deTurckRHSSectionBg (I := I) gBase g)) α
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Kdx b =
      partialDeriv (E := E) (Kdx 0)
          (chartDeTurckRHSComp (I := I) gBase g α
            ((Matrix.vecTail Kdx) 0) ((Matrix.vecTail Kdx) 1))
          (extChartAt I α b) +
        covDerivLowerOrderTerm (I := I) (M := M) gBase 0 2
          (deTurckRHSSectionBg (I := I) gBase g) α (Kdx 0)
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E)))
          (Matrix.vecTail Kdx) (toEuclidean (E := E) (extChartAt I α b)) := by
  let d : Fin (Module.finrank ℝ E) := Kdx 0
  let Jdx : Fin 2 → Fin (Module.finrank ℝ E) := Matrix.vecTail Kdx
  let y : EuclN := toEuclidean (E := E) (extChartAt I α b)
  have hy : y ∈ chartTargetEuclid (I := I) (M := M) α :=
    ⟨extChartAt I α b, (extChartAt I α).map_source hb_src, rfl⟩
  have hround :
      (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = b := by
    dsimp [y]
    simpa using (extChartAt I α).left_inv hb_src
  have hcons : (Fin.cons d Jdx : Fin 3 → Fin (Module.finrank ℝ E)) = Kdx :=
    Fin.cons_self_tail Kdx
  have hinv := euclidPartial_chartPushedRaw_general_eq_covGrad_sub_lowerOrder
    (I := I) (M := M) gBase 2
      (deTurckRHSSectionBg (I := I) gBase g) α d Jdx hy
  rw [hcons, hround] at hinv
  have hderiv := rhs_partial_eq (I := I) (M := M) gBase g α d Jdx hy
  have hyround : (toEuclidean (E := E)).symm y = extChartAt I α b := by
    dsimp [y]
    simp
  rw [hyround] at hderiv
  rw [hderiv] at hinv
  simpa only [d, Jdx, y] using (eq_sub_iff_add_eq.mp hinv).symm



theorem rhs_raw_lip {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M) (D : LowRegCoeff)
    (hD : IsLowRegCoeff (I := I) gBase gSeq D) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k₁ k₂ : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ Idx : Fin 0 → Fin (Module.finrank ℝ E),
            ∀ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
              |tensorChartComponentRaw (I := I) (M := M) gBase 0 2
                (deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
                  deTurckRHSSectionBg (I := I) gBase (gSeq k₂))
                α Idx Jdx b| ≤
                B * ∑ i ∈ Finset.range 3,
                  Real.sqrt (riemannianFiberNormSq (I := I) (M := M)
                    gBase 0 (2 + i) b
                    ((iteratedCovGrad (I := I) gBase 0 2 i
                      (metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
                        metricCcTensor (I := I) (M := M) gBase (gSeq k₂))).toSection b)) := by
  classical
  choose Cjet hCjet hjet using fun α : M =>
    metricJet2_intrinsic (I := I) (M := M) gBase α
  let CjetAll : ℝ :=
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Cjet α
  have hCjetAll : 0 ≤ CjetAll := by
    dsimp [CjetAll]
    exact Finset.sum_nonneg fun α _ => hCjet α
  have hCjet_le : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      Cjet α ≤ CjetAll := by
    intro α hα
    dsimp [CjetAll]
    exact Finset.single_le_sum (fun β _ => hCjet β) hα
  let B : ℝ := D.rhsLip * CjetAll
  have hB : 0 ≤ B := mul_nonneg hD.rhsLip_pos.le hCjetAll
  refine ⟨B, hB, ?_⟩
  intro α hα k₁ k₂ b hb Idx Jdx
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact chartAtlasPOU_isSubordinate I M α hb
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α :=
    (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source
      (I := I) α b).2 hb_src
  set A : ℝ := ∑ i ∈ Finset.range 3,
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M)
      gBase 0 (2 + i) b
      ((iteratedCovGrad (I := I) gBase 0 2 i
        (metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
          metricCcTensor (I := I) (M := M) gBase (gSeq k₂))).toSection b)) with hA_def
  have hA : 0 ≤ A := by
    rw [hA_def]
    exact Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hjet' := hjet α (gSeq k₁) (gSeq k₂) hb
  have hjetAll : chartMetricJet2DiffSup (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b) ≤ CjetAll * A := by
    rw [hA_def]
    exact hjet'.trans (mul_le_mul_of_nonneg_right (hCjet_le α hα)
      (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _))
  rw [rhs_raw_sub_eq (I := I) (M := M) gBase (gSeq k₁) (gSeq k₂) α hb_good]
  calc
    |chartDeTurckRHSComp (I := I) gBase (gSeq k₁) α (Jdx 0) (Jdx 1)
          (extChartAt I α b) -
        chartDeTurckRHSComp (I := I) gBase (gSeq k₂) α (Jdx 0) (Jdx 1)
          (extChartAt I α b)|
        ≤ D.rhsLip * chartMetricJet2DiffSup (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α (extChartAt I α b) :=
      hD.rhs_lipschitz α hα k₁ k₂ b hb (Jdx 0) (Jdx 1)
    _ ≤ D.rhsLip * (CjetAll * A) :=
      mul_le_mul_of_nonneg_left hjetAll hD.rhsLip_pos.le
    _ = B * ∑ i ∈ Finset.range 3,
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M)
            gBase 0 (2 + i) b
            ((iteratedCovGrad (I := I) gBase 0 2 i
              (metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
                metricCcTensor (I := I) (M := M) gBase (gSeq k₂))).toSection b)) := by
      rw [hA_def]
      dsimp [B]
      ring



theorem rhs_cov_lip {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M) (D : LowRegCoeff)
    (hD : IsLowRegCoeff (I := I) gBase gSeq D) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k₁ k₂ : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ Idx : Fin 0 → Fin (Module.finrank ℝ E),
            ∀ Kdx : Fin 3 → Fin (Module.finrank ℝ E),
              |tensorChartComponentRaw (I := I) (M := M) gBase 0 3
                (covGrad (I := I) (M := M) gBase 0 2
                  (deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
                    deTurckRHSSectionBg (I := I) gBase (gSeq k₂)))
                α Idx Kdx b| ≤
                B * ∑ i ∈ Finset.range 4,
                  Real.sqrt (riemannianFiberNormSq (I := I) (M := M)
                    gBase 0 (2 + i) b
                    ((iteratedCovGrad (I := I) gBase 0 2 i
                      (metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
                        metricCcTensor (I := I) (M := M) gBase (gSeq k₂))).toSection b)) := by
  classical
  obtain ⟨B₀, hB₀, hraw₀⟩ := rhs_raw_lip (I := I) (M := M) gBase gSeq D hD
  choose Cjet hCjet hjet using fun α : M =>
    metricJet3_intrinsic (I := I) (M := M) gBase α
  let CjetAll : ℝ :=
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Cjet α
  have hCjetAll : 0 ≤ CjetAll := by
    dsimp [CjetAll]
    exact Finset.sum_nonneg fun α _ => hCjet α
  have hCjet_le : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      Cjet α ≤ CjetAll := by
    intro α hα
    dsimp [CjetAll]
    exact Finset.single_le_sum (fun β _ => hCjet β) hα
  choose Cα hCα hCα_bd using fun α : M =>
    exists_lowerOrderCoeff_uniform_boundR
      (I := I) (M := M) gBase 0 2 α 0
  let CΓ : ℝ := ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Cα α
  have hCΓ : 0 ≤ CΓ := by
    dsimp [CΓ]
    exact Finset.sum_nonneg fun α _ => hCα α
  have hcoeff : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ m : Fin (Module.finrank ℝ E),
        ∀ Idx : Fin 0 → Fin (Module.finrank ℝ E),
          ∀ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
            ∀ p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
                (Fin 2 → Fin (Module.finrank ℝ E)),
              ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
                |covDerivLowerOrderCoeff (I := I) (M := M)
                  gBase 0 2 α m Idx p.1 Jdx p.2 y| ≤ CΓ := by
    intro α hα m Idx Jdx p y hy
    have h := hCα_bd α m Idx Jdx p 0 (by omega) y hy
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    exact h.trans (Finset.single_le_sum (f := Cα)
      (fun β _ => hCα β) hα)
  let L : ℝ :=
    ∑ _p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
      (Fin 2 → Fin (Module.finrank ℝ E)), CΓ * B₀
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Finset.sum_nonneg fun _ _ => mul_nonneg hCΓ hB₀
  let B : ℝ := D.rhsD1Lip * CjetAll + L
  have hB : 0 ≤ B :=
    add_nonneg (mul_nonneg hD.rhsD1Lip_pos.le hCjetAll) hL
  refine ⟨B, hB, ?_⟩
  intro α hα k₁ k₂ b hb Idx Kdx
  have hIdx : Idx = fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E)) :=
    Subsingleton.elim _ _
  subst Idx
  let d : Fin (Module.finrank ℝ E) := Kdx 0
  let Jdx : Fin 2 → Fin (Module.finrank ℝ E) := Matrix.vecTail Kdx
  let y : EuclN := toEuclidean (E := E) (extChartAt I α b)
  set A : ℝ := ∑ i ∈ Finset.range 4,
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M)
      gBase 0 (2 + i) b
      ((iteratedCovGrad (I := I) gBase 0 2 i
        (metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
          metricCcTensor (I := I) (M := M) gBase (gSeq k₂))).toSection b)) with hA_def
  have hA : 0 ≤ A := by
    rw [hA_def]
    exact Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hA3 : (∑ i ∈ Finset.range 3,
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M)
        gBase 0 (2 + i) b
        ((iteratedCovGrad (I := I) gBase 0 2 i
          (metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
            metricCcTensor (I := I) (M := M) gBase (gSeq k₂))).toSection b))) ≤ A := by
    rw [hA_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) ?_
    intro i _ _
    exact Real.sqrt_nonneg _
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact chartAtlasPOU_isSubordinate I M α hb
  have hround :
      (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = b := by
    dsimp [y]
    simpa using (extChartAt I α).left_inv hb_src
  have hyK : y ∈ chartImagePOUTsupport (I := I) (M := M) α := by
    dsimp [y]
    exact ⟨extChartAt I α b, ⟨b, hb, rfl⟩, rfl⟩
  have hjet' := hjet α (gSeq k₁) (gSeq k₂) hb
  have hjetAll : metricJet3DiffSup (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b) ≤ CjetAll * A := by
    rw [hA_def]
    exact hjet'.trans (mul_le_mul_of_nonneg_right (hCjet_le α hα)
      (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _))
  have hlower :
      |covDerivLowerOrderTerm (I := I) (M := M) gBase 0 2
        (deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
          deTurckRHSSectionBg (I := I) gBase (gSeq k₂)) α d
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx y| ≤ L * A := by
    rw [covDerivLowerOrderTerm_def]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      (∑ p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
          (Fin 2 → Fin (Module.finrank ℝ E)),
          |covDerivLowerOrderCoeff (I := I) (M := M) gBase 0 2 α d
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) p.1 Jdx p.2 y *
            tensorChartComponentRaw (I := I) (M := M) gBase 0 2
              (deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
                deTurckRHSSectionBg (I := I) gBase (gSeq k₂)) α p.1 p.2
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))|)
          ≤ ∑ _p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
              (Fin 2 → Fin (Module.finrank ℝ E)), CΓ * (B₀ * A) :=
        Finset.sum_le_sum fun p _ => by
          rw [abs_mul, hround]
          exact mul_le_mul (hcoeff α hα d _ Jdx p y hyK)
            ((hraw₀ α hα k₁ k₂ b hb p.1 p.2).trans
              (mul_le_mul_of_nonneg_left hA3 hB₀))
            (abs_nonneg _) hCΓ
      _ = L * A := by
        dsimp [L]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hrawcov :
      tensorChartComponentRaw (I := I) (M := M) gBase 0 3
          (covGrad (I := I) (M := M) gBase 0 2
            (deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
              deTurckRHSSectionBg (I := I) gBase (gSeq k₂))) α
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Kdx b =
        tensorChartComponentRaw (I := I) (M := M) gBase 0 3
            (covGrad (I := I) (M := M) gBase 0 2
              (deTurckRHSSectionBg (I := I) gBase (gSeq k₁))) α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Kdx b -
          tensorChartComponentRaw (I := I) (M := M) gBase 0 3
            (covGrad (I := I) (M := M) gBase 0 2
              (deTurckRHSSectionBg (I := I) gBase (gSeq k₂))) α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Kdx b := by
    rw [covGrad_sub (I := I) (M := M) gBase 0 2]
    exact rawComp_sub (I := I) (M := M) gBase 0 3 _ _ α _ _ b
  have hcov₁ := rhs_cov_raw_eq (I := I) (M := M)
    gBase (gSeq k₁) α hb_src Kdx
  have hcov₂ := rhs_cov_raw_eq (I := I) (M := M)
    gBase (gSeq k₂) α hb_src Kdx
  have hlower_eq := lowerTerm_sub (I := I) (M := M) gBase 0 2
    (deTurckRHSSectionBg (I := I) gBase (gSeq k₁))
    (deTurckRHSSectionBg (I := I) gBase (gSeq k₂)) α d
    (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx y
  have hcov :
      tensorChartComponentRaw (I := I) (M := M) gBase 0 3
          (covGrad (I := I) (M := M) gBase 0 2
            (deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
              deTurckRHSSectionBg (I := I) gBase (gSeq k₂))) α
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Kdx b =
        (partialDeriv (E := E) d
            (chartDeTurckRHSComp (I := I) gBase (gSeq k₁) α (Jdx 0) (Jdx 1))
              (extChartAt I α b) -
          partialDeriv (E := E) d
            (chartDeTurckRHSComp (I := I) gBase (gSeq k₂) α (Jdx 0) (Jdx 1))
              (extChartAt I α b)) +
        covDerivLowerOrderTerm (I := I) (M := M) gBase 0 2
          (deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
            deTurckRHSSectionBg (I := I) gBase (gSeq k₂)) α d
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx y := by
    rw [hrawcov, hcov₁, hcov₂, hlower_eq]
    dsimp [d, Jdx, y]
    ring
  have hderiv :
      |partialDeriv (E := E) d
          (chartDeTurckRHSComp (I := I) gBase (gSeq k₁) α (Jdx 0) (Jdx 1))
            (extChartAt I α b) -
        partialDeriv (E := E) d
          (chartDeTurckRHSComp (I := I) gBase (gSeq k₂) α (Jdx 0) (Jdx 1))
            (extChartAt I α b)| ≤ D.rhsD1Lip * (CjetAll * A) :=
    (hD.rhs_d1_lipschitz α hα k₁ k₂ b hb d (Jdx 0) (Jdx 1)).trans
      (mul_le_mul_of_nonneg_left hjetAll hD.rhsD1Lip_pos.le)
  rw [hcov]
  calc
    |(partialDeriv (E := E) d
          (chartDeTurckRHSComp (I := I) gBase (gSeq k₁) α (Jdx 0) (Jdx 1))
            (extChartAt I α b) -
        partialDeriv (E := E) d
          (chartDeTurckRHSComp (I := I) gBase (gSeq k₂) α (Jdx 0) (Jdx 1))
            (extChartAt I α b)) +
      covDerivLowerOrderTerm (I := I) (M := M) gBase 0 2
        (deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
          deTurckRHSSectionBg (I := I) gBase (gSeq k₂)) α d
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx y|
        ≤ |partialDeriv (E := E) d
              (chartDeTurckRHSComp (I := I) gBase (gSeq k₁) α (Jdx 0) (Jdx 1))
                (extChartAt I α b) -
            partialDeriv (E := E) d
              (chartDeTurckRHSComp (I := I) gBase (gSeq k₂) α (Jdx 0) (Jdx 1))
                (extChartAt I α b)| +
          |covDerivLowerOrderTerm (I := I) (M := M) gBase 0 2
            (deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
              deTurckRHSSectionBg (I := I) gBase (gSeq k₂)) α d
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx y| :=
      abs_add_le _ _
    _ ≤ D.rhsD1Lip * (CjetAll * A) + L * A := add_le_add hderiv hlower
    _ = B * ∑ i ∈ Finset.range 4,
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M)
            gBase 0 (2 + i) b
            ((iteratedCovGrad (I := I) gBase 0 2 i
              (metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
                metricCcTensor (I := I) (M := M) gBase (gSeq k₂))).toSection b)) := by
      rw [hA_def]
      dsimp [B]
      ring



theorem rhs_h0_lip {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M) (D : LowRegCoeff)
    (hD : IsLowRegCoeff (I := I) gBase gSeq D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k₁ k₂ : ι,
      ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
        (deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
          deTurckRHSSectionBg (I := I) gBase (gSeq k₂))‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ)
          (metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
            metricCcTensor (I := I) (M := M) gBase (gSeq k₂))‖ := by
  classical
  obtain ⟨B₀, hB₀, hraw₀⟩ := rhs_raw_lip (I := I) (M := M) gBase gSeq D hD
  obtain ⟨C₀, hC₀, hL2₀⟩ := l2_le_of_raw_sum
    (I := I) (M := M) gBase 2 3 (fun i => 2 + i) B₀ hB₀
  obtain ⟨Csp, hCsp, hsp⟩ := hs_le_jet (I := I) (M := M) gBase 2 0
  obtain ⟨Cin, hCin, hin⟩ := hsJet_le (I := I) (M := M) gBase 2 2
  refine ⟨Csp * C₀ * Cin, mul_nonneg (mul_nonneg hCsp hC₀) hCin, ?_⟩
  intro k₁ k₂
  let U : SmoothCcTensor gBase 0 2 :=
    metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
      metricCcTensor (I := I) (M := M) gBase (gSeq k₂)
  let S : SmoothCcTensor gBase 0 2 :=
    deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
      deTurckRHSSectionBg (I := I) gBase (gSeq k₂)
  let T : ∀ i : ℕ, SmoothCcTensor gBase 0 (2 + i) := fun i =>
    iteratedCovGrad (I := I) gBase 0 2 i U
  have hS : ‖S‖ ≤ C₀ * ∑ i ∈ Finset.range 3, ‖T i‖ := by
    apply hL2₀ T S
    intro α hα b hb Idx Jdx
    simpa only [S, U, T] using hraw₀ α hα k₁ k₂ b hb Idx Jdx
  have hout : ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ) S‖ ≤
      Csp * ‖S‖ := by
    have hsp' := hsp S
    have hcast : ((0 : ℕ) : ℝ) = (0 : ℝ) := by norm_num
    rw [hcast] at hsp'
    simpa only [Finset.sum_range_one, iteratedCovGrad_zero, Nat.zero_add] using hsp'
  have hinput : ∑ i ∈ Finset.range 3, ‖T i‖ ≤
      Cin * ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ) U‖ := by
    simpa only [T] using hin U
  change ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ) S‖ ≤
    (Csp * C₀ * Cin) *
      ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ) U‖
  calc
    ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ) S‖
        ≤ Csp * ‖S‖ := hout
    _ ≤ Csp * (C₀ * ∑ i ∈ Finset.range 3, ‖T i‖) :=
      mul_le_mul_of_nonneg_left hS hCsp
    _ ≤ Csp * (C₀ *
          (Cin * ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ) U‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinput hC₀) hCsp
    _ = (Csp * C₀ * Cin) *
          ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ) U‖ := by ring



theorem rhs_h1_bdd {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M) (D : LowRegCoeff)
    (hD : IsLowRegCoeff (I := I) gBase gSeq D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ι,
      ‖ccTensorToHs (I := I) (M := M) gBase 2 (1 : ℝ)
        (deTurckRHSSectionBg (I := I) gBase (gSeq k))‖ ≤ C := by
  classical
  let S : ι → SmoothCcTensor gBase 0 2 := fun k =>
    deTurckRHSSectionBg (I := I) gBase (gSeq k)
  have hraw0 : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ Idx : Fin 0 → Fin (Module.finrank ℝ E),
          ∀ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
            |tensorChartComponentRaw (I := I) (M := M)
              gBase 0 2 (S k) α Idx Jdx b| ≤ D.rhsBound := by
    intro α hα k b hb Idx Jdx
    have hb_src : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact chartAtlasPOU_isSubordinate I M α hb
    have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α :=
      (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source
        (I := I) α b).2 hb_src
    rw [show S k = deTurckRHSSectionBg (I := I) gBase (gSeq k) from rfl,
      rhs_raw_eq (I := I) (M := M) gBase (gSeq k) α hb_good]
    exact hD.rhs_bound α hα k b hb (Jdx 0) (Jdx 1)
  obtain ⟨C₀, hC₀, hL2₀⟩ := l2_bdd_of_raw
    (I := I) (M := M) gBase 0 2 S D.rhsBound hD.rhsBound_pos.le hraw0

  choose Cα hCα hCα_bd using fun α : M =>
    exists_lowerOrderCoeff_uniform_boundR
      (I := I) (M := M) gBase 0 2 α 0
  let CΓ : ℝ := ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Cα α
  have hCΓ : 0 ≤ CΓ := by
    dsimp [CΓ]
    exact Finset.sum_nonneg fun α _ => hCα α
  have hcoeff : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ m : Fin (Module.finrank ℝ E),
        ∀ Idx : Fin 0 → Fin (Module.finrank ℝ E),
          ∀ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
            ∀ p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
                (Fin 2 → Fin (Module.finrank ℝ E)),
              ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
                |covDerivLowerOrderCoeff (I := I) (M := M)
                  gBase 0 2 α m Idx p.1 Jdx p.2 y| ≤ CΓ := by
    intro α hα m Idx Jdx p y hy
    have h := hCα_bd α m Idx Jdx p 0 (by omega) y hy
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    refine h.trans ?_
    exact Finset.single_le_sum (f := Cα)
      (fun β _ => hCα β) hα
  let L : ℝ :=
    ∑ _p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
        (Fin 2 → Fin (Module.finrank ℝ E)), CΓ * D.rhsBound
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Finset.sum_nonneg fun _ _ =>
      mul_nonneg hCΓ hD.rhsBound_pos.le
  let B₁ : ℝ := D.rhsD1Bound + L
  have hB₁ : 0 ≤ B₁ := by
    dsimp [B₁]
    exact add_nonneg hD.rhsD1Bound_pos.le hL
  have hlower : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m : Fin (Module.finrank ℝ E),
          ∀ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
            |covDerivLowerOrderTerm (I := I) (M := M) gBase 0 2
              (S k) α m (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx
              (toEuclidean (E := E) (extChartAt I α b))| ≤ L := by
    intro α hα k b hb m Jdx
    have hb_src : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact chartAtlasPOU_isSubordinate I M α hb
    have hround :
        (extChartAt I α).symm
          ((toEuclidean (E := E)).symm
            (toEuclidean (E := E) (extChartAt I α b))) = b := by
      simpa using (extChartAt I α).left_inv hb_src
    have hyK : toEuclidean (E := E) (extChartAt I α b) ∈
        chartImagePOUTsupport (I := I) (M := M) α :=
      ⟨extChartAt I α b, ⟨b, hb, rfl⟩, rfl⟩
    have hsum :
        (∑ p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
            (Fin 2 → Fin (Module.finrank ℝ E)),
          |covDerivLowerOrderCoeff (I := I) (M := M) gBase 0 2 α m
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) p.1 Jdx p.2
              (toEuclidean (E := E) (extChartAt I α b)) *
            tensorChartComponentRaw (I := I) (M := M) gBase 0 2 (S k) α p.1 p.2
              ((extChartAt I α).symm
                ((toEuclidean (E := E)).symm
                  (toEuclidean (E := E) (extChartAt I α b))))|) ≤
          ∑ _p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
            (Fin 2 → Fin (Module.finrank ℝ E)), CΓ * D.rhsBound := by
      exact Finset.sum_le_sum fun p _ => by
        rw [abs_mul, hround]
        exact mul_le_mul (hcoeff α hα m _ Jdx p _ hyK)
          (hraw0 α hα k b hb p.1 p.2) (abs_nonneg _) hCΓ
    rw [covDerivLowerOrderTerm_def]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (hsum.trans_eq rfl)
  have hraw1 : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ Idx : Fin 0 → Fin (Module.finrank ℝ E),
          ∀ Kdx : Fin 3 → Fin (Module.finrank ℝ E),
            |tensorChartComponentRaw (I := I) (M := M) gBase 0 3
              (covGrad (I := I) (M := M) gBase 0 2 (S k))
              α Idx Kdx b| ≤ B₁ := by
    intro α hα k b hb Idx Kdx
    have hIdx : Idx = fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E)) :=
      Subsingleton.elim _ _
    subst Idx
    let d : Fin (Module.finrank ℝ E) := Kdx 0
    let Jdx : Fin 2 → Fin (Module.finrank ℝ E) := Matrix.vecTail Kdx
    let y : EuclN := toEuclidean (E := E) (extChartAt I α b)
    have hb_src : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact chartAtlasPOU_isSubordinate I M α hb
    have hy : y ∈ chartTargetEuclid (I := I) (M := M) α :=
      ⟨extChartAt I α b, (extChartAt I α).map_source hb_src, rfl⟩
    have hround :
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = b := by
      dsimp [y]
      simpa using (extChartAt I α).left_inv hb_src
    have hcons : (Fin.cons d Jdx : Fin 3 → Fin (Module.finrank ℝ E)) = Kdx := by
      exact Fin.cons_self_tail Kdx
    have hinv := euclidPartial_chartPushedRaw_general_eq_covGrad_sub_lowerOrder
      (I := I) (M := M) gBase 2 (S k) α d Jdx hy
    rw [hcons, hround] at hinv
    have hderiv := rhs_partial_eq
      (I := I) (M := M) gBase (gSeq k) α d Jdx hy
    have hyround : (toEuclidean (E := E)).symm y = extChartAt I α b := by
      dsimp [y]
      simp
    rw [hyround] at hderiv
    rw [hderiv] at hinv
    have hcov :
        tensorChartComponentRaw (I := I) (M := M) gBase 0 3
            (covGrad (I := I) (M := M) gBase 0 2 (S k)) α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Kdx b =
          partialDeriv (E := E) d
              (chartDeTurckRHSComp (I := I) gBase (gSeq k) α
                (Jdx 0) (Jdx 1)) (extChartAt I α b) +
            covDerivLowerOrderTerm (I := I) (M := M) gBase 0 2
              (S k) α d (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx y := by
      linarith
    rw [hcov]
    calc
      |partialDeriv (E := E) d
            (chartDeTurckRHSComp (I := I) gBase (gSeq k) α
              (Jdx 0) (Jdx 1)) (extChartAt I α b) +
          covDerivLowerOrderTerm (I := I) (M := M) gBase 0 2
            (S k) α d (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx y|
          ≤ |partialDeriv (E := E) d
              (chartDeTurckRHSComp (I := I) gBase (gSeq k) α
                (Jdx 0) (Jdx 1)) (extChartAt I α b)| +
            |covDerivLowerOrderTerm (I := I) (M := M) gBase 0 2
              (S k) α d (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx y| :=
            abs_add_le _ _
      _ ≤ D.rhsD1Bound + L := add_le_add
        (hD.rhs_d1_bound α hα k b hb d (Jdx 0) (Jdx 1))
        (by simpa [y] using hlower α hα k b hb d Jdx)
      _ = B₁ := rfl
  obtain ⟨C₁, hC₁, hL2₁⟩ := l2_bdd_of_raw
    (I := I) (M := M) gBase 0 3
    (fun k => covGrad (I := I) (M := M) gBase 0 2 (S k))
    B₁ hB₁ hraw1
  obtain ⟨Csp, hCsp, hsp⟩ := hs_le_jet (I := I) (M := M) gBase 2 1
  refine ⟨Csp * (C₀ + C₁), mul_nonneg hCsp (add_nonneg hC₀ hC₁), fun k => ?_⟩
  have hsum : ∑ j ∈ Finset.range (1 + 1),
        ‖iteratedCovGrad (I := I) gBase 0 2 j (S k)‖ =
      ‖S k‖ + ‖covGrad (I := I) (M := M) gBase 0 2 (S k)‖ := by
    rw [show (1 + 1) = 2 by omega, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero]
  calc
    ‖ccTensorToHs (I := I) (M := M) gBase 2 (1 : ℝ) (S k)‖
        ≤ Csp * ∑ j ∈ Finset.range (1 + 1),
            ‖iteratedCovGrad (I := I) gBase 0 2 j (S k)‖ := by
              have hcast : (1 : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
              rw [hcast]
              exact hsp (S k)
    _ = Csp * (‖S k‖ + ‖covGrad (I := I) (M := M) gBase 0 2 (S k)‖) := by
      rw [hsum]
    _ ≤ Csp * (C₀ + C₁) :=
      mul_le_mul_of_nonneg_left (add_le_add (hL2₀ k) (hL2₁ k)) hCsp



theorem rhs_h1_lip {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M) (D : LowRegCoeff)
    (hD : IsLowRegCoeff (I := I) gBase gSeq D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k₁ k₂ : ι,
      ‖ccTensorToHs (I := I) (M := M) gBase 2 (1 : ℝ)
        (deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
          deTurckRHSSectionBg (I := I) gBase (gSeq k₂))‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) gBase 2 (3 : ℝ)
          (metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
            metricCcTensor (I := I) (M := M) gBase (gSeq k₂))‖ := by
  classical
  obtain ⟨B₀, hB₀, hraw₀⟩ := rhs_raw_lip (I := I) (M := M) gBase gSeq D hD
  obtain ⟨B₁, hB₁, hraw₁⟩ := rhs_cov_lip (I := I) (M := M) gBase gSeq D hD
  obtain ⟨C₀, hC₀, hL2₀⟩ := l2_le_of_raw_sum
    (I := I) (M := M) gBase 2 3 (fun i => 2 + i) B₀ hB₀
  obtain ⟨C₁, hC₁, hL2₁⟩ := l2_le_of_raw_sum
    (I := I) (M := M) gBase 3 4 (fun i => 2 + i) B₁ hB₁
  obtain ⟨Csp, hCsp, hsp⟩ := hs_le_jet (I := I) (M := M) gBase 2 1
  obtain ⟨Cin, hCin, hin⟩ := hsJet_le (I := I) (M := M) gBase 2 3
  refine ⟨Csp * (C₀ + C₁) * Cin,
    mul_nonneg (mul_nonneg hCsp (add_nonneg hC₀ hC₁)) hCin, ?_⟩
  intro k₁ k₂
  let U : SmoothCcTensor gBase 0 2 :=
    metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
      metricCcTensor (I := I) (M := M) gBase (gSeq k₂)
  let S : SmoothCcTensor gBase 0 2 :=
    deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
      deTurckRHSSectionBg (I := I) gBase (gSeq k₂)
  let T : ∀ i : ℕ, SmoothCcTensor gBase 0 (2 + i) := fun i =>
    iteratedCovGrad (I := I) gBase 0 2 i U
  have hS₀ : ‖S‖ ≤ C₀ * ∑ i ∈ Finset.range 3, ‖T i‖ := by
    apply hL2₀ T S
    intro α hα b hb Idx Jdx
    simpa only [S, U, T] using hraw₀ α hα k₁ k₂ b hb Idx Jdx
  have hS₁ : ‖covGrad (I := I) (M := M) gBase 0 2 S‖ ≤
      C₁ * ∑ i ∈ Finset.range 4, ‖T i‖ := by
    apply hL2₁ T (covGrad (I := I) (M := M) gBase 0 2 S)
    intro α hα b hb Idx Kdx
    simpa only [S, U, T] using hraw₁ α hα k₁ k₂ b hb Idx Kdx
  have hsum : ∑ j ∈ Finset.range (1 + 1),
        ‖iteratedCovGrad (I := I) gBase 0 2 j S‖ =
      ‖S‖ + ‖covGrad (I := I) (M := M) gBase 0 2 S‖ := by
    rw [show (1 + 1) = 2 by omega, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero]
  have hT34 : (∑ i ∈ Finset.range 3, ‖T i‖) ≤
      ∑ i ∈ Finset.range 4, ‖T i‖ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) ?_
    intro i _ _
    exact norm_nonneg (T i)
  have hS₀' : ‖S‖ ≤ C₀ * ∑ i ∈ Finset.range 4, ‖T i‖ :=
    hS₀.trans (mul_le_mul_of_nonneg_left hT34 hC₀)
  have hout :
      ‖ccTensorToHs (I := I) (M := M) gBase 2 (1 : ℝ) S‖ ≤
        Csp * (‖S‖ + ‖covGrad (I := I) (M := M) gBase 0 2 S‖) := by
    calc
      ‖ccTensorToHs (I := I) (M := M) gBase 2 (1 : ℝ) S‖
          ≤ Csp * ∑ j ∈ Finset.range (1 + 1),
              ‖iteratedCovGrad (I := I) gBase 0 2 j S‖ := by
        have hcast : (1 : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
        rw [hcast]
        exact hsp S
      _ = Csp * (‖S‖ + ‖covGrad (I := I) (M := M) gBase 0 2 S‖) := by
        rw [hsum]
  have hpair :
      ‖S‖ + ‖covGrad (I := I) (M := M) gBase 0 2 S‖ ≤
        (C₀ + C₁) * ∑ i ∈ Finset.range 4, ‖T i‖ := by
    calc
      ‖S‖ + ‖covGrad (I := I) (M := M) gBase 0 2 S‖
          ≤ C₀ * ∑ i ∈ Finset.range 4, ‖T i‖ +
              C₁ * ∑ i ∈ Finset.range 4, ‖T i‖ := add_le_add hS₀' hS₁
      _ = (C₀ + C₁) * ∑ i ∈ Finset.range 4, ‖T i‖ := by ring
  have hinput : ∑ i ∈ Finset.range 4, ‖T i‖ ≤
      Cin * ‖ccTensorToHs (I := I) (M := M) gBase 2 (3 : ℝ) U‖ := by
    simpa only [T] using hin U
  change ‖ccTensorToHs (I := I) (M := M) gBase 2 (1 : ℝ) S‖ ≤
    (Csp * (C₀ + C₁) * Cin) *
      ‖ccTensorToHs (I := I) (M := M) gBase 2 (3 : ℝ) U‖
  calc
    ‖ccTensorToHs (I := I) (M := M) gBase 2 (1 : ℝ) S‖
        ≤ Csp * (‖S‖ + ‖covGrad (I := I) (M := M) gBase 0 2 S‖) := hout
    _ ≤ Csp * ((C₀ + C₁) * ∑ i ∈ Finset.range 4, ‖T i‖) :=
      mul_le_mul_of_nonneg_left hpair hCsp
    _ ≤ Csp * ((C₀ + C₁) *
          (Cin * ‖ccTensorToHs (I := I) (M := M) gBase 2 (3 : ℝ) U‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinput (add_nonneg hC₀ hC₁)) hCsp
    _ = (Csp * (C₀ + C₁) * Cin) *
          ‖ccTensorToHs (I := I) (M := M) gBase 2 (3 : ℝ) U‖ := by ring

end DifferentialGeometry.PDE.RicciFlow
