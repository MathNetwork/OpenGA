import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.CovChartMetricGramInv


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators Matrix
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private noncomputable abbrev rsTriv (r s : ℕ) (α : M) :
    Bundle.Trivialization (TensorRSModel r s ℝ E)
      (Bundle.TotalSpace.proj :
        Bundle.TotalSpace (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) → M) :=
  trivializationAt (TensorRSModel r s ℝ E)
    (fun x : M => TensorRSSpace r s I x) α

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma rsTriv_baseSet (r s : ℕ) (α : M) :
    (rsTriv (I := I) (M := M) r s α).baseSet = (chartAt H α).source := by
  change ((trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) α).baseSet) =
        (chartAt H α).source
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
  rw [Set.inter_self]
  rfl

noncomputable def chartBasisFiberSection (r s : ℕ) (α : M)
    (Q : CompIdx E r s) :
    (b : M) → TensorRSSpace r s I b :=
  fun b => (rsTriv (I := I) (M := M) r s α).symmL ℝ b
    (tensorChartBasisElement (E := E) r s Q.1 Q.2)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma continuousLinearMapAt_chartBasisFiberSection (r s : ℕ) (α : M)
    (Q : CompIdx E r s) {b : M} (hb : b ∈ (chartAt H α).source) :
    (rsTriv (I := I) (M := M) r s α).continuousLinearMapAt ℝ b
        (chartBasisFiberSection (I := I) (M := M) r s α Q b) =
      tensorChartBasisElement (E := E) r s Q.1 Q.2 := by
  have hb' : b ∈ (rsTriv (I := I) (M := M) r s α).baseSet := by
    rw [rsTriv_baseSet (I := I) (M := M) r s α]; exact hb
  exact Bundle.Trivialization.continuousLinearMapAt_symmL
    (rsTriv (I := I) (M := M) r s α) hb'
    (tensorChartBasisElement (E := E) r s Q.1 Q.2)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartBasisFiberSection_contMDiffOn (r s : ℕ) (α : M)
    (Q : CompIdx E r s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M =>
        Bundle.TotalSpace.mk' (TensorRSModel r s ℝ E) b
          (chartBasisFiberSection (I := I) (M := M) r s α Q b))
      ((chartAt H α).source) := by
  classical
  have hbase := rsTriv_baseSet (I := I) (M := M) r s α
  have hiff := (rsTriv (I := I) (M := M) r s α).contMDiffOn_section_baseSet_iff
    (s := chartBasisFiberSection (I := I) (M := M) r s α Q) (IB := I) (n := ∞)
  rw [hbase] at hiff
  refine hiff.mpr ?_
  refine ContMDiffOn.congr
    (contMDiffOn_const (c := tensorChartBasisElement (E := E) r s Q.1 Q.2)) ?_
  intro b hb
  have hb' : b ∈ (rsTriv (I := I) (M := M) r s α).baseSet := by
    rw [rsTriv_baseSet (I := I) (M := M) r s α]; exact hb
  rw [show ((rsTriv (I := I) (M := M) r s α)
        ⟨b, chartBasisFiberSection (I := I) (M := M) r s α Q b⟩).2 =
      (rsTriv (I := I) (M := M) r s α).continuousLinearMapAt ℝ b
        (chartBasisFiberSection (I := I) (M := M) r s α Q b) from by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
      (rsTriv (I := I) (M := M) r s α).coe_linearMapAt_of_mem (R := ℝ) hb']]
  exact continuousLinearMapAt_chartBasisFiberSection
    (I := I) (M := M) r s α Q hb

noncomputable def chartBasisTensorSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (χ : M → ℝ)
    (_hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (_hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s) :
    SmoothCcTensor g r s where
  toSection :=
    { toFun := fun b => χ b • chartBasisFiberSection (I := I) (M := M) r s α Q b
      contMDiff_toFun := by
        exact ContMDiffOn.smul_section_of_tsupport
          (s := chartBasisFiberSection (I := I) (M := M) r s α Q)
          (ψ := χ) (n := ∞) (u := (chartAt H α).source)
          _hχs (chartAt H α).open_source _hχt
          (chartBasisFiberSection_contMDiffOn (I := I) (M := M) r s α Q) }
  hasCompactSupport := by
    have htsupp_closed : IsClosed
        (tsupport (fun b : M => TensorRSSpace.toModel
          (((fun b : M => χ b •
            chartBasisFiberSection (I := I) (M := M) r s α Q b) : (b : M) →
              TensorRSSpace r s I b) b))) :=
      isClosed_tsupport _
    exact isCompact_univ.of_isClosed_subset htsupp_closed (fun _ _ => trivial)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartBasisTensorSection_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s) (b : M) :
    (chartBasisTensorSection (I := I) (M := M) g r s α χ hχs hχt Q).toSection b =
      χ b • chartBasisFiberSection (I := I) (M := M) r s α Q b := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorTrivProj_chartBasisTensorSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s) {b : M} (hb : b ∈ (chartAt H α).source) :
    tensorTrivProj (I := I) (M := M) g r s
        (chartBasisTensorSection (I := I) (M := M) g r s α χ hχs hχt Q) α b =
      χ b • tensorChartBasisElement (E := E) r s Q.1 Q.2 := by
  classical
  unfold tensorTrivProj
  rw [chartBasisTensorSection_toSection_apply (I := I) (M := M) g r s α hχs hχt
    Q b]
  rw [map_smul]
  rw [continuousLinearMapAt_chartBasisFiberSection (I := I) (M := M) r s α Q hb]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorChartComponentRaw_chartBasisTensorSection_on_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (chartBasisTensorSection (I := I) (M := M) g r s α χ hχs hχt Q)
        α Idx Jdx b =
      χ b * (if (Idx, Jdx) = Q then (1 : ℝ) else 0) := by
  classical
  unfold tensorChartComponentRaw
  rw [tensorTrivProj_chartBasisTensorSection (I := I) (M := M) g r s α hχs hχt
    Q hb]
  rw [map_smul, smul_eq_mul]
  congr 1
  rw [tensorChartComponentProjection_basisElement (E := E) r s Idx Q.1 Jdx Q.2]
  by_cases hQ : (Idx, Jdx) = Q
  · have h1 : Idx = Q.1 := congrArg Prod.fst hQ
    have h2 : Q.2 = Jdx := (congrArg Prod.snd hQ).symm
    rw [if_pos h1, if_pos h2, if_pos hQ, mul_one]
  · rw [if_neg hQ]
    by_cases h1 : Idx = Q.1
    · have h2 : Q.2 ≠ Jdx := by
        intro h2
        exact hQ (Prod.ext h1 h2.symm)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartBasisTensorSection_chartComp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (chartBasisTensorSection (I := I) (M := M) g r s α χ hχs hχt Q)
        α Idx Jdx ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      chartPushedRaw I α χ y * (if (Idx, Jdx) = Q then (1 : ℝ) else 0) := by
  classical
  have hb : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  rw [tensorChartComponentRaw_chartBasisTensorSection_on_source
    (I := I) (M := M) g r s α hχs hχt Q Idx Jdx hb]
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α χ hy]

noncomputable def gramInvWeight
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r s) (b : M) : ℝ :=
  covChartMetricGramInv (I := I) (M := M) g r s α
    (toEuclidean (E := E) ((extChartAt I α) b)) Q P₀

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma toEuclidean_extChartAt_contMDiffOn (α : M) :
    ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞
      (fun b : M => toEuclidean (E := E) ((extChartAt I α) b))
      ((chartAt H α).source) := by
  have hext : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α)
      ((chartAt H α).source) := contMDiffOn_extChartAt (I := I) (x := α)
  have htoEuc : ContMDiff 𝓘(ℝ, E)
      𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞
      (toEuclidean (E := E)) :=
    (toEuclidean (E := E)).toContinuousLinearMap.contMDiff
  exact htoEuc.comp_contMDiffOn hext

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma toEuclidean_extChartAt_mapsTo (α : M) :
    Set.MapsTo (fun b : M => toEuclidean (E := E) ((extChartAt I α) b))
      ((chartAt H α).source)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro b hb
  refine ⟨(extChartAt I α) b, ?_, rfl⟩
  rw [← extChartAt_source_eq_chartAt_source (I := I)] at hb
  exact (extChartAt I α).map_source hb

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma gramInvWeight_contMDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ Q : CompIdx E r s) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (gramInvWeight (I := I) (M := M) g r s α P₀ Q)
      ((chartAt H α).source) := by
  have hentry : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
      𝓘(ℝ, ℝ) ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (contMDiffOn_iff_contDiffOn).mpr
      (covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α Q P₀)
  exact hentry.comp (toEuclidean_extChartAt_contMDiffOn (I := I) (M := M) α)
    (toEuclidean_extChartAt_mapsTo (I := I) (M := M) α)

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gramInvWeight_mul_bump_contMDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ Q : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => gramInvWeight (I := I) (M := M) g r s α P₀ Q b * χ b)
      ((chartAt H α).source) :=
  (gramInvWeight_contMDiffOn (I := I) (M := M) g r s α P₀ Q).mul hχs

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma gramInvWeight_mul_bump_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ Q : CompIdx E r s)
    {χ : M → ℝ} (hχt : tsupport χ ⊆ (chartAt H α).source) :
    tsupport (fun b : M => gramInvWeight (I := I) (M := M) g r s α P₀ Q b * χ b)
      ⊆ (chartAt H α).source := by
  have hsub :
      tsupport (fun b : M => gramInvWeight (I := I) (M := M) g r s α P₀ Q b *
        χ b) ⊆ tsupport χ := by
    have h_eq : (fun b : M => gramInvWeight (I := I) (M := M) g r s α P₀ Q b *
        χ b) =
        (fun b : M => gramInvWeight (I := I) (M := M) g r s α P₀ Q b • χ b) := by
      funext b; rfl
    rw [h_eq]
    exact tsupport_smul_subset_right
      (f := fun b : M => gramInvWeight (I := I) (M := M) g r s α P₀ Q b)
      (g := χ)
  exact hsub.trans hχt

noncomputable def rotatedTestSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    (χ : M → ℝ)
    (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) :
    SmoothCcTensor g r s :=
  ∑ Q : CompIdx E r s,
    chartBasisTensorSection (I := I) (M := M) g r s α
      (fun b : M => gramInvWeight (I := I) (M := M) g r s α P₀ Q b * χ b)
      (gramInvWeight_mul_bump_contMDiffOn (I := I) (M := M) g r s α P₀ Q hχs)
      (gramInvWeight_mul_bump_tsupport (I := I) (M := M) g r s α P₀ Q hχt)
      Q

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorTrivProj_finsetSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {ι : Type*} (t : Finset ι) (S : ι → SmoothCcTensor g r s) (b : M) :
    tensorTrivProj (I := I) (M := M) g r s (∑ i ∈ t, S i) α b =
      ∑ i ∈ t, tensorTrivProj (I := I) (M := M) g r s (S i) α b := by
  classical
  have hadd : ∀ S₁ S₂ : SmoothCcTensor g r s,
      tensorTrivProj (I := I) (M := M) g r s (S₁ + S₂) α b =
        tensorTrivProj (I := I) (M := M) g r s S₁ α b +
          tensorTrivProj (I := I) (M := M) g r s S₂ α b := by
    intro S₁ S₂
    unfold tensorTrivProj
    rw [show (S₁ + S₂).toSection b = S₁.toSection b + S₂.toSection b from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    exact map_add _ _ _
  have hzero : tensorTrivProj (I := I) (M := M) g r s
      (0 : SmoothCcTensor g r s) α b = 0 := by
    unfold tensorTrivProj
    rw [show (0 : SmoothCcTensor g r s).toSection b = 0 from by
      rw [SmoothCcTensor.toSection_zero]; rfl]
    exact map_zero _
  induction t using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, hzero]
  | insert i A hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, ih]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorChartComponentRaw_finsetSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {ι : Type*} (t : Finset ι) (S : ι → SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (b : M) :
    tensorChartComponentRaw (I := I) (M := M) g r s (∑ i ∈ t, S i)
        α Idx Jdx b =
      ∑ i ∈ t, tensorChartComponentRaw (I := I) (M := M) g r s (S i)
        α Idx Jdx b := by
  classical
  unfold tensorChartComponentRaw
  rw [tensorTrivProj_finsetSum (I := I) (M := M) g r s α t S b]
  exact map_sum (tensorChartComponentProjection (E := E) r s Idx Jdx) _ _

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rotatedTestSection_chartComp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
        α Q.1 Q.2 ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ *
        chartPushedRaw I α χ y := by
  classical
  rw [rotatedTestSection,
    tensorChartComponentRaw_finsetSum (I := I) (M := M) g r s α
      Finset.univ _ Q.1 Q.2 ((extChartAt I α).symm
        ((toEuclidean (E := E)).symm y))]
  have hterm : ∀ Q' : CompIdx E r s,
      tensorChartComponentRaw (I := I) (M := M) g r s
          (chartBasisTensorSection (I := I) (M := M) g r s α
            (fun b : M => gramInvWeight (I := I) (M := M) g r s α P₀ Q' b * χ b)
            (gramInvWeight_mul_bump_contMDiffOn (I := I) (M := M) g r s α P₀ Q'
              hχs)
            (gramInvWeight_mul_bump_tsupport (I := I) (M := M) g r s α P₀ Q'
              hχt)
            Q')
          α Q.1 Q.2 ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
        chartPushedRaw I α
            (fun b : M => gramInvWeight (I := I) (M := M) g r s α P₀ Q' b * χ b)
            y *
          (if (Q.1, Q.2) = Q' then (1 : ℝ) else 0) :=
    fun Q' => chartBasisTensorSection_chartComp (I := I) (M := M) g r s α
      (gramInvWeight_mul_bump_contMDiffOn (I := I) (M := M) g r s α P₀ Q' hχs)
      (gramInvWeight_mul_bump_tsupport (I := I) (M := M) g r s α P₀ Q' hχt)
      Q' Q.1 Q.2 hy
  rw [Finset.sum_congr rfl (fun Q' _ => hterm Q')]
  rw [Finset.sum_eq_single Q]
  · rw [show ((Q.1, Q.2) : CompIdx E r s) = Q from Prod.ext rfl rfl]
    rw [if_pos rfl, mul_one]
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    have hb_eq : (toEuclidean (E := E))
        ((extChartAt I α)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) = y := by
      have hy' : y ∈ (toEuclidean (E := E)).symm ⁻¹' (extChartAt I α).target := by
        rw [← chartTargetEuclid_eq_preimage_symm (I := I) (M := M)]; exact hy
      rw [(extChartAt I α).right_inv hy', ContinuousLinearEquiv.apply_symm_apply]
    rw [show gramInvWeight (I := I) (M := M) g r s α P₀ Q
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
        covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ from by
      unfold gramInvWeight; rw [hb_eq]]
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α χ hy]
  · intro Q' _ hne
    rw [show ((Q.1, Q.2) : CompIdx E r s) = Q from Prod.ext rfl rfl]
    rw [if_neg (fun h => hne h.symm), mul_zero]
  · intro hQ
    exact absurd (Finset.mem_univ Q) hQ

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem toSection_eq_sum_chartBasisFiberSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (α : M)
    {b : M} (hb : b ∈ (chartAt H α).source) :
    S.toSection b = ∑ Q : CompIdx E r s,
      tensorChartComponentRaw (I := I) (M := M) g r s S α Q.1 Q.2 b •
        chartBasisFiberSection (I := I) (M := M) r s α Q b := by
  classical
  have hb' : b ∈ (rsTriv (I := I) (M := M) r s α).baseSet := by
    rw [rsTriv_baseSet (I := I) (M := M) r s α]; exact hb
  have hmodel := tensorRSModel_eq_sum_basis (E := E) r s
    (tensorTrivProj (I := I) (M := M) g r s S α b)
  calc S.toSection b
      = (rsTriv (I := I) (M := M) r s α).symmL ℝ b
          ((rsTriv (I := I) (M := M) r s α).continuousLinearMapAt ℝ b
            (S.toSection b)) :=
        ((rsTriv (I := I) (M := M) r s α).symmL_continuousLinearMapAt
          hb' (S.toSection b)).symm
    _ = (rsTriv (I := I) (M := M) r s α).symmL ℝ b
          (tensorTrivProj (I := I) (M := M) g r s S α b) := rfl
    _ = (rsTriv (I := I) (M := M) r s α).symmL ℝ b
          (∑ Idx, ∑ Jdx,
            tensorChartComponentProjection (E := E) r s Idx Jdx
                (tensorTrivProj (I := I) (M := M) g r s S α b) •
              tensorChartBasisElement (E := E) r s Idx Jdx) := by
        rw [← hmodel]
    _ = ∑ Idx, ∑ Jdx,
          tensorChartComponentProjection (E := E) r s Idx Jdx
              (tensorTrivProj (I := I) (M := M) g r s S α b) •
            (rsTriv (I := I) (M := M) r s α).symmL ℝ b
              (tensorChartBasisElement (E := E) r s Idx Jdx) := by
        rw [map_sum]
        refine Finset.sum_congr rfl (fun Idx _ => ?_)
        rw [map_sum]
        refine Finset.sum_congr rfl (fun Jdx _ => ?_)
        rw [map_smul]
    _ = ∑ Q : CompIdx E r s,
          tensorChartComponentRaw (I := I) (M := M) g r s S α Q.1 Q.2 b •
            chartBasisFiberSection (I := I) (M := M) r s α Q b := by
        rw [Fintype.sum_prod_type'
          (f := fun Idx Jdx =>
            tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b •
              chartBasisFiberSection (I := I) (M := M) r s α (Idx, Jdx) b)]
        refine Finset.sum_congr rfl (fun Idx _ => ?_)
        refine Finset.sum_congr rfl (fun Jdx _ => ?_)
        rfl

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covChartMetricGram_mul_inv_collapse
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (P P₀ : CompIdx E r s) :
    ∑ Q : CompIdx E r s, covChartMetricGram (I := I) (M := M) g r s α P Q y *
        covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ =
      (if P = P₀ then (1 : ℝ) else 0) := by
  classical
  have hmul := mul_covChartMetricGramInv (I := I) (M := M) g r s α hy
  have hentry :
      (covChartMetricGramMatrix (I := I) (M := M) g r s α y *
          covChartMetricGramInv (I := I) (M := M) g r s α y) P P₀ =
        (1 : Matrix (CompIdx E r s) (CompIdx E r s) ℝ) P P₀ :=
    congrFun (congrFun hmul P) P₀
  rw [Matrix.mul_apply, Matrix.one_apply] at hentry
  rw [← hentry]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [covChartMetricGramMatrix_apply]

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
