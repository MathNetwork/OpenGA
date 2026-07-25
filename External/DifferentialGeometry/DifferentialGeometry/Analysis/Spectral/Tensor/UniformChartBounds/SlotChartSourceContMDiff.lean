import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.SlotUniformBound
import DifferentialGeometry.Tensor.RSTensor.Coordinates.TensorRSModelEvalBasis
import DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.ChartTwistIdentity
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartLeviCivitaParallelExtend
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartTensor0SCovariantDerivative
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartSmooth


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open Tensor0SBundle

section ParallelGeneral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

private local instance parallelGeneral_complete_E : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private lemma chartE_section_repr_contMDiffOn_chartSource
    (α : M) {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b : M => chartE_section_repr (I := I) α X b)
      ((chartAt H α).source) := by
  classical
  intro b hb_src
  have hbase_eq :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [hbase_eq]; exact hb_src
  have hX_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (T% X) b :=
    hX.contMDiffAt
  have h := (contMDiffAt_section_iff_chartE I α X (k := (⊤ : ℕ∞)) hb_base).mp hX_at
  exact h.contMDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private lemma chartE_section_repr_basis_component_contMDiffOn_chartSource
    (α : M) {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        ((chartModelBasis E).repr (chartE_section_repr (I := I) α X b)) j)
      ((chartAt H α).source) := by
  classical
  have hbase :=
    chartE_section_repr_contMDiffOn_chartSource (I := I) (M := M) α (X := X) hX
  have hcoord_clm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (((chartModelBasis E).coord j).toContinuousLinearMap) :=
    (((chartModelBasis E).coord j).toContinuousLinearMap).contMDiff
  intro b hb
  exact (hcoord_clm.contMDiffAt).comp_contMDiffWithinAt b (hbase b hb)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
private lemma chartChristoffel_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => chartChristoffel (I := I) g α i j k (extChartAt I α b))
      ((chartAt H α).source) := by
  classical
  intro b hb_src
  have hφ_at : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) b :=
    contMDiffAt_extChartAt' (I := I) (n := ∞) hb_src
  have h_target_open : IsOpen ((extChartAt I α).target : Set E) :=
    isOpen_extChartAt_target α
  have h_int_eq : interior ((extChartAt I α).target : Set E) =
      (extChartAt I α).target := h_target_open.interior_eq
  have hb_ext_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hb_src
  have hxφ_tgt : extChartAt I α b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_ext_src
  have hxφ_int : extChartAt I α b ∈
      interior ((extChartAt I α).target : Set E) := by
    rw [h_int_eq]; exact hxφ_tgt
  have hΓ_on : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j k)
      (interior (extChartAt I α).target) :=
    chartChristoffel_contDiffOn_interior (I := I) g α i j k
  have hΓ_chart : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g α i j k)
      (extChartAt I α b) :=
    hΓ_on.contDiffAt (isOpen_interior.mem_nhds hxφ_int)
  exact (hΓ_chart.comp_contMDiffAt hφ_at).contMDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
private lemma christoffelCorrectionCLM_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (christoffelCorrectionCLM (I := I) g α X)
      ((chartAt H α).source) := by
  classical
  unfold christoffelCorrectionCLM
  refine contMDiffOn_finset_sum (t := Finset.univ) (fun i _ => ?_)
  refine contMDiffOn_finset_sum (t := Finset.univ) (fun j _ => ?_)
  refine contMDiffOn_finset_sum (t := Finset.univ) (fun k _ => ?_)
  have hrepr_smooth :=
    chartE_section_repr_basis_component_contMDiffOn_chartSource
      (I := I) (M := M) α (X := X) hX (j := j)
  have hΓ_smooth :=
    chartChristoffel_contMDiffOn_chartSource (I := I) (M := M) g α i j k
  have hscalar : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        ((chartModelBasis E).repr (chartE_section_repr (I := I) α X b)) j *
        chartChristoffel (I := I) g α i j k (extChartAt I α b))
      ((chartAt H α).source) :=
    hrepr_smooth.mul hΓ_smooth
  have hblock_const : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun (_ : M) => christoffelBlockCLM (E := E) i k)
      ((chartAt H α).source) :=
    contMDiffOn_const
  exact hscalar.smul hblock_const

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private lemma chartLeviCivitaParallelCLM_trivImage_eq_christoffelCorrectionCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π b : M, TangentSpace I b) {b : M}
    (hb : b ∈ (chartAt H α).source) :
    (trivializationAt (E →L[ℝ] E)
        (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
        ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2 =
      christoffelCorrectionCLM (I := I) g α X b := by
  classical
  have hbase_eq :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [hbase_eq]; exact hb
  have htriv :
      (trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2 =
        ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
          α b α b (chartLeviCivitaParallelCLM (I := I) g α b X) := rfl
  rw [htriv]
  ext w
  have hLHS_unfold :
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
        α b α b (chartLeviCivitaParallelCLM (I := I) g α b X) w =
      trivToE (I := I) α b
        ((chartLeviCivitaParallelCLM (I := I) g α b X) (trivFromE (I := I) α b w)) :=
    rfl
  rw [hLHS_unfold]
  rw [chartLeviCivitaParallelCLM_apply (I := I) g α b X (trivFromE (I := I) α b w)]
  rw [trivToE_trivFromE (I := I) α hb_base]
  have hY :
      trivToE (I := I) α b (X b) =
        chartE_section_repr (I := I) α X b := rfl
  rw [hY]
  exact christoffelCorrection_eq_christoffelCorrectionCLM (I := I) g α X hb_base w

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
theorem chartLeviCivitaParallelCLM_trivImage_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π b : M, TangentSpace I b)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : M =>
        (trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2)
      ((chartAt H α).source) := by
  classical
  have h_χ : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (christoffelCorrectionCLM (I := I) g α X)
      ((chartAt H α).source) :=
    christoffelCorrectionCLM_contMDiffOn_chartSource
      (I := I) (M := M) g α (X := X) hX
  refine h_χ.congr ?_
  intro b hb
  exact (chartLeviCivitaParallelCLM_trivImage_eq_christoffelCorrectionCLM
    (I := I) (M := M) g α X hb)

end ParallelGeneral

section ParallelChartBasis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

private local instance parallelChartBasis_complete_E : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private lemma chartE_section_repr_chartBasisVec_eq_const_on_chart_source
    (α : M) (j : Fin (Module.finrank ℝ E)) :
    ∀ b ∈ (chartAt H α).source,
      chartE_section_repr (I := I) α (chartBasisVecFiber (I := I) α j) b =
        (chartModelBasis E) j := by
  intro b hb
  have hbase_eq :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [hbase_eq]; exact hb
  have h1 :
      chartE_section_repr (I := I) α (chartBasisVecFiber (I := I) α j) b =
        trivToE (I := I) α b (chartBasisVecFiber (I := I) α j b) := rfl
  rw [h1]
  have h2 := trivializationAt_chartBasisVec_snd (I := I) α j (x := b) hb_base
  change (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
      (chartBasisVecFiber (I := I) α j b) = (chartModelBasis E) j
  rw [Bundle.Trivialization.continuousLinearMapAt_apply
    (R := ℝ) (trivializationAt E (TangentSpace I) α) b]
  rw [(trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem
    (R := ℝ) hb_base]
  exact h2

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private lemma chartE_section_repr_chartBasisVec_basis_component_contMDiffOn_chartSource
    (α : M) (j : Fin (Module.finrank ℝ E))
    (j' : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        ((chartModelBasis E).repr
          (chartE_section_repr (I := I) α
            (chartBasisVecFiber (I := I) α j) b)) j')
      ((chartAt H α).source) := by
  classical
  have h_const_on :
      ∀ b ∈ (chartAt H α).source,
        ((chartModelBasis E).repr
          (chartE_section_repr (I := I) α
            (chartBasisVecFiber (I := I) α j) b)) j' =
          (if j' = j then (1 : ℝ) else 0) := by
    intro b hb
    have h_repr_eq :
        chartE_section_repr (I := I) α
          (chartBasisVecFiber (I := I) α j) b =
          (chartModelBasis E) j :=
      chartE_section_repr_chartBasisVec_eq_const_on_chart_source
        (I := I) (M := M) α j b hb
    rw [h_repr_eq]
    have h_repr_self :
        (chartModelBasis E).repr ((chartModelBasis E) j) =
          Finsupp.single j (1 : ℝ) :=
      Module.Basis.repr_self (chartModelBasis E) j
    rw [h_repr_self]
    by_cases hj' : j' = j
    · simp [hj']
    · simp [hj']
  refine ContMDiffOn.congr (contMDiffOn_const (c :=
    (if j' = j then (1 : ℝ) else 0))) ?_
  intro b hb
  exact h_const_on b hb

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
private lemma chartChristoffel_contMDiffOn_chartSource'
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j' k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => chartChristoffel (I := I) g α i j' k (extChartAt I α b))
      ((chartAt H α).source) := by
  classical
  intro b hb_src
  have hφ_at : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) b :=
    contMDiffAt_extChartAt' (I := I) (n := ∞) hb_src
  have h_target_open : IsOpen ((extChartAt I α).target : Set E) :=
    isOpen_extChartAt_target α
  have h_int_eq : interior ((extChartAt I α).target : Set E) =
      (extChartAt I α).target := h_target_open.interior_eq
  have hb_ext_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hb_src
  have hxφ_tgt : extChartAt I α b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_ext_src
  have hxφ_int : extChartAt I α b ∈
      interior ((extChartAt I α).target : Set E) := by
    rw [h_int_eq]; exact hxφ_tgt
  have hΓ_on : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j' k)
      (interior (extChartAt I α).target) :=
    chartChristoffel_contDiffOn_interior (I := I) g α i j' k
  have hΓ_chart : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g α i j' k)
      (extChartAt I α b) :=
    hΓ_on.contDiffAt (isOpen_interior.mem_nhds hxφ_int)
  exact (hΓ_chart.comp_contMDiffAt hφ_at).contMDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
private lemma christoffelCorrectionCLM_chartBasisVec_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (christoffelCorrectionCLM (I := I) g α
        (chartBasisVecFiber (I := I) α j))
      ((chartAt H α).source) := by
  classical
  unfold christoffelCorrectionCLM
  refine contMDiffOn_finset_sum (t := Finset.univ) (fun i _ => ?_)
  refine contMDiffOn_finset_sum (t := Finset.univ) (fun j' _ => ?_)
  refine contMDiffOn_finset_sum (t := Finset.univ) (fun k _ => ?_)
  have hrepr_smooth :=
    chartE_section_repr_chartBasisVec_basis_component_contMDiffOn_chartSource
      (I := I) (M := M) α j j'
  have hΓ_smooth :=
    chartChristoffel_contMDiffOn_chartSource' (I := I) (M := M) g α i j' k
  have hscalar : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        ((chartModelBasis E).repr
          (chartE_section_repr (I := I) α
            (chartBasisVecFiber (I := I) α j) b)) j' *
        chartChristoffel (I := I) g α i j' k (extChartAt I α b))
      ((chartAt H α).source) :=
    hrepr_smooth.mul hΓ_smooth
  have hblock_const : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun (_ : M) => christoffelBlockCLM (E := E) i k)
      ((chartAt H α).source) :=
    contMDiffOn_const
  exact hscalar.smul hblock_const

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
theorem chartLeviCivitaParallelCLM_chartBasisVec_trivImage_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : M =>
        (trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α j)⟩).2)
      ((chartAt H α).source) := by
  classical
  have h_χ : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (christoffelCorrectionCLM (I := I) g α
        (chartBasisVecFiber (I := I) α j))
      ((chartAt H α).source) :=
    christoffelCorrectionCLM_chartBasisVec_contMDiffOn_chartSource
      (I := I) (M := M) g α j
  refine h_χ.congr ?_
  intro b hb
  classical
  have hbase_eq :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [hbase_eq]; exact hb
  ext w
  have hLHS_unfold :
      (trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α j)⟩).2 w =
        ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
          α b α b
          (chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α j)) w := rfl
  rw [hLHS_unfold]
  have hLHS_unfold' :
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
          α b α b
          (chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α j)) w =
        trivToE (I := I) α b
          ((chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α j))
            (trivFromE (I := I) α b w)) := rfl
  rw [hLHS_unfold']
  rw [chartLeviCivitaParallelCLM_apply (I := I) g α b
    (chartBasisVecFiber (I := I) α j) (trivFromE (I := I) α b w)]
  rw [trivToE_trivFromE (I := I) α hb_base]
  have hY :
      trivToE (I := I) α b (chartBasisVecFiber (I := I) α j b) =
        chartE_section_repr (I := I) α
          (chartBasisVecFiber (I := I) α j) b := rfl
  rw [hY]
  exact christoffelCorrection_eq_christoffelCorrectionCLM
    (I := I) g α (chartBasisVecFiber (I := I) α j) hb_base w

end ParallelChartBasis

section SlotSubst

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [CompactSpace M]

private local instance slotSubst_complete_E : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [CompactSpace M] in
private lemma chartLeviCivitaParallelCLM_chartBasisVec_matrixEntry_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (i_out j_in : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        ((chartModelBasis E).repr
          ((trivializationAt (E →L[ℝ] E)
            (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
            ⟨b, chartLeviCivitaParallelCLM (I := I) g α b
              (chartBasisVecFiber (I := I) α j)⟩).2
              ((chartModelBasis E) j_in))) i_out)
      ((chartAt H α).source) := by
  classical
  have hΦ_smooth :
      ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
        (fun b : M =>
          (trivializationAt (E →L[ℝ] E)
            (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
            ⟨b, chartLeviCivitaParallelCLM (I := I) g α b
              (chartBasisVecFiber (I := I) α j)⟩).2)
        ((chartAt H α).source) :=
    chartLeviCivitaParallelCLM_chartBasisVec_trivImage_contMDiffOn_chartSource
      (I := I) (M := M) g α j
  have hbasis_smooth : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun (_ : M) => (chartModelBasis E) j_in)
      ((chartAt H α).source) := contMDiffOn_const
  have hΦv_smooth : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b : M =>
        ((trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α j)⟩).2)
            ((chartModelBasis E) j_in))
      ((chartAt H α).source) :=
    hΦ_smooth.clm_apply hbasis_smooth
  have hcoord_smooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun v : E => ((chartModelBasis E).repr v) i_out) := by
    have h1 : Continuous fun v : E => ((chartModelBasis E).repr v) i_out :=
      ((Finsupp.lapply (R := ℝ) (M := ℝ) (α := Fin (Module.finrank ℝ E)) i_out).comp
        (chartModelBasis E).repr.toLinearMap).continuous_of_finiteDimensional
    let L : E →L[ℝ] ℝ :=
      ((Finsupp.lapply (R := ℝ) (M := ℝ) (α := Fin (Module.finrank ℝ E)) i_out).comp
        (chartModelBasis E).repr.toLinearMap).toContinuousLinearMap
    exact L.contMDiff
  have hfinal : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        ((chartModelBasis E).repr
          ((trivializationAt (E →L[ℝ] E)
            (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
            ⟨b, chartLeviCivitaParallelCLM (I := I) g α b
              (chartBasisVecFiber (I := I) α j)⟩).2
              ((chartModelBasis E) j_in))) i_out)
      ((chartAt H α).source) :=
    hcoord_smooth.comp_contMDiffOn hΦv_smooth
  exact hfinal

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [CompactSpace M] in
private lemma chartJ_chartJinv_on_chartSource
    (α : M) {b : M} (hb : b ∈ (chartAt H α).source) (v : E) :
    chartTrivializationLinearMap (I := I) (M := M) α b
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b v) = v := by
  classical
  have hbase : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  exact chartJ_chartJinv (I := I) (M := M) α hbase v

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [CompactSpace M] in
private lemma chartJinv_chartJ_self_on_chartSource
    (α : M) {b : M} (hb : b ∈ (chartAt H α).source) (v : E) :
    chartTrivializationLinearMapSymm (I := I) (M := M) α b
        (chartTrivializationLinearMap (I := I) (M := M) α b v) = v := by
  classical
  have hbase : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  exact chartJinv_chartJ_self (I := I) (M := M) α hbase v

omit [NeZero (Module.finrank ℝ E)] in
private lemma eval0SCLE_symm_pi_single_at_basis_tuple
    (r : ℕ) (Idx : Fin r → Fin (Module.finrank ℝ E))
    (φ : Fin r → Fin (Module.finrank ℝ E)) :
    ((eval0SCLE (E := E) r).symm
        (Pi.single Idx (1 : ℝ)))
        (fun k : Fin r => (chartModelBasis E) (φ k)) =
      Pi.single (M := fun _ => ℝ) Idx (1 : ℝ) φ := by
  classical
  have h := (eval0SCLE (E := E) r).apply_symm_apply
    (Pi.single Idx (1 : ℝ))
  have h' := congr_fun h φ
  simpa [eval0SCLE_apply] using h'

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [CompactSpace M] in
private lemma slotSubst_trivProj_entry_closedForm
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M) (k : Fin r)
    (X : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source)
    (Idx Jdx : Fin r → Fin (Module.finrank ℝ E)) :
    evalAtBasisCLE_TensorRSModel (E := E) r r
      ((trivializationAt (TensorRSModel r r ℝ E)
        (fun y : M => TensorRSSpace r r I y) α).continuousLinearMapAt ℝ b
        ((tensorSlotSubstCLM (I := I) r b
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b X))) : TensorRSSpace r r I b))
      (Idx, Jdx) =
      (if ∀ i : Fin r, i ≠ k → Idx i = Jdx i then
        (((chartModelBasis E).repr
          (((trivializationAt (E →L[ℝ] E)
            (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
            ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2)
            ((chartModelBasis E) (Jdx k)))) (Idx k))
      else 0) := by
  classical
  have hbridge := triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
    (I := I) (M := M) r r α (b := b) hb
    (T := ((tensorSlotSubstCLM (I := I) r b
        (tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b X))) : TensorRSSpace r r I b))
  rw [hbridge]
  rw [evalAtBasisCLE_TensorRSModel_apply]
  rw [chartRSTwistInv_apply]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hslot_apply :
      ∀ (m : Fin r → TangentSpace I b),
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin r => TangentSpace I b) ℝ from
          (tensorSlotSubstCLM (I := I) r b
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b X)))
            (show Tensor0SSpace r I b from
              (((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))).compContinuousLinearMap
                (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)))) m =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin r => TangentSpace I b) ℝ from
          (show Tensor0SSpace r I b from
            (((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))).compContinuousLinearMap
              (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
          (fun i =>
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b X) i) (m i)) := by
    intro m
    exact tensorSlotSubstCLM_apply (I := I) r b
      (tangentSlotCLM (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b X))
      _ m
  change (show ContinuousMultilinearMap ℝ
        (fun _ : Fin r => TangentSpace I b) ℝ from
      (tensorSlotSubstCLM (I := I) r b
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b X)))
        (show Tensor0SSpace r I b from
          (((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))).compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
      (fun i : Fin r =>
        chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) (Jdx i))) = _
  rw [hslot_apply]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  set Ri : Fin r → E :=
    (fun i : Fin r =>
      chartTrivializationLinearMap (I := I) (M := M) α b
        ((tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b X) i)
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b
            ((chartModelBasis E) (Jdx i)))))
    with hRi_def
  change ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) Ri = _
  by_cases hagree : ∀ i : Fin r, i ≠ k → Idx i = Jdx i
  · rw [if_pos hagree]
    have hRi_other : ∀ i, i ≠ k →
        Ri i = (chartModelBasis E) (Idx i) := by
      intro i hi
      have hother := tangentSlotCLM_other (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b X) (i := i) hi
      simp only [Ri, hother, ContinuousLinearMap.id_apply]
      rw [chartJ_chartJinv_on_chartSource (I := I) (M := M) α hb]
      rw [hagree i hi]
    have hRi_at_k :
        Ri k = ((trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2)
          ((chartModelBasis E) (Jdx k)) := by
      have hself := tangentSlotCLM_self (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b X)
      simp only [Ri, hself]
      rfl
    set M_mat : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
      fun a c => ((chartModelBasis E).repr
        ((trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2
          ((chartModelBasis E) c))) a
      with hM_mat_def
    have hRi_k_decomp :
        Ri k = ∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) • (chartModelBasis E) a := by
      rw [hRi_at_k]
      simp only [hM_mat_def]
      exact ((chartModelBasis E).sum_repr
        ((trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2
          ((chartModelBasis E) (Jdx k)))).symm
    have hsigma_eq :
        ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) Ri =
        ∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) *
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (fun i => if i = k then (chartModelBasis E) a
                      else (chartModelBasis E) (Idx i)) := by
      have hupdate :
          Ri = Function.update Ri k (Ri k) := by
        funext i; simp
      have hRi_update : Ri = Function.update Ri k
          (∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) • (chartModelBasis E) a) := by
        rw [← hRi_k_decomp]
        funext i; by_cases hi : i = k
        · subst hi; simp
        · simp [hi]
      rw [hRi_update]
      have hsum := ((eval0SCLE (E := E) r).symm
        (Pi.single Idx (1 : ℝ))).toMultilinearMap.map_update_sum
        (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (i := k)
        (g := fun a : Fin (Module.finrank ℝ E) => M_mat a (Jdx k) • (chartModelBasis E) a)
        (m := Ri)
      have hsum' :
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (Function.update Ri k
              (∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) • (chartModelBasis E) a)) =
          ∑ a : Fin (Module.finrank ℝ E),
            ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
              (Function.update Ri k (M_mat a (Jdx k) • (chartModelBasis E) a)) := hsum
      rw [hsum']
      refine Finset.sum_congr rfl ?_
      intro a _
      have hsmul := ((eval0SCLE (E := E) r).symm
        (Pi.single Idx (1 : ℝ))).toMultilinearMap.map_update_smul
          (m := Ri) (i := k) (c := M_mat a (Jdx k)) (x := (chartModelBasis E) a)
      have hsmul' :
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (Function.update Ri k (M_mat a (Jdx k) • (chartModelBasis E) a)) =
          M_mat a (Jdx k) •
            ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
              (Function.update Ri k ((chartModelBasis E) a)) := hsmul
      rw [hsmul']
      have hupd_eq :
          Function.update Ri k ((chartModelBasis E) a) =
            fun i => if i = k then (chartModelBasis E) a
                     else (chartModelBasis E) (Idx i) := by
        funext i
        by_cases hi : i = k
        · subst hi; simp
        · simp [hi, hRi_other i hi]
      rw [hupd_eq]
      rw [smul_eq_mul]
    rw [hsigma_eq]
    have hphi_form :
        ∀ a : Fin (Module.finrank ℝ E),
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (fun i => if i = k then (chartModelBasis E) a
                      else (chartModelBasis E) (Idx i)) =
            Pi.single (M := fun _ => ℝ) Idx (1 : ℝ)
              (fun i => if i = k then a else Idx i) := by
      intro a
      have hfeq :
          (fun i : Fin r => if i = k then (chartModelBasis E) a
                            else (chartModelBasis E) (Idx i)) =
          (fun i : Fin r => (chartModelBasis E)
            ((fun i' => if i' = k then a else Idx i') i)) := by
        funext i
        by_cases hi : i = k
        · subst hi; simp
        · simp [hi]
      rw [hfeq]
      have := eval0SCLE_symm_pi_single_at_basis_tuple (E := E) r Idx
        (fun i' => if i' = k then a else Idx i')
      change (show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from
        (eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
        (fun k_0 : Fin r => (chartModelBasis E) (
          (fun i' => if i' = k then a else Idx i') k_0)) = _
      exact this
    have hsum_simp :
        ∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) *
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (fun i => if i = k then (chartModelBasis E) a
                      else (chartModelBasis E) (Idx i)) =
        ∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) *
          Pi.single (M := fun _ => ℝ) Idx (1 : ℝ)
            (fun i => if i = k then a else Idx i) := by
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [hphi_form a]
    rw [hsum_simp]
    have hpi_simp :
        ∀ a : Fin (Module.finrank ℝ E),
          Pi.single (M := fun _ => ℝ) Idx (1 : ℝ)
            (fun i => if i = k then a else Idx i) =
          (if Idx k = a then (1 : ℝ) else 0) := by
      intro a
      classical
      by_cases ha : Idx k = a
      · have hidx_eq : Idx = (fun i : Fin r => if i = k then a else Idx i) := by
          funext i
          by_cases hi : i = k
          · subst hi; simp [ha]
          · simp [hi]
        rw [← hidx_eq]
        rw [Pi.single_eq_same]
        simp [ha]
      · have hne : (fun i : Fin r => if i = k then a else Idx i) ≠ Idx := by
          intro heq
          have hk := congr_fun heq k
          simp at hk
          exact ha hk.symm
        rw [Pi.single_eq_of_ne hne]
        simp [ha]
    have hsum_simp2 :
        ∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) *
          Pi.single (M := fun _ => ℝ) Idx (1 : ℝ)
            (fun i => if i = k then a else Idx i) =
        ∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) *
          (if Idx k = a then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [hpi_simp a]
    rw [hsum_simp2]
    have hcollapse :
        (∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) *
            (if Idx k = a then (1 : ℝ) else 0)) =
          M_mat (Idx k) (Jdx k) := by
      rw [Finset.sum_eq_single (Idx k)]
      · simp
      · intro a _ ha
        have : Idx k ≠ a := fun h => ha h.symm
        simp [this]
      · intro hne
        exfalso; exact hne (Finset.mem_univ _)
    rw [hcollapse]
  · rw [if_neg hagree]
    have hagree' : ∃ i : Fin r, i ≠ k ∧ Idx i ≠ Jdx i := by
      classical
      by_contra hall
      apply hagree
      intro i hi
      by_contra hne
      exact hall ⟨i, hi, hne⟩
    obtain ⟨i₀, hi₀_ne_k, hi₀_disagree⟩ := hagree'
    have hRi_other : ∀ i, i ≠ k →
        Ri i = (chartModelBasis E) (Jdx i) := by
      intro i hi
      have hother := tangentSlotCLM_other (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b X) (i := i) hi
      simp only [Ri, hother, ContinuousLinearMap.id_apply]
      rw [chartJ_chartJinv_on_chartSource (I := I) (M := M) α hb]
    set M_mat : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
      fun a c => ((chartModelBasis E).repr
        ((trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2
          ((chartModelBasis E) c))) a
      with hM_mat_def
    have hRi_at_k :
        Ri k = ((trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2)
          ((chartModelBasis E) (Jdx k)) := by
      have hself := tangentSlotCLM_self (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b X)
      simp only [Ri, hself]
      rfl
    have hRi_k_decomp :
        Ri k = ∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) • (chartModelBasis E) a := by
      rw [hRi_at_k]
      simp only [hM_mat_def]
      exact ((chartModelBasis E).sum_repr
        ((trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2
          ((chartModelBasis E) (Jdx k)))).symm
    have hRi_update : Ri = Function.update Ri k
        (∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) • (chartModelBasis E) a) := by
      rw [← hRi_k_decomp]
      funext i; by_cases hi : i = k
      · subst hi; simp
      · simp [hi]
    have hsigma_eq :
        ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) Ri =
        ∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) *
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (fun i => if i = k then (chartModelBasis E) a
                      else (chartModelBasis E) (Jdx i)) := by
      rw [hRi_update]
      have hsum := ((eval0SCLE (E := E) r).symm
        (Pi.single Idx (1 : ℝ))).toMultilinearMap.map_update_sum
        (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (i := k)
        (g := fun a : Fin (Module.finrank ℝ E) => M_mat a (Jdx k) • (chartModelBasis E) a)
        (m := Ri)
      have hsum' :
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (Function.update Ri k
              (∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) • (chartModelBasis E) a)) =
          ∑ a : Fin (Module.finrank ℝ E),
            ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
              (Function.update Ri k (M_mat a (Jdx k) • (chartModelBasis E) a)) := hsum
      rw [hsum']
      refine Finset.sum_congr rfl ?_
      intro a _
      have hsmul := ((eval0SCLE (E := E) r).symm
        (Pi.single Idx (1 : ℝ))).toMultilinearMap.map_update_smul
          (m := Ri) (i := k) (c := M_mat a (Jdx k)) (x := (chartModelBasis E) a)
      have hsmul' :
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (Function.update Ri k (M_mat a (Jdx k) • (chartModelBasis E) a)) =
          M_mat a (Jdx k) •
            ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
              (Function.update Ri k ((chartModelBasis E) a)) := hsmul
      rw [hsmul']
      have hupd_eq :
          Function.update Ri k ((chartModelBasis E) a) =
            fun i => if i = k then (chartModelBasis E) a
                     else (chartModelBasis E) (Jdx i) := by
        funext i
        by_cases hi : i = k
        · subst hi; simp
        · simp [hi, hRi_other i hi]
      rw [hupd_eq]
      rw [smul_eq_mul]
    rw [hsigma_eq]
    have hphi_zero :
        ∀ a : Fin (Module.finrank ℝ E),
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (fun i => if i = k then (chartModelBasis E) a
                      else (chartModelBasis E) (Jdx i)) = 0 := by
      intro a
      have hfeq :
          (fun i : Fin r => if i = k then (chartModelBasis E) a
                            else (chartModelBasis E) (Jdx i)) =
          (fun i : Fin r => (chartModelBasis E)
            ((fun i' => if i' = k then a else Jdx i') i)) := by
        funext i
        by_cases hi : i = k
        · subst hi; simp
        · simp [hi]
      rw [hfeq]
      have hwell := eval0SCLE_symm_pi_single_at_basis_tuple (E := E) r Idx
        (fun i' => if i' = k then a else Jdx i')
      change (show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from
        (eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
        (fun k_0 : Fin r => (chartModelBasis E) (
          (fun i' => if i' = k then a else Jdx i') k_0)) = 0
      rw [hwell]
      have hne : (fun i : Fin r => if i = k then a else Jdx i) ≠ Idx := by
        intro heq
        have hi₀_val := congr_fun heq i₀
        simp [hi₀_ne_k] at hi₀_val
        exact hi₀_disagree hi₀_val.symm
      rw [Pi.single_eq_of_ne hne]
    rw [show (∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) *
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (fun i => if i = k then (chartModelBasis E) a
                      else (chartModelBasis E) (Jdx i))) = 0 from ?_]
    rw [Finset.sum_eq_zero]
    intro a _
    rw [hphi_zero a]
    simp

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [CompactSpace M] in
theorem tensorSlotSubstCLM_chartLeviCivita_chartBasisVec_trivImage_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (j : Fin (Module.finrank ℝ E)) (k : Fin r) :
    ContMDiffOn I 𝓘(ℝ, TensorRSModel r r ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel r r ℝ E)
          (fun y : M => TensorRSSpace r r I y) α
          ⟨b, ((tensorSlotSubstCLM (I := I) r b
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α j)))) : TensorRSSpace r r I b)⟩).2)
      ((chartAt H α).source) := by
  classical
  change ContMDiffOn I
    𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) ∞
    (fun b : M =>
      (trivializationAt (TensorRSModel r r ℝ E)
        (fun y : M => TensorRSSpace r r I y) α
        ⟨b, TensorRSSpace.ofCLM (𝕜 := ℝ) (I := I)
          (tensorSlotSubstCLM (I := I) r b
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b
                (chartBasisVecFiber (I := I) α j))))⟩).2)
    ((chartAt H α).source)
  rw [contMDiffOn_into_tensorRSModel_of_eval_basis (E := E) (r := r) (s := r) (I := I)]
  intro Idx Jdx
  have hentry_eq :
      ∀ b ∈ (chartAt H α).source,
        evalAtBasisCLE_TensorRSModel (E := E) r r
          ((trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α
            ⟨b, TensorRSSpace.ofCLM (𝕜 := ℝ) (I := I)
              (tensorSlotSubstCLM (I := I) r b
                (tangentSlotCLM (I := I) r k
                  (chartLeviCivitaParallelCLM (I := I) g α b
                    (chartBasisVecFiber (I := I) α j))))⟩).2)
          (Idx, Jdx) =
        (if ∀ i : Fin r, i ≠ k → Idx i = Jdx i then
          (((chartModelBasis E).repr
            (((trivializationAt (E →L[ℝ] E)
              (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
              ⟨b, chartLeviCivitaParallelCLM (I := I) g α b
                (chartBasisVecFiber (I := I) α j)⟩).2)
              ((chartModelBasis E) (Jdx k)))) (Idx k))
        else 0) := by
    intro b hb
    have hbaseHom : b ∈ (trivializationAt (TensorRSModel r r ℝ E)
        (fun y : M => TensorRSSpace r r I y) α).baseSet := by
      change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
        (trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).baseSet
      refine ⟨?_, ?_⟩
      · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
        exact hb
      · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
        exact hb
    have hkey := slotSubst_trivProj_entry_closedForm
      (I := I) (M := M) g r α k
      (X := (chartBasisVecFiber (I := I) α j)) (b := b) hb Idx Jdx
    have hbridge_clmat :
        ∀ T : TensorRSSpace r r I b,
          (trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α).continuousLinearMapAt ℝ b T =
          ((trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α) ⟨b, T⟩).2 := by
      intro T
      have hclmat :
          (trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α).continuousLinearMapAt ℝ b T =
          (trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α).linearMapAt ℝ b T := rfl
      rw [hclmat]
      have hcoe := (trivializationAt (TensorRSModel r r ℝ E)
          (fun y : M => TensorRSSpace r r I y) α).coe_linearMapAt_of_mem
        (R := ℝ) (b := b) hbaseHom
      exact congrFun hcoe T
    rw [hbridge_clmat] at hkey
    exact hkey
  refine ContMDiffOn.congr ?_ hentry_eq
  by_cases hagree : ∀ i : Fin r, i ≠ k → Idx i = Jdx i
  · have hagree_smooth :=
      chartLeviCivitaParallelCLM_chartBasisVec_matrixEntry_contMDiffOn_chartSource
        (I := I) (M := M) g α j (Idx k) (Jdx k)
    refine hagree_smooth.congr ?_
    intro b _
    rw [if_pos hagree]
  · have hzero_smooth : ContMDiffOn I 𝓘(ℝ) ∞ (fun (_ : M) => (0 : ℝ))
        ((chartAt H α).source) := contMDiffOn_const
    refine hzero_smooth.congr ?_
    intro b _
    rw [if_neg hagree]

end SlotSubst

section SlotCorrection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [CompactSpace M]

private local instance slotCorrection_complete_E : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [CompactSpace M] in
private lemma triv_compInput_eq_trivT_compL_trivS
    (r s : ℕ) (α : M) {b : M} (hb : b ∈ (chartAt H α).source)
    (Tb : TensorRSSpace r s I b) (Sb : TensorRSSpace r r I b) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α
        ⟨b, ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb).comp
              (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
            : TensorRSSpace r s I b)⟩).2 =
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, Tb⟩).2).comp
        ((trivializationAt (TensorRSModel r r ℝ E)
          (fun y : M => TensorRSSpace r r I y) α
          ⟨b, Sb⟩).2) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  have hbase_rs : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    refine ⟨?_, ?_⟩
    · exact hb_base
    · exact hb_base
  have hbase_rr : b ∈ (trivializationAt (TensorRSModel r r ℝ E)
      (fun y : M => TensorRSSpace r r I y) α).baseSet := by
    change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet
    exact ⟨hb_base, hb_base⟩
  have hLHS_coe :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb).comp
                (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
              : TensorRSSpace r s I b)⟩).2 =
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb).comp
                (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
              : TensorRSSpace r s I b)) := by
    have hcoeRS := (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
      (R := ℝ) hbase_rs
    have h1 :
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              (((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb).comp
                  (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
                : TensorRSSpace r s I b)) =
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b
              (((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb).comp
                  (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
                : TensorRSSpace r s I b)) := rfl
    rw [h1]
    exact (congrFun hcoeRS _).symm
  have hT_coe :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α ⟨b, Tb⟩).2 =
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Tb := by
    have hcoeRS := (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
      (R := ℝ) hbase_rs
    have h1 :
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Tb =
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b Tb := rfl
    rw [h1]
    exact (congrFun hcoeRS _).symm
  have hS_coe :
      (trivializationAt (TensorRSModel r r ℝ E)
          (fun y : M => TensorRSSpace r r I y) α ⟨b, Sb⟩).2 =
        (trivializationAt (TensorRSModel r r ℝ E)
          (fun y : M => TensorRSSpace r r I y) α).continuousLinearMapAt ℝ b Sb := by
    have hcoeRR := (trivializationAt (TensorRSModel r r ℝ E)
        (fun y : M => TensorRSSpace r r I y) α).coe_linearMapAt_of_mem
      (R := ℝ) hbase_rr
    have h1 :
        (trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α).continuousLinearMapAt ℝ b Sb =
        (trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α).linearMapAt ℝ b Sb := rfl
    rw [h1]
    exact (congrFun hcoeRR _).symm
  rw [hLHS_coe, hT_coe, hS_coe]
  have hbridge_LHS :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
      (I := I) (M := M) r s α (b := b) hb
      (T := (((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb).comp
              (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
            : TensorRSSpace r s I b)))
  have hbridge_T :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
      (I := I) (M := M) r s α (b := b) hb (T := Tb)
  have hbridge_S :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
      (I := I) (M := M) r r α (b := b) hb (T := Sb)
  rw [hbridge_LHS, hbridge_T, hbridge_S]
  refine ContinuousLinearMap.ext ?_
  intro α'
  rw [chartRSTwistInv_apply]
  rw [ContinuousLinearMap.comp_apply, chartRSTwistInv_apply, chartRSTwistInv_apply]
  refine ContinuousMultilinearMap.ext ?_
  intro w
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change
    (show ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ from
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
          (α'.compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
      (fun i => chartTrivializationLinearMapSymm (I := I) (M := M) α b (w i)) = _
  have hinner_round_trip :
      ((((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
            (α'.compContinuousLinearMap
              (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))).compContinuousLinearMap
              (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b)).compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)) =
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
          (α'.compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)) :
          ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) := by
    refine ContinuousMultilinearMap.ext ?_
    intro u
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext kk
    exact chartJinv_chartJ_self (I := I) (M := M) α hb_base (u kk)
  change _ =
    (show ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ from
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
        ((((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
              (α'.compContinuousLinearMap
                (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))).compContinuousLinearMap
                (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b)).compContinuousLinearMap
              (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)))
      (fun i => chartTrivializationLinearMapSymm (I := I) (M := M) α b (w i))
  rw [hinner_round_trip]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [CompactSpace M] in
private lemma triv_compOutput_eq_trivS_compL_trivT
    (r s : ℕ) (α : M) {b : M} (hb : b ∈ (chartAt H α).source)
    (Tb : TensorRSSpace r s I b) (Sb : TensorRSSpace s s I b) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α
        ⟨b, ((show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from Sb).comp
              (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
            : TensorRSSpace r s I b)⟩).2 =
      ((trivializationAt (TensorRSModel s s ℝ E)
          (fun y : M => TensorRSSpace s s I y) α
          ⟨b, Sb⟩).2).comp
        ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, Tb⟩).2) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  have hbase_rs : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    exact ⟨hb_base, hb_base⟩
  have hbase_ss : b ∈ (trivializationAt (TensorRSModel s s ℝ E)
      (fun y : M => TensorRSSpace s s I y) α).baseSet := by
    change b ∈ (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    exact ⟨hb_base, hb_base⟩
  have hLHS_coe :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, ((show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from Sb).comp
                (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
              : TensorRSSpace r s I b)⟩).2 =
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (((show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from Sb).comp
                (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
              : TensorRSSpace r s I b)) := by
    have hcoeRS := (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
      (R := ℝ) hbase_rs
    have h1 :
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              (((show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from Sb).comp
                  (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
                : TensorRSSpace r s I b)) =
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b
              (((show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from Sb).comp
                  (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
                : TensorRSSpace r s I b)) := rfl
    rw [h1]
    exact (congrFun hcoeRS _).symm
  have hT_coe :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α ⟨b, Tb⟩).2 =
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Tb := by
    have hcoeRS := (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
      (R := ℝ) hbase_rs
    have h1 :
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Tb =
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b Tb := rfl
    rw [h1]
    exact (congrFun hcoeRS _).symm
  have hS_coe :
      (trivializationAt (TensorRSModel s s ℝ E)
          (fun y : M => TensorRSSpace s s I y) α ⟨b, Sb⟩).2 =
        (trivializationAt (TensorRSModel s s ℝ E)
          (fun y : M => TensorRSSpace s s I y) α).continuousLinearMapAt ℝ b Sb := by
    have hcoeRR := (trivializationAt (TensorRSModel s s ℝ E)
        (fun y : M => TensorRSSpace s s I y) α).coe_linearMapAt_of_mem
      (R := ℝ) hbase_ss
    have h1 :
        (trivializationAt (TensorRSModel s s ℝ E)
            (fun y : M => TensorRSSpace s s I y) α).continuousLinearMapAt ℝ b Sb =
        (trivializationAt (TensorRSModel s s ℝ E)
            (fun y : M => TensorRSSpace s s I y) α).linearMapAt ℝ b Sb := rfl
    rw [h1]
    exact (congrFun hcoeRR _).symm
  rw [hLHS_coe, hT_coe, hS_coe]
  have hbridge_LHS :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
      (I := I) (M := M) r s α (b := b) hb
      (T := (((show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from Sb).comp
              (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
            : TensorRSSpace r s I b)))
  have hbridge_T :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
      (I := I) (M := M) r s α (b := b) hb (T := Tb)
  have hbridge_S :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
      (I := I) (M := M) s s α (b := b) hb (T := Sb)
  rw [hbridge_LHS, hbridge_T, hbridge_S]
  refine ContinuousLinearMap.ext ?_
  intro α'
  rw [chartRSTwistInv_apply]
  rw [ContinuousLinearMap.comp_apply, chartRSTwistInv_apply, chartRSTwistInv_apply]
  refine ContinuousMultilinearMap.ext ?_
  intro w
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change
    (show ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ from
      (show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from Sb)
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
          (α'.compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
      (fun i => chartTrivializationLinearMapSymm (I := I) (M := M) α b (w i)) = _
  have hround :
      ((((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
            (α'.compContinuousLinearMap
              (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))).compContinuousLinearMap
              (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b)).compContinuousLinearMap
            (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b)) =
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
          (α'.compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)) :
          ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) := by
    refine ContinuousMultilinearMap.ext ?_
    intro u
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext kk
    exact chartJinv_chartJ_self (I := I) (M := M) α hb_base (u kk)
  change _ =
    (show ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ from
      (show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from Sb)
        ((((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
              (α'.compContinuousLinearMap
                (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))).compContinuousLinearMap
                (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b)).compContinuousLinearMap
              (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b)))
      (fun i => chartTrivializationLinearMapSymm (I := I) (M := M) α b (w i))
  rw [hround]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [CompactSpace M] in
theorem chartTensorRSInputSlotCorrection_chartBasisVec_trivImage_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun y : M => TensorRSSpace r s I y) b (T b)))
    (j : Fin (Module.finrank ℝ E)) (k : Fin r) :
    ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => T b')
                (chartBasisVecFiber (I := I) α j) b k⟩).2)
      ((chartAt H α).source) := by
  classical
  have hbase_rs : (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet = (chartAt H α).source := by
    change (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
        (trivializationAt (Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SSpace s I y) α).baseSet = _
    have h_r : (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet =
          (trivializationAt E (TangentSpace I) α).baseSet := rfl
    have h_s : (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet =
          (trivializationAt E (TangentSpace I) α).baseSet := rfl
    rw [h_r, h_s, Set.inter_self]
    exact DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  have hT_proj : ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, T b⟩).2)
      ((chartAt H α).source) := by
    have hsmooth_total :
        ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
          (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun y : M => TensorRSSpace r s I y) x (T x)) := hT
    have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
      (e := trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α)).mp hsmooth_total.contMDiffOn
    rw [hbase_rs] at hrewrite
    exact hrewrite
  have hSubst_proj : ContMDiffOn I 𝓘(ℝ, TensorRSModel r r ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel r r ℝ E)
          (fun y : M => TensorRSSpace r r I y) α
          ⟨b, ((tensorSlotSubstCLM (I := I) r b
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α j))))
              : TensorRSSpace r r I b)⟩).2)
      ((chartAt H α).source) :=
    tensorSlotSubstCLM_chartLeviCivita_chartBasisVec_trivImage_contMDiffOn_chartSource
      (I := I) (M := M) g r α j k
  have hbridge : ∀ b ∈ (chartAt H α).source,
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => T b')
                (chartBasisVecFiber (I := I) α j) b k⟩).2 =
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α
            ⟨b, T b⟩).2).comp
          ((trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α
            ⟨b, ((tensorSlotSubstCLM (I := I) r b
                (tangentSlotCLM (I := I) r k
                  (chartLeviCivitaParallelCLM (I := I) g α b
                    (chartBasisVecFiber (I := I) α j))))
                : TensorRSSpace r r I b)⟩).2) := by
    intro b hb
    have hunfold :
        chartTensorRSInputSlotCorrection (I := I) r s g α
          (fun b' => T b')
          (chartBasisVecFiber (I := I) α j) b k =
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b).comp
          (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from
            ((tensorSlotSubstCLM (I := I) r b
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α j))))
              : TensorRSSpace r r I b))
          : TensorRSSpace r s I b) := by
      unfold chartTensorRSInputSlotCorrection
      rfl
    rw [hunfold]
    exact triv_compInput_eq_trivT_compL_trivS
      (I := I) (M := M) r s α (b := b) hb (Tb := T b)
      (Sb := ((tensorSlotSubstCLM (I := I) r b
        (tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α j))))
        : TensorRSSpace r r I b))
  have hcomp : ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun b : M =>
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α
            ⟨b, T b⟩).2).comp
          ((trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α
            ⟨b, ((tensorSlotSubstCLM (I := I) r b
                (tangentSlotCLM (I := I) r k
                  (chartLeviCivitaParallelCLM (I := I) g α b
                    (chartBasisVecFiber (I := I) α j))))
                : TensorRSSpace r r I b)⟩).2))
      ((chartAt H α).source) := hT_proj.clm_comp hSubst_proj
  refine hcomp.congr ?_
  intro b hb
  exact hbridge b hb

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [CompactSpace M] in
theorem chartTensorRSOutputSlotCorrection_chartBasisVec_trivImage_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun y : M => TensorRSSpace r s I y) b (T b)))
    (j : Fin (Module.finrank ℝ E)) (l : Fin s) :
    ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => T b')
                (chartBasisVecFiber (I := I) α j) b l⟩).2)
      ((chartAt H α).source) := by
  classical
  have hbase_rs : (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet = (chartAt H α).source := by
    change (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
        (trivializationAt (Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SSpace s I y) α).baseSet = _
    have h_r : (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet =
          (trivializationAt E (TangentSpace I) α).baseSet := rfl
    have h_s : (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet =
          (trivializationAt E (TangentSpace I) α).baseSet := rfl
    rw [h_r, h_s, Set.inter_self]
    exact DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  have hT_proj : ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, T b⟩).2)
      ((chartAt H α).source) := by
    have hsmooth_total :
        ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
          (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun y : M => TensorRSSpace r s I y) x (T x)) := hT
    have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
      (e := trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α)).mp hsmooth_total.contMDiffOn
    rw [hbase_rs] at hrewrite
    exact hrewrite
  have hSubst_proj : ContMDiffOn I 𝓘(ℝ, TensorRSModel s s ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel s s ℝ E)
          (fun y : M => TensorRSSpace s s I y) α
          ⟨b, ((tensorSlotSubstCLM (I := I) s b
              (tangentSlotCLM (I := I) s l
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α j))))
              : TensorRSSpace s s I b)⟩).2)
      ((chartAt H α).source) :=
    tensorSlotSubstCLM_chartLeviCivita_chartBasisVec_trivImage_contMDiffOn_chartSource
      (I := I) (M := M) g s α j l
  have hbridge : ∀ b ∈ (chartAt H α).source,
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => T b')
                (chartBasisVecFiber (I := I) α j) b l⟩).2 =
        ((trivializationAt (TensorRSModel s s ℝ E)
            (fun y : M => TensorRSSpace s s I y) α
            ⟨b, ((tensorSlotSubstCLM (I := I) s b
                (tangentSlotCLM (I := I) s l
                  (chartLeviCivitaParallelCLM (I := I) g α b
                    (chartBasisVecFiber (I := I) α j))))
                : TensorRSSpace s s I b)⟩).2).comp
          ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α
            ⟨b, T b⟩).2) := by
    intro b hb
    have hunfold :
        chartTensorRSOutputSlotCorrection (I := I) r s g α
          (fun b' => T b')
          (chartBasisVecFiber (I := I) α j) b l =
        ((show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from
            ((tensorSlotSubstCLM (I := I) s b
              (tangentSlotCLM (I := I) s l
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α j))))
              : TensorRSSpace s s I b)).comp
          (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          : TensorRSSpace r s I b) := by
      unfold chartTensorRSOutputSlotCorrection
      rfl
    rw [hunfold]
    exact triv_compOutput_eq_trivS_compL_trivT
      (I := I) (M := M) r s α (b := b) hb (Tb := T b)
      (Sb := ((tensorSlotSubstCLM (I := I) s b
        (tangentSlotCLM (I := I) s l
          (chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α j))))
        : TensorRSSpace s s I b))
  have hcomp : ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun b : M =>
        ((trivializationAt (TensorRSModel s s ℝ E)
            (fun y : M => TensorRSSpace s s I y) α
            ⟨b, ((tensorSlotSubstCLM (I := I) s b
                (tangentSlotCLM (I := I) s l
                  (chartLeviCivitaParallelCLM (I := I) g α b
                    (chartBasisVecFiber (I := I) α j))))
                : TensorRSSpace s s I b)⟩).2).comp
          ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α
            ⟨b, T b⟩).2))
      ((chartAt H α).source) := hSubst_proj.clm_comp hT_proj
  refine hcomp.congr ?_
  intro b hb
  exact hbridge b hb

end SlotCorrection

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
