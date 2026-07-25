import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.IntrinsicComponent
import DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.ChartTwistIdentity
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivative


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators
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
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def chartFrameBasisModel (α b : M) (r : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E)) :
    Tensor0SSpace r I b :=
  (dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
    (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartFrameBasisModel_apply (α b : M) (r : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (v : Fin r → TangentSpace I b) :
    chartFrameBasisModel (I := I) (M := M) α b r Idx v =
      ∏ k : Fin r,
        ((chartModelBasis E).coord (Idx k))
          (chartTrivializationLinearMap (I := I) (M := M) α b (v k)) := by
  classical
  have h : ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)) v =
      ∏ k : Fin r,
        ((chartModelBasis E).coord (Idx k))
          (chartTrivializationLinearMap (I := I) (M := M) α b (v k)) := by
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      dualCovariantCMM_apply]
  exact h

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartFrameBasisModel_apply_chartFrameTuple (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (r : ℕ)
    (Idx Jdx : Fin r → Fin (Module.finrank ℝ E)) :
    chartFrameBasisModel (I := I) (M := M) α b r Idx
        (fun k : Fin r => chartBasisVecFiber (I := I) α (Jdx k) b) =
      if Idx = Jdx then (1 : ℝ) else 0 := by
  classical
  rw [chartFrameBasisModel_apply]
  have hchartJ : ∀ k : Fin r,
      chartTrivializationLinearMap (I := I) (M := M) α b
          (chartBasisVecFiber (I := I) α (Jdx k) b) =
        (chartModelBasis E) (Jdx k) := by
    intro k
    have hcbf : chartBasisVecFiber (I := I) α (Jdx k) b =
        chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) (Jdx k)) := by
      unfold chartBasisVecFiber chartTrivializationLinearMapSymm
      rfl
    rw [hcbf]
    exact chartJ_chartJinv (I := I) (M := M) α hb ((chartModelBasis E) (Jdx k))
  rw [Finset.prod_congr rfl (fun k _ => by rw [hchartJ k])]
  by_cases hEq : Idx = Jdx
  · subst hEq
    rw [if_pos rfl]
    refine (Finset.prod_eq_one ?_).trans rfl
    intro k _
    rw [Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, if_pos rfl]
  · rw [if_neg hEq]
    have h_exists : ∃ k : Fin r, Idx k ≠ Jdx k := by
      by_contra h_all
      exact hEq (funext fun k => by
        by_contra hne
        exact h_all ⟨k, hne⟩)
    obtain ⟨k₀, hk₀⟩ := h_exists
    refine Finset.prod_eq_zero (Finset.mem_univ k₀) ?_
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    exact if_neg hk₀.symm

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma sum_chartFrame_coord_eq (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (w : E) :
    ∑ p : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).coord p) (chartTrivializationLinearMap (I := I) (M := M) α b w) •
          chartBasisVecFiber (I := I) α p b = w := by
  classical
  have hbasis : ∑ p : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).coord p) (chartTrivializationLinearMap (I := I) (M := M) α b w) •
          (chartModelBasis E) p =
      chartTrivializationLinearMap (I := I) (M := M) α b w := by
    have hrep := (chartModelBasis E).sum_repr (chartTrivializationLinearMap (I := I) (M := M) α b w)
    rw [show (∑ p : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).coord p) (chartTrivializationLinearMap (I := I) (M := M) α b w) •
            (chartModelBasis E) p) =
        ∑ p : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (chartTrivializationLinearMap (I := I) (M := M) α b w)) p •
            (chartModelBasis E) p from
      Finset.sum_congr rfl (fun p _ => by rw [Module.Basis.coord_apply])]
    exact hrep
  have hcbf : ∀ p : Fin (Module.finrank ℝ E),
      chartBasisVecFiber (I := I) α p b =
        chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) p) := by
    intro p
    unfold chartBasisVecFiber chartTrivializationLinearMapSymm
    rfl
  calc ∑ p : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).coord p) (chartTrivializationLinearMap (I := I) (M := M) α b w) •
            chartBasisVecFiber (I := I) α p b
      = ∑ p : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).coord p) (chartTrivializationLinearMap (I := I) (M := M) α b w) •
            chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) p) := by
        exact Finset.sum_congr rfl (fun p _ => by rw [hcbf p])
    _ = chartTrivializationLinearMapSymm (I := I) (M := M) α b
          (∑ p : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).coord p) (chartTrivializationLinearMap (I := I) (M := M) α b w) •
              (chartModelBasis E) p) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun p _ => by rw [map_smul])
    _ = chartTrivializationLinearMapSymm (I := I) (M := M) α b (chartTrivializationLinearMap (I := I) (M := M) α b w) := by
        rw [hbasis]
    _ = w := chartJinv_chartJ_self (I := I) (M := M) α hb w

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensor0S_eq_sum_chartFrameBasis (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (r : ℕ)
    (f : Tensor0SSpace r I b) :
    f = ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          f (fun k : Fin r => chartBasisVecFiber (I := I) α (Idx k) b) •
            chartFrameBasisModel (I := I) (M := M) α b r Idx := by
  classical
  refine tensor0SSpace_ext r b (fun v => ?_)
  have hv_eq : v =
      fun k : Fin r => ∑ p : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).coord p)
            (chartTrivializationLinearMap (I := I) (M := M) α b (v k)) •
          chartBasisVecFiber (I := I) α p b := by
    funext k
    exact (sum_chartFrame_coord_eq (I := I) (M := M) α hb (v k)).symm
  rw [show f v = f (fun k : Fin r =>
        ∑ p : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).coord p)
              (chartTrivializationLinearMap (I := I) (M := M) α b (v k)) •
            chartBasisVecFiber (I := I) α p b) from congrArg f hv_eq]
  rw [ContinuousMultilinearMap.map_sum
    (f := f)
    (g := fun (k : Fin r) (p : Fin (Module.finrank ℝ E)) =>
      ((chartModelBasis E).coord p) (chartTrivializationLinearMap (I := I) (M := M) α b (v k)) •
        chartBasisVecFiber (I := I) α p b)]
  have h_pull : ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      f (fun k : Fin r =>
          ((chartModelBasis E).coord (Idx k))
              (chartTrivializationLinearMap (I := I) (M := M) α b (v k)) •
            chartBasisVecFiber (I := I) α (Idx k) b) =
        (∏ k : Fin r, ((chartModelBasis E).coord (Idx k))
            (chartTrivializationLinearMap (I := I) (M := M) α b (v k))) *
          f (fun k : Fin r => chartBasisVecFiber (I := I) α (Idx k) b) := by
    intro Idx
    have hpull := f.toMultilinearMap.map_smul_univ
      (c := fun k : Fin r => ((chartModelBasis E).coord (Idx k))
        (chartTrivializationLinearMap (I := I) (M := M) α b (v k)))
      (m := fun k : Fin r => chartBasisVecFiber (I := I) α (Idx k) b)
    have hpull' :
        f (fun k : Fin r =>
            ((chartModelBasis E).coord (Idx k))
                (chartTrivializationLinearMap (I := I) (M := M) α b (v k)) •
              chartBasisVecFiber (I := I) α (Idx k) b) =
          (∏ k : Fin r, ((chartModelBasis E).coord (Idx k))
              (chartTrivializationLinearMap (I := I) (M := M) α b (v k))) •
            f (fun k : Fin r => chartBasisVecFiber (I := I) α (Idx k) b) := hpull
    rw [hpull']
    rfl
  rw [show ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        f (fun k : Fin r =>
            ((chartModelBasis E).coord (Idx k))
                (chartTrivializationLinearMap (I := I) (M := M) α b (v k)) •
              chartBasisVecFiber (I := I) α (Idx k) b) =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        (∏ k : Fin r, ((chartModelBasis E).coord (Idx k))
            (chartTrivializationLinearMap (I := I) (M := M) α b (v k))) *
          f (fun k : Fin r => chartBasisVecFiber (I := I) α (Idx k) b) from
    Finset.sum_congr rfl (fun Idx _ => h_pull Idx)]
  rw [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun Idx _ => ?_)
  rw [ContinuousMultilinearMap.smul_apply, chartFrameBasisModel_apply,
    smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tensorSlotSubstCLM_eval (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b))
    (τ : Tensor0SSpace n I b) (m : Fin n → TangentSpace I b) :
    (tensorSlotSubstCLM (I := I) n b Φ τ) m =
      τ (fun i : Fin n => Φ i (m i)) :=
  tensorSlotSubstCLM_apply (I := I) n b Φ τ m

noncomputable def chartFrameMatrixEntry (α b : M)
    (Ψ : TangentSpace I b →L[ℝ] TangentSpace I b)
    (p q : Fin (Module.finrank ℝ E)) : ℝ :=
  ((chartModelBasis E).coord p)
    (chartTrivializationLinearMap (I := I) (M := M) α b (Ψ (chartBasisVecFiber (I := I) α q b)))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartFrameMatrixEntry_def (α b : M)
    (Ψ : TangentSpace I b →L[ℝ] TangentSpace I b)
    (p q : Fin (Module.finrank ℝ E)) :
    chartFrameMatrixEntry (I := I) (M := M) α b Ψ p q =
      ((chartModelBasis E).coord p)
        (chartTrivializationLinearMap (I := I) (M := M) α b
          (Ψ (chartBasisVecFiber (I := I) α q b))) := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma slotCLM_chartFrameVec_eq (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (Ψ : TangentSpace I b →L[ℝ] TangentSpace I b)
    (q : Fin (Module.finrank ℝ E)) :
    Ψ (chartBasisVecFiber (I := I) α q b) =
      ∑ p : Fin (Module.finrank ℝ E),
        chartFrameMatrixEntry (I := I) (M := M) α b Ψ p q •
          chartBasisVecFiber (I := I) α p b := by
  classical
  have h := sum_chartFrame_coord_eq (I := I) (M := M) α hb
    (Ψ (chartBasisVecFiber (I := I) α q b))
  rw [← h]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [chartFrameMatrixEntry_def]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensor0S_apply_slotTransform_chartFrameBasis_eq_sum (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (s : ℕ)
    (σ : Tensor0SSpace s I b)
    (Φ : Fin s → (TangentSpace I b →L[ℝ] TangentSpace I b))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    σ (fun j : Fin s =>
        Φ j (chartBasisVecFiber (I := I) α (Jdx j) b)) =
      ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
        (∏ j : Fin s,
            chartFrameMatrixEntry (I := I) (M := M) α b (Φ j)
              (Jdx' j) (Jdx j)) *
          σ (fun j : Fin s => chartBasisVecFiber (I := I) α (Jdx' j) b) := by
  classical
  have hslot_eq : (fun j : Fin s =>
        Φ j (chartBasisVecFiber (I := I) α (Jdx j) b)) =
      fun j : Fin s => ∑ p : Fin (Module.finrank ℝ E),
        chartFrameMatrixEntry (I := I) (M := M) α b (Φ j) p (Jdx j) •
          chartBasisVecFiber (I := I) α p b := by
    funext j
    exact slotCLM_chartFrameVec_eq (I := I) (M := M) α hb (Φ j) (Jdx j)
  rw [show σ (fun j : Fin s =>
        Φ j (chartBasisVecFiber (I := I) α (Jdx j) b)) =
      σ (fun j : Fin s => ∑ p : Fin (Module.finrank ℝ E),
          chartFrameMatrixEntry (I := I) (M := M) α b (Φ j) p (Jdx j) •
            chartBasisVecFiber (I := I) α p b) from congrArg σ hslot_eq]
  rw [ContinuousMultilinearMap.map_sum
    (f := σ)
    (g := fun (j : Fin s) (p : Fin (Module.finrank ℝ E)) =>
      chartFrameMatrixEntry (I := I) (M := M) α b (Φ j) p (Jdx j) •
        chartBasisVecFiber (I := I) α p b)]
  refine Finset.sum_congr rfl (fun Jdx' _ => ?_)
  have hpull := σ.toMultilinearMap.map_smul_univ
    (c := fun j : Fin s =>
      chartFrameMatrixEntry (I := I) (M := M) α b (Φ j) (Jdx' j) (Jdx j))
    (m := fun j : Fin s => chartBasisVecFiber (I := I) α (Jdx' j) b)
  have hpull' :
      σ (fun j : Fin s =>
          chartFrameMatrixEntry (I := I) (M := M) α b (Φ j) (Jdx' j) (Jdx j) •
            chartBasisVecFiber (I := I) α (Jdx' j) b) =
        (∏ j : Fin s,
            chartFrameMatrixEntry (I := I) (M := M) α b (Φ j)
              (Jdx' j) (Jdx j)) •
          σ (fun j : Fin s => chartBasisVecFiber (I := I) α (Jdx' j) b) := hpull
  rw [hpull', smul_eq_mul]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorSlotSubstCLM_proj_eq (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (r : ℕ)
    (Φ : Fin r → (TangentSpace I b →L[ℝ] TangentSpace I b))
    (τ : Tensor0SSpace r I b)
    (Idx : Fin r → Fin (Module.finrank ℝ E)) :
    (tensorSlotSubstCLM (I := I) r b Φ τ)
        (fun k : Fin r => chartBasisVecFiber (I := I) α (Idx k) b) =
      ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
        (∏ i : Fin r,
            chartFrameMatrixEntry (I := I) (M := M) α b (Φ i)
              (Idx' i) (Idx i)) *
          τ (fun k : Fin r => chartBasisVecFiber (I := I) α (Idx' k) b) := by
  classical
  rw [tensorSlotSubstCLM_eval (I := I) r b Φ τ
    (fun k : Fin r => chartBasisVecFiber (I := I) α (Idx k) b)]
  exact tensor0S_apply_slotTransform_chartFrameBasis_eq_sum (I := I) (M := M) α hb r τ Φ Idx

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma coord_christoffelCorrection_eq
    (g : SmoothRiemannianMetric I M) (α b : M) (Y : E)
    (v : TangentSpace I b) (p : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).coord p)
        (christoffelCorrection (I := I) g α b Y v) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (trivToE (I := I) α b v)) i *
            ((chartModelBasis E).repr Y) j *
            chartChristoffel (I := I) g α i j p (extChartAt I α b) := by
  classical
  rw [christoffelCorrection_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_sum]
  rw [Finset.sum_eq_single p]
  · rw [map_smul, smul_eq_mul]
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      if_pos rfl, mul_one]
  · intro k' _ hk'
    rw [map_smul, smul_eq_mul]
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      if_neg hk', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartJ_chartLeviCivitaParallelCLM
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (X : Π b' : M, TangentSpace I b') (v : TangentSpace I b) :
    chartTrivializationLinearMap (I := I) (M := M) α b
        (chartLeviCivitaParallelCLM (I := I) g α b X v) =
      christoffelCorrection (I := I) g α b
        (trivToE (I := I) α b (X b)) v := by
  classical
  rw [chartLeviCivitaParallelCLM_apply]
  change chartTrivializationLinearMap (I := I) (M := M) α b
      (chartTrivializationLinearMapSymm (I := I) (M := M) α b
        (christoffelCorrection (I := I) g α b
          (trivToE (I := I) α b (X b)) v)) = _
  exact chartJ_chartJinv (I := I) (M := M) α hb _

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (m : Fin (Module.finrank ℝ E))
    (p q : Fin (Module.finrank ℝ E)) :
    chartFrameMatrixEntry (I := I) (M := M) α b
        (chartLeviCivitaParallelCLM (I := I) g α b
          (chartBasisVecFiber (I := I) α m)) p q =
      chartChristoffel (I := I) g α q m p (extChartAt I α b) := by
  classical
  rw [chartFrameMatrixEntry_def]
  rw [chartJ_chartLeviCivitaParallelCLM (I := I) (M := M) g α hb
    (chartBasisVecFiber (I := I) α m)
    (chartBasisVecFiber (I := I) α q b)]
  rw [coord_christoffelCorrection_eq (I := I) g α b
    (trivToE (I := I) α b (chartBasisVecFiber (I := I) α m b))
    (chartBasisVecFiber (I := I) α q b) p]
  have htriv_of : ∀ n' : Fin (Module.finrank ℝ E),
      trivToE (I := I) α b (chartBasisVecFiber (I := I) α n' b) =
        (chartModelBasis E) n' := by
    intro n'
    change chartTrivializationLinearMap (I := I) (M := M) α b
        (chartBasisVecFiber (I := I) α n' b) = (chartModelBasis E) n'
    have hcbf : chartBasisVecFiber (I := I) α n' b =
        chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) n') := by
      unfold chartBasisVecFiber chartTrivializationLinearMapSymm
      rfl
    rw [hcbf]
    exact chartJ_chartJinv (I := I) (M := M) α hb ((chartModelBasis E) n')
  have hv_coord : ∀ i : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
          (trivToE (I := I) α b (chartBasisVecFiber (I := I) α q b))) i =
        if q = i then (1 : ℝ) else 0 := by
    intro i
    rw [htriv_of q, Module.Basis.repr_self, Finsupp.single_apply]
  have hY_coord : ∀ j : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
          (trivToE (I := I) α b (chartBasisVecFiber (I := I) α m b))) j =
        if m = j then (1 : ℝ) else 0 := by
    intro j
    rw [htriv_of m, Module.Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_congr rfl (fun i _ =>
    Finset.sum_congr rfl (fun j _ => by
      rw [hv_coord i, hY_coord j]))]
  rw [Finset.sum_eq_single q]
  · rw [Finset.sum_eq_single m]
    · rw [if_pos rfl, if_pos rfl, one_mul, one_mul]
    · intro j _ hj
      rw [if_neg (Ne.symm hj), mul_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ m) h
  · intro i _ hi
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [if_neg (Ne.symm hi), zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ q) h

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaParallelCLM_coordEntry_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (p q : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        chartFrameMatrixEntry (I := I) (M := M) α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartLeviCivitaParallelCLM (I := I) g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            (chartBasisVecFiber (I := I) α m))
          p q)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ContDiffOn.congr (chartChristoffelEuclid_contDiffOn (I := I) (M := M)
    g α q m p) ?_
  intro y hy
  have hb_chart : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hphi_b : extChartAt I α
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      (toEuclidean (E := E)).symm y :=
    (extChartAt I α).right_inv hy_pre
  rw [chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) (M := M)
    g α hb_base m p q]
  rw [hphi_b, chartChristoffelEuclid_def]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartFrameMatrixEntry_id (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (p q : Fin (Module.finrank ℝ E)) :
    chartFrameMatrixEntry (I := I) (M := M) α b
        (ContinuousLinearMap.id ℝ (TangentSpace I b)) p q =
      if q = p then (1 : ℝ) else 0 := by
  classical
  rw [chartFrameMatrixEntry_def]
  have hid : (ContinuousLinearMap.id ℝ (TangentSpace I b))
      (chartBasisVecFiber (I := I) α q b) =
      chartBasisVecFiber (I := I) α q b := rfl
  rw [hid]
  have htriv : chartTrivializationLinearMap (I := I) (M := M) α b
      (chartBasisVecFiber (I := I) α q b) = (chartModelBasis E) q := by
    have hcbf : chartBasisVecFiber (I := I) α q b =
        chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) q) := by
      unfold chartBasisVecFiber chartTrivializationLinearMapSymm
      rfl
    rw [hcbf]
    exact chartJ_chartJinv (I := I) (M := M) α hb ((chartModelBasis E) q)
  rw [htriv, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_eq_chartFrame
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) {b : M}
    (hb : b ∈ (chartAt H α).source)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b =
      (S.toSection b : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        (chartFrameBasisModel (I := I) (M := M) α b r Idx)
        (fun j : Fin s => chartBasisVecFiber (I := I) α (Jdx j) b) := by
  classical
  rw [tensorChartComponentRaw_def]
  unfold tensorTrivProj
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb (S.toSection b)]
  rw [tensorChartComponentProjection_apply, chartRSTwistInv_apply]
  rfl

noncomputable def inputSlotCoeff
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E)) (k : Fin r)
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    ∏ i : Fin r,
      chartFrameMatrixEntry (I := I) (M := M) α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            (chartBasisVecFiber (I := I) α m))
          i)
        (Idx i) (Idx' i)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma inputSlotCoeff_eq_entry_mul_const
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E)) (k : Fin r)
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y =
      chartFrameMatrixEntry (I := I) (M := M) α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartLeviCivitaParallelCLM (I := I) g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            (chartBasisVecFiber (I := I) α m))
          (Idx k) (Idx' k) *
        ∏ i ∈ Finset.univ.erase k,
          (if Idx' i = Idx i then (1 : ℝ) else 0) := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  unfold inputSlotCoeff
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  congr 1
  · rw [tangentSlotCLM_self]
  · refine Finset.prod_congr rfl (fun i hi => ?_)
    have hi_ne : i ≠ k := Finset.ne_of_mem_erase hi
    rw [tangentSlotCLM_other (I := I) r k _ hi_ne,
      chartFrameMatrixEntry_id (I := I) (M := M) α hb_base]

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem inputSlotCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E)) (k : Fin r)
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx')
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hconst : ContDiffOn ℝ ∞
      (fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        ∏ i ∈ Finset.univ.erase k,
          (if Idx' i = Idx i then (1 : ℝ) else 0))
      (chartTargetEuclid (I := I) (M := M) α) := contDiffOn_const
  refine ContDiffOn.congr
    ((chartLeviCivitaParallelCLM_coordEntry_contDiffOn (I := I) (M := M)
        g α m (Idx k) (Idx' k)).mul hconst) ?_
  intro y hy
  rw [inputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g r α m k Idx Idx' hy]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma inputSlotCoeff_eq_chartFrameProj
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E)) (k : Fin r)
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    {b : M} (hb_def : b = (extChartAt I α).symm ((toEuclidean (E := E)).symm y)) :
    inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y =
      (tensorSlotSubstCLM (I := I) r b
        (tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α m)))
        (chartFrameBasisModel (I := I) (M := M) α b r Idx))
        (fun i : Fin r => chartBasisVecFiber (I := I) α (Idx' i) b) := by
  classical
  subst hb_def
  rw [tensorSlotSubstCLM_eval (I := I) r
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    (tangentSlotCLM (I := I) r k
      (chartLeviCivitaParallelCLM (I := I) g α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartBasisVecFiber (I := I) α m)))
    (chartFrameBasisModel (I := I) (M := M) α
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) r Idx)
    (fun i : Fin r => chartBasisVecFiber (I := I) α (Idx' i)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))]
  rw [chartFrameBasisModel_apply]
  unfold inputSlotCoeff
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [chartFrameMatrixEntry_def]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartTensorRSInputSlotCorrection_component_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E)) (k : Fin r)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTensorRSInputSlotCorrection (I := I) r s g α S.toSection
            (chartBasisVecFiber (I := I) α m)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) k)) =
      ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
        inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
          tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  set Sb : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b := S.toSection b
    with hSb_def
  set ψIdx : Tensor0SSpace r I b :=
    tensorSlotSubstCLM (I := I) r b
      (tangentSlotCLM (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b
          (chartBasisVecFiber (I := I) α m)))
      (chartFrameBasisModel (I := I) (M := M) α b r Idx) with hψIdx_def
  have htuple : (fun i : Fin s =>
        chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) (Jdx i))) =
      (fun j : Fin s => chartBasisVecFiber (I := I) α (Jdx j) b) := by
    funext j
    show chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) (Jdx j)) =
      chartBasisVecFiber (I := I) α (Jdx j) b
    unfold chartBasisVecFiber chartTrivializationLinearMapSymm
    rfl
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb_chart _, tensorChartComponentProjection_apply, chartRSTwistInv_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change (Sb ψIdx)
      (fun i : Fin s =>
        chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) (Jdx i))) =
    ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
      inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b
  have hψexp : ψIdx =
      ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
        inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y •
          chartFrameBasisModel (I := I) (M := M) α b r Idx' := by
    refine (tensor0S_eq_sum_chartFrameBasis (I := I) (M := M) α hb_base r ψIdx).trans ?_
    refine Finset.sum_congr rfl (fun Idx' _ => ?_)
    refine congrArg (fun c : ℝ => c •
      chartFrameBasisModel (I := I) (M := M) α b r Idx') ?_
    rw [hψIdx_def]
    exact (inputSlotCoeff_eq_chartFrameProj (I := I) (M := M) g r α m k Idx Idx'
      hb_def).symm
  rw [hψexp, map_sum Sb, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun Idx' _ => ?_)
  rw [map_smul Sb, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g r s S α
    hb_chart Idx' Jdx, htuple, hSb_def]

noncomputable def outputSlotCoeff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E)) (l : Fin s)
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    ∏ j : Fin s,
      chartFrameMatrixEntry (I := I) (M := M) α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (tangentSlotCLM (I := I) s l
          (chartLeviCivitaParallelCLM (I := I) g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            (chartBasisVecFiber (I := I) α m))
          j)
        (Jdx' j) (Jdx j)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma outputSlotCoeff_eq_entry_mul_const
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E)) (l : Fin s)
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y =
      chartFrameMatrixEntry (I := I) (M := M) α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartLeviCivitaParallelCLM (I := I) g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            (chartBasisVecFiber (I := I) α m))
          (Jdx' l) (Jdx l) *
        ∏ j ∈ Finset.univ.erase l,
          (if Jdx j = Jdx' j then (1 : ℝ) else 0) := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  unfold outputSlotCoeff
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l)]
  congr 1
  · rw [tangentSlotCLM_self]
  · refine Finset.prod_congr rfl (fun j hj => ?_)
    have hj_ne : j ≠ l := Finset.ne_of_mem_erase hj
    rw [tangentSlotCLM_other (I := I) s l _ hj_ne,
      chartFrameMatrixEntry_id (I := I) (M := M) α hb_base]

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem outputSlotCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E)) (l : Fin s)
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx')
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hconst : ContDiffOn ℝ ∞
      (fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        ∏ j ∈ Finset.univ.erase l,
          (if Jdx j = Jdx' j then (1 : ℝ) else 0))
      (chartTargetEuclid (I := I) (M := M) α) := contDiffOn_const
  refine ContDiffOn.congr
    ((chartLeviCivitaParallelCLM_coordEntry_contDiffOn (I := I) (M := M)
        g α m (Jdx' l) (Jdx l)).mul hconst) ?_
  intro y hy
  rw [outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g s α m l Jdx Jdx' hy]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma outputSlotCoeff_eq_chartFrameProj
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E)) (l : Fin s)
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    {b : M} (hb_def : b = (extChartAt I α).symm ((toEuclidean (E := E)).symm y)) :
    outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y =
      ∏ j : Fin s,
        chartFrameMatrixEntry (I := I) (M := M) α b
          (tangentSlotCLM (I := I) s l
            (chartLeviCivitaParallelCLM (I := I) g α b
              (chartBasisVecFiber (I := I) α m))
            j)
          (Jdx' j) (Jdx j) := by
  classical
  subst hb_def
  unfold outputSlotCoeff
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartTensorRSOutputSlotCorrection_component_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E)) (l : Fin s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTensorRSOutputSlotCorrection (I := I) r s g α S.toSection
            (chartBasisVecFiber (I := I) α m)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) l)) =
      ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
        outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
          tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx'
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  set Sb : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b := S.toSection b
    with hSb_def
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb_chart _, tensorChartComponentProjection_apply, chartRSTwistInv_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change (tensorSlotSubstCLM (I := I) s b
        (tangentSlotCLM (I := I) s l
          (chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α m)))
        (Sb (chartFrameBasisModel (I := I) (M := M) α b r Idx)))
      (fun j : Fin s => chartBasisVecFiber (I := I) α (Jdx j) b) =
    ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
      outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx' b
  rw [tensorSlotSubstCLM_eval (I := I) s b
    (tangentSlotCLM (I := I) s l
      (chartLeviCivitaParallelCLM (I := I) g α b
        (chartBasisVecFiber (I := I) α m)))
    (Sb (chartFrameBasisModel (I := I) (M := M) α b r Idx))
    (fun j : Fin s => chartBasisVecFiber (I := I) α (Jdx j) b)]
  rw [tensor0S_apply_slotTransform_chartFrameBasis_eq_sum (I := I) (M := M) α hb_base s
    (Sb (chartFrameBasisModel (I := I) (M := M) α b r Idx))
    (tangentSlotCLM (I := I) s l
      (chartLeviCivitaParallelCLM (I := I) g α b
        (chartBasisVecFiber (I := I) α m)))
    Jdx]
  refine Finset.sum_congr rfl (fun Jdx' _ => ?_)
  rw [← outputSlotCoeff_eq_chartFrameProj (I := I) (M := M) g s α m l Jdx Jdx'
    hb_def,
    tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g r s S α
      hb_chart Idx Jdx', hSb_def]

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
