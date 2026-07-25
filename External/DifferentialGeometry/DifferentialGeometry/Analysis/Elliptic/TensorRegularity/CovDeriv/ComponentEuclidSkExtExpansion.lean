import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.SecondCovDerivExpansion.SkExtChartComponentEqCovDerivEuclid
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.SecondCovDerivExpansion.ChartProjectionSecondCovDerivViaSkExt
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ComponentSecondFormula


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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem chartPushedRaw_eqOn_covDerivComponentEuclid_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E))
    {b₀ : M} (hb₀ : b₀ ∈ chartLeviCivitaGoodSet (I := I) α) :
    ∃ S_k_ext : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                       fun b : M => TensorRSSpace r s I b⟯,
    ∃ V : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
      IsOpen V ∧
      V ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      (toEuclidean (E := E)) ((extChartAt I α) b₀) ∈ V ∧
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        Set.EqOn
          (chartPushedRaw I α
            (fun b : M =>
              tensorChartComponentProjection r s Idx Jdx
                ((trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ
                  b ((S_k_ext : Π b' : M, TensorRSSpace r s I b') b))))
          (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx)
          V := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  obtain ⟨S_k_ext, U, hU_open, hb₀_U, hU_sub_good, hU_eq⟩ :=
    covApply_covRS_chartBasis_globalSmoothExtension
      (I := I) (M := M) g r s α T₀ k (b₀ := b₀) hb₀
  set V : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartTargetEuclid (I := I) (M := M) α ∩
      {y | (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ U} with hV_def
  have hchartT_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hcont_te : Continuous
      ((toEuclidean (E := E)).symm :
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E) :=
    (toEuclidean (E := E)).symm.continuous
  have hcont_extsymm :
      ContinuousOn (extChartAt I α).symm (extChartAt I α).target :=
    continuousOn_extChartAt_symm α
  have hmap_target : MapsTo
      ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α)
      (extChartAt I α).target := by
    intro y hy
    rcases hy with ⟨z, hz_target, hz_eq⟩
    have hyz : (toEuclidean (E := E)).symm y = z := by
      rw [← hz_eq]; exact (toEuclidean (E := E)).symm_apply_apply _
    rw [hyz]; exact hz_target
  have hcont_comp :
      ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) :=
    hcont_extsymm.comp hcont_te.continuousOn hmap_target
  have hV_open : IsOpen V := hcont_comp.isOpen_inter_preimage hchartT_open hU_open
  have hV_sub : V ⊆ chartTargetEuclid (I := I) (M := M) α := fun y hy => hy.1
  have hb₀_good : b₀ ∈ chartLeviCivitaGoodSet (I := I) α := hU_sub_good hb₀_U
  have hb₀_src : b₀ ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb₀_good
  have hb₀_tgt : (extChartAt I α) b₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb₀_src
  have hb₀_V : (toEuclidean (E := E)) ((extChartAt I α) b₀) ∈ V := by
    refine ⟨⟨(extChartAt I α) b₀, hb₀_tgt, rfl⟩, ?_⟩
    change (extChartAt I α).symm
        ((toEuclidean (E := E)).symm
          ((toEuclidean (E := E)) ((extChartAt I α) b₀))) ∈ U
    rw [(toEuclidean (E := E)).symm_apply_apply, (extChartAt I α).left_inv hb₀_src]
    exact hb₀_U
  refine ⟨S_k_ext, V, hV_open, hV_sub, hb₀_V, ?_⟩
  intro Idx Jdx y hy
  have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := hy.1
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_U : b ∈ U := hy.2
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hU_sub_good hb_U
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_target]
  rw [covDerivComponentEuclid_def]
  congr 1
  congr 1
  have hStep_BTCi :
      (S_k_ext : Π b' : M, TensorRSSpace r s I b') b =
      covApply
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
        (chartBasisVecFiber (I := I) α k) T₀.toSection b := hU_eq b hb_U
  rw [hStep_BTCi]
  rw [covApply_apply]
  have hCovDerivAt : (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun T₀.toSection b
        (chartBasisVecFiber (I := I) α k b) =
      tensorCovDerivAt (I := I) (M := M) g r s T₀ b
        (chartBasisVecFiber (I := I) α k b) := by
    rw [tensorCovDerivAt_def]
  rw [hCovDerivAt]
  exact tensorCovDerivAt_eq_chartTensorRSCovariantDerivative
    (I := I) (M := M) g r s T₀ α k (b := b) hb_good

private def packageAsCcExp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                fun b : M => TensorRSSpace r s I b⟯) :
    SmoothCcTensor g r s where
  toSection := S
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma packageAsCcExp_toSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                fun b : M => TensorRSSpace r s I b⟯) :
    (packageAsCcExp (I := I) (M := M) g r s S).toSection = S := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorChartComponentRaw_packageAsCcExp_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S_k_ext : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                       fun b : M => TensorRSSpace r s I b⟯)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (packageAsCcExp (I := I) (M := M) g r s S_k_ext) α Idx Jdx =
      fun b : M =>
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ
            b ((S_k_ext : Π b' : M, TensorRSSpace r s I b') b)) := by
  funext b
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPushedRaw_tensorChartComponentRaw_S_k_packed_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E))
    (S_k_ext : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                       fun b : M => TensorRSSpace r s I b⟯)
    (V : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (hVeqOn : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      Set.EqOn
        (chartPushedRaw I α
          (fun b : M =>
            tensorChartComponentProjection r s Idx Jdx
              ((trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ
                b ((S_k_ext : Π b' : M, TensorRSSpace r s I b') b))))
        (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx)
        V)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Set.EqOn
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s
          (packageAsCcExp (I := I) (M := M) g r s S_k_ext) α Idx Jdx))
      (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx)
      V := by
  classical
  intro y hy
  have h := hVeqOn Idx Jdx hy
  rw [tensorChartComponentRaw_packageAsCcExp_eq]
  exact h

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_eqOn_of_eqOn_open
    (V : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (hV_open : IsOpen V)
    (u v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    (huv : Set.EqOn u v V)
    (n : Fin (Module.finrank ℝ E)) :
    Set.EqOn (euclidPartial (E := E) n u) (euclidPartial (E := E) n v) V := by
  classical
  intro y hy
  have hVeq : u =ᶠ[𝓝 y] v := huv.eventuallyEq_of_mem (hV_open.mem_nhds hy)
  have hfderiv : fderiv ℝ u y = fderiv ℝ v y :=
    Filter.EventuallyEq.fderiv_eq hVeq
  rw [euclidPartial_def, euclidPartial_def, hfderiv]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma euclidPartial_covDerivComponentEuclid_T₀_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (k n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (euclidPartial (E := E) n
        (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hcd : ContDiffOn ℝ ∞
      (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
    covDerivComponentEuclid_contDiffOn (I := I) (M := M) g r s α T₀ k Idx Jdx
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hfderiv : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ
        (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx) z)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have hsucc : ContDiffOn ℝ ((∞ : WithTop ℕ∞) + 1)
        (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]; exact hcd
    have hfw : ContDiffOn ℝ ∞
        (fderivWithin ℝ
          (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_succ_iff_fderivWithin hopen.uniqueDiffOn).mp hsucc).2.2
    refine hfw.congr (fun z hz => ?_)
    exact (fderivWithin_of_isOpen (f :=
      covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx)
      (𝕜 := ℝ) hopen hz).symm
  have hcomp : ContDiffOn ℝ ∞
      ((fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
          L (EuclideanSpace.single n 1)) ∘
        (fun z => fderiv ℝ
          (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx) z))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single n 1)).contDiff.comp_contDiffOn hfderiv
  refine hcomp.congr (fun z _ => ?_)
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma covDerivComponentEuclid_T₀_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Set.EqOn (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx)
      (fun y =>
        euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y
          + covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k Idx Jdx y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  covDerivComponentEuclid_eqOn (I := I) (M := M) g r s α T₀ k Idx Jdx

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivComponentEuclid_S_k_ext_eq_iteratedFDeriv_T₀_add_lowerOrder
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (k l : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b₀ : M} (hb₀ : b₀ ∈ chartLeviCivitaGoodSet (I := I) α) :
    ∃ S_k_ext : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                       fun b : M => TensorRSSpace r s I b⟯,
    ∃ V : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
    ∃ (Corr_T₀l_LO Corr_S_k_LO :
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
      IsOpen V ∧
      V ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      (toEuclidean (E := E)) ((extChartAt I α) b₀) ∈ V ∧
      ContDiffOn ℝ ∞ Corr_T₀l_LO (chartTargetEuclid (I := I) (M := M) α) ∧
      ContDiffOn ℝ ∞ Corr_S_k_LO (chartTargetEuclid (I := I) (M := M) α) ∧
      (∀ y ∈ V,
        covDerivComponentEuclid (I := I) (M := M) g r s α
            (packageAsCcExp (I := I) (M := M) g r s S_k_ext) l Idx Jdx y =
          euclidPartial (E := E) l
              (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y
            + Corr_T₀l_LO y + Corr_S_k_LO y) := by
  classical
  obtain ⟨S_k_ext, V, hV_open, hV_sub, hb₀_V, hVeqOn⟩ :=
    chartPushedRaw_eqOn_covDerivComponentEuclid_uniform
      (I := I) (M := M) g r s α T₀ k (b₀ := b₀) hb₀
  set S_k_packed : SmoothCcTensor g r s :=
    packageAsCcExp (I := I) (M := M) g r s S_k_ext with hS_k_packed_def
  let Corr_T₀l_LO : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    euclidPartial (E := E) l
      (covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k Idx Jdx)
  let Corr_S_k_LO : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    covDerivLowerOrderTerm (I := I) (M := M) g r s S_k_packed α l Idx Jdx
  refine ⟨S_k_ext, V, Corr_T₀l_LO, Corr_S_k_LO, hV_open, hV_sub, hb₀_V, ?_, ?_, ?_⟩
  · have hLO_T₀ : ContDiffOn ℝ ∞
        (covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) :=
      covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g r s T₀ α k Idx Jdx
        (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
          (I := I) (M := M) g r s T₀ α Idx' Jdx')
    have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have hfderiv : ContDiffOn ℝ ∞
        (fun z => fderiv ℝ
          (covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k Idx Jdx) z)
        (chartTargetEuclid (I := I) (M := M) α) := by
      have hsucc : ContDiffOn ℝ ((∞ : WithTop ℕ∞) + 1)
          (covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) := by
        rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]; exact hLO_T₀
      have hfw : ContDiffOn ℝ ∞
          (fderivWithin ℝ
            (covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α))
          (chartTargetEuclid (I := I) (M := M) α) :=
        ((contDiffOn_succ_iff_fderivWithin hopen.uniqueDiffOn).mp hsucc).2.2
      refine hfw.congr (fun z hz => ?_)
      exact (fderivWithin_of_isOpen (f :=
        covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k Idx Jdx)
        (𝕜 := ℝ) hopen hz).symm
    have hcomp : ContDiffOn ℝ ∞
        ((fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
            L (EuclideanSpace.single l 1)) ∘
          (fun z => fderiv ℝ
            (covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k Idx Jdx) z))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single l 1)).contDiff.comp_contDiffOn hfderiv
    refine hcomp.congr (fun z _ => ?_)
    rfl
  · exact covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g r s
      S_k_packed α l Idx Jdx
      (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
        (I := I) (M := M) g r s S_k_packed α Idx' Jdx')
  · intro y hy
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := hV_sub hy
    have hStepA :
        covDerivComponentEuclid (I := I) (M := M) g r s α S_k_packed l Idx Jdx y =
          euclidPartial (E := E) l
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s S_k_packed α Idx Jdx)) y
            + covDerivLowerOrderTerm (I := I) (M := M) g r s S_k_packed α l Idx Jdx y := by
      have h := covDerivComponentEuclid_eqOn (I := I) (M := M) g r s α
        S_k_packed l Idx Jdx hy_target
      exact h
    rw [hStepA]
    have hChartPushedRaw_eq :
        Set.EqOn
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s S_k_packed α Idx Jdx))
          (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx)
          V :=
      chartPushedRaw_tensorChartComponentRaw_S_k_packed_eqOn
        (I := I) (M := M) g r s α T₀ k S_k_ext V hVeqOn Idx Jdx
    have hPartialEq :
        euclidPartial (E := E) l
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s S_k_packed α Idx Jdx)) y =
          euclidPartial (E := E) l
            (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx) y :=
      euclidPartial_eqOn_of_eqOn_open (E := E) V hV_open _ _
        hChartPushedRaw_eq l hy
    rw [hPartialEq]
    have hT₀_eqOn := covDerivComponentEuclid_T₀_eqOn
      (I := I) (M := M) g r s α T₀ k Idx Jdx
    have hT₀_partial_eq :
        euclidPartial (E := E) l
            (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx) y =
          euclidPartial (E := E) l
            (fun y' =>
              euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y'
                + covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k Idx Jdx y') y :=
      euclidPartial_eqOn_of_eqOn_open (E := E)
        (chartTargetEuclid (I := I) (M := M) α)
        (chartTargetEuclid_isOpen (I := I) (M := M) α) _ _ hT₀_eqOn l hy_target
    rw [hT₀_partial_eq]
    have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h1 : ContDiffOn ℝ ∞
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g r s T₀ α k Idx Jdx
    have h2 : ContDiffOn ℝ ∞
        (covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) :=
      covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g r s T₀ α k Idx Jdx
        (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
          (I := I) (M := M) g r s T₀ α Idx' Jdx')
    have h1_diff : DifferentiableAt ℝ
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y := by
      have hd : DifferentiableOn ℝ
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        h1.differentiableOn (by norm_cast)
      exact (hd.differentiableAt (hopen.mem_nhds hy_target))
    have h2_diff : DifferentiableAt ℝ
        (covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k Idx Jdx) y := by
      have hd : DifferentiableOn ℝ
          (covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) :=
        h2.differentiableOn (by norm_cast)
      exact (hd.differentiableAt (hopen.mem_nhds hy_target))
    have hSplit :
        euclidPartial (E := E) l
            (fun y' =>
              euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y'
                + covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k Idx Jdx y') y =
          euclidPartial (E := E) l
              (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y
            + euclidPartial (E := E) l
                (covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k Idx Jdx) y := by
      rw [euclidPartial_def, euclidPartial_def, euclidPartial_def]
      rw [fderiv_fun_add h1_diff h2_diff]
      rw [ContinuousLinearMap.add_apply]
    rw [hSplit]

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
