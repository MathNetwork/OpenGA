import DifferentialGeometry.Geometry.Connection.DivergenceCovariantTrace
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Geometry.Coordinates.CoordinateFrame
import DifferentialGeometry.Geometry.Coordinates.Christoffel
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
import DifferentialGeometry.Tensor.RSTensor.Derivation.NablaOnTensors
import Mathlib.Geometry.Manifold.MFDeriv.Tangent





































noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 3

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E



def nablaCovTensor (g : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 b :=
  (((continuousMultilinearCurryFin1 ℝ (TangentSpace I b) ℝ).symm.toContinuousLinearMap).comp
    ((g.inner b).comp ((LeviCivita (I := I) g).toFun Z.toFun b))).uncurryLeft

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma nablaCovTensor_apply (g : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M)
    (v : Fin 2 → TangentSpace I b) :
    nablaCovTensor (I := I) g Z b v =
      g.inner b ((LeviCivita (I := I) g).toFun Z.toFun b (v 0)) (v 1) := by
  simp only [nablaCovTensor, ContinuousLinearMap.uncurryLeft_apply,
    ContinuousLinearMap.comp_apply]
  rfl



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartInvGram_metricInverse (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    MetricInverseInBasis_gen (I := I) g b (chartBasisFamily (I := I) α hb)
      (fun m n => chartInvGramMatrix (I := I) g α b m n) := by
  intro i j
  refine ⟨?_, ?_⟩
  · have hmul := chartInvGramMatrix_mul_chartGramMatrix (I := I) g α hb
    have hentry : (chartInvGramMatrix (I := I) g α b * chartGramMatrix (I := I) g α b) i j
        = (1 : Matrix _ _ ℝ) i j := by rw [hmul]
    rw [Matrix.mul_apply, Matrix.one_apply] at hentry
    rw [← hentry]
    exact Finset.sum_congr rfl fun k _ => by
      rw [chartGramMatrix_apply, chartBasisFamily_apply, chartBasisFamily_apply]
  · have hmul := chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hb
    have hentry : (chartGramMatrix (I := I) g α b * chartInvGramMatrix (I := I) g α b) i j
        = (1 : Matrix _ _ ℝ) i j := by rw [hmul]
    rw [Matrix.mul_apply, Matrix.one_apply] at hentry
    rw [← hentry]
    exact Finset.sum_congr rfl fun k _ => by
      rw [chartGramMatrix_apply, chartBasisFamily_apply, chartBasisFamily_apply]



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma metricTracePair0SAt_nablaCov_eq_chartSum
    (g : SmoothRiemannianMetric I M) (α : M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    metricTracePair0SAt (I := I) g (nablaCovTensor (I := I) g Z b) =
      ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α b m n *
          g.inner b
            ((LeviCivita (I := I) g).toFun Z.toFun b (chartBasisVecFiber (I := I) α m b))
            (chartBasisVecFiber (I := I) α n b) := by
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g (chartBasisFamily (I := I) α hb)
    (fun m n => chartInvGramMatrix (I := I) g α b m n)
    (chartInvGram_metricInverse (I := I) g α hb)]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [nablaCovTensor_apply]
  rw [chartBasisFamily_apply, chartBasisFamily_apply]
  simp only [vec2]
  norm_num

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma self_mem_goodSet (x : M) :
    x ∈ chartLeviCivitaGoodSet (I := I) x := by
  rw [mem_chartLeviCivitaGoodSet_iff]
  refine ⟨mem_extChartAt_source (I := I) x,
    mem_baseSet_trivializationAt E (TangentSpace I) x, ?_⟩
  rw [(isOpen_extChartAt_target (I := I) x).interior_eq]
  exact (extChartAt I x).map_source (mem_extChartAt_source (I := I) x)




omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricTracePair0SAt_nablaCov_eq_divergence
    (g : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    metricTracePair0SAt (I := I) g (nablaCovTensor (I := I) g Z x) =
      divergence_g (I := I) g Z x := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x := self_mem_goodSet (I := I) x
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx_good
  have hx_src : x ∈ (chartAt H x).source := mem_chart_source H x
  rw [metricTracePair0SAt_nablaCov_eq_chartSum (I := I) g x Z hx_base]
  rw [metricTrace_eq_coord_covariant_divergence (I := I) g x Z hx_good]
  rw [voss_weyl_divergence_formula (I := I) g x Z hx_src]
  rw [localDivergence_eq_coord_covariant_divergence (I := I) g x Z hx_good]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [show (∑ i : Fin (Module.finrank ℝ E),
          chartCoeffOnE (I := I) x Z i (extChartAt I x x) *
            ∑ k : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g x i k k (extChartAt I x x)) =
        ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g x i k k (extChartAt I x x) *
            chartCoeffOnE (I := I) x Z i (extChartAt I x x) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [chartChristoffel_symm (I := I) g x k i k]







omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem divergence_g_eq_finBasis_metricTrace
    (g : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergence_g (I := I) g Z x =
      ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
              (I := I) g x i j (extChartAt I x x) *
            g.inner x
              ((LeviCivita (I := I) g).toFun Z.toFun x
                (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x))
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x) := by
  classical
  rw [← metricTracePair0SAt_nablaCov_eq_divergence (I := I) g Z x]
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g
    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x)
    (fun i j => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := I) g x i j (extChartAt I x x))
    (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [nablaCovTensor_apply]
  rw [DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply,
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply]
  simp only [vec2]
  norm_num





omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma coeff_cov_eq_deriv_add_christoffel
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x₀ : M) (i k : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff k x₀
        ((cov Z.toFun x₀) (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀ i x₀)) =
      extDerivFun (I := I)
          (fun y : M =>
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff k y (Z.toFun y))
          x₀ (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀ i x₀) +
        ∑ l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ i l k *
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff l x₀ (Z.toFun x₀) := by
  classical
  set hframe := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀ with hframe_def
  set frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀ with hfr_def
  set u := DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x₀ with hu_def
  have hx₀ : x₀ ∈ u := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) x₀
  have hu_open : IsOpen u := DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open (I := I) x₀
  have hu_nhds : u ∈ 𝓝 x₀ := hu_open.mem_nhds hx₀
  have hZ1 : ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
      (fun y : M => (⟨y, Z.toFun y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ :=
    (Z.contMDiff x₀).of_le (by norm_num)
  set Zc : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> M -> Real :=
    fun l y => hframe.coeff l y (Z.toFun y) with hZc_def
  have hZc_diff : ∀ l, MDifferentiableAt I 𝓘(Real, Real) (Zc l) x₀ := by
    intro l
    set e := DifferentialGeometry.Tensor.Coordinates.coordinateTrivializationAt (I := I) x₀ with he_def
    have hxe : x₀ ∈ e.baseSet := by
      simp [e, DifferentialGeometry.Tensor.Coordinates.coordinateTrivializationAt]
    have hraw :=
      contMDiffAt_localFrame_coeff
        (I := I) (V := TangentSpace I) (e := e)
        (b := Module.finBasis Real E) (s := Z.toFun)
        (k := (1 : WithTop ℕ∞)) hxe hZ1 l
    have hcoeff : ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞) (Zc l) x₀ := by
      simpa [Zc, hframe_def, e, DifferentialGeometry.Tensor.Coordinates.coordinateTrivializationAt,
        DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one,
        DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt] using hraw
    exact hcoeff.mdifferentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hframevec_diff : ∀ l,
      MDifferentiableAt I (I.prod 𝓘(Real, E))
        (fun y : M => (⟨y, frame l y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ :=
    fun l => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mdifferentiableAt (I := I) x₀ l
  have hZdiff :
      MDifferentiableAt I (I.prod 𝓘(Real, E))
        (fun y : M => (⟨y, Z.toFun y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ :=
    Z.mdifferentiableAt

  have hZexp : ∀ᶠ y in 𝓝 x₀, Z.toFun y = ∑ l, Zc l y • frame l y := by
    filter_upwards [hu_nhds] with y hy
    exact hframe.coeff_sum_eq (fun z => Z.toFun z) hy

  have hsummand_diff : ∀ l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      MDifferentiableAt I (I.prod 𝓘(Real, E))
        (fun y : M => (⟨y, Zc l y • frame l y⟩ :
          TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    intro l
    exact (hZc_diff l).smul_section (hframevec_diff l)

  have hpartial_diff : ∀ (s : Finset (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)),
      MDifferentiableAt I (I.prod 𝓘(Real, E))
        (fun y : M => (⟨y, ∑ l ∈ s, Zc l y • frame l y⟩ :
          TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hz : MDifferentiableAt I (I.prod 𝓘(Real, E))
            (fun y : M => (⟨y, (0 : TangentSpace I y)⟩ :
              TotalSpace E (TangentSpace I : M -> Type _))) x₀ :=
          mdifferentiableAt_zeroSection (𝕜 := Real) (E := (TangentSpace I : M → Type _))
            (F := E) (IB := I) (x := x₀)
        simpa using hz
    | insert a s ha ih =>
        have heq : (fun y : M => (⟨y, ∑ l ∈ insert a s, Zc l y • frame l y⟩ :
              TotalSpace E (TangentSpace I : M -> Type _))) =
            (fun y : M => (⟨y, Zc a y • frame a y + ∑ l ∈ s, Zc l y • frame l y⟩ :
              TotalSpace E (TangentSpace I : M -> Type _))) := by
          funext y; rw [Finset.sum_insert ha]
        rw [heq]
        exact mdifferentiableAt_add_section (hsummand_diff a) ih

  have hcov_sum :
      cov (fun y : M => ∑ l, Zc l y • frame l y) x₀ =
        ∑ l, (Zc l x₀ • cov (frame l) x₀ +
          (extDerivFun (I := I) (Zc l) x₀).smulRight (frame l x₀)) := by
    classical
    have hadd : ∀ (s : Finset (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)),
        cov (fun y : M => ∑ l ∈ s, Zc l y • frame l y) x₀ =
          ∑ l ∈ s, (Zc l x₀ • cov (frame l) x₀ +
            (extDerivFun (I := I) (Zc l) x₀).smulRight (frame l x₀)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simp only [Finset.sum_empty]
          exact cov.isCovariantDerivativeOnUniv.zero
      | insert a s ha ih =>
          have heqfun : (fun y : M => ∑ l ∈ insert a s, Zc l y • frame l y) =
              ((fun y : M => Zc a y • frame a y) + fun y : M => ∑ l ∈ s, Zc l y • frame l y) := by
            funext y; simp only [Pi.add_apply]; rw [Finset.sum_insert ha]
          rw [heqfun]
          rw [cov.isCovariantDerivativeOnUniv.add (hsummand_diff a) (hpartial_diff s)]
          rw [Finset.sum_insert ha, ih]
          congr 1
          have hleib := cov.isCovariantDerivativeOnUniv.leibniz
            (σ := fun y => frame a y) (g := Zc a) (hframevec_diff a) (hZc_diff a)
          have hsmul_eq : (fun y : M => Zc a y • frame a y) = Zc a • (fun y => frame a y) := rfl
          rw [hsmul_eq, hleib]
    simpa using hadd Finset.univ

  have hcovZ :
      cov Z.toFun x₀ =
        ∑ l, (Zc l x₀ • cov (frame l) x₀ +
          (extDerivFun (I := I) (Zc l) x₀).smulRight (frame l x₀)) := by
    rw [← hcov_sum]
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZdiff
      (by
        have hsumdiff := hpartial_diff (Finset.univ)
        simpa using hsumdiff)
      univ_mem hZexp

  rw [hcovZ]
  rw [ContinuousLinearMap.sum_apply]
  rw [map_sum]

  have hk_each : ∀ l,
      hframe.coeff k x₀
          ((Zc l x₀ • cov (frame l) x₀ +
            (extDerivFun (I := I) (Zc l) x₀).smulRight (frame l x₀)) (frame i x₀)) =
        Zc l x₀ *
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe x₀ i l k +
          (if k = l then extDerivFun (I := I) (Zc k) x₀ (frame i x₀) else 0) := by
    intro l
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, map_add]
    congr 1
    · rw [map_smul, smul_eq_mul]
      congr 1
    · rw [map_smul, smul_eq_mul]
      have hcoeff_frame : hframe.coeff k x₀ (frame l x₀) = (if k = l then (1 : Real) else 0) := by
        rw [IsLocalFrameOn.coeff_apply_of_mem hframe hx₀]
        rw [show frame l x₀ = (hframe.toBasisAt hx₀) l from
          (IsLocalFrameOn.toBasisAt_coe hframe hx₀ l).symm]
        rw [Module.Basis.repr_self_apply]
        by_cases hlk : l = k
        · simp [hlk]
        · rw [if_neg hlk, if_neg (fun h => hlk h.symm)]
      rw [hcoeff_frame]
      by_cases hkl : k = l
      · simp [hkl]
      · simp [hkl]
  rw [Finset.sum_congr rfl fun l _ => hk_each l]
  rw [Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  · rw [Finset.sum_ite_eq Finset.univ k (fun _ => extDerivFun (I := I) (Zc k) x₀ (frame i x₀))]
    rw [if_pos (Finset.mem_univ k)]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [hZc_def]
    ring



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma inner_cov_frame_eq
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x₀ : M) (i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    g.inner x₀ ((cov Z.toFun x₀) (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀ i x₀))
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀ j x₀) =
      ∑ k : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        (extDerivFun (I := I)
            (fun y : M =>
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff k y (Z.toFun y))
            x₀ (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀ i x₀) +
          ∑ l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov
                (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀)
                (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ i l k *
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff l x₀ (Z.toFun x₀)) *
        g.inner x₀ (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀ k x₀)
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀ j x₀) := by
  classical
  set hframe := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀ with hframe_def
  set frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀ with hfr_def
  have hx₀ : x₀ ∈ DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x₀ :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) x₀

  have hexpand : (cov Z.toFun x₀) (frame i x₀) =
      ∑ k, hframe.coeff k x₀ ((cov Z.toFun x₀) (frame i x₀)) • frame k x₀ :=
    hframe.coeff_sum_eq (fun _ => (cov Z.toFun x₀) (frame i x₀)) hx₀
  rw [hexpand]
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [coeff_cov_eq_deriv_add_christoffel cov Z x₀ i k]






omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem divergence_g_eq_coordinateFrame_covariant_divergence
    (g : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergence_g (I := I) g Z x =
      ∑ p : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        (extDerivFun (I := I)
            (fun y : M =>
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x).coeff p y (Z.toFun y))
            x (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x p x) +
          ∑ l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame (LeviCivita (I := I) g)
                (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
                (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x) x p l p *
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x).coeff l x (Z.toFun x)) := by
  classical
  set frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x with hfr_def
  set hfo := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x with hfo_def
  set gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := I) g x i j (extChartAt I x x) with hgInv_def
  have hinv := DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
    (I := I) g x
  set hfb := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x with hfb_def
  have hbasis_app : ∀ q, hfb q = frame q x := fun q =>
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply (I := I) x q

  set C : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i k =>
      extDerivFun (I := I) (fun y : M => hfo.coeff k y (Z.toFun y)) x (frame i x) +
        ∑ l, DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame (LeviCivita (I := I) g)
            frame hfo x i l k * hfo.coeff l x (Z.toFun x) with hC_def
  rw [divergence_g_eq_finBasis_metricTrace (I := I) g Z x]

  have hcontract : ∀ i k,
      (∑ j, gInv i j * g.inner x (frame k x) (frame j x)) = (if i = k then (1 : Real) else 0) := by
    intro i k
    have h := (hinv i k).1
    calc (∑ j, gInv i j * g.inner x (frame k x) (frame j x))
        = ∑ j, gInv i j * g.inner x (hfb j) (hfb k) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hbasis_app j, hbasis_app k, g.symm x (frame k x) (frame j x)]
      _ = if i = k then (1 : Real) else 0 := h
  calc (∑ i, ∑ j, gInv i j * g.inner x ((LeviCivita (I := I) g).toFun Z.toFun x (frame i x)) (frame j x))
      = ∑ i, ∑ j, gInv i j * ∑ k, C i k * g.inner x (frame k x) (frame j x) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [inner_cov_frame_eq (LeviCivita (I := I) g) g Z x i j]
    _ = ∑ i, ∑ k, C i k * (∑ j, gInv i j * g.inner x (frame k x) (frame j x)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (∑ j, gInv i j * ∑ k, C i k * g.inner x (frame k x) (frame j x)) =
              ∑ j, ∑ k, gInv i j * (C i k * g.inner x (frame k x) (frame j x)) from by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ i, ∑ k, C i k * (if i = k then (1 : Real) else 0) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [hcontract i k]
    _ = ∑ i, C i i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single i]
        · rw [if_pos rfl, mul_one]
        · intro k _ hki; rw [if_neg (fun h => hki h.symm), mul_zero]
        · intro hi; exact absurd (Finset.mem_univ i) hi

end DifferentialGeometry.Integral.Connection
