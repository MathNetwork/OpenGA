import DifferentialGeometry.Analysis.ODE.GlobalLipschitzAffineExistence
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLapDiffMeas
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarLapDiffCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjPotential
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false










noncomputable section

open Bundle Filter MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open Classical in


def scalarGalVec
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0))
    (c : TensorEigenIdx (I := I) (M := M) q 0 0 → Real) (σ : Real) :
    tensorHs (I := I) (M := M) q 0 0 σ where
  coeff i := if i ∈ F then c i else 0
  weighted_summable := by
    refine summable_of_ne_finset_zero (s := F) ?_
    intro i hi
    rw [if_neg hi]
    ring

open Classical in
omit [BoundarylessManifold I M] in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem scalarGalVec_coeff
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0))
    (c : TensorEigenIdx (I := I) (M := M) q 0 0 → Real) (σ : Real)
    (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
    (scalarGalVec (I := I) (M := M) q F c σ).coeff i =
      (if i ∈ F then c i else 0) :=
  rfl

open Classical in
omit [BoundarylessManifold I M] in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalarGalVec_supp
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0))
    (c : TensorEigenIdx (I := I) (M := M) q 0 0 → Real) (σ : Real) :
    Function.support
        (scalarGalVec (I := I) (M := M) q F c σ).coeff ⊆
      (F : Set (TensorEigenIdx (I := I) (M := M) q 0 0)) := by
  intro i hi
  by_contra hiF
  have hiF' : i ∉ F := by
    simpa only [Finset.mem_coe] using hiF
  have hzero : (scalarGalVec (I := I) (M := M) q F c σ).coeff i = 0 := by
    rw [scalarGalVec_coeff, if_neg hiF']
  exact hi hzero

open Classical in
omit [BoundarylessManifold I M] in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalarGalVec_finite
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0))
    (c : TensorEigenIdx (I := I) (M := M) q 0 0 → Real) (σ : Real) :
    (Function.support
      (scalarGalVec (I := I) (M := M) q F c σ).coeff).Finite :=
  F.finite_toSet.subset (scalarGalVec_supp (I := I) (M := M) q F c σ)

open Classical in
omit [BoundarylessManifold I M] in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalarGalVec_inc
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0))
    (c : TensorEigenIdx (I := I) (M := M) q 0 0 → Real)
    {τ σ : Real} (hτσ : τ ≤ σ) :
    tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0) hτσ
        (scalarGalVec (I := I) (M := M) q F c σ) =
      scalarGalVec (I := I) (M := M) q F c τ := by
  apply tensorHs.ext
  funext i
  simp only [tensorHsInclusion_coeff_apply, scalarGalVec_coeff]

omit [BoundarylessManifold I M] in


theorem scalarGalRepr_eq
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0))
    (c : TensorEigenIdx (I := I) (M := M) q 0 0 → Real)
    (σ τ : Real) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
      (I := I) (M := M)
        (scalarGalVec (I := I) (M := M) q F c σ)
        (scalarGalVec_finite (I := I) (M := M) q F c σ) =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
        (I := I) (M := M)
        (scalarGalVec (I := I) (M := M) q F c τ)
        (scalarGalVec_finite (I := I) (M := M) q F c τ) := by
  rfl

open Classical in
private noncomputable def scalarGalEmbedLM
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0)) :
    EuclideanSpace Real {i // i ∈ F} →ₗ[Real]
      tensorHs (I := I) (M := M) q 0 0 2 where
  toFun w := scalarGalVec (I := I) (M := M) q F
    (fun i => if h : i ∈ F then w.ofLp ⟨i, h⟩ else 0) 2
  map_add' w w' := by
    apply tensorHs.ext
    funext i
    simp only [tensorHs.add_coeff, scalarGalVec_coeff]
    by_cases hi : i ∈ F
    · simp only [if_pos hi, dif_pos hi, WithLp.ofLp_add, Pi.add_apply]
    · simp only [if_neg hi, add_zero]
  map_smul' c w := by
    apply tensorHs.ext
    funext i
    simp only [tensorHs.smul_coeff, RingHom.id_apply, scalarGalVec_coeff]
    by_cases hi : i ∈ F
    · simp only [if_pos hi, dif_pos hi, WithLp.ofLp_smul, Pi.smul_apply,
        smul_eq_mul]
    · simp only [if_neg hi, mul_zero]


noncomputable def scalarGalEmbed
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0)) :
    EuclideanSpace Real {i // i ∈ F} →L[Real]
      tensorHs (I := I) (M := M) q 0 0 2 :=
  (scalarGalEmbedLM (I := I) (M := M) q F).toContinuousLinearMap

open Classical in
omit [BoundarylessManifold I M] in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem scalarGalEmbed_apply
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0))
    (w : EuclideanSpace Real {i // i ∈ F}) :
    scalarGalEmbed (I := I) (M := M) q F w =
      scalarGalVec (I := I) (M := M) q F
        (fun i => if h : i ∈ F then w.ofLp ⟨i, h⟩ else 0) 2 :=
  rfl

open Classical in
omit [BoundarylessManifold I M] in


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalarGalVec_cont
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0))
    (c : Real → TensorEigenIdx (I := I) (M := M) q 0 0 → Real)
    {A : Set Real}
    (hc : ∀ i ∈ F, ContinuousOn (fun t => c t i) A) :
    ContinuousOn
      (fun t => scalarGalVec (I := I) (M := M) q F (c t) 2) A := by
  let e := EuclideanSpace.equiv {i // i ∈ F} Real
  let w : Real → EuclideanSpace Real {i // i ∈ F} :=
    fun t => e.symm (fun j => c t j.1)
  have hw : ContinuousOn w A :=
    e.symm.continuous.comp_continuousOn
      (continuousOn_pi.2 fun j => hc j.1 j.2)
  have hemb :=
    (scalarGalEmbed (I := I) (M := M) q F).continuous.comp_continuousOn hw
  refine hemb.congr (fun t _ => ?_)
  change scalarGalVec (I := I) (M := M) q F (c t) 2 =
    scalarGalEmbed (I := I) (M := M) q F (w t)
  rw [scalarGalEmbed_apply]
  apply tensorHs.ext
  funext i
  simp only [scalarGalVec_coeff]
  by_cases hi : i ∈ F
  · simp only [if_pos hi, dif_pos hi]
    have hwt : (w t).ofLp ⟨i, hi⟩ = c t i := by
      dsimp only [w]
      change e (e.symm (fun j => c t j.1)) ⟨i, hi⟩ = c t i
      rw [e.apply_symm_apply]
    exact hwt.symm
  · simp only [if_neg hi, dif_neg hi]


noncomputable def scalarGalRestrict
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0)) :
    tensorHs (I := I) (M := M) q 0 0 0 →L[Real]
      EuclideanSpace Real {i // i ∈ F} :=
  (EuclideanSpace.equiv {i // i ∈ F} Real).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j : {i // i ∈ F} =>
      DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorHsCoeffL
        (I := I) (M := M) (a := (0 : Real)) j.1))

omit [BoundarylessManifold I M] in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem scalarGalRest_apply
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0))
    (v : tensorHs (I := I) (M := M) q 0 0 0) (j : {i // i ∈ F}) :
    scalarGalRestrict (I := I) (M := M) q F v j = v.coeff j.1 :=
  rfl

private noncomputable def scalarGalDiagLM
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0)) :
    EuclideanSpace Real {i // i ∈ F} →ₗ[Real]
      EuclideanSpace Real {i // i ∈ F} where
  toFun w := WithLp.toLp 2
    (fun j => -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * w.ofLp j)
  map_add' w w' := by
    apply WithLp.ofLp_injective 2
    funext j
    simp only [WithLp.ofLp_add, Pi.add_apply]
    ring
  map_smul' c w := by
    apply WithLp.ofLp_injective 2
    funext j
    simp only [WithLp.ofLp_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring


noncomputable def scalarGalDiag
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0)) :
    EuclideanSpace Real {i // i ∈ F} →L[Real]
      EuclideanSpace Real {i // i ∈ F} :=
  (scalarGalDiagLM (I := I) (M := M) q F).toContinuousLinearMap

omit [BoundarylessManifold I M] in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem scalarGalDiag_apply
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0))
    (w : EuclideanSpace Real {i // i ∈ F}) (j : {i // i ∈ F}) :
    scalarGalDiag (I := I) (M := M) q F w j =
      -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * w j :=
  rfl



noncomputable def scalarGalPert
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T : D.RegularTime) (t : Real) :
    tensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 2 →L[Real]
      tensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 0 :=
  lapDiffA20 (I := I) (M := M) S.family T t +
    (conjA1 (I := I) (M := M) S T t).comp
      (tensorHsInclusion (I := I) (M := M)
        (g := S.family.metric (T : Real)) (r := 0) (s := 0)
        (show (1 : Real) ≤ 2 by norm_num))



theorem scalarGalPert_fin
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime) :
    let q := S.family.metric (T : Real)
    ∀ᶠ s in 𝓝 (0 : Real),
      ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0))
        (c : TensorEigenIdx (I := I) (M := M) q 0 0 → Real)
        (i : TensorEigenIdx (I := I) (M := M) q 0 0),
        let v := scalarGalVec (I := I) (M := M) q F c 0
        let hv := scalarGalVec_finite (I := I) (M := M) q F c 0
        let U :=
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
            (I := I) (M := M) v hv
        (scalarGalPert (I := I) (M := M) S T s
            (scalarGalVec (I := I) (M := M) q F c 2)).coeff i =
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) q 0 0)
            (SmoothCcTensor.toL2
              (scalarLapDiffCc (I := I) q
                  (S.family.metric ((T : Real) - s)) U +
                DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul
                  (I := I) (M := M) q 0 0
                  (conjCoeff (I := I) (M := M) S
                    ((T : Real) - s)) U)) i := by
  filter_upwards [lapDiffA20_core (I := I) (M := M)
    S.family hS.smoothMetric T] with s hs
  intro F c i
  dsimp only
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let hc := tensorResolventL2_isCompactOperator
    (I := I) (M := M) q 0 0
  let v2 := scalarGalVec (I := I) (M := M) q F c 2
  let hv2 := scalarGalVec_finite (I := I) (M := M) q F c 2
  let v1 := scalarGalVec (I := I) (M := M) q F c 1
  let hv1 := scalarGalVec_finite (I := I) (M := M) q F c 1
  let v0 := scalarGalVec (I := I) (M := M) q F c 0
  let hv0 := scalarGalVec_finite (I := I) (M := M) q F c 0
  let U :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
      (I := I) (M := M) v0 hv0
  have hA2 :
      (lapDiffA20 (I := I) (M := M) S.family T s v2).coeff i =
        tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2
            (scalarLapDiffCc (I := I) q
              (S.family.metric ((T : Real) - s)) U)) i := by
    rw [← tensorHsZeroEquivL2_tensorL2Coeff (I := I) (M := M) hc]
    rw [hs ⟨v2, hv2⟩, lapDiffCore_eq_cc]
    rw [scalarGalRepr_eq (I := I) (M := M) q F c 2 0]
  have hinc :
      tensorHsInclusion (I := I) (M := M)
          (g := q) (r := 0) (s := 0)
          (show (1 : Real) ≤ 2 by norm_num) v2 = v1 := by
    exact scalarGalVec_inc (I := I) (M := M) q F c
      (show (1 : Real) ≤ 2 by norm_num)
  have hA1 :
      ((conjA1 (I := I) (M := M) S T s).comp
          (tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0)
            (show (1 : Real) ≤ 2 by norm_num)) v2).coeff i =
        tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul
              (I := I) (M := M) q 0 0
              (conjCoeff (I := I) (M := M) S ((T : Real) - s)) U)) i := by
    rw [ContinuousLinearMap.comp_apply, hinc, conjA1, scalarPotH0_apply]
    rw [tensorHsZeroEquivL2_symm_coeff]
    rw [scalarPotOp_core (I := I) (M := M) q
      (conjCoeff (I := I) (M := M) S ((T : Real) - s)) ⟨v1, hv1⟩]
    rw [scalarPotCore_apply]
    rw [scalarGalRepr_eq (I := I) (M := M) q F c 1 0]
  change
    (lapDiffA20 (I := I) (M := M) S.family T s v2).coeff i +
      ((conjA1 (I := I) (M := M) S T s).comp
        (tensorHsInclusion (I := I) (M := M)
          (g := q) (r := 0) (s := 0)
          (show (1 : Real) ≤ 2 by norm_num)) v2).coeff i = _
  rw [hA2, hA1, map_add, tensorL2Coeff_add]


noncomputable def scalarGalField
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T : D.RegularTime)
    (F : Finset (TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0)) (t : Real) :
    EuclideanSpace Real {i // i ∈ F} →L[Real]
      EuclideanSpace Real {i // i ∈ F} :=
  scalarGalDiag (I := I) (M := M) (S.family.metric (T : Real)) F +
    (scalarGalRestrict (I := I) (M := M)
      (S.family.metric (T : Real)) F).comp
      ((scalarGalPert (I := I) (M := M) S T t).comp
        (scalarGalEmbed (I := I) (M := M)
          (S.family.metric (T : Real)) F))


@[simp] theorem scalarGalField_app
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T : D.RegularTime)
    (F : Finset (TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0))
    (t : Real) (w : EuclideanSpace Real {i // i ∈ F})
    (j : {i // i ∈ F}) :
    scalarGalField (I := I) (M := M) S T F t w j =
      -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * w j +
        (scalarGalPert (I := I) (M := M) S T t
          (scalarGalEmbed (I := I) (M := M)
            (S.family.metric (T : Real)) F w)).coeff j.1 := by
  change scalarGalDiag (I := I) (M := M)
      (S.family.metric (T : Real)) F w j +
    scalarGalRestrict (I := I) (M := M)
      (S.family.metric (T : Real)) F
        (scalarGalPert (I := I) (M := M) S T t
          (scalarGalEmbed (I := I) (M := M)
            (S.family.metric (T : Real)) F w)) j = _
  rw [scalarGalDiag_apply, scalarGalRest_apply]


noncomputable def scalarGalRhs
    (q : SmoothRiemannianMetric I M)
    (A : Real → tensorHs (I := I) (M := M) q 0 0 2 →L[Real]
      tensorHs (I := I) (M := M) q 0 0 0)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0))
    (V : Real → TensorEigenIdx (I := I) (M := M) q 0 0 → Real)
    (t : Real) (i : TensorEigenIdx (I := I) (M := M) q 0 0) : Real :=
  -(TensorEigenIdx.lambda (I := I) (M := M) i) * V t i +
    (A t (scalarGalVec (I := I) (M := M) q F (V t) 2)).coeff i

open Classical in


structure IsConjGalSol
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T : D.RegularTime) (tau : Real)
    (u0 : tensorHs (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 0)
    (F : Finset (TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0))
    (V : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real) : Prop where
  cont : ∀ i ∈ F, ContinuousOn (fun t => V t i) (Set.Icc (0 : Real) tau)
  deriv : ∀ t ∈ Set.Ico (0 : Real) tau, ∀ i ∈ F,
    HasDerivWithinAt (fun r => V r i) (scalarGalRhs (I := I) (M := M)
      (S.family.metric (T : Real))
      (scalarGalPert (I := I) (M := M) S T) F V t i) (Set.Ici t) t
  init : ∀ i ∈ F, V 0 i = u0.coeff i
  support : ∀ t i, i ∉ F → V t i = 0



structure ConjGalTime where
  tau : Real



structure IsConjGalTime
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T : D.RegularTime) (G : ConjGalTime) : Prop where
  pos : 0 < G.tau
  le_one : G.tau ≤ 1
  exists_sol :
    ∀ (u0 : tensorHs (I := I) (M := M)
        (S.family.metric (T : Real)) 0 0 0)
      (F : Finset (TensorEigenIdx (I := I) (M := M)
        (S.family.metric (T : Real)) 0 0)),
      ∃ V : Real → TensorEigenIdx (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0 → Real,
        IsConjGalSol (I := I) (M := M) S T G.tau u0 F V

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in



theorem scalar_gal_exists
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime) :
    ∃ G : ConjGalTime, IsConjGalTime (I := I) (M := M) S T G := by
  classical
  obtain ⟨tau2, htau2, htau2one, hcont2, _hmeas2, hbound2, _hboundAE2⟩ :=
    lapDiffA20_short (I := I) (M := M) S.family hS.smoothMetric T
      (epsilon := (1 : Real)) zero_lt_one
  obtain ⟨tau1, htau1, htau1one, C1, hcont1, _hmeas1, hbound1,
      _hboundAE1⟩ :=
    conjA1_short (I := I) (M := M) S hS T
  let tau : Real := min tau2 tau1
  have htau : 0 < tau := by
    exact lt_min htau2 htau1
  have htau_one : tau ≤ 1 := by
    exact (min_le_left tau2 tau1).trans htau2one
  have htau_tau2 : tau ≤ tau2 := min_le_left _ _
  have htau_tau1 : tau ≤ tau1 := min_le_right _ _
  have hIcc2 : Set.Icc (0 : Real) tau ⊆ Set.Icc (0 : Real) tau2 :=
    fun _ ht => ⟨ht.1, ht.2.trans htau_tau2⟩
  have hIcc1 : Set.Icc (0 : Real) tau ⊆ Set.Icc (0 : Real) tau1 :=
    fun _ ht => ⟨ht.1, ht.2.trans htau_tau1⟩
  refine ⟨⟨tau⟩, { pos := htau, le_one := htau_one, exists_sol := ?_ }⟩
  intro u0 F
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let Inc :
      tensorHs (I := I) (M := M) q 0 0 2 →L[Real]
        tensorHs (I := I) (M := M) q 0 0 1 :=
    tensorHsInclusion (I := I) (M := M)
      (g := q) (r := 0) (s := 0)
      (show (1 : Real) ≤ 2 by norm_num)
  let Emb :
      EuclideanSpace Real {i // i ∈ F} →L[Real]
        tensorHs (I := I) (M := M) q 0 0 2 :=
    scalarGalEmbed (I := I) (M := M) q F
  let Rst :
      tensorHs (I := I) (M := M) q 0 0 0 →L[Real]
        EuclideanSpace Real {i // i ∈ F} :=
    scalarGalRestrict (I := I) (M := M) q F
  let Diag :
      EuclideanSpace Real {i // i ∈ F} →L[Real]
        EuclideanSpace Real {i // i ∈ F} :=
    scalarGalDiag (I := I) (M := M) q F
  let B : Real :=
    ‖Diag‖ + ‖Rst‖ * (1 + (C1 : Real) * ‖Inc‖) * ‖Emb‖
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  let K : NNReal := ⟨B, hB⟩
  have hfield_apply
      (t : Real) (ht : t ∈ Set.Icc (0 : Real) tau)
      (w : EuclideanSpace Real {i // i ∈ F}) :
      ‖scalarGalField (I := I) (M := M) S T F t w‖ ≤
        B * ‖w‖ := by
    let Lap :
        tensorHs (I := I) (M := M) q 0 0 2 →L[Real]
          tensorHs (I := I) (M := M) q 0 0 0 :=
      lapDiffA20 (I := I) (M := M) S.family T t
    let Pot :
        tensorHs (I := I) (M := M) q 0 0 1 →L[Real]
          tensorHs (I := I) (M := M) q 0 0 0 :=
      conjA1 (I := I) (M := M) S T t
    let Pert :
        tensorHs (I := I) (M := M) q 0 0 2 →L[Real]
          tensorHs (I := I) (M := M) q 0 0 0 :=
      scalarGalPert (I := I) (M := M) S T t
    have hLap : ‖Lap‖ ≤ 1 := hbound2 t (hIcc2 ht)
    have hPot : ‖Pot‖ ≤ (C1 : Real) := hbound1 t (hIcc1 ht)
    have hPert_apply
        (v : tensorHs (I := I) (M := M) q 0 0 2) :
        ‖Pert v‖ ≤
          (1 + (C1 : Real) * ‖Inc‖) * ‖v‖ := by
      calc
        ‖Pert v‖ = ‖Lap v + Pot (Inc v)‖ := by
          simp only [Pert, scalarGalPert, Lap, Pot, Inc, q,
            ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
        _ ≤ ‖Lap v‖ + ‖Pot (Inc v)‖ := norm_add_le _ _
        _ ≤ ‖Lap‖ * ‖v‖ + ‖Pot‖ * ‖Inc v‖ :=
          add_le_add (Lap.le_opNorm v) (Pot.le_opNorm (Inc v))
        _ ≤ ‖Lap‖ * ‖v‖ +
            ‖Pot‖ * (‖Inc‖ * ‖v‖) := by
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left
              (Inc.le_opNorm v) (norm_nonneg Pot))
        _ ≤ 1 * ‖v‖ +
            (C1 : Real) * (‖Inc‖ * ‖v‖) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hLap (norm_nonneg v))
            (mul_le_mul_of_nonneg_right hPot
              (mul_nonneg (norm_nonneg Inc) (norm_nonneg v)))
        _ = (1 + (C1 : Real) * ‖Inc‖) * ‖v‖ := by ring
    have hfac : 0 ≤ 1 + (C1 : Real) * ‖Inc‖ := by
      positivity
    calc
      ‖scalarGalField (I := I) (M := M) S T F t w‖ =
          ‖Diag w + Rst (Pert (Emb w))‖ := by
        simp only [scalarGalField, q, Diag, Rst, Pert, Emb,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
      _ ≤ ‖Diag w‖ + ‖Rst (Pert (Emb w))‖ := norm_add_le _ _
      _ ≤ ‖Diag‖ * ‖w‖ + ‖Rst‖ * ‖Pert (Emb w)‖ :=
        add_le_add (Diag.le_opNorm w) (Rst.le_opNorm (Pert (Emb w)))
      _ ≤ ‖Diag‖ * ‖w‖ + ‖Rst‖ *
          ((1 + (C1 : Real) * ‖Inc‖) * ‖Emb w‖) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left
            (hPert_apply (Emb w)) (norm_nonneg Rst))
      _ ≤ ‖Diag‖ * ‖w‖ + ‖Rst‖ *
          ((1 + (C1 : Real) * ‖Inc‖) * (‖Emb‖ * ‖w‖)) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Emb.le_opNorm w) hfac)
            (norm_nonneg Rst))
      _ = B * ‖w‖ := by
        dsimp only [B]
        ring
  have hlip_t : ∀ t ∈ Set.Icc (0 : Real) tau,
      LipschitzWith K (scalarGalField (I := I) (M := M) S T F t) := by
    intro t ht
    refine LipschitzWith.of_dist_le_mul (fun w w' => ?_)
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    simpa only [K, NNReal.coe_mk] using hfield_apply t ht (w - w')
  have hcont_t : ∀ w : EuclideanSpace Real {i // i ∈ F},
      ContinuousOn (fun t => scalarGalField (I := I) (M := M) S T F t w)
        (Set.Icc (0 : Real) tau) := by
    intro w
    have hLap := (hcont2.mono hIcc2).clm_apply
      (continuousOn_const : ContinuousOn
        (fun _ : Real => Emb w) (Set.Icc (0 : Real) tau))
    have hPot := (hcont1.mono hIcc1).clm_apply
      (continuousOn_const : ContinuousOn
        (fun _ : Real => Inc (Emb w)) (Set.Icc (0 : Real) tau))
    have hPert : ContinuousOn
        (fun t => scalarGalPert (I := I) (M := M) S T t (Emb w))
        (Set.Icc (0 : Real) tau) := by
      simpa only [scalarGalPert, q, Inc, Emb, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.comp_apply] using hLap.add hPot
    have hRst : ContinuousOn
        (fun t => Rst (scalarGalPert (I := I) (M := M) S T t (Emb w)))
        (Set.Icc (0 : Real) tau) :=
      Rst.continuous.comp_continuousOn hPert
    simpa only [scalarGalField, q, Diag, Rst, Emb,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply] using
        (continuousOn_const.add hRst)
  have haff_t : ∀ t ∈ Set.Icc (0 : Real) tau,
      ∀ w : EuclideanSpace Real {i // i ∈ F},
        ‖scalarGalField (I := I) (M := M) S T F t w‖ ≤
          0 + (K : Real) * ‖w‖ := by
    intro t ht w
    simpa only [zero_add, K, NNReal.coe_mk] using hfield_apply t ht w
  let w0 : EuclideanSpace Real {i // i ∈ F} :=
    WithLp.toLp 2 (fun j : {i // i ∈ F} => u0.coeff j.1)
  obtain ⟨γ, hγ0, hγcont, hγderiv⟩ :=
    forward_solution_of_lipschitzWith_affineBound
      (E := EuclideanSpace Real {i // i ∈ F})
      (f := fun t => scalarGalField (I := I) (M := M) S T F t)
      htau (show (0 : Real) ≤ 0 by rfl) hlip_t hcont_t haff_t w0
  let V : Real → TensorEigenIdx (I := I) (M := M) q 0 0 → Real :=
    fun t i => if h : i ∈ F then (γ t).ofLp ⟨i, h⟩ else 0
  refine ⟨V, { cont := ?_, deriv := ?_, init := ?_, support := ?_ }⟩
  · intro i hi
    have hcoord : ContinuousOn (fun t => (γ t).ofLp ⟨i, hi⟩)
        (Set.Icc (0 : Real) tau) := by
      have hproj : Continuous (fun y : EuclideanSpace Real {i // i ∈ F} =>
          y.ofLp (⟨i, hi⟩ : {i // i ∈ F})) :=
        (EuclideanSpace.proj (𝕜 := Real)
          (⟨i, hi⟩ : {i // i ∈ F})).continuous
      exact hproj.comp_continuousOn hγcont
    refine hcoord.congr (fun t _ => ?_)
    simp only [V, dif_pos hi]
  · intro t ht i hi
    have hderiv_proj :=
      ((EuclideanSpace.proj (𝕜 := Real)
        (⟨i, hi⟩ : {i // i ∈ F})).hasFDerivAt
          (x := γ t)).comp_hasDerivWithinAt t (hγderiv t ht)
    have hderiv_proj' :
        HasDerivWithinAt (fun s => (γ s).ofLp ⟨i, hi⟩)
          ((EuclideanSpace.proj (𝕜 := Real) ⟨i, hi⟩)
            (scalarGalField (I := I) (M := M) S T F t (γ t)))
          (Set.Ici (0 : Real)) t :=
      hderiv_proj
    have hembed : scalarGalEmbed (I := I) (M := M) q F (γ t) =
        scalarGalVec (I := I) (M := M) q F (V t) 2 := by
      apply tensorHs.ext
      funext j
      simp only [scalarGalEmbed_apply, scalarGalVec_coeff, V]
    have hRHS :
        (EuclideanSpace.proj (𝕜 := Real) ⟨i, hi⟩)
            (scalarGalField (I := I) (M := M) S T F t (γ t)) =
          scalarGalRhs (I := I) (M := M) q
            (scalarGalPert (I := I) (M := M) S T) F V t i := by
      change scalarGalField (I := I) (M := M) S T F t (γ t) ⟨i, hi⟩ = _
      change scalarGalField (I := I) (M := M) S T F t (γ t) ⟨i, hi⟩ =
        -(TensorEigenIdx.lambda (I := I) (M := M) i) * V t i +
          (scalarGalPert (I := I) (M := M) S T t
            (scalarGalVec (I := I) (M := M) q F (V t) 2)).coeff i
      rw [scalarGalField_app, hembed]
      simp only [V, dif_pos hi]
    have hfinal : HasDerivWithinAt (fun s => (γ s).ofLp ⟨i, hi⟩)
        (scalarGalRhs (I := I) (M := M) q
          (scalarGalPert (I := I) (M := M) S T) F V t i)
        (Set.Ici (0 : Real)) t :=
      hRHS ▸ hderiv_proj'
    have hIci :
        HasDerivWithinAt (fun s => (γ s).ofLp ⟨i, hi⟩)
          (scalarGalRhs (I := I) (M := M) q
            (scalarGalPert (I := I) (M := M) S T) F V t i)
          (Set.Ici t) t :=
      DifferentialGeometry.Analysis.ODE.hasDerivWithinAt_Ici_of_Ici_zero
        hfinal ht.1
    have hcongr : (fun r => V r i) = (fun r => (γ r).ofLp ⟨i, hi⟩) := by
      funext r
      simp only [V, dif_pos hi]
    rw [hcongr]
    exact hIci
  · intro i hi
    simp only [V, dif_pos hi]
    rw [hγ0]
  · intro t i hi
    simp only [V, dif_neg hi]

end DifferentialGeometry.PDE.RicciFlow.Entropy

end
