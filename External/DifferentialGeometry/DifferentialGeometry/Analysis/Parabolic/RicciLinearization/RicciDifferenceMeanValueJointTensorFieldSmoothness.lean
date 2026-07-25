import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.MetricFamilyChartLinearization
import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import DifferentialGeometry.Bundle.RicciDifferenceMeanValueClmSectionJointSmoothness


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1600000

open Set Function MeasureTheory intervalIntegral Bundle Tensor0SBundle
open scoped Topology Manifold BigOperators ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance instCompleteSpaceE_keystone : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem jointContMDiff_toModel_continuous_slice
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (x : M) :
    ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x)) S := by

  have hmap : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => (x, t)) :=
    (contMDiff_const).prodMk contMDiff_id
  have hmaps : Set.MapsTo (fun t : ℝ => (x, t)) S ((Set.univ : Set M) ×ˢ S) :=
    fun t ht => ⟨Set.mem_univ _, ht⟩
  have hslice : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun t : ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x ((Φ t).toSection x)) S :=
    hjoint.comp hmap.contMDiffOn hmaps

  have hcont_total : ContinuousOn (fun t : ℝ =>
      TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x ((Φ t).toSection x)) S :=
    hslice.continuousOn

  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x with he
  have hxbase : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  have hcoord : ContinuousOn (fun t : ℝ =>
      (e (TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x ((Φ t).toSection x))).2) S :=
    continuous_snd.comp_continuousOn (e.continuousOn_toFun.comp hcont_total
      (fun t _ => e.mem_source.mpr hxbase))

  have hfibre : ContinuousOn (fun t : ℝ => (Φ t).toSection x) S := by
    have hkey : ∀ t : ℝ, (Φ t).toSection x =
        (e.continuousLinearEquivAt ℝ x hxbase).symm
          ((e (TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x
            ((Φ t).toSection x))).2) := by
      intro t
      have hp := Trivialization.apply_eq_prod_continuousLinearEquivAt
        (R := ℝ) (e := e) (b := x) hxbase ((Φ t).toSection x)
      have hsnd := congrArg Prod.snd hp
      simp only at hsnd
      rw [hsnd, ContinuousLinearEquiv.symm_apply_apply]
    have hrhs : ContinuousOn (fun t : ℝ =>
        (e.continuousLinearEquivAt ℝ x hxbase).symm
          ((e (TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x
            ((Φ t).toSection x))).2)) S :=
      (e.continuousLinearEquivAt ℝ x hxbase).symm.continuous.comp_continuousOn hcoord
    exact hrhs.congr (fun t _ => hkey t)
  exact Tensor0SBundle.TensorRSSpace.toModel_continuous.comp_continuousOn hfibre

open DifferentialGeometry.Integral.DivergenceTheorem in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem interiorProductField_jointContMDiffOn_vecJoint (s : ℕ) {S : Set ℝ}
    (X : ∀ p : M × ℝ, TangentSpace I p.1)
    (hX : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (X p))
      ((Set.univ : Set M) ×ˢ S))
    (α : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (s + 1) I p.1)
    (hα : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) p.1 (α p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z) p.1
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s p.1 (X p) (α p)))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hα' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z)).mp (hα p₀ hp₀)
  have hX' := (Bundle.contMDiffWithinAt_totalSpace (F := E) (E := TangentSpace I)).mp (hX p₀ hp₀)
  have h_combine :
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E) ∞
        (fun p : M × ℝ => Tensor0SBundle.model_interior_bilinear ℝ E s
          ((trivializationAt E (TangentSpace I) x₀ ⟨p.1, X p⟩).2)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x₀ ⟨p.1, α p⟩).2))
        ((Set.univ : Set M) ×ˢ S) p₀ :=
    ((contMDiffWithinAt_const (c := Tensor0SBundle.model_interior_bilinear ℝ E s)).clm_apply
      hX'.2).clm_apply hα'.2
  refine h_combine.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    apply ContinuousMultilinearMap.ext
    intro v
    set symmL := (trivializationAt E (TangentSpace I) x₀).symmL ℝ p.1 with hsymmL
    set gtilde : E := (trivializationAt E (TangentSpace I) x₀ ⟨p.1, X p⟩).2 with hgtilde
    change (α p) (@Fin.cons s (fun _ => E) ((X p : TangentSpace I p.1) : E) (fun i => symmL (v i))) =
      (α p) (fun i => symmL (@Fin.cons s (fun _ => E) gtilde v i))
    congr 1
    funext i
    refine Fin.cases ?_ ?_ i
    · change ((X p : TangentSpace I p.1) : E) = symmL gtilde
      have h := (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
        (R := ℝ) hx (X p)
      have hcl : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p.1 (X p) =
          gtilde := by
        change (trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p.1 (X p) = _
        rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
      rw [hcl] at h
      exact h.symm
    · intro j
      rfl
  · have hx : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt _ _ x₀
    apply ContinuousMultilinearMap.ext
    intro v
    set symmL := (trivializationAt E (TangentSpace I) x₀).symmL ℝ p₀.1 with hsymmL
    set gtilde : E := (trivializationAt E (TangentSpace I) x₀ ⟨p₀.1, X p₀⟩).2 with hgtilde
    change (α p₀) (@Fin.cons s (fun _ => E) ((X p₀ : TangentSpace I p₀.1) : E)
        (fun i => symmL (v i))) =
      (α p₀) (fun i => symmL (@Fin.cons s (fun _ => E) gtilde v i))
    congr 1
    funext i
    refine Fin.cases ?_ ?_ i
    · change ((X p₀ : TangentSpace I p₀.1) : E) = symmL gtilde
      have hx0 : p₀.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by rw [← hx₀]; exact hx
      have h := (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
        (R := ℝ) hx0 (X p₀)
      have hcl : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p₀.1 (X p₀) =
          gtilde := by
        change (trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p₀.1 (X p₀) = _
        rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := ℝ) hx0]
      rw [hcl] at h
      exact h.symm
    · intro j
      rfl

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem contractTraceField_joint_pointwise (r s : ℕ) (x₀ : M) (z : M)
    (Tz : Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z)
    (hx : z ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace r s I y) x₀
        ⟨z, Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s z Tz⟩).2 =
      Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s
        ((trivializationAt (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I y) x₀ ⟨z, Tz⟩).2) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (1 + r) (s + 1)
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (1 + r)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r
  set L : E →L[ℝ] E := (trivializationAt E (TangentSpace I) x₀).symmL ℝ z with hLdef
  set Linv : E →L[ℝ] E := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ z with hLinvdef
  set Tx : Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E :=
    Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) (1 + r) (s + 1) z Tz with hTxdef
  have hL : L.comp Linv = ContinuousLinearMap.id ℝ E := by
    ext y
    exact (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt (R := ℝ) hx y
  have hR : Linv.comp L = ContinuousLinearMap.id ℝ E := by
    ext y
    exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL (R := ℝ) hx y
  have h_cLMAt : ∀ (k : ℕ) (U : Tensor0SBundle.Tensor0SSpace k I z) (v : Fin k → E),
      (trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).continuousLinearMapAt ℝ z U v =
      U (fun i => L (v i)) := by
    intro k U v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).linearMapAt ℝ z) =
        fun y => (trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀ ⟨z, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
    rfl
  have h_symmL : ∀ (k : ℕ) (U : Tensor0SBundle.Tensor0SModel k ℝ E) (u : Fin k → E),
      ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).symmL ℝ z U) u =
        U (fun i => Linv (u i)) := by
    intro k U u
    have h_inv : ∀ y : E, L (Linv y) = y := by
      intro y
      have h := congrArg (fun f : E →L[ℝ] E => f y) hL
      simpa [ContinuousLinearMap.comp_apply] using h
    have hu : u = fun i => L (Linv (u i)) := by
      funext i; exact (h_inv (u i)).symm
    calc
      ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).symmL ℝ z U) u
          = ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).symmL ℝ z U)
              (fun i => L (Linv (u i))) := by rw [← hu]
      _ = (trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).continuousLinearMapAt ℝ z
            ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).symmL ℝ z U)
            (fun i => Linv (u i)) := (h_cLMAt k _ _).symm
      _ = U (fun i => Linv (u i)) := by
            rw [(trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).continuousLinearMapAt_symmL
              (R := ℝ) hx]
  have h_input :
      ((trivializationAt (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I y) x₀ ⟨z, Tz⟩).2) =
      (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (s + 1) L).comp
        (Tx.comp (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace (s + 1) I y) x₀).continuousLinearMapAt ℝ z
        ((Tz) ((trivializationAt (Tensor0SBundle.Tensor0SModel (1 + r) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (1 + r) I y) x₀).symmL ℝ z β)) v =
      ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (s + 1) L)
        (Tx ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv) β))) v
    rw [h_cLMAt, Tensor0SBundle.model_covariantChange_apply]
    have hβ :
        (trivializationAt (Tensor0SBundle.Tensor0SModel (1 + r) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (1 + r) I y) x₀).symmL ℝ z β =
          (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      rw [h_symmL]; rfl
    rw [hβ]; rfl
  have h_output :
      (trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace r s I y) x₀
        ⟨z, Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s z Tz⟩).2 =
      (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) s L).comp
        ((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s Tx).comp
          (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace s I y) x₀).continuousLinearMapAt ℝ z
        ((Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s z Tz)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) x₀).symmL ℝ z β)) v =
      ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) s L)
        ((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s Tx)
          ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv) β))) v
    rw [h_cLMAt, Tensor0SBundle.model_covariantChange_apply]
    change ((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s
          ((Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) (1 + r) (s + 1) z) Tz))
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r z)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) x₀).symmL ℝ z β))) (fun i => L (v i)) =
      (((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s) Tx)
        ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv) β)) (fun i => L (v i))
    have hβ2 : (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r z)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) x₀).symmL ℝ z β) =
          (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      rw [Tensor0SBundle.model_covariantChange_apply]
      exact h_symmL r β u
    rw [hβ2]
  rw [h_input, h_output]
  exact (Tensor0SBundle.model_contract_trace_naturality (𝕜 := ℝ) (E := E)
    r s L Linv hL hR Tx).symm

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem contractTraceField_jointContMDiffOn (r s : ℕ) {S : Set ℝ}
    (T : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I p.1)
    (hT : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) p.1 (T p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1
        (Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s p.1 (T p)))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (1 + r) (s + 1)
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (1 + r)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hT' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z)).mp (hT p₀ hp₀)
  have hTrace : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ => Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s
        ((trivializationAt (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) x₀ ⟨p.1, T p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    (Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s).contMDiff.contMDiffAt.comp_contMDiffWithinAt
      p₀ hT'.2
  refine hTrace.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact contractTraceField_joint_pointwise (I := I) r s x₀ p.1 (T p) hx
  · have hx : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt _ _ x₀
    have hx0 : p₀.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by rw [← hx₀]; exact hx
    exact contractTraceField_joint_pointwise (I := I) r s x₀ p₀.1 (T p₀) hx0

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem domDomCongrField_joint_pointwise {d : ℕ} (ρ : Equiv.Perm (Fin d)) (x₀ : M) (z : M)
    (Zz : Tensor0SBundle.Tensor0SSpace d I z)
    (hx : z ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀
        ⟨z, Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := z)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel Zz))⟩).2 =
      ContinuousMultilinearMap.domDomCongr ρ
        ((trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀ ⟨z, Zz⟩).2) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  set L : E →L[ℝ] E := (trivializationAt E (TangentSpace I) x₀).symmL ℝ z with hLdef

  have h_cLMAt : ∀ (U : Tensor0SBundle.Tensor0SSpace d I z) (v : Fin d → E),
      (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀).continuousLinearMapAt ℝ z U v =
      U (fun i => L (v i)) := by
    intro U v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀).linearMapAt ℝ z) =
        fun y => (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀ ⟨z, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
    rfl
  have h_coord : ∀ (U : Tensor0SBundle.Tensor0SSpace d I z) (v : Fin d → E),
      (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀ ⟨z, U⟩).2 v =
      U (fun i => L (v i)) := by
    intro U v
    rw [← h_cLMAt U v, Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀).linearMapAt ℝ z) =
        fun y => (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀ ⟨z, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [h_coord, h_coord]

  have hof : ∀ (m : Fin d → E),
      (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := z)
        (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz))) m =
      (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz)) m := by
    intro m
    have h := Tensor0SBundle.Tensor0SSpace.toModel_ofModel (𝕜 := ℝ) (I := I) (x := z)
      (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz))
    calc (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := z)
            (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz))) m
        = Tensor0SBundle.Tensor0SSpace.toModel
            (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := z)
              (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz))) m := rfl
      _ = (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz)) m := by
            rw [h]
  rw [hof, ContinuousMultilinearMap.domDomCongr_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem domDomCongrField_jointContMDiffOn {d : ℕ} (ρ : Equiv.Perm (Fin d)) {S : Set ℝ}
    (Z : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (Z p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel (Z p)))))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hZ' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hZ p₀ hp₀)
  have hcongr : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E) ∞
      (fun p : M × ℝ => ContinuousMultilinearMap.domDomCongr ρ
        ((trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ ⟨p.1, Z p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hop : ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)
        𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E) ∞
        (fun U : Tensor0SBundle.Tensor0SModel d ℝ E => ContinuousMultilinearMap.domDomCongr ρ U) :=
      (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ ρ).toContinuousLinearEquiv.toContinuousLinearMap.contMDiff
    exact hop.contMDiffAt.comp_contMDiffWithinAt p₀ hZ'.2
  refine hcongr.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (domDomCongrField_joint_pointwise (I := I) ρ x₀ p.1 (Z p) hx).symm
  · have hx : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt _ _ x₀
    have hx0 : p₀.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by rw [← hx₀]; exact hx
    exact (domDomCongrField_joint_pointwise (I := I) ρ x₀ p₀.1 (Z p₀) hx0).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem jointTotalSpace_add {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact ((e.linear ℝ hx).map_add (A p) (B p)).symm
  · exact ((e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem jointTotalSpace_sub {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact ((e.linear ℝ hx).map_sub (A p) (B p)).symm
  · exact ((e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem jointTotalSpace_smul {d : ℕ} {S : Set ℝ} (a : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (a • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := a)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact ((e.linear ℝ hx).map_smul a (A p)).symm
  · exact ((e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      a (A p₀)).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem jointTotalSpaceRS_add {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    rw [Pi.add_apply]
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · rw [Pi.add_apply]
    exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem curriedField_jointContMDiffOn {d : ℕ} {S : Set ℝ}
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (d + 1) I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace d I z) p.1
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d p.1 (A p)))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (d + 1)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z)).mp (hA p₀ hp₀)
  have hcurry : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E) ∞
      (fun p : M × ℝ => continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ
        ((trivializationAt (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) x₀ ⟨p.1, A p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hop : ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E) ∞
        (fun U : Tensor0SBundle.Tensor0SModel (d + 1) ℝ E =>
          continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ U) :=
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ
        ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
    exact hop.contMDiffAt.comp_contMDiffWithinAt p₀ hA'.2
  refine hcurry.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    have hc := TensorMultilinear.trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun z : M => A ⟨z, p.2⟩) x₀ p.1 hx
    rw [TensorMultilinear.curriedSection] at hc
    exact hc
  · have hx0 : p₀.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).baseSet := by
      rw [← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀
    have hc := TensorMultilinear.trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun z : M => A ⟨z, p₀.2⟩) x₀ p₀.1 hx0
    rw [TensorMultilinear.curriedSection] at hc
    exact hc

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem uncurriedField_jointContMDiffOn {d : ℕ} {S : Set ℝ}
    (G : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace d I p.1)
    (hG : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace d I z) p.1 (G p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d p.1).symm (G p)))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (d + 1)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hG' := (Bundle.contMDiffWithinAt_totalSpace (F := E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace d I z)).mp (hG p₀ hp₀)
  have huncurry : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E) ∞
      (fun p : M × ℝ => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ).symm
        ((trivializationAt (E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace d I z) x₀
          ⟨p.1, G p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hop : ContMDiff 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
        𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E) ∞
        (fun U : E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E =>
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ).symm U) :=
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ
        ).toContinuousLinearEquiv.symm.toContinuousLinearMap).contMDiff
    exact hop.contMDiffAt.comp_contMDiffWithinAt p₀ hG'.2

  have hpt : ∀ p : M × ℝ,
      p.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀).baseSet →
      (trivializationAt (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (d + 1) I y) x₀
          ⟨p.1, (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d p.1).symm (G p)⟩).2 =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ).symm
          ((trivializationAt (E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
            (fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace d I y) x₀
            ⟨p.1, G p⟩).2) := by
    intro p hz
    have hUcurry : TensorMultilinear.curriedSection (I := I) (M := M)
        (fun y : M => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d y).symm (G ⟨y, p.2⟩)) p.1 =
          G p := by
      rw [TensorMultilinear.curriedSection]
      exact ContinuousLinearEquiv.apply_symm_apply _ _
    have hfwd := TensorMultilinear.trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun y : M => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d y).symm (G ⟨y, p.2⟩)) x₀ p.1 hz
    rw [hUcurry] at hfwd
    rw [show (fun y : M => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d y).symm (G ⟨y, p.2⟩)) p.1 =
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d p.1).symm (G p) from rfl] at hfwd
    rw [hfwd]
    exact (LinearIsometryEquiv.symm_apply_apply
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ) _).symm
  refine huncurry.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact hpt p hx
  · have hx0 : p₀.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).baseSet := by
      rw [← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀
    exact hpt p₀ hx0

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem slotInsertEndo0Field_apply_jointContMDiffOn {d : ℕ} {S : Set ℝ}
    (Λ : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] TangentSpace I p.1)
    (hΛ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1 (Λ p))
      ((Set.univ : Set M) ×ˢ S))
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (d + 1) I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1
        (slotInsertEndoFib (I := I) (M := M) (d + 1) 0 p.1 (Λ p) (A p)))
      ((Set.univ : Set M) ×ˢ S) := by

  have hcurry := curriedField_jointContMDiffOn (I := I) (M := M) (d := d) (S := S) A hA

  have hcomp : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace d I z) p.1
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d p.1 (A p)).comp (Λ p)))
      ((Set.univ : Set M) ×ˢ S) := by
    apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := Tensor0SBundle.Tensor0SModel d ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace d I x)
      (φ := fun p : M × ℝ => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d p.1 (A p)).comp (Λ p))
      (S := S)
    intro Z

    have hZjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Z p.1))
        ((Set.univ : Set M) ×ˢ S) :=
      Z.contMDiff.comp_contMDiffOn contMDiffOn_fst
    have hΛZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Λ p (Z p.1)))
        ((Set.univ : Set M) ×ˢ S) :=
      ContMDiffOn.clm_bundle_apply (b := Prod.fst) hΛ hZjoint

    have happ := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hcurry hΛZ
    refine happ.congr (fun p _ => ?_)
    rfl

  have huncurry := uncurriedField_jointContMDiffOn (I := I) (M := M) (d := d) (S := S)
    (fun p : M × ℝ => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d p.1 (A p)).comp (Λ p)) hcomp
  refine huncurry.congr (fun p _ => ?_)
  congr 1
  exact slotInsertEndoFib_zero (I := I) (M := M) d p.1 (Λ p) (A p)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem slotInsertEndo1Field_apply_jointContMDiffOn {d : ℕ} {S : Set ℝ}
    (g : SmoothRiemannianMetric I M)
    (Λ : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] TangentSpace I p.1)
    (hΛ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1 (Λ p))
      ((Set.univ : Set M) ×ˢ S))
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (d + 2) I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 2) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 2) I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 2) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 2) I z) p.1
        (slotInsertEndoFib (I := I) (M := M) (d + 2) 1 p.1 (Λ p) (A p)))
      ((Set.univ : Set M) ×ˢ S) := by

  have hcurry := curriedField_jointContMDiffOn (I := I) (M := M) (d := d + 1) (S := S) A hA

  have hcomp : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1
        ((slotInsertEndoFib (I := I) (M := M) (d + 1) 0 p.1 (Λ p)).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (d + 1) p.1 (A p))))
      ((Set.univ : Set M) ×ˢ S) := by
    apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
      (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (d + 1) I x)
      (φ := fun p : M × ℝ => (slotInsertEndoFib (I := I) (M := M) (d + 1) 0 p.1 (Λ p)).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (d + 1) p.1 (A p)))
      (S := S)
    intro Z

    have hcurryZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (d + 1) p.1 (A p) (Z p.1)))
        ((Set.univ : Set M) ×ˢ S) := by
      have hZjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Z p.1))
          ((Set.univ : Set M) ×ˢ S) :=
        Z.contMDiff.comp_contMDiffOn contMDiffOn_fst
      exact ContMDiffOn.clm_bundle_apply (b := Prod.fst) hcurry hZjoint

    have happ := slotInsertEndo0Field_apply_jointContMDiffOn (I := I) (M := M) (d := d) (S := S)
      (Λ := Λ) hΛ
      (A := fun p : M × ℝ =>
        tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (d + 1) p.1 (A p) (Z p.1)) hcurryZ
    refine happ.congr (fun p _ => ?_)
    rfl

  have huncurry := uncurriedField_jointContMDiffOn (I := I) (M := M) (d := d + 1) (S := S)
    (fun p : M × ℝ => (slotInsertEndoFib (I := I) (M := M) (d + 1) 0 p.1 (Λ p)).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (d + 1) p.1 (A p))) hcomp
  refine huncurry.congr (fun p _ => ?_)
  congr 1
  rw [show (1 : Fin (d + 2)) = (0 : Fin (d + 1)).succ from rfl,
    slotInsertEndoFib_succ (I := I) (M := M) g (d + 1) 0 p.1 (Λ p),
    slotExtendFib_apply (I := I) (M := M) g (d + 1) (d + 1) p.1]

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
