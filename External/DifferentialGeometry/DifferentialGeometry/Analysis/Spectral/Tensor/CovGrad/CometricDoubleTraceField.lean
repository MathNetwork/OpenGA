import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
import DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradParallelNaturality
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCovariantCalculus
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

noncomputable def modelRankCast {m n : ℕ} (h : m = n) :
    Tensor0SBundle.Tensor0SModel m ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E :=
  (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
    (finCongr h)).toContinuousLinearEquiv.toContinuousLinearMap


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
@[simp] theorem modelRankCast_refl {m : ℕ} (T : Tensor0SBundle.Tensor0SModel m ℝ E) :
    modelRankCast (E := E) (rfl : m = m) T = T := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [modelRankCast, finCongr_refl]
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem interiorProductField_contMDiff (s : ℕ)
    (α : ∀ x : M, Tensor0SBundle.Tensor0SSpace (s + 1) I x)
    (hα : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x (α x)))
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z) x
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x (X x) (α x))) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  intro x₀
  rw [Bundle.contMDiffAt_section (F := Tensor0SBundle.Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z)]
  have hα' := (Bundle.contMDiffAt_section (F := Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x₀).mp (hα x₀)
  have hX' := (Bundle.contMDiffAt_section (F := E) (E := TangentSpace I) x₀).mp (X.contMDiff x₀)
  have h_combine :
      ContMDiffAt I 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E) ∞
        (fun x => Tensor0SBundle.model_interior_bilinear ℝ E s
          ((trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
            (fun x => Tensor0SBundle.Tensor0SSpace (s + 1) I x) x₀ ⟨x, α x⟩).2)) x₀ :=
    ((contMDiffAt_const (c := Tensor0SBundle.model_interior_bilinear ℝ E s)).clm_apply hX').clm_apply hα'
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx

  apply ContinuousMultilinearMap.ext
  intro v
  set symmL := (trivializationAt E (TangentSpace I) x₀).symmL ℝ x with hsymmL
  set gtilde : E := (trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2 with hgtilde
  change (α x) (@Fin.cons s (fun _ => E) ((X x : TangentSpace I x) : E) (fun i => symmL (v i))) =
    (α x) (fun i => symmL (@Fin.cons s (fun _ => E) gtilde v i))
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · change ((X x : TangentSpace I x) : E) = symmL gtilde
    have h := (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := ℝ) hx (X x)
    have hcl : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x (X x) = gtilde := by
      change (trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ x (X x) = _
      rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
    rw [hcl] at h
    exact h.symm
  · intro j
    rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem contractTraceField_contMDiff (r s : ℕ)
    (T : ∀ x : M, Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I x)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) x (T x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x
        (Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x (T x))) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (1 + r) (s + 1)
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (1 + r)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r
  intro x₀
  rw [Bundle.contMDiffAt_section (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)]
  have hT' := (Bundle.contMDiffAt_section (F := Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) x₀).mp (hT x₀)
  have hTrace : ContMDiffAt I 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E) ∞
      (fun x => Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s
        ((trivializationAt (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) x₀ ⟨x, T x⟩).2)) x₀ :=
    (Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s).contMDiffAt.comp x₀ hT'
  refine hTrace.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx

  set L : E →L[ℝ] E := (trivializationAt E (TangentSpace I) x₀).symmL ℝ x with hLdef
  set Linv : E →L[ℝ] E := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x with hLinvdef
  set Tx : Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E :=
    Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) (1 + r) (s + 1) x (T x) with hTxdef
  have hL : L.comp Linv = ContinuousLinearMap.id ℝ E := by
    ext z
    exact (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt (R := ℝ) hx z
  have hR : Linv.comp L = ContinuousLinearMap.id ℝ E := by
    ext z
    exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL (R := ℝ) hx z
  have h_cLMAt : ∀ (k : ℕ) (U : Tensor0SBundle.Tensor0SSpace k I x) (v : Fin k → E),
      (trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).continuousLinearMapAt ℝ x U v =
      U (fun i => L (v i)) := by
    intro k U v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).linearMapAt ℝ x) =
        fun y => (trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
    rfl
  have h_symmL : ∀ (k : ℕ) (U : Tensor0SBundle.Tensor0SModel k ℝ E) (u : Fin k → E),
      ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).symmL ℝ x U) u =
        U (fun i => Linv (u i)) := by
    intro k U u
    have h_inv : ∀ z : E, L (Linv z) = z := by
      intro z
      have h := congrArg (fun f : E →L[ℝ] E => f z) hL
      simpa [ContinuousLinearMap.comp_apply] using h
    have hu : u = fun i => L (Linv (u i)) := by
      funext i; exact (h_inv (u i)).symm
    calc
      ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).symmL ℝ x U) u
          = ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).symmL ℝ x U)
              (fun i => L (Linv (u i))) := by rw [← hu]
      _ = (trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).continuousLinearMapAt ℝ x
            ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).symmL ℝ x U)
            (fun i => Linv (u i)) := (h_cLMAt k _ _).symm
      _ = U (fun i => Linv (u i)) := by
            rw [(trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).continuousLinearMapAt_symmL
              (R := ℝ) hx]
  have h_input :
      ((trivializationAt (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) x₀ ⟨x, T x⟩).2) =
      (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (s + 1) L).comp
        (Tx.comp (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x₀).continuousLinearMapAt ℝ x
        ((T x) ((trivializationAt (Tensor0SBundle.Tensor0SModel (1 + r) ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace (1 + r) I z) x₀).symmL ℝ x β)) v =
      ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (s + 1) L)
        (Tx ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv) β))) v
    rw [h_cLMAt, Tensor0SBundle.model_covariantChange_apply]
    have hβ :
        (trivializationAt (Tensor0SBundle.Tensor0SModel (1 + r) ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace (1 + r) I z) x₀).symmL ℝ x β =
          (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      rw [h_symmL]; rfl
    rw [hβ]; rfl
  have h_output :
      (trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀
        ⟨x, Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x (T x)⟩).2 =
      (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) s L).comp
        ((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s Tx).comp
          (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace s I z) x₀).continuousLinearMapAt ℝ x
        ((Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x (T x))
          ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace r I z) x₀).symmL ℝ x β)) v =
      ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) s L)
        ((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s Tx)
          ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv) β))) v
    rw [h_cLMAt, Tensor0SBundle.model_covariantChange_apply]

    change ((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s
          ((Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) (1 + r) (s + 1) x) (T x)))
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r x)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace r I z) x₀).symmL ℝ x β))) (fun i => L (v i)) =
      (((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s) Tx)
        ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv) β)) (fun i => L (v i))
    have hβ2 : (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r x)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace r I z) x₀).symmL ℝ x β) =
          (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      rw [Tensor0SBundle.model_covariantChange_apply]
      exact h_symmL r β u
    rw [hβ2]
  rw [h_input, h_output]
  exact (Tensor0SBundle.model_contract_trace_naturality (𝕜 := ℝ) (E := E)
    r s L Linv hL hR Tx).symm

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem tensor0SField_castRank_contMDiff {m n : ℕ} (h : m = n)
    (Y : ∀ x : M, Tensor0SBundle.Tensor0SSpace m I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel m ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace m I z) x (Y x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace n I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (modelRankCast (E := E) h (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
  subst h
  refine hY.congr (fun x => ?_)

  simp only [modelRankCast_refl, Tensor0SBundle.Tensor0SSpace.ofModel_toModel]

noncomputable def cometricLmodel (g₀ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E :=
  (inverseMetricSharpFib (I := I) g₀ x).comp
    (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm.toContinuousLinearMap

noncomputable def modelDoubleTrace (s : ℕ) (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) :
    Tensor0SBundle.Tensor0SModel (s + 2) ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel s ℝ E :=
  ∑ k : Fin (Module.finrank ℝ E),
    (Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s ((Module.finBasis ℝ E) k)).comp
      (Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) (s + 1)
        (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))))


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem modelDoubleTrace_apply (s : ℕ) (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel (s + 2) ℝ E) (m : Fin s → E) :
    modelDoubleTrace (E := E) s L D m =
      ∑ k : Fin (Module.finrank ℝ E),
        D (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) m)) := by
  classical
  rw [modelDoubleTrace]
  simp only [ContinuousLinearMap.sum_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousLinearMap.comp_apply]
  rfl

noncomputable def ricciCometricDoubleTraceFib (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    Tensor0SBundle.Tensor0SSpace (4 + a) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a) I x :=
  (-2 : ℝ) •
    (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (2 + a) x).symm.toContinuousLinearMap.comp
      ((modelDoubleTrace (E := E) (2 + a) (cometricLmodel (I := I) g₀ x)).comp
        ((modelRankCast (E := E) (by omega : (4 + a) = (2 + a) + 2)).comp
          (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (4 + a) x).toContinuousLinearMap))


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem ricciCometricDoubleTraceFib_toModel (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace (4 + a) I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (ricciCometricDoubleTraceFib (I := I) g₀ a x D) =
      (-2 : ℝ) • modelDoubleTrace (E := E) (2 + a) (cometricLmodel (I := I) g₀ x)
        (modelRankCast (E := E) (by omega : (4 + a) = (2 + a) + 2)
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := rfl

noncomputable def raiseSlot0ModelL (s : ℕ) (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) :
    Tensor0SBundle.Tensor0SModel (s + 2) ℝ E →L[ℝ] Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E :=
  ContinuousLinearMap.flip
    ((Tensor0SBundle.model_interior_bilinear ℝ E (s + 1)).comp L)


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
@[simp] theorem raiseSlot0ModelL_apply (s : ℕ) (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel (s + 2) ℝ E) (β : Tensor0SBundle.Tensor0SModel 1 ℝ E) :
    raiseSlot0ModelL (E := E) s L D β =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) (s + 1) (L β) D := rfl


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem model_contract_trace_raiseSlot0ModelL (s : ℕ)
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel (s + 2) ℝ E) :
    (Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) 0 s (raiseSlot0ModelL (E := E) s L D))
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
      modelDoubleTrace (E := E) s L D := by
  classical
  apply ContinuousMultilinearMap.ext
  intro m
  rw [Tensor0SBundle.model_contract_trace_apply_basis (Module.finBasis ℝ E) 0 s
    (raiseSlot0ModelL (E := E) s L D)
    (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) m,
    modelDoubleTrace_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)

  have htw : Tensor0SBundle.model_tensorWithCovector_first (𝕜 := ℝ) (E := E) 0
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)))
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
      Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    rw [Tensor0SBundle.model_tensorWithCovector_first, LinearMap.coe_toContinuousLinearMap']
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Bundle.continuousMultilinearMap.modelProduct_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, mul_one,
      Tensor0SBundle.model_covectorOfCLM_apply, Tensor0SBundle.model_covectorOfCLM_apply]
    rfl
  rw [htw, raiseSlot0ModelL_apply]

  rw [show ((Module.finBasis ℝ E).cDualBasis i) =
      LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i) from by
        rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
        congr 1
        exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) i]
  rfl

noncomputable def cometricRaiseSlot0Fib (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    Tensor0SBundle.Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SBundle.TensorRSSpace 1 (s + 1) I x :=
  (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 1 (s + 1) x).symm.toContinuousLinearMap.comp
    ((raiseSlot0ModelL (E := E) s (cometricLmodel (I := I) g₀ x)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (s + 2) x).toContinuousLinearMap)


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem cometricRaiseSlot0Fib_toModel (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace (s + 2) I x) :
    Tensor0SBundle.TensorRSSpace.toModel (cometricRaiseSlot0Fib (I := I) g₀ s x D) =
      raiseSlot0ModelL (E := E) s (cometricLmodel (I := I) g₀ x)
        (Tensor0SBundle.Tensor0SSpace.toModel D) := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem cometricRaiseSlot0Fib_section_contMDiff (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Y : ∀ x : M, Tensor0SBundle.Tensor0SSpace (s + 2) I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 2) I z) x (Y x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (s + 1) I z) x
        (cometricRaiseSlot0Fib (I := I) g₀ s x (Y x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel (s + 1) ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (s + 1) I x)
    (φ := fun x => (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + 1) I x from
      cometricRaiseSlot0Fib (I := I) g₀ s x (Y x)))
  intro β

  have hsharpβ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (inverseMetricSharpFib (I := I) g₀ x (β x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (inverseMetricSharpField_contMDiff (I := I) g₀) β.contMDiff
  let sharpβ : ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    ⟨fun x : M => inverseMetricSharpFib (I := I) g₀ x (β x), hsharpβ⟩

  have hcontract := interiorProductField_contMDiff (I := I) (s + 1) (fun x => Y x) hY sharpβ
  refine hcontract.congr (fun x => ?_)

  change TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) x (sharpβ x) (Y x)) =
    TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x
      ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + 1) I x from
        cometricRaiseSlot0Fib (I := I) g₀ s x (Y x)) (β x))

  congr 1


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem contract_trace_unitZero_toModel (s : ℕ) (x : M)
    (T : Tensor0SBundle.TensorRSSpace 1 (s + 1) I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 s x T)
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      (Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) 0 s
          (Tensor0SBundle.TensorRSSpace.toModel T))
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) := by
  rw [Tensor0SBundle.contract_trace]
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [CompactSpace M] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem ricciCometricDoubleTraceFib_contMDiff (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel (4 + a) (2 + a) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel (4 + a) (2 + a) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace (4 + a) (2 + a) I z) x
        (ricciCometricDoubleTraceFib (I := I) g₀ a x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel (4 + a) ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace (4 + a) I x)
    (F₂ := Tensor0SBundle.Tensor0SModel (2 + a) ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (2 + a) I x)
    (φ := fun x => ricciCometricDoubleTraceFib (I := I) g₀ a x)
  intro Y

  let Y' : ∀ x : M, Tensor0SBundle.Tensor0SSpace ((2 + a) + 2) I x :=
    fun x => Tensor0SBundle.Tensor0SSpace.ofModel
      (modelRankCast (E := E) (by omega : (4 + a) = (2 + a) + 2)
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))
  have hY' : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel ((2 + a) + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel ((2 + a) + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace ((2 + a) + 2) I z) x (Y' x)) :=
    tensor0SField_castRank_contMDiff (I := I) (by omega : (4 + a) = (2 + a) + 2) (fun x => Y x) Y.contMDiff

  have hraise := cometricRaiseSlot0Fib_section_contMDiff (I := I) g₀ (2 + a) Y' hY'

  have htrace := contractTraceField_contMDiff (I := I) 0 (2 + a)
    (fun x => cometricRaiseSlot0Fib (I := I) g₀ (2 + a) x (Y' x)) hraise
  have htraceUnit : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (2 + a) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (2 + a) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (2 + a) I z) x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a) I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 (2 + a) x
            (cometricRaiseSlot0Fib (I := I) g₀ (2 + a) x (Y' x)))
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    ContMDiff.clm_bundle_apply (b := id) htrace
      (Integral.Connection.unitZeroSec (I := I) (M := M)).contMDiff

  have hscaled : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (2 + a) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (2 + a) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (2 + a) I z) x
        ((-2 : ℝ) • ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a) I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 (2 + a) x
            (cometricRaiseSlot0Fib (I := I) g₀ (2 + a) x (Y' x)))
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) :=
    ContMDiff.const_smul_section (a := (-2 : ℝ)) htraceUnit
  refine hscaled.congr (fun x => ?_)

  congr 1
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [ricciCometricDoubleTraceFib_toModel, Tensor0SBundle.Tensor0SSpace.toModel_smul]
  congr 1

  rw [← model_contract_trace_raiseSlot0ModelL (E := E) (2 + a) (cometricLmodel (I := I) g₀ x)
    (modelRankCast (E := E) (by omega : (4 + a) = (2 + a) + 2)
      (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))]

  rw [contract_trace_unitZero_toModel (I := I) (2 + a) x
    (cometricRaiseSlot0Fib (I := I) g₀ (2 + a) x (Y' x))]
  congr 1

open DifferentialGeometry.Integral.Connection

noncomputable def cometricDoubleTraceFib (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (x : M) :
    Tensor0SBundle.Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace p I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) p x).symm.toContinuousLinearMap.comp
    ((modelDoubleTrace (E := E) p (cometricLmodel (I := I) g₀ x)).comp
      ((modelRankCast (E := E) (rfl : (p + 2) = p + 2)).comp
        (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (p + 2) x).toContinuousLinearMap))


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem cometricDoubleTraceFib_toModel (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace (p + 2) I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₀ p x D) =
      modelDoubleTrace (E := E) p (cometricLmodel (I := I) g₀ x)
        (Tensor0SBundle.Tensor0SSpace.toModel D) := by
  rw [cometricDoubleTraceFib]
  change modelDoubleTrace (E := E) p (cometricLmodel (I := I) g₀ x)
      (modelRankCast (E := E) (rfl : (p + 2) = p + 2) (Tensor0SBundle.Tensor0SSpace.toModel D)) = _
  rw [modelRankCast_refl]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [CompactSpace M] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem cometricDoubleTraceFib_contMDiff (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel (p + 2) p ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel (p + 2) p ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace (p + 2) p I z) x
        (cometricDoubleTraceFib (I := I) g₀ p x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel (p + 2) ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace (p + 2) I x)
    (F₂ := Tensor0SBundle.Tensor0SModel p ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace p I x)
    (φ := fun x => cometricDoubleTraceFib (I := I) g₀ p x)
  intro Y

  have hraise := cometricRaiseSlot0Fib_section_contMDiff (I := I) g₀ p (fun x => Y x) Y.contMDiff

  have htrace := contractTraceField_contMDiff (I := I) 0 p
    (fun x => cometricRaiseSlot0Fib (I := I) g₀ p x (Y x)) hraise
  have htraceUnit : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace p I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 p x
            (cometricRaiseSlot0Fib (I := I) g₀ p x (Y x)))
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    ContMDiff.clm_bundle_apply (b := id) htrace
      (Integral.Connection.unitZeroSec (I := I) (M := M)).contMDiff
  refine htraceUnit.congr (fun x => ?_)

  congr 1
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [cometricDoubleTraceFib_toModel]
  rw [← model_contract_trace_raiseSlot0ModelL (E := E) p (cometricLmodel (I := I) g₀ x)
    (Tensor0SBundle.Tensor0SSpace.toModel (Y x))]
  rw [contract_trace_unitZero_toModel (I := I) p x
    (cometricRaiseSlot0Fib (I := I) g₀ p x (Y x))]
  congr 1

noncomputable def cometricDoubleTraceField (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    Integral.L2.SmoothCcTensor g₀ (p + 2) p where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace (p + 2) p I x from
          cometricDoubleTraceFib (I := I) g₀ p x)
      contMDiff_toFun := cometricDoubleTraceFib_contMDiff (I := I) g₀ p }
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] theorem cometricDoubleTraceField_toSection (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (x : M) :
    (cometricDoubleTraceField (I := I) g₀ p).toSection x =
      (show Tensor0SBundle.TensorRSSpace (p + 2) p I x from
        cometricDoubleTraceFib (I := I) g₀ p x) := rfl


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
private theorem model_cons_slot0_sum {s : ℕ} {ι : Type*} (fs : Finset ι)
    (T : Tensor0SBundle.Tensor0SModel (s + 1) ℝ E) (f : ι → E) (rest : Fin s → E) :
    T (Fin.cons (∑ i ∈ fs, f i) rest) = ∑ i ∈ fs, T (Fin.cons (f i) rest) := by
  have h : ∀ u : E, T (Fin.cons u rest) =
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1) => E) ℝ) T u) rest := by
    intro u
    rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [h, map_sum, ContinuousMultilinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => (h (f i)).symm


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
private theorem model_cons_slot0_smul {s : ℕ} (c : ℝ) (u : E)
    (T : Tensor0SBundle.Tensor0SModel (s + 1) ℝ E) (rest : Fin s → E) :
    T (Fin.cons (c • u) rest) = c * T (Fin.cons u rest) := by
  have h : ∀ z : E, T (Fin.cons z rest) =
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1) => E) ℝ) T z) rest := by
    intro z
    rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [h, map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul, ← h]


omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem smoothOrthoFrame_basis_at (g₀ : SmoothRiemannianMetric I M) (x : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x) :
    ∃ bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y),
      ∀ i, bse i = smoothOrthoFrame (I := I) g₀ x i y := by
  classical
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner y (smoothOrthoFrame (I := I) g₀ x a y)
        (smoothOrthoFrame (I := I) g₀ x b y) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal (I := I) g₀ x hy a b
  have he_li : LinearIndependent ℝ
      (fun i => smoothOrthoFrame (I := I) g₀ x i y) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g₀.inner y (smoothOrthoFrame (I := I) g₀ x k y)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g₀ x j y) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g₀.inner y (smoothOrthoFrame (I := I) g₀ x k y)
        (c j • smoothOrthoFrame (I := I) g₀ x j y) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g₀.inner y (smoothOrthoFrame (I := I) g₀ x k y)).map_smul (c j),
        smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E :=
    Fintype.card_fin _
  exact ⟨basisOfLinearIndependentOfCardEqFinrank he_li hcard,
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i⟩


omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem smoothOrthoFrame_expansion_at (g₀ : SmoothRiemannianMetric I M) (x : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x) (u : TangentSpace I y) :
    u = ∑ i : Fin (Module.finrank ℝ E),
      g₀.inner y u (smoothOrthoFrame (I := I) g₀ x i y) •
        smoothOrthoFrame (I := I) g₀ x i y := by
  classical
  obtain ⟨bse, hbse⟩ := smoothOrthoFrame_basis_at (I := I) g₀ x hy
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner y (smoothOrthoFrame (I := I) g₀ x a y)
        (smoothOrthoFrame (I := I) g₀ x b y) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal (I := I) g₀ x hy a b
  have hcoeff : ∀ j : Fin (Module.finrank ℝ E),
      g₀.inner y u (smoothOrthoFrame (I := I) g₀ x j y) = bse.repr u j := by
    intro j
    rw [g₀.symm y u (smoothOrthoFrame (I := I) g₀ x j y)]
    conv_lhs => rw [← bse.sum_repr u]
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [(g₀.inner y (smoothOrthoFrame (I := I) g₀ x j y)).map_smul (bse.repr u i),
        smul_eq_mul, hbse i, horth j i])]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [if_pos rfl, mul_one]
    · intro i _ hij
      rw [if_neg (fun h => hij h.symm), mul_zero]
  calc u = ∑ i : Fin (Module.finrank ℝ E), bse.repr u i • bse i := (bse.sum_repr u).symm
    _ = ∑ i : Fin (Module.finrank ℝ E),
        g₀.inner y u (smoothOrthoFrame (I := I) g₀ x i y) •
          smoothOrthoFrame (I := I) g₀ x i y := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoeff i, hbse i]


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem cometricLmodel_dualBasis_inner (g₀ : SmoothRiemannianMetric I M) (y : M)
    (k : Fin (Module.finrank ℝ E)) (u : TangentSpace I y) :
    g₀.inner y (cometricLmodel (I := I) g₀ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) u =
      (Module.finBasis ℝ E).repr (u : E) k := by
  have h1 : cometricLmodel (I := I) g₀ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) =
      inverseMetricSharpFib (I := I) g₀ y
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 y).symm
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) := rfl
  rw [h1, inverseMetricSharpFib_inner (I := I) g₀ y _ u, cotangentToDualLinear_apply,
    cotangentToDual_apply]
  have h2 : (((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 y).symm
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) (fun _ : Fin 1 => u) : ℝ) =
      Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k) (fun _ : Fin 1 => (u : E)) := rfl
  rw [h2, Tensor0SBundle.model_covectorOfCLM_apply]
  rw [show ((Module.finBasis ℝ E).cDualBasis k) =
      LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) from by
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    congr 1
    exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k]
  rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]


omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem cometric_dualTrace_eq_orthoFrame_diag (g₀ : SmoothRiemannianMetric I M)
    {s : ℕ} (x : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x)
    (T : Tensor0SBundle.Tensor0SModel (s + 2) ℝ E) (mm : Fin s → E) :
    ∑ k : Fin (Module.finrank ℝ E),
        T (Fin.cons (cometricLmodel (I := I) g₀ y
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) mm)) =
      ∑ i : Fin (Module.finrank ℝ E),
        T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) mm)) := by
  classical
  have hsharp : ∀ (k : Fin (Module.finrank ℝ E)) (u : TangentSpace I y),
      g₀.inner y (cometricLmodel (I := I) g₀ y
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) u =
        (Module.finBasis ℝ E).repr (u : E) k :=
    fun k u => cometricLmodel_dualBasis_inner (I := I) g₀ y k u
  have hexp : ∀ k : Fin (Module.finrank ℝ E),
      cometricLmodel (I := I) g₀ y
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr
              ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) •
            smoothOrthoFrame (I := I) g₀ x i y := by
    intro k
    conv_lhs => rw [smoothOrthoFrame_expansion_at (I := I) g₀ x hy
      (cometricLmodel (I := I) g₀ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)))]
    exact Finset.sum_congr rfl fun i _ => by
      rw [hsharp k (smoothOrthoFrame (I := I) g₀ x i y)]
  calc ∑ k : Fin (Module.finrank ℝ E),
      T (Fin.cons (cometricLmodel (I := I) g₀ y
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) mm))
      = ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr
              ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) *
            T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
                (Fin.cons ((Module.finBasis ℝ E) k) mm)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hexp k, model_cons_slot0_sum (E := E)]
        exact Finset.sum_congr rfl fun i _ => model_cons_slot0_smul (E := E) _ _ T _
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr
              ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) *
            T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
                (Fin.cons ((Module.finBasis ℝ E) k) mm)) := Finset.sum_comm
    _ = ∑ i : Fin (Module.finrank ℝ E),
          T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) mm)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hcurry : ∀ z : E,
            T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
                (Fin.cons z mm)) =
            ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 2) => E) ℝ) T
                ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E))
              (Fin.cons z mm) := by
          intro z
          rw [continuousMultilinearCurryLeftEquiv_apply]
        calc ∑ k : Fin (Module.finrank ℝ E),
            ((Module.finBasis ℝ E).repr
                ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) *
              T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
                  (Fin.cons ((Module.finBasis ℝ E) k) mm))
            = ∑ k : Fin (Module.finrank ℝ E),
                ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 2) => E) ℝ) T
                    ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E))
                  (Fin.cons (((Module.finBasis ℝ E).repr
                      ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) •
                    ((Module.finBasis ℝ E) k)) mm) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [model_cons_slot0_smul (E := E), ← hcurry]
          _ = ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 2) => E) ℝ) T
                  ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E))
                (Fin.cons (∑ k : Fin (Module.finrank ℝ E),
                  ((Module.finBasis ℝ E).repr
                      ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) •
                    ((Module.finBasis ℝ E) k)) mm) :=
              (model_cons_slot0_sum (E := E) Finset.univ _ _ mm).symm
          _ = T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) mm)) := by
              rw [(Module.finBasis ℝ E).sum_repr
                ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E), ← hcurry]


omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tensor0SCovDeriv_finset_sum (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    {ι : Type*} (fs : Finset ι)
    (σ : ι → Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel s ℝ E,
      (fun y : M => Tensor0SBundle.Tensor0SSpace s I y)⟯) (x : M) :
    Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g₀)
        (fun y : M => ∑ i ∈ fs, σ i y) x =
      ∑ i ∈ fs, Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g₀)
        (fun y : M => σ i y) x := by
  classical
  induction fs using Finset.cons_induction with
  | empty =>
    rw [show (fun y : M => ∑ i ∈ (∅ : Finset ι), σ i y) =
        (0 : Π y : M, Tensor0SBundle.Tensor0SSpace s I y) from
      funext fun y => Finset.sum_empty]
    rw [Finset.sum_empty]
    exact (Tensor0SNabla.tensor0SCovariantDerivative I M s
      (LeviCivita (I := I) g₀)).isCovariantDerivativeOnUniv.zero (Set.mem_univ x)
  | cons b fs' hb ih =>
    have hsum_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z) y (∑ i ∈ fs', σ i y)) := by
      refine (∑ i ∈ fs', σ i :
        Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel s ℝ E,
          (fun y : M => Tensor0SBundle.Tensor0SSpace s I y)⟯).contMDiff.congr fun y => ?_
      rw [ContMDiffSection.finset_sum_apply]
    have hadd := (Tensor0SNabla.tensor0SCovariantDerivative I M s
        (LeviCivita (I := I) g₀)).isCovariantDerivativeOnUniv.add
      (σ := fun y : M => σ b y) (σ' := fun y : M => ∑ i ∈ fs', σ i y) (x := x)
      (((σ b).contMDiff x).mdifferentiableAt (by norm_num))
      ((hsum_smooth x).mdifferentiableAt (by norm_num)) (Set.mem_univ x)
    rw [show (fun y : M => ∑ i ∈ Finset.cons b fs' hb, σ i y) =
        ((fun y : M => σ b y) + fun y : M => ∑ i ∈ fs', σ i y) from
      funext fun y => Finset.sum_cons hb]
    rw [hadd, ih, Finset.sum_cons]


omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem cometricDoubleTraceFib_eq_orthoFrame_diag (g₀ : SmoothRiemannianMetric I M)
    (p : ℕ) (x : M) {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x)
    (D : Tensor0SBundle.Tensor0SSpace (p + 2) I y) :
    cometricDoubleTraceFib (I := I) g₀ p y D =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p y
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) y D
            (smoothOrthoFrame (I := I) g₀ x i y))
          (smoothOrthoFrame (I := I) g₀ x i y) := by
  classical
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun mm => ?_
  beta_reduce
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ p y D]
  rw [modelDoubleTrace_apply (E := E) p (cometricLmodel (I := I) g₀ y)
    (Tensor0SBundle.Tensor0SSpace.toModel D) mm]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p y
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) y D
              (smoothOrthoFrame (I := I) g₀ x i y))
            (smoothOrthoFrame (I := I) g₀ x i y)) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p y
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) y D
              (smoothOrthoFrame (I := I) g₀ x i y))
            (smoothOrthoFrame (I := I) g₀ x i y)) from
    map_sum (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) p y) _ _]
  rw [ContinuousMultilinearMap.sum_apply]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ (s := p) x hy
    (Tensor0SBundle.Tensor0SSpace.toModel D) mm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) y D
        (smoothOrthoFrame (I := I) g₀ x i y))
      (v0 := ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)) (vs := mm),
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (T := D)
      (v0 := ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E))
      (vs := Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) mm)]


omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem orthoFrame_skew_correction_cancel (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (x : M)
    (v : E) (T : Tensor0SBundle.Tensor0SModel (p + 2) ℝ E) (mm : Fin p → E) :
    (∑ i : Fin (Module.finrank ℝ E),
        T (Fin.cons (((LeviCivita (I := I) g₀).toFun
              (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm)))
      + (∑ i : Fin (Module.finrank ℝ E),
          T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
              (Fin.cons (((LeviCivita (I := I) g₀).toFun
                  (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E) mm))) = 0 := by
  classical
  set a : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    g₀.inner x ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)
      (smoothOrthoFrame (I := I) g₀ x j x) with ha_def
  have haskew : ∀ i j, a i j = - a j i := by
    intro i j
    change g₀.inner x ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)
        (smoothOrthoFrame (I := I) g₀ x j x) =
      - g₀.inner x ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x j) x v)
        (smoothOrthoFrame (I := I) g₀ x i x)
    rw [smoothOrthoFrame_cov_skew (I := I) g₀ x i j v]
    rw [g₀.symm x (smoothOrthoFrame (I := I) g₀ x i x)
      ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x j) x v)]
  have hexp : ∀ i : Fin (Module.finrank ℝ E),
      (LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v =
        ∑ j : Fin (Module.finrank ℝ E), a i j • smoothOrthoFrame (I := I) g₀ x j x :=
    fun i => smoothOrthoFrame_expansion_at (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)
  have hS1 : (∑ i : Fin (Module.finrank ℝ E),
      T (Fin.cons (((LeviCivita (I := I) g₀).toFun
            (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (((LeviCivita (I := I) g₀).toFun
          (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E) =
        ((∑ j : Fin (Module.finrank ℝ E),
          a i j • smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E) from by
      rw [← hexp i]]
    rw [model_cons_slot0_sum (E := E)]
    exact Finset.sum_congr rfl fun j _ => model_cons_slot0_smul (E := E) _ _ T _
  have hS2 : (∑ i : Fin (Module.finrank ℝ E),
      T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
          (Fin.cons (((LeviCivita (I := I) g₀).toFun
              (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E) mm))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E) mm)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcurry : ∀ z : E,
        T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
            (Fin.cons z mm)) =
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (p + 2) => E) ℝ) T
            ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E))
          (Fin.cons z mm) := by
      intro z
      rw [continuousMultilinearCurryLeftEquiv_apply]
    rw [hcurry]
    rw [show (((LeviCivita (I := I) g₀).toFun
          (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E) =
        ((∑ j : Fin (Module.finrank ℝ E),
          a i j • smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E) from by
      rw [← hexp i]]
    rw [model_cons_slot0_sum (E := E)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [model_cons_slot0_smul (E := E), ← hcurry]
  rw [hS1, hS2]
  have h2 : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E) mm))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        -(a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [haskew j i, neg_mul]
  rw [h2]
  rw [show (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      -(a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm)))) =
      -(∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm))) from by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_neg_distrib]]
  exact add_neg_cancel _


omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem orthoFrame_corrections_sum_eq_zero (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (x : M)
    (v : E) (W : Tensor0SBundle.Tensor0SSpace (p + 2) I x) :
    (∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x W
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v))
          (smoothOrthoFrame (I := I) g₀ x i x))
      + (∑ i : Fin (Module.finrank ℝ E),
          Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x W
              (smoothOrthoFrame (I := I) g₀ x i x))
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)) = 0 := by
  classical
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun mm => ?_
  beta_reduce
  have heval : ∀ (z₁ z₂ : TangentSpace I x),
      Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x W z₁) z₂) mm =
        Tensor0SBundle.Tensor0SSpace.toModel W
          (Fin.cons ((z₁ : TangentSpace I x) : E)
            (Fin.cons ((z₂ : TangentSpace I x) : E) mm)) := by
    intro z₁ z₂
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x W z₁)
      (v0 := ((z₂ : TangentSpace I x) : E)) (vs := mm)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (T := W)
      (v0 := ((z₁ : TangentSpace I x) : E))
      (vs := Fin.cons ((z₂ : TangentSpace I x) : E) mm)]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_add]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x W
              ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v))
            (smoothOrthoFrame (I := I) g₀ x i x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x W
              ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v))
            (smoothOrthoFrame (I := I) g₀ x i x)) from
    map_sum (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) p x) _ _]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x W
              (smoothOrthoFrame (I := I) g₀ x i x))
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x W
              (smoothOrthoFrame (I := I) g₀ x i x))
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)) from
    map_sum (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) p x) _ _]
  rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.sum_apply]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    heval ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)
      (smoothOrthoFrame (I := I) g₀ x i x))]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    heval (smoothOrthoFrame (I := I) g₀ x i x)
      ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v))]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_zero, ContinuousMultilinearMap.zero_apply]
  exact orthoFrame_skew_correction_cancel (I := I) g₀ p x v
    (Tensor0SBundle.Tensor0SSpace.toModel W) mm


omit [CompactSpace M] [I.Boundaryless] in
omit [CompleteSpace E] in
private theorem covDeriv_doubleInsert_leibniz (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (w : ∀ y : M, Tensor0SBundle.Tensor0SSpace (p + 2) I y)
    (hw : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + 2) I z) y (w y)))
    (x : M) (i : Fin (Module.finrank ℝ E)) (v : E) :
    Tensor0SNabla.tensor0SCovariantDerivative I M p (LeviCivita (I := I) g₀)
        (fun y : M => (Tensor0SNabla.curriedSection I M
          (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
            (smoothOrthoFrame (I := I) g₀ x i z)) y)
          (smoothOrthoFrame (I := I) g₀ x i y)) x v =
      Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x
            (Tensor0SNabla.tensor0SCovariantDerivative I M (p + 2) (LeviCivita (I := I) g₀)
              (fun y : M => w y) x v)
            (smoothOrthoFrame (I := I) g₀ x i x))
          (smoothOrthoFrame (I := I) g₀ x i x)
        + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x (w x)
              ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v))
            (smoothOrthoFrame (I := I) g₀ x i x)
        + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x (w x)
              (smoothOrthoFrame (I := I) g₀ x i x))
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v) := by
  classical
  have hCi_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        (smoothOrthoFrame (I := I) g₀ x i y)) :=
    smoothOrthoFrame_smooth (I := I) g₀ x i
  let Ci : ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    ⟨fun y : M => smoothOrthoFrame (I := I) g₀ x i y, hCi_smooth⟩
  have hu_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + 1) I z) y
        ((Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
          (smoothOrthoFrame (I := I) g₀ x i y))) := by
    have hcurried : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel (p + 1) ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel (p + 1) ℝ E)
          (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace (p + 1) I z) y
          (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)) :=
      fun y => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section
        (I := I) (M := M) (fun z' : M => w z') y (hw y)
    exact ContMDiff.clm_bundle_apply (b := id) hcurried Ci.contMDiff
  have hu_at : TensorSectionMDiffAt (I := I) (p + 1)
      (fun y : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
        (smoothOrthoFrame (I := I) g₀ x i y)) x :=
    (hu_smooth x).mdifferentiableAt (by norm_num)
  have hw_at : TensorSectionMDiffAt (I := I) (p + 2) (fun y : M => w y) x :=
    (hw x).mdifferentiableAt (by norm_num)
  have h1 : Tensor0SNabla.tensor0SCovariantDerivative I M p (LeviCivita (I := I) g₀)
        (fun y : M => (Tensor0SNabla.curriedSection I M
          (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
            (smoothOrthoFrame (I := I) g₀ x i z)) y)
          (smoothOrthoFrame (I := I) g₀ x i y)) x v =
      Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
          (Tensor0SNabla.tensor0SCovariantDerivative I M (p + 1) (LeviCivita (I := I) g₀)
            (fun y : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
              (smoothOrthoFrame (I := I) g₀ x i y)) x v)
          (smoothOrthoFrame (I := I) g₀ x i x)
        + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x (w x)
              (smoothOrthoFrame (I := I) g₀ x i x))
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v) :=
    Integral.Connection.tensor0SCovariantDerivative_curriedSection_hom_leibniz
      (I := I) (M := M) g₀ p
      (fun y : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
        (smoothOrthoFrame (I := I) g₀ x i y)) (x := x) hu_at Ci v
  have h2 : Tensor0SNabla.tensor0SCovariantDerivative I M (p + 1) (LeviCivita (I := I) g₀)
        (fun y : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
          (smoothOrthoFrame (I := I) g₀ x i y)) x v =
      Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x
          (Tensor0SNabla.tensor0SCovariantDerivative I M (p + 2) (LeviCivita (I := I) g₀)
            (fun y : M => w y) x v)
          (smoothOrthoFrame (I := I) g₀ x i x)
        + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x (w x)
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v) :=
    Integral.Connection.tensor0SCovariantDerivative_curriedSection_hom_leibniz
      (I := I) (M := M) g₀ (p + 1) (fun y : M => w y) (x := x) hw_at Ci v
  rw [h1, h2, map_add (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x),
    ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in

omit [CompleteSpace E] in
theorem cometricDoubleTraceField_covGrad_eq_zero (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ (p + 2) p
        (cometricDoubleTraceField (I := I) g₀ p) = 0 := by
  classical
  have hdir : ∀ (x : M) (v : E),
      Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ (p + 2) p
        (cometricDoubleTraceField (I := I) g₀ p) x v = 0 := by
    intro x v
    apply ContinuousLinearMap.ext
    intro D
    obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)
      (V := fun y : M => Tensor0SBundle.Tensor0SSpace (p + 2) I y) (n := (⊤ : ℕ∞)) x D
    have hPR := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) (p + 2) p
      (LeviCivita (I := I) g₀) (cometricDoubleTraceField (I := I) g₀ p).toSection w x v
    rw [Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_def (I := I) (M := M) g₀ (p + 2) p
      (cometricDoubleTraceField (I := I) g₀ p) x v, ContinuousLinearMap.zero_apply, ← hw]
    refine Eq.trans hPR ?_
    rw [sub_eq_zero]
    have hCi_smooth : ∀ i : Fin (Module.finrank ℝ E),
        ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
            (smoothOrthoFrame (I := I) g₀ x i y)) :=
      fun i => smoothOrthoFrame_smooth (I := I) g₀ x i
    have hu_smooth : ∀ i : Fin (Module.finrank ℝ E),
        ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + 1) ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + 1) ℝ E)
            (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + 1) I z) y
            ((Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
              (smoothOrthoFrame (I := I) g₀ x i y))) := by
      intro i
      have hcurried : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel (p + 1) ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel (p + 1) ℝ E)
            (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace (p + 1) I z) y
            (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)) :=
        fun y => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section
          (I := I) (M := M) (fun z' : M => w z') y (w.contMDiff y)
      exact ContMDiff.clm_bundle_apply (b := id) hcurried (hCi_smooth i)
    have ht_smooth : ∀ i : Fin (Module.finrank ℝ E),
        ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
            (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) y
            ((Tensor0SNabla.curriedSection I M
              (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
                (smoothOrthoFrame (I := I) g₀ x i z)) y)
              (smoothOrthoFrame (I := I) g₀ x i y))) := by
      intro i
      have hcurried : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel p ℝ E)
            (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace p I z) y
            (Tensor0SNabla.curriedSection I M
              (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
                (smoothOrthoFrame (I := I) g₀ x i z)) y)) :=
        fun y => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section
          (I := I) (M := M)
          (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
            (smoothOrthoFrame (I := I) g₀ x i z)) y (hu_smooth i y)
      exact ContMDiff.clm_bundle_apply (b := id) hcurried (hCi_smooth i)
    let ti : Fin (Module.finrank ℝ E) →
        Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel p ℝ E,
          (fun y : M => Tensor0SBundle.Tensor0SSpace p I y)⟯ := fun i =>
      ⟨fun y : M => (Tensor0SNabla.curriedSection I M
          (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
            (smoothOrthoFrame (I := I) g₀ x i z)) y)
          (smoothOrthoFrame (I := I) g₀ x i y), ht_smooth i⟩
    have hP_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) y
          ((show Tensor0SBundle.Tensor0SSpace (p + 2) I y →L[ℝ] Tensor0SBundle.Tensor0SSpace p I y from
            (cometricDoubleTraceField (I := I) g₀ p).toSection y) (w y))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (cometricDoubleTraceField (I := I) g₀ p).toSection.contMDiff w.contMDiff
    set Q : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel p ℝ E,
        (fun y : M => Tensor0SBundle.Tensor0SSpace p I y)⟯ :=
      ∑ i : Fin (Module.finrank ℝ E), ti i with hQ_def
    have hQ_coe : ∀ y : M, Q y = ∑ i : Fin (Module.finrank ℝ E), ti i y := by
      intro y
      rw [hQ_def, ContMDiffSection.finset_sum_apply]
    have hagree : ∀ᶠ y in nhds x,
        (show Tensor0SBundle.Tensor0SSpace (p + 2) I y →L[ℝ] Tensor0SBundle.Tensor0SSpace p I y from
          (cometricDoubleTraceField (I := I) g₀ p).toSection y) (w y) = Q y := by
      filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x] with y hy
      rw [hQ_coe y]
      rw [show (show Tensor0SBundle.Tensor0SSpace (p + 2) I y →L[ℝ]
            Tensor0SBundle.Tensor0SSpace p I y from
          (cometricDoubleTraceField (I := I) g₀ p).toSection y) (w y) =
        cometricDoubleTraceFib (I := I) g₀ p y (w y) from rfl]
      rw [cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g₀ p x hy (w y)]
      rfl
    have hcongr := (Tensor0SNabla.tensor0SCovariantDerivative I M p
        (LeviCivita (I := I) g₀)).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (σ := fun y : M =>
        (show Tensor0SBundle.Tensor0SSpace (p + 2) I y →L[ℝ] Tensor0SBundle.Tensor0SSpace p I y from
          (cometricDoubleTraceField (I := I) g₀ p).toSection y) (w y))
      (σ' := fun y : M => Q y) (x := x)
      ((hP_smooth x).mdifferentiableAt (by norm_num))
      ((Q.contMDiff x).mdifferentiableAt (by norm_num)) Filter.univ_mem hagree
    have hfinal : (Tensor0SNabla.tensor0SCovariantDerivative I M p
          (LeviCivita (I := I) g₀)).toFun
          (fun y : M =>
            (show Tensor0SBundle.Tensor0SSpace (p + 2) I y →L[ℝ] Tensor0SBundle.Tensor0SSpace p I y from
              (cometricDoubleTraceField (I := I) g₀ p).toSection y) (w y)) x v =
        (show Tensor0SBundle.Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace p I x from
          (cometricDoubleTraceField (I := I) g₀ p).toSection x)
          ((Tensor0SNabla.tensor0SCovariantDerivative I M (p + 2)
            (LeviCivita (I := I) g₀)).toFun (fun y : M => w y) x v) := by
      calc (Tensor0SNabla.tensor0SCovariantDerivative I M p (LeviCivita (I := I) g₀)).toFun
            (fun y : M =>
              (show Tensor0SBundle.Tensor0SSpace (p + 2) I y →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace p I y from
                (cometricDoubleTraceField (I := I) g₀ p).toSection y) (w y)) x v
          = (Tensor0SNabla.tensor0SCovariantDerivative I M p (LeviCivita (I := I) g₀)).toFun
              (fun y : M => Q y) x v := by rw [hcongr]
        _ = ((Tensor0SNabla.tensor0SCovariantDerivative I M p
              (LeviCivita (I := I) g₀)).toFun
              (fun y : M => ∑ i : Fin (Module.finrank ℝ E), ti i y) x) v := by
            rw [show (fun y : M => Q y) =
                (fun y : M => ∑ i : Fin (Module.finrank ℝ E), ti i y) from funext hQ_coe]
        _ = ((∑ i : Fin (Module.finrank ℝ E),
              (Tensor0SNabla.tensor0SCovariantDerivative I M p
                (LeviCivita (I := I) g₀)).toFun (fun y : M => ti i y) x) v) := by
            rw [tensor0SCovDeriv_finset_sum (I := I) g₀ p Finset.univ ti x]
        _ = (∑ i : Fin (Module.finrank ℝ E),
              (Tensor0SNabla.tensor0SCovariantDerivative I M p
                (LeviCivita (I := I) g₀)).toFun (fun y : M => ti i y) x v) := by
            rw [ContinuousLinearMap.sum_apply]
        _ = (∑ i : Fin (Module.finrank ℝ E),
              (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
                  (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x
                    ((Tensor0SNabla.tensor0SCovariantDerivative I M (p + 2)
                      (LeviCivita (I := I) g₀)).toFun (fun y : M => w y) x v)
                    (smoothOrthoFrame (I := I) g₀ x i x))
                  (smoothOrthoFrame (I := I) g₀ x i x)
                + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
                    (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x (w x)
                      ((LeviCivita (I := I) g₀).toFun
                        (smoothOrthoFrame (I := I) g₀ x i) x v))
                    (smoothOrthoFrame (I := I) g₀ x i x)
                + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
                    (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x (w x)
                      (smoothOrthoFrame (I := I) g₀ x i x))
                    ((LeviCivita (I := I) g₀).toFun
                      (smoothOrthoFrame (I := I) g₀ x i) x v))) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            exact covDeriv_doubleInsert_leibniz (I := I) g₀ p (fun y : M => w y) w.contMDiff x i v
        _ = (∑ i : Fin (Module.finrank ℝ E),
              Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) p x
                (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (p + 1) x
                  ((Tensor0SNabla.tensor0SCovariantDerivative I M (p + 2)
                    (LeviCivita (I := I) g₀)).toFun (fun y : M => w y) x v)
                  (smoothOrthoFrame (I := I) g₀ x i x))
                (smoothOrthoFrame (I := I) g₀ x i x)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, add_assoc,
              orthoFrame_corrections_sum_eq_zero (I := I) g₀ p x v (w x), add_zero]
        _ = (show Tensor0SBundle.Tensor0SSpace (p + 2) I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace p I x from
              (cometricDoubleTraceField (I := I) g₀ p).toSection x)
              ((Tensor0SNabla.tensor0SCovariantDerivative I M (p + 2)
                (LeviCivita (I := I) g₀)).toFun (fun y : M => w y) x v) :=
            (cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g₀ p x
              (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
              ((Tensor0SNabla.tensor0SCovariantDerivative I M (p + 2)
                (LeviCivita (I := I) g₀)).toFun (fun y : M => w y) x v)).symm
    exact hfinal
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [Integral.L2.SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply,
    Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval
      (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p) x D m,
    hdir x (m 0), ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply]

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
