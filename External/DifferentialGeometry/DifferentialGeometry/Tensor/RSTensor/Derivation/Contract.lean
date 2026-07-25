


import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Curry
import DifferentialGeometry.Tensor.Multilinear.Tensor
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import DifferentialGeometry.Tensor.Auxiliary.PredualBasis
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.Trace


namespace Tensor0SBundle
noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

noncomputable def model_interior_product (s : ℕ) (v : E) :
    Tensor0SModel (s + 1) 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E :=
  (ContinuousLinearMap.apply 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) v).comp
    (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def model_interior_bilinear (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] (s : ℕ) :
    E →L[𝕜] (Tensor0SModel (s + 1) 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E) :=
  ContinuousLinearMap.flip
    (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

theorem model_interior_bilinear_apply (s : ℕ) (v : E) (T : Tensor0SModel (s + 1) 𝕜 E) :
    model_interior_bilinear 𝕜 E s v T = model_interior_product s v T := rfl

noncomputable def interior_product (s : ℕ) (x : M)
    (v : TangentSpace I x) :
    Tensor0SSpace (s + 1) I x →L[𝕜] Tensor0SSpace s I x :=
  (tensor0SSpace_continuousLinearEquiv (I := I) s x).symm.toContinuousLinearMap.comp
    ((model_interior_product s (v : E)).comp
      (tensor0SSpace_continuousLinearEquiv (I := I) (s + 1) x).toContinuousLinearMap)

noncomputable def model_tensorWithCovector (r : ℕ) (α : Tensor0SModel 1 𝕜 E) :
    Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (r + 1) 𝕜 E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun β => Bundle.continuousMultilinearMap.modelProduct r 1 β α
      map_add' := fun β₁ β₂ => by
        ext v
        simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousMultilinearMap.add_apply, add_mul]
      map_smul' := fun c β => by
        ext v
        simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousMultilinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

noncomputable def model_tensorWithCovector_first (r : ℕ) (α : Tensor0SModel 1 𝕜 E) :
    Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (1 + r) 𝕜 E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun β => Bundle.continuousMultilinearMap.modelProduct 1 r α β
      map_add' := fun β₁ β₂ => by
        ext v
        simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousMultilinearMap.add_apply, mul_add]
      map_smul' := fun c β => by
        ext v
        simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousMultilinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

noncomputable def model_tensorWithCovector_first_bilinear (r : ℕ) :
    Tensor0SModel 1 𝕜 E →L[𝕜]
      (Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (1 + r) 𝕜 E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α =>
        LinearMap.toContinuousLinearMap
          { toFun := fun β => Bundle.continuousMultilinearMap.modelProduct 1 r α β
            map_add' := fun β₁ β₂ => by
              ext v
              simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
                ContinuousMultilinearMap.add_apply, mul_add]
            map_smul' := fun c β => by
              ext v
              simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
                ContinuousMultilinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
              ring }
      map_add' := fun α₁ α₂ => by
        ext β v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply, add_mul]
      map_smul' := fun c α => by
        ext β v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply,
          smul_eq_mul, RingHom.id_apply]
        ring }

theorem model_tensorWithCovector_first_bilinear_apply (r : ℕ)
    (α : Tensor0SModel 1 𝕜 E) (β : Tensor0SModel r 𝕜 E) :
    model_tensorWithCovector_first_bilinear (𝕜 := 𝕜) (E := E) r α β =
      model_tensorWithCovector_first r α β := rfl

noncomputable def model_contract_covariant_bilinear (r s : ℕ) :
    E →L[𝕜] (TensorRSModel r (s + 1) 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E) :=
  (ContinuousLinearMap.compL 𝕜
      (Tensor0SModel r 𝕜 E)
      (Tensor0SModel (s + 1) 𝕜 E)
      (Tensor0SModel s 𝕜 E)).comp
    (model_interior_bilinear 𝕜 E s)

theorem model_contract_covariant_bilinear_apply (r s : ℕ) (v : E)
    (T : TensorRSModel r (s + 1) 𝕜 E) :
    model_contract_covariant_bilinear (𝕜 := 𝕜) (E := E) r s v T =
      (model_interior_product s v).comp T := rfl

noncomputable def model_contract_contravariant_first_bilinear (r s : ℕ) :
    Tensor0SModel 1 𝕜 E →L[𝕜]
      (TensorRSModel (1 + r) s 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E) :=
  (ContinuousLinearMap.compL 𝕜
        (Tensor0SModel r 𝕜 E) (Tensor0SModel (1 + r) 𝕜 E) (Tensor0SModel s 𝕜 E)).flip.comp
    (model_tensorWithCovector_first_bilinear (𝕜 := 𝕜) (E := E) r)

theorem model_contract_contravariant_first_bilinear_apply (r s : ℕ)
    (α : Tensor0SModel 1 𝕜 E) (T : TensorRSModel (1 + r) s 𝕜 E) :
    model_contract_contravariant_first_bilinear (𝕜 := 𝕜) (E := E) r s α T =
      T.comp (model_tensorWithCovector_first r α) := rfl

section FieldContraction

variable (n : WithTop ℕ∞ := ⊤) [IsManifold I ω M]

noncomputable def contract_Tensor0SField_fun (s : ℕ)
    (α : (x : M) → Tensor0SSpace (s + 1) I x)
    (X : (x : M) → TangentSpace I x) :
    (x : M) → Tensor0SSpace s I x :=
  fun x => interior_product s x (X x) (α x)

noncomputable def contract_Tensor0SField (s : ℕ)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) (s + 1))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _)) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (s + 1)
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  refine ⟨contract_Tensor0SField_fun s (fun x => α x) (fun x => X x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hα := α.contMDiff x₀
  rw [contMDiffAt_section] at hα
  have hX := X.contMDiff x₀
  rw [contMDiffAt_section] at hX

  have h_combine :
      ContMDiffAt I 𝓘(𝕜, Tensor0SModel s 𝕜 E) n
        (fun x => model_interior_bilinear 𝕜 E s
          ((trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2)
          ((trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
            (fun x => Tensor0SSpace (s + 1) I x) x₀ ⟨x, α x⟩).2)) x₀ :=
    ((contMDiffAt_const (c := model_interior_bilinear 𝕜 E s)).clm_apply hX).clm_apply hα
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx

  ext v

  set symmL := (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x with hsymmL
  set gtilde : E := (trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2 with hgtilde
  change (α x) (@Fin.cons s (fun _ => E) (X x : E) (fun i => symmL (v i))) =
    (α x) (fun i => symmL (@Fin.cons s (fun _ => E) gtilde v i))
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · change (X x : E) = symmL gtilde
    have h := (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hx (X x)
    have hcl : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (X x) = gtilde := by
      change (trivializationAt E (TangentSpace I) x₀).linearMapAt 𝕜 x (X x) = _
      rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rw [hcl] at h
    exact h.symm
  · intro j
    rfl

noncomputable def contract_covariant (r s : ℕ) (x : M)
    (v : TangentSpace I x) :
    TensorRSSpace r (s + 1) I x →L[𝕜] TensorRSSpace r s I x :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.compL 𝕜
        (Tensor0SModel r 𝕜 E)
        (Tensor0SModel (s + 1) 𝕜 E)
        (Tensor0SModel s 𝕜 E)
        (model_interior_product s (v : E))).comp
      (tensorRSSpace_continuousLinearEquiv (I := I) r (s + 1) x).toContinuousLinearMap)

noncomputable def contract_contravariant (r s : ℕ) (x : M)
    (α : Tensor0SSpace 1 I x) :
    TensorRSSpace (r + 1) s I x →L[𝕜] TensorRSSpace r s I x :=
  let α_model : Tensor0SModel 1 𝕜 E := Tensor0SSpace.toModel α
  let embed_model : Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (r + 1) 𝕜 E :=
    model_tensorWithCovector r α_model
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.compL 𝕜
        (Tensor0SModel r 𝕜 E)
        (Tensor0SModel (r + 1) 𝕜 E)
        (Tensor0SModel s 𝕜 E)).flip embed_model).comp
      (tensorRSSpace_continuousLinearEquiv (I := I) (r + 1) s x).toContinuousLinearMap)

noncomputable def model_covectorOfCLM :
    (E →L[𝕜] 𝕜) →L[𝕜] Tensor0SModel 1 𝕜 E :=
  (continuousMultilinearCurryFin1 𝕜 E 𝕜).symm.toContinuousLinearMap

@[simp]
theorem model_covectorOfCLM_apply (α : E →L[𝕜] 𝕜) (v : Fin 1 → E) :
    model_covectorOfCLM (𝕜 := 𝕜) (E := E) α v = α (v 0) := by
  change ((continuousMultilinearCurryFin1 𝕜 E 𝕜).symm α) v = α (v 0)
  rfl

noncomputable def model_contract_trace (r s : ℕ) :
    TensorRSModel (1 + r) (s + 1) 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E :=
  let d := Module.finrank 𝕜 E
  let B : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 (E →L[𝕜] 𝕜) := B.cDualBasis
  ∑ i : Fin d,
    (model_contract_covariant_bilinear (𝕜 := 𝕜) (E := E) r s (B i)).comp
      (model_contract_contravariant_first_bilinear
        (𝕜 := 𝕜) (E := E) r (s + 1)
        (model_covectorOfCLM (𝕜 := 𝕜) (E := E) (b i)))

theorem model_contract_trace_apply (r s : ℕ)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E) :
    model_contract_trace (𝕜 := 𝕜) (E := E) r s T =
      ∑ i : Fin (Module.finrank 𝕜 E),
        (model_contract_covariant_bilinear
          (𝕜 := 𝕜) (E := E) r s
          ((Module.finBasis 𝕜 E) i))
          ((model_contract_contravariant_first_bilinear
            (𝕜 := 𝕜) (E := E) r (s + 1)
            (model_covectorOfCLM (𝕜 := 𝕜) (E := E)
              ((Module.finBasis 𝕜 E).cDualBasis i))) T) := by
  simp [model_contract_trace]

noncomputable def contract_trace (r s : ℕ) (x : M) :
    TensorRSSpace (1 + r) (s + 1) I x →L[𝕜] TensorRSSpace r s I x :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap.comp
    ((model_contract_trace (𝕜 := 𝕜) (E := E) r s).comp
      (tensorRSSpace_continuousLinearEquiv (I := I) (1 + r) (s + 1) x).toContinuousLinearMap)

omit [IsManifold I ω M] in
theorem contract_trace_apply (r s : ℕ) (x : M)
    (T : TensorRSSpace (1 + r) (s + 1) I x) :
    contract_trace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x T =
      (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm
        (model_contract_trace (𝕜 := 𝕜) (E := E) r s
          (tensorRSSpace_continuousLinearEquiv (I := I) (1 + r) (s + 1) x T)) := by
  rfl

private theorem trace_bilinear_change_frame_coord
    (L K : E →L[𝕜] E) (hKL : ∀ z, K (L z) = z)
    (F : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜) :
    (∑ i : Fin (Module.finrank 𝕜 E),
        F ((LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord i)).comp L)
          (K ((Module.finBasis 𝕜 E) i))) =
      ∑ i : Fin (Module.finrank 𝕜 E),
        F (LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord i))
          ((Module.finBasis 𝕜 E) i) := by
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  change (∑ i : Fin d, F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)
      (K (b i))) =
    ∑ i : Fin d, F (LinearMap.toContinuousLinearMap (b.coord i)) (b i)
  have h_cov : ∀ j : Fin d,
      (∑ i : Fin d, (b.coord j (K (b i))) •
          ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) =
        LinearMap.toContinuousLinearMap (b.coord j) := by
    intro j
    ext z
    calc
      (∑ i : Fin d, (b.coord j (K (b i))) •
          ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) z
          = ∑ i : Fin d, b.coord j (K (b i)) * b.coord i (L z) := by
              simp [smul_eq_mul]
      _ = b.coord j (∑ i : Fin d, b.coord i (L z) • K (b i)) := by
              symm
              rw [map_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_smul]
              simp [smul_eq_mul, mul_comm]
      _ = b.coord j (K (∑ i : Fin d, b.coord i (L z) • b i)) := by
              congr 1
              symm
              rw [map_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_smul]
      _ = b.coord j (K (L z)) := by
              rw [show (∑ i : Fin d, b.coord i (L z) • b i) = L z from b.sum_repr (L z)]
      _ = b.coord j z := by rw [hKL z]
      _ = (LinearMap.toContinuousLinearMap (b.coord j)) z := rfl
  calc
    (∑ i : Fin d, F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (K (b i)))
        = ∑ i : Fin d, ∑ j : Fin d,
            (b.coord j (K (b i))) •
              F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (b j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (K (b i))
                = F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)
                    (∑ j : Fin d, b.coord j (K (b i)) • b j) := by
                  rw [show (∑ j : Fin d, b.coord j (K (b i)) • b j) = K (b i) from
                    b.sum_repr (K (b i))]
            _ = ∑ j : Fin d, (b.coord j (K (b i))) •
                    F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (b j) := by
                  rw [map_sum]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [map_smul]
    _ = ∑ j : Fin d, ∑ i : Fin d,
            (b.coord j (K (b i))) •
              F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (b j) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin d, F
            (∑ i : Fin d, (b.coord j (K (b i))) •
              ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_sum]
          simp [map_smul]
    _ = ∑ j : Fin d, F (LinearMap.toContinuousLinearMap (b.coord j)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h_cov j]

private theorem trace_bilinear_change_frame_cdual
    (L K : E →L[𝕜] E) (hKL : ∀ z, K (L z) = z)
    (F : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜) :
    (∑ i : Fin (Module.finrank 𝕜 E),
        F (((Module.finBasis 𝕜 E).cDualBasis i).comp L)
          (K ((Module.finBasis 𝕜 E) i))) =
      ∑ i : Fin (Module.finrank 𝕜 E),
        F ((Module.finBasis 𝕜 E).cDualBasis i)
          ((Module.finBasis 𝕜 E) i) := by
  simpa [Module.Basis.cDualBasis, Module.Basis.coe_dualBasis]
    using trace_bilinear_change_frame_coord (𝕜 := 𝕜) (E := E) L K hKL F

private noncomputable def model_trace_pairing_first (r s : ℕ)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E)
    (β : Tensor0SModel r 𝕜 E) (tail : Fin s → E) :
    (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜 :=
  let covToTensor : (E →L[𝕜] 𝕜) →L[𝕜] Tensor0SModel (1 + r) 𝕜 E :=
    ((ContinuousLinearMap.apply 𝕜 (Tensor0SModel (1 + r) 𝕜 E) β).comp
      ((model_tensorWithCovector_first_bilinear (𝕜 := 𝕜) (E := E) r).comp
        (model_covectorOfCLM (𝕜 := 𝕜) (E := E))))
  let covToOutput : (E →L[𝕜] 𝕜) →L[𝕜] Tensor0SModel (s + 1) 𝕜 E :=
    T.comp covToTensor
  let evalTail : Tensor0SModel s 𝕜 E →L[𝕜] 𝕜 :=
    ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin s => E) 𝕜 tail
  let curry :
      Tensor0SModel (s + 1) 𝕜 E →L[𝕜] E →L[𝕜] Tensor0SModel s 𝕜 E :=
    (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap
  let outputToPair : Tensor0SModel (s + 1) 𝕜 E →L[𝕜] E →L[𝕜] 𝕜 :=
    ((ContinuousLinearMap.compL 𝕜 E (Tensor0SModel s 𝕜 E) 𝕜) evalTail).comp curry
  outputToPair.comp covToOutput

private theorem model_trace_pairing_first_apply (r s : ℕ)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E)
    (β : Tensor0SModel r 𝕜 E) (tail : Fin s → E)
    (α : E →L[𝕜] 𝕜) (X : E) :
    model_trace_pairing_first (𝕜 := 𝕜) (E := E) r s T β tail α X =
      (model_interior_product s X
        (T (model_tensorWithCovector_first r
          (model_covectorOfCLM (𝕜 := 𝕜) (E := E) α) β))) tail := by
  simp [model_trace_pairing_first, model_tensorWithCovector_first_bilinear_apply,
    model_interior_product]

private theorem trace_bilinear_basis_coord
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx 𝕜 E)
    (F : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜) :
    (∑ i : Idx,
        F (LinearMap.toContinuousLinearMap (basis.coord i)) (basis i)) =
      ∑ j : Fin (Module.finrank 𝕜 E),
        F (LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord j))
          ((Module.finBasis 𝕜 E) j) := by
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  change (∑ i : Idx,
      F (LinearMap.toContinuousLinearMap (basis.coord i)) (basis i)) =
    ∑ j : Fin d, F (LinearMap.toContinuousLinearMap (b.coord j)) (b j)
  have h_cov : ∀ j : Fin d,
      (∑ i : Idx, (b.coord j (basis i)) •
          LinearMap.toContinuousLinearMap (basis.coord i)) =
        LinearMap.toContinuousLinearMap (b.coord j) := by
    intro j
    ext z
    calc
      (∑ i : Idx, (b.coord j (basis i)) •
          LinearMap.toContinuousLinearMap (basis.coord i)) z
          = ∑ i : Idx, b.coord j (basis i) * basis.coord i z := by
              simp [smul_eq_mul]
      _ = b.coord j (∑ i : Idx, basis.coord i z • basis i) := by
              symm
              rw [map_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_smul]
              simp [smul_eq_mul, mul_comm]
      _ = b.coord j z := by
              rw [show (∑ i : Idx, basis.coord i z • basis i) = z from basis.sum_repr z]
      _ = (LinearMap.toContinuousLinearMap (b.coord j)) z := rfl
  calc
    (∑ i : Idx, F (LinearMap.toContinuousLinearMap (basis.coord i)) (basis i))
        = ∑ i : Idx, ∑ j : Fin d,
            (b.coord j (basis i)) •
              F (LinearMap.toContinuousLinearMap (basis.coord i)) (b j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            F (LinearMap.toContinuousLinearMap (basis.coord i)) (basis i)
                = F (LinearMap.toContinuousLinearMap (basis.coord i))
                    (∑ j : Fin d, b.coord j (basis i) • b j) := by
                  rw [show (∑ j : Fin d, b.coord j (basis i) • b j) = basis i from
                    b.sum_repr (basis i)]
            _ = ∑ j : Fin d, (b.coord j (basis i)) •
                    F (LinearMap.toContinuousLinearMap (basis.coord i)) (b j) := by
                  rw [map_sum]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [map_smul]
    _ = ∑ j : Fin d, ∑ i : Idx,
            (b.coord j (basis i)) •
              F (LinearMap.toContinuousLinearMap (basis.coord i)) (b j) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin d, F
            (∑ i : Idx, (b.coord j (basis i)) •
              LinearMap.toContinuousLinearMap (basis.coord i)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_sum]
          simp [map_smul]
    _ = ∑ j : Fin d, F (LinearMap.toContinuousLinearMap (b.coord j)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h_cov j]


theorem model_contract_trace_apply_basis
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx 𝕜 E) (r s : ℕ)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E)
    (β : Tensor0SModel r 𝕜 E) (tail : Fin s → E) :
    (model_contract_trace (𝕜 := 𝕜) (E := E) r s T β) tail =
      ∑ i : Idx,
        (model_interior_product s (basis i)
          (T (model_tensorWithCovector_first r
            (model_covectorOfCLM (𝕜 := 𝕜) (E := E)
              (LinearMap.toContinuousLinearMap (basis.coord i))) β))) tail := by
  rw [model_contract_trace_apply]
  rw [ContinuousLinearMap.sum_apply]
  rw [ContinuousMultilinearMap.sum_apply]
  symm
  calc
    (∑ i : Idx,
        (model_interior_product s (basis i)
          (T (model_tensorWithCovector_first r
            (model_covectorOfCLM (𝕜 := 𝕜) (E := E)
              (LinearMap.toContinuousLinearMap (basis.coord i))) β))) tail)
        = ∑ i : Idx,
            model_trace_pairing_first (𝕜 := 𝕜) (E := E) r s T β tail
              (LinearMap.toContinuousLinearMap (basis.coord i)) (basis i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [model_trace_pairing_first_apply]
    _ = ∑ j : Fin (Module.finrank 𝕜 E),
          model_trace_pairing_first (𝕜 := 𝕜) (E := E) r s T β tail
            (LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord j))
            ((Module.finBasis 𝕜 E) j) := by
          exact trace_bilinear_basis_coord (𝕜 := 𝕜) (E := E) basis
            (model_trace_pairing_first (𝕜 := 𝕜) (E := E) r s T β tail)
    _ = ∑ j : Fin (Module.finrank 𝕜 E),
          (model_contract_covariant_bilinear
            (𝕜 := 𝕜) (E := E) r s
            ((Module.finBasis 𝕜 E) j))
            ((model_contract_contravariant_first_bilinear
              (𝕜 := 𝕜) (E := E) r (s + 1)
              (model_covectorOfCLM (𝕜 := 𝕜) (E := E)
                ((Module.finBasis 𝕜 E).cDualBasis j))) T) β tail := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [model_trace_pairing_first_apply,
            model_contract_covariant_bilinear_apply,
            model_contract_contravariant_first_bilinear_apply]
          simp [Module.Basis.cDualBasis, Module.Basis.coe_dualBasis]

noncomputable def model_covariantChange (k : ℕ) (L : E →L[𝕜] E) :
    Tensor0SModel k 𝕜 E →L[𝕜] Tensor0SModel k 𝕜 E :=
  ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k => L)

omit [CompleteSpace 𝕜] in
@[simp]
theorem model_covariantChange_apply (k : ℕ) (L : E →L[𝕜] E)
    (T : Tensor0SModel k 𝕜 E) (v : Fin k → E) :
    model_covariantChange (𝕜 := 𝕜) (E := E) k L T v =
      T (fun i => L (v i)) := by
  rfl

omit [CompleteSpace 𝕜] in
private theorem model_interior_product_covariantChange_apply (s : ℕ)
    (L : E →L[𝕜] E) (X : E) (U : Tensor0SModel (s + 1) 𝕜 E)
    (v : Fin s → E) :
    (model_interior_product s X
      (model_covariantChange (𝕜 := 𝕜) (E := E) (s + 1) L U)) v =
    (model_interior_product s (L X) U) (fun i => L (v i)) := by
  change (model_covariantChange (𝕜 := 𝕜) (E := E) (s + 1) L U)
      (Fin.cons X v) =
    U (Fin.cons (L X) (fun i => L (v i)))
  rw [model_covariantChange_apply]
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

private theorem model_covariantChange_tensorWithCovector_first (r : ℕ)
    (L : E →L[𝕜] E) (α : E →L[𝕜] 𝕜) (β : Tensor0SModel r 𝕜 E) :
    model_covariantChange (𝕜 := 𝕜) (E := E) (1 + r) L
      (model_tensorWithCovector_first r (model_covectorOfCLM (𝕜 := 𝕜) (E := E) α) β) =
    model_tensorWithCovector_first r
      (model_covectorOfCLM (𝕜 := 𝕜) (E := E) (α.comp L))
      (model_covariantChange (𝕜 := 𝕜) (E := E) r L β) := by
  refine ContinuousMultilinearMap.ext fun w => ?_
  change (Bundle.continuousMultilinearMap.modelProduct 1 r
      (model_covectorOfCLM (𝕜 := 𝕜) (E := E) α) β)
      (fun i => L (w i)) =
    (Bundle.continuousMultilinearMap.modelProduct 1 r
      (model_covectorOfCLM (𝕜 := 𝕜) (E := E) (α.comp L))
      (model_covariantChange (𝕜 := 𝕜) (E := E) r L β)) w
  rw [Bundle.continuousMultilinearMap.modelProduct_apply,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1


theorem model_contract_trace_naturality
    (r s : ℕ) (L Linv : E →L[𝕜] E)
    (hL : L.comp Linv = ContinuousLinearMap.id 𝕜 E)
    (_hR : Linv.comp L = ContinuousLinearMap.id 𝕜 E)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E) :
    model_contract_trace (𝕜 := 𝕜) (E := E) r s
      ((model_covariantChange (𝕜 := 𝕜) (E := E) (s + 1) L).comp
        (T.comp (model_covariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv))) =
    (model_covariantChange (𝕜 := 𝕜) (E := E) s L).comp
      ((model_contract_trace (𝕜 := 𝕜) (E := E) r s T).comp
        (model_covariantChange (𝕜 := 𝕜) (E := E) r Linv)) := by
  ext β v
  let β' : Tensor0SModel r 𝕜 E :=
    model_covariantChange (𝕜 := 𝕜) (E := E) r Linv β
  let tail : Fin s → E := fun i => L (v i)
  let F : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜 :=
    model_trace_pairing_first (𝕜 := 𝕜) (E := E) r s T β' tail
  have hKL : ∀ z : E, L (Linv z) = z := by
    intro z
    have h := congrArg (fun f : E →L[𝕜] E => f z) hL
    simpa [ContinuousLinearMap.comp_apply] using h
  calc
    ((model_contract_trace (𝕜 := 𝕜) (E := E) r s
        ((model_covariantChange (𝕜 := 𝕜) (E := E) (s + 1) L).comp
          (T.comp (model_covariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv)))) β) v
        =
      ∑ i : Fin (Module.finrank 𝕜 E),
        F (((Module.finBasis 𝕜 E).cDualBasis i).comp Linv)
          (L ((Module.finBasis 𝕜 E) i)) := by
          rw [model_contract_trace_apply]
          rw [ContinuousLinearMap.sum_apply]
          rw [ContinuousMultilinearMap.sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [model_contract_covariant_bilinear_apply,
            model_contract_contravariant_first_bilinear_apply]
          change (model_interior_product s ((Module.finBasis 𝕜 E) i)
              ((model_covariantChange (𝕜 := 𝕜) (E := E) (s + 1) L)
                (T ((model_covariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv)
                  (model_tensorWithCovector_first r
                    (model_covectorOfCLM (𝕜 := 𝕜) (E := E)
                      ((Module.finBasis 𝕜 E).cDualBasis i)) β))))) v =
            F (((Module.finBasis 𝕜 E).cDualBasis i).comp Linv)
              (L ((Module.finBasis 𝕜 E) i))
          rw [model_interior_product_covariantChange_apply]
          rw [model_covariantChange_tensorWithCovector_first]
          rw [model_trace_pairing_first_apply]
    _ = ∑ i : Fin (Module.finrank 𝕜 E),
        F ((Module.finBasis 𝕜 E).cDualBasis i)
          ((Module.finBasis 𝕜 E) i) := by
          exact trace_bilinear_change_frame_cdual (𝕜 := 𝕜) (E := E)
            (L := Linv) (K := L) hKL F
    _ =
      (((model_covariantChange (𝕜 := 𝕜) (E := E) s L).comp
        ((model_contract_trace (𝕜 := 𝕜) (E := E) r s T).comp
          (model_covariantChange (𝕜 := 𝕜) (E := E) r Linv))) β) v := by
          change ∑ i : Fin (Module.finrank 𝕜 E),
              F ((Module.finBasis 𝕜 E).cDualBasis i)
                ((Module.finBasis 𝕜 E) i) =
            (model_covariantChange (𝕜 := 𝕜) (E := E) s L
              ((model_contract_trace (𝕜 := 𝕜) (E := E) r s T) β')) v
          rw [model_covariantChange_apply]
          rw [model_contract_trace_apply]
          rw [ContinuousLinearMap.sum_apply]
          rw [ContinuousMultilinearMap.sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [model_trace_pairing_first_apply,
            model_contract_covariant_bilinear_apply,
            model_contract_contravariant_first_bilinear_apply]
          rfl


omit [IsManifold I ω M] in
theorem contract_trace_trivialization_eq
    {r s : ℕ} {x₀ x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace (1 + r) (s + 1) I x) :
    (trivializationAt (TensorRSModel r s 𝕜 E)
      (TensorRSSpace r s I) x₀
      ⟨x, contract_trace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x T⟩).2 =
    model_contract_trace (𝕜 := 𝕜) (E := E) r s
      ((trivializationAt (TensorRSModel (1 + r) (s + 1) 𝕜 E)
        (TensorRSSpace (1 + r) (s + 1) I) x₀
        ⟨x, T⟩).2) := by
  let L : E →L[𝕜] E := (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x
  let Linv : E →L[𝕜] E :=
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x
  let Tx : TensorRSModel (1 + r) (s + 1) 𝕜 E :=
    tensorRSSpace_continuousLinearEquiv (I := I) (1 + r) (s + 1) x T
  have hL : L.comp Linv = ContinuousLinearMap.id 𝕜 E := by
    ext z
    exact (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hx z
  have hR : Linv.comp L = ContinuousLinearMap.id 𝕜 E := by
    ext z
    exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL
      (R := 𝕜) hx z
  have h_cLMAt : ∀ (k : ℕ) (U : Tensor0SSpace k I x) (v : Fin k → E),
      (trivializationAt (Tensor0SModel k 𝕜 E)
        (Tensor0SSpace k I) x₀).continuousLinearMapAt 𝕜 x U v =
      U (fun i => L (v i)) := by
    intro k U v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel k 𝕜 E)
        (Tensor0SSpace k I) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel k 𝕜 E)
          (Tensor0SSpace k I) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl
  have h_symmL : ∀ (k : ℕ) (U : Tensor0SModel k 𝕜 E) (u : Fin k → E),
      ((trivializationAt (Tensor0SModel k 𝕜 E)
        (Tensor0SSpace k I) x₀).symmL 𝕜 x U) u =
        U (fun i => Linv (u i)) := by
    intro k U u
    have h_inv : ∀ z : E, L (Linv z) = z := by
      intro z
      have h := congrArg (fun f : E →L[𝕜] E => f z) hL
      simpa [ContinuousLinearMap.comp_apply] using h
    have hu : u = fun i => L (Linv (u i)) := by
      funext i
      exact (h_inv (u i)).symm
    calc
      ((trivializationAt (Tensor0SModel k 𝕜 E)
        (Tensor0SSpace k I) x₀).symmL 𝕜 x U) u
          = ((trivializationAt (Tensor0SModel k 𝕜 E)
              (Tensor0SSpace k I) x₀).symmL 𝕜 x U)
              (fun i => L (Linv (u i))) := by rw [← hu]
      _ = (trivializationAt (Tensor0SModel k 𝕜 E)
            (Tensor0SSpace k I) x₀).continuousLinearMapAt 𝕜 x
            ((trivializationAt (Tensor0SModel k 𝕜 E)
              (Tensor0SSpace k I) x₀).symmL 𝕜 x U)
            (fun i => Linv (u i)) := (h_cLMAt k _ _).symm
      _ = U (fun i => Linv (u i)) := by
            rw [(trivializationAt (Tensor0SModel k 𝕜 E)
              (Tensor0SSpace k I) x₀).continuousLinearMapAt_symmL
              (R := 𝕜) hx]
  have h_input :
      ((trivializationAt (TensorRSModel (1 + r) (s + 1) 𝕜 E)
        (TensorRSSpace (1 + r) (s + 1) I) x₀
        ⟨x, T⟩).2) =
      (model_covariantChange (𝕜 := 𝕜) (E := E) (s + 1) L).comp
        (Tx.comp (model_covariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
        (Tensor0SSpace (s + 1) I) x₀).continuousLinearMapAt 𝕜 x
        (T ((trivializationAt (Tensor0SModel (1 + r) 𝕜 E)
          (Tensor0SSpace (1 + r) I) x₀).symmL 𝕜 x β)) v =
      ((model_covariantChange (𝕜 := 𝕜) (E := E) (s + 1) L)
        (Tx ((model_covariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv) β))) v
    rw [h_cLMAt]
    rw [model_covariantChange_apply]
    have hβ :
        (trivializationAt (Tensor0SModel (1 + r) 𝕜 E)
          (Tensor0SSpace (1 + r) I) x₀).symmL 𝕜 x β =
          (model_covariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      rw [h_symmL]
      rfl
    rw [hβ]
    rfl
  have h_output :
      (trivializationAt (TensorRSModel r s 𝕜 E)
        (TensorRSSpace r s I) x₀
        ⟨x, contract_trace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x T⟩).2 =
      (model_covariantChange (𝕜 := 𝕜) (E := E) s L).comp
        ((model_contract_trace (𝕜 := 𝕜) (E := E) r s Tx).comp
          (model_covariantChange (𝕜 := 𝕜) (E := E) r Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SModel s 𝕜 E)
        (Tensor0SSpace s I) x₀).continuousLinearMapAt 𝕜 x
        ((contract_trace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x T)
          ((trivializationAt (Tensor0SModel r 𝕜 E)
            (Tensor0SSpace r I) x₀).symmL 𝕜 x β)) v =
      ((model_covariantChange (𝕜 := 𝕜) (E := E) s L)
        ((model_contract_trace (𝕜 := 𝕜) (E := E) r s Tx)
          ((model_covariantChange (𝕜 := 𝕜) (E := E) r Linv) β))) v
    rw [h_cLMAt]
    rw [model_covariantChange_apply]
    rw [contract_trace_apply]
    have hβ :
        (trivializationAt (Tensor0SModel r 𝕜 E)
          (Tensor0SSpace r I) x₀).symmL 𝕜 x β =
          (model_covariantChange (𝕜 := 𝕜) (E := E) r Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      rw [h_symmL]
      rfl
    rw [hβ]
    rfl
  rw [h_input, h_output]
  exact (model_contract_trace_naturality (𝕜 := 𝕜) (E := E)
    r s L Linv hL hR Tx).symm

noncomputable def contract_covariantField_fun (r s : ℕ)
    (α : (x : M) → TensorRSSpace r (s + 1) I x)
    (X : (x : M) → TangentSpace I x) :
    (x : M) → TensorRSSpace r s I x :=
  fun x => contract_covariant r s x (X x) (α x)

set_option maxHeartbeats 800000 in

noncomputable def contract_covariantField (r s : ℕ)
    (α : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r (s + 1))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _)) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r (s + 1)
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (s + 1)
  refine ⟨contract_covariantField_fun r s (fun x => α x) (fun x => X x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hα := α.contMDiff x₀
  rw [contMDiffAt_section] at hα
  have hX := X.contMDiff x₀
  rw [contMDiffAt_section] at hX

  set biop :
      E →L[𝕜] (TensorRSModel r (s + 1) 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E) :=
    (ContinuousLinearMap.compL 𝕜
      (Tensor0SModel r 𝕜 E) (Tensor0SModel (s + 1) 𝕜 E) (Tensor0SModel s 𝕜 E)).comp
      (model_interior_bilinear 𝕜 E s) with hbiop
  have h_combine :
      ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) n
        (fun x => biop
          ((trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2)
          ((trivializationAt (TensorRSModel r (s + 1) 𝕜 E)
            (fun x => TensorRSSpace r (s + 1) I x) x₀ ⟨x, α x⟩).2)) x₀ :=
    ((contMDiffAt_const (c := biop)).clm_apply hX).clm_apply hα
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  refine ContinuousLinearMap.ext fun γ => ?_
  refine ContinuousMultilinearMap.ext fun w => ?_
  set sL := (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x with hsL
  set Xtilde : E := (trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2 with hXtilde
  set gtilde : Tensor0SSpace r I x :=
    (trivializationAt (Tensor0SModel r 𝕜 E) (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x γ
    with hgtilde

  have h_cLMAt_s : ∀ (T : Tensor0SSpace s I x) (v : Fin s → E),
      (trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).continuousLinearMapAt 𝕜 x T v =
      T (fun i => sL (v i)) := by
    intro T v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel s 𝕜 E)
          (fun x => Tensor0SSpace s I x) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl
  have h_cLMAt_s1 : ∀ (T : Tensor0SSpace (s + 1) I x) (v : Fin (s + 1) → E),
      (trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
        (fun x => Tensor0SSpace (s + 1) I x) x₀).continuousLinearMapAt 𝕜 x T v =
      T (fun i => sL (v i)) := by
    intro T v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
        (fun x => Tensor0SSpace (s + 1) I x) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
          (fun x => Tensor0SSpace (s + 1) I x) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl

  change (trivializationAt (Tensor0SModel s 𝕜 E)
      (fun x => Tensor0SSpace s I x) x₀).continuousLinearMapAt 𝕜 x
      (model_interior_product s (X x : E)
        ((show Tensor0SSpace r I x →L[𝕜] Tensor0SSpace (s + 1) I x from α x) gtilde)) w =
    (trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
      (fun x => Tensor0SSpace (s + 1) I x) x₀).continuousLinearMapAt 𝕜 x
      ((show Tensor0SSpace r I x →L[𝕜] Tensor0SSpace (s + 1) I x from α x) gtilde)
      (Fin.cons Xtilde w)
  rw [h_cLMAt_s, h_cLMAt_s1]

  change ((show Tensor0SSpace r I x →L[𝕜] Tensor0SSpace (s + 1) I x from α x) gtilde :
        Tensor0SModel (s + 1) 𝕜 E)
      (@Fin.cons s (fun _ => E) (X x : E) (fun i => sL (w i))) =
    ((show Tensor0SSpace r I x →L[𝕜] Tensor0SSpace (s + 1) I x from α x) gtilde)
      (fun i => sL (@Fin.cons s (fun _ => E) Xtilde w i))
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · change (X x : E) = sL Xtilde
    have h := (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hx (X x)
    have hcl : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (X x)
        = Xtilde := by
      change (trivializationAt E (TangentSpace I) x₀).linearMapAt 𝕜 x (X x) = _
      rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rw [hcl] at h
    exact h.symm
  · intro j
    rfl

noncomputable def contract_contravariantField_fun (r s : ℕ)
    (α : (x : M) → TensorRSSpace (r + 1) s I x)
    (φ : (x : M) → Tensor0SSpace 1 I x) :
    (x : M) → TensorRSSpace r s I x :=
  fun x => contract_contravariant r s x (φ x) (α x)

set_option maxHeartbeats 800000 in

noncomputable def contract_contravariantField (r s : ℕ)
    (α : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) (r + 1) s)
    (φ : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) 1) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (r + 1) s
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (r + 1)
  refine ⟨contract_contravariantField_fun r s (fun x => α x) (fun x => φ x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hα := α.contMDiff x₀
  rw [contMDiffAt_section] at hα
  have hφ := φ.contMDiff x₀
  rw [contMDiffAt_section] at hφ

  let mtwc_bilinear :
      Tensor0SModel 1 𝕜 E →L[𝕜] (Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (r + 1) 𝕜 E) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun a => model_tensorWithCovector r a
        map_add' := fun a₁ a₂ => by
          refine ContinuousLinearMap.ext fun β => ?_
          refine ContinuousMultilinearMap.ext fun w => ?_
          simp only [model_tensorWithCovector, LinearMap.coe_toContinuousLinearMap',
            LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.add_apply,
            Bundle.continuousMultilinearMap.modelProduct_apply,
            ContinuousMultilinearMap.add_apply, mul_add]
        map_smul' := fun c a => by
          refine ContinuousLinearMap.ext fun β => ?_
          refine ContinuousMultilinearMap.ext fun w => ?_
          simp only [model_tensorWithCovector, LinearMap.coe_toContinuousLinearMap',
            LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.smul_apply,
            Bundle.continuousMultilinearMap.modelProduct_apply,
            ContinuousMultilinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
          ring }

  set biop_ctr :
      Tensor0SModel 1 𝕜 E →L[𝕜] (TensorRSModel (r + 1) s 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E) :=
    (ContinuousLinearMap.compL 𝕜
      (Tensor0SModel r 𝕜 E) (Tensor0SModel (r + 1) 𝕜 E) (Tensor0SModel s 𝕜 E)).flip.comp
      mtwc_bilinear with hbiop
  have h_combine :
      ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) n
        (fun x => biop_ctr
          ((trivializationAt (Tensor0SModel 1 𝕜 E)
            (fun x => Tensor0SSpace 1 I x) x₀ ⟨x, φ x⟩).2)
          ((trivializationAt (TensorRSModel (r + 1) s 𝕜 E)
            (fun x => TensorRSSpace (r + 1) s I x) x₀ ⟨x, α x⟩).2)) x₀ :=
    ((contMDiffAt_const (c := biop_ctr)).clm_apply hφ).clm_apply hα
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  refine ContinuousLinearMap.ext fun β => ?_
  refine ContinuousMultilinearMap.ext fun v => ?_
  set sL := (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x with hsL

  have h_cLMAt_s : ∀ (T : Tensor0SSpace s I x) (u : Fin s → E),
      (trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).continuousLinearMapAt 𝕜 x T u =
      T (fun i => sL (u i)) := by
    intro T u
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel s 𝕜 E)
          (fun x => Tensor0SSpace s I x) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl
  have h_cLMAt_r : ∀ (T : Tensor0SSpace r I x) (u : Fin r → E),
      (trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).continuousLinearMapAt 𝕜 x T u =
      T (fun i => sL (u i)) := by
    intro T u
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl
  have h_cLMAt_r1 : ∀ (T : Tensor0SSpace (r + 1) I x) (u : Fin (r + 1) → E),
      (trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
        (fun x => Tensor0SSpace (r + 1) I x) x₀).continuousLinearMapAt 𝕜 x T u =
      T (fun i => sL (u i)) := by
    intro T u
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
        (fun x => Tensor0SSpace (r + 1) I x) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
          (fun x => Tensor0SSpace (r + 1) I x) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl
  have h_cLMAt_1 : ∀ (T : Tensor0SSpace 1 I x) (u : Fin 1 → E),
      (trivializationAt (Tensor0SModel 1 𝕜 E)
        (fun x => Tensor0SSpace 1 I x) x₀).continuousLinearMapAt 𝕜 x T u =
      T (fun i => sL (u i)) := by
    intro T u
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel 1 𝕜 E)
        (fun x => Tensor0SSpace 1 I x) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel 1 𝕜 E)
          (fun x => Tensor0SSpace 1 I x) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl

  set β_symm : Tensor0SSpace r I x :=
    (trivializationAt (Tensor0SModel r 𝕜 E) (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x β
    with hβ_symm
  set atilde_x : Tensor0SModel 1 𝕜 E :=
    (trivializationAt (Tensor0SModel 1 𝕜 E) (fun x => Tensor0SSpace 1 I x) x₀ ⟨x, φ x⟩).2
    with hatilde_x

  change (trivializationAt (Tensor0SModel s 𝕜 E)
      (fun x => Tensor0SSpace s I x) x₀).continuousLinearMapAt 𝕜 x
      ((show Tensor0SSpace (r + 1) I x →L[𝕜] Tensor0SSpace s I x from α x)
        (model_tensorWithCovector r (Tensor0SSpace.toModel (φ x)) β_symm)) v =
    (trivializationAt (Tensor0SModel s 𝕜 E)
      (fun x => Tensor0SSpace s I x) x₀).continuousLinearMapAt 𝕜 x
      ((show Tensor0SSpace (r + 1) I x →L[𝕜] Tensor0SSpace s I x from α x)
        ((trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
          (fun x => Tensor0SSpace (r + 1) I x) x₀).symmL 𝕜 x
          (model_tensorWithCovector r atilde_x β))) v
  rw [h_cLMAt_s, h_cLMAt_s]

  congr 1
  congr 1

  refine ContinuousMultilinearMap.ext fun w => ?_
  have hw : w = fun i => sL ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt
      𝕜 x (w i)) := by
    funext i
    exact ((trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hx (w i)).symm

  have hrhs :
      ((trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
          (fun x => Tensor0SSpace (r + 1) I x) x₀).symmL 𝕜 x
          ((model_tensorWithCovector r atilde_x) β)) w =
        ((model_tensorWithCovector r atilde_x) β)
          (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (w i)) := by
    calc ((trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
            (fun x => Tensor0SSpace (r + 1) I x) x₀).symmL 𝕜 x
            ((model_tensorWithCovector r atilde_x) β)) w
        = ((trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
              (fun x => Tensor0SSpace (r + 1) I x) x₀).symmL 𝕜 x
              ((model_tensorWithCovector r atilde_x) β))
            (fun i => sL ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt
              𝕜 x (w i))) := by rw [← hw]
      _ = (trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
            (fun x => Tensor0SSpace (r + 1) I x) x₀).continuousLinearMapAt 𝕜 x
            ((trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
              (fun x => Tensor0SSpace (r + 1) I x) x₀).symmL 𝕜 x
              ((model_tensorWithCovector r atilde_x) β))
            (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (w i)) :=
          (h_cLMAt_r1 _ _).symm
      _ = ((model_tensorWithCovector r atilde_x) β)
            (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (w i)) := by
          rw [(trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
            (fun x => Tensor0SSpace (r + 1) I x) x₀).continuousLinearMapAt_symmL (R := 𝕜) hx]
  refine Eq.trans ?_ hrhs.symm

  change (Bundle.continuousMultilinearMap.modelProduct r 1 β_symm
      (Tensor0SSpace.toModel (φ x))) w =
    Bundle.continuousMultilinearMap.modelProduct r 1 β atilde_x
      (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (w i))
  rw [Bundle.continuousMultilinearMap.modelProduct_apply,
    Bundle.continuousMultilinearMap.modelProduct_apply]

  congr 1
  · have hwc : (w ∘ Fin.castAdd 1) = fun i => sL
        ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x
          ((w ∘ Fin.castAdd 1) i)) := by
      funext i
      exact ((trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
        (R := 𝕜) hx ((w ∘ Fin.castAdd 1) i)).symm
    conv_lhs => rw [hwc]
    rw [← h_cLMAt_r]
    rw [(trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀).continuousLinearMapAt_symmL (R := 𝕜) hx]
    rfl
  · have h_atilde_eq :
        (trivializationAt (Tensor0SModel 1 𝕜 E) (fun x => Tensor0SSpace 1 I x) x₀).continuousLinearMapAt
          𝕜 x (Tensor0SSpace.toModel (φ x)) = atilde_x := by
      ext u'
      rw [h_cLMAt_1]
      rfl
    have hwn : (w ∘ Fin.natAdd r) = fun i => sL
        ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x
          ((w ∘ Fin.natAdd r) i)) := by
      funext i
      exact ((trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
        (R := 𝕜) hx ((w ∘ Fin.natAdd r) i)).symm
    conv_lhs => rw [hwn]
    rw [← h_cLMAt_1]
    rw [h_atilde_eq]
    rfl

noncomputable def contract_TensorRSField_fun (r s : ℕ)
    (T : (x : M) → TensorRSSpace (1 + r) (s + 1) I x) :
    (x : M) → TensorRSSpace r s I x :=
  fun x => contract_trace r s x (T x)

noncomputable def contract_TensorRSField (r s : ℕ)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n)
      (1 + r) (s + 1)) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (1 + r) (s + 1)
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  refine ⟨contract_TensorRSField_fun r s (fun x => T x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hT := T.contMDiff x₀
  rw [contMDiffAt_section] at hT
  have hTrace :
      ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) n
        (fun x => model_contract_trace (𝕜 := 𝕜) (E := E) r s
          ((trivializationAt (TensorRSModel (1 + r) (s + 1) 𝕜 E)
            (fun x => TensorRSSpace (1 + r) (s + 1) I x) x₀ ⟨x, T x⟩).2)) x₀ :=
    (model_contract_trace (𝕜 := 𝕜) (E := E) r s).contMDiffAt.comp x₀ hT
  refine hTrace.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  exact contract_trace_trivialization_eq
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (r := r) (s := s) (x₀ := x₀) (x := x) hx (T x)

end FieldContraction

end
end Tensor0SBundle
