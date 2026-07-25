import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Tensor0S
import DifferentialGeometry.Bundle.Frame
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.BumpFunction











namespace Tensor0SBundle

open Bundle Set TensorLieDeriv
open scoped Manifold ContDiff Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in






theorem totalNabla0S_eval_tangentConstInChart_contMDiffAt
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin (s + 1) -> Fin (Module.finrank Real E)) :
    ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov α p)
          (fun a : Fin (s + 1) =>
            tangentConstInChart (𝕜 := Real) (I := I) x₀
              ((Module.finBasis Real E) (slots a)) p)) x₀ := by
  classical
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let b : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    Module.finBasis Real E
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  let hframe := e.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Xext, hXext⟩ :=
    hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet hx₀
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Xext (slots 0)
  have hcoeff :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            s cov X α p)
            (fun a : Fin s =>
              tangentConstInChart (𝕜 := Real) (I := I) x₀
                (b (slots a.succ)) p)) x₀ := by
    simpa [b] using
      nabla0SFun_eval_tangentConstInChart_contMDiffAt
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s := s) cov hcov X α x₀ (fun a : Fin s => slots a.succ)
  refine hcoeff.congr_of_eventuallyEq ?_
  filter_upwards [hXext, e.open_baseSet.mem_nhds hx₀] with p hXeq hp
  have hX :
      X p =
        tangentConstInChart (𝕜 := Real) (I := I) x₀
          (b (slots 0)) p := by
    calc
      X p = e.localFrame b (slots 0) p := hXeq (slots 0)
      _ = e.symmL Real p (b (slots 0)) := by
        exact e.localFrame_apply_of_mem_baseSet (b := b) hp
      _ = tangentConstInChart (𝕜 := Real) (I := I) x₀
          (b (slots 0)) p := by
        rfl
  have hslots :
      (fun a : Fin (s + 1) =>
          tangentConstInChart (𝕜 := Real) (I := I) x₀
            (b (slots a)) p) =
        Fin.cons (X p)
          (fun a : Fin s =>
            tangentConstInChart (𝕜 := Real) (I := I) x₀
              (b (slots a.succ)) p) := by
    funext a
    cases a using Fin.cases with
    | zero =>
        simpa [Fin.cons_zero] using hX.symm
    | succ a =>
        simp [Fin.cons_succ]
  rw [hslots]
  exact totalNabla0SFun_apply_section
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    s cov X α p
    (fun a : Fin s =>
      tangentConstInChart (𝕜 := Real) (I := I) x₀
        (b (slots a.succ)) p)

set_option backward.isDefEq.respectTransparency false in


theorem totalNabla0S_reg (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    TotalNabla0SRegular (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov α := by
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) (s + 1)
  let F : (p : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (s + 1) p :=
    fun p : M =>
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov α p
  let d := Module.finrank Real E
  let b : Module.Basis (Fin d) Real E := Module.finBasis Real E
  have hsec :
      ContMDiff I (I.prod 𝓘(Real, Tensor0SModel (s + 1) Real E))
        (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, F p⟩ :
            TotalSpace (Tensor0SModel (s + 1) Real E)
              (fun p : M => Tensor0SSpace (s + 1) I p))) := by
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
      (∞ : WithTop ℕ∞) b F).mpr ?_
    intro σ x₀
    have hcoeff :=
      totalNabla0S_eval_tangentConstInChart_contMDiffAt
        (E := E) (H := H) (I := I) (M := M)
        (s := s) cov hcov α x₀ σ
    refine hcoeff.congr_of_eventuallyEq ?_
    let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
    have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
    filter_upwards [e.open_baseSet.mem_nhds hx₀] with p hp
    rw [continuousMultilinearMap_basis_repr]
    change ((trivializationAt (Tensor0SModel (s + 1) Real E)
        (Bundle.continuousMultilinearMap Real (s + 1) E
          (TangentSpace I : M -> Type _)) x₀
        ⟨p, F p⟩).2)
        (fun a : Fin (s + 1) => b (σ a)) =
      F p
        (fun a : Fin (s + 1) =>
          tangentConstInChart (𝕜 := Real) (I := I) x₀ (b (σ a)) p)
    change (F p).compContinuousLinearMap
        (fun _ : Fin (s + 1) =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real p)
        (fun a : Fin (s + 1) => b (σ a)) =
      F p
        (fun a : Fin (s + 1) =>
          tangentConstInChart (𝕜 := Real) (I := I) x₀ (b (σ a)) p)
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr
  exact hsec



noncomputable def CanonicalSpatialDerivs0S.of_smooth_connection {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    CanonicalSpatialDerivs0S (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) cov A := by
  let hreg1 := totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
    s cov hcov A
  let nablaA := totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) s cov A hreg1
  let hreg2 := totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
    (s + 1) cov hcov nablaA
  refine
    { nablaA := nablaA
      nabla2A := totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) (s + 1) cov nablaA hreg2
      first := ?_
      second := ?_ }
  · exact totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) s cov A hreg1
  · exact totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (s + 1) cov nablaA hreg2

end

end Tensor0SBundle
