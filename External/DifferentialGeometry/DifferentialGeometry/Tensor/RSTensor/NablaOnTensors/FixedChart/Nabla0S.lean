import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.FixedChart.Models




namespace TensorLieDeriv

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section SmoothVectorFieldRSNabla









variable [IsManifold I 1 M] [IsManifold I (n + 1) M]





noncomputable def fixedChartNabla0SModel (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (x₀ : M) [IsManifold I 2 M] (y : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) s
    (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I))
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
    (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s x₀ (fun x => α x))
    (range I) y



omit [IsManifold I n M] [IsManifold I (n + 1) M] in
theorem fixedChartNabla0SModel_apply_slots (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (x₀ : M) [IsManifold I 2 M] (y : E) (slots : Fin s → E) :
    fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (n := n) s cov X α x₀ y slots =
      fderivWithin 𝕜
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) s x₀ (fun x => α x))
        (range I) y
        (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I) y)
        slots -
      ∑ a : Fin s,
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) s x₀ (fun x => α x)) y
          (Function.update slots a
            ((connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov
              (fun x => X x) x₀ y) (slots a))) := by
  unfold fixedChartNabla0SModel
  rw [covariantDeriv_tensor0SModelWithin_apply_slots]




omit [IsManifold I n M] [IsManifold I (n + 1) M] in
theorem fixedChartNabla0SModel_apply_slots_of_mem (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (x₀ : M) [IsManifold I 2 M] {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (slots : Fin s → E) :
    fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (n := n) s cov X α x₀ y slots =
      fderivWithin 𝕜
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) s x₀ (fun x => α x))
        (range I) y
        (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I) y)
        slots -
      ∑ a : Fin s,
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) s x₀ (fun x => α x)) y
          (Function.update slots a
            ((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt
              𝕜 ((extChartAt I x₀).symm y)
                ((cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (slots a))
                ((extChartAt I x₀).symm y))
                (X ((extChartAt I x₀).symm y))))) := by
  unfold fixedChartNabla0SModel
  rw [covariantDeriv_tensor0SModelWithin_apply_slots]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  exact connectionEndomorphismInChart_apply_of_mem
    (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀ hy (slots a)




omit [IsManifold I n M] in
theorem fixedChartNabla0SModel_contDiffWithinAt (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov n)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (x₀ : M) [IsManifold I 2 M] [IsManifold I (n + 1 + 1) M]
    (hmn : n + 1 ≤ n) :
    ContDiffWithinAt 𝕜 n
      (fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (n := n) s cov X α x₀)
      (range I) (extChartAt I x₀ x₀) := by
  have hα :
      ContDiffWithinAt 𝕜 n
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) s x₀ (fun x => α x))
        (range I) (extChartAt I x₀ x₀) := by
    have h := tensor0SModelInChart_contMDiffWithinAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s x₀ α
    simpa using h.contDiffWithinAt
  have hX :
      ContDiffWithinAt 𝕜 n
        (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I))
        (range I) (extChartAt I x₀ x₀) := by
    haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
    let z₀ : E := extChartAt I x₀ x₀
    let W : E → E :=
      mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I)
    let e := trivializationAt E (TangentSpace 𝓘(𝕜, E) : E → Type _) z₀
    have h :=
      VectorField.contMDiffWithinAt_mpullbackWithin_extChartAt_symm
        (I := I) (M := M) (n := n + 1)
        (m := n) (s := Set.univ) (V := fun x => X x)
        (X.contMDiff x₀) uniqueMDiffOn_univ (Set.mem_univ x₀)
        (by simp)
    have htotal :
        ContMDiffWithinAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E)) n
          (fun y : E =>
            (⟨y, W y⟩ :
              TotalSpace E (TangentSpace 𝓘(𝕜, E) : E → Type _)))
          (range I) z₀ := by
      have htarget :
          (extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' Set.univ
            ∈ 𝓝[range I] z₀ := by
        simpa [z₀] using extChartAt_target_mem_nhdsWithin (I := I) x₀
      have h' := h.mono_of_mem_nhdsWithin htarget
      simpa [W, z₀, Set.univ_inter] using h'
    have hzsrc :
        (⟨z₀, W z₀⟩ :
          TotalSpace E (TangentSpace 𝓘(𝕜, E) : E → Type _)) ∈ e.source := by
      exact FiberBundle.mem_trivializationAt_proj_source
    have hcoord :
        ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
          (fun y : E =>
            (e (⟨y, W y⟩ :
              TotalSpace E (TangentSpace 𝓘(𝕜, E) : E → Type _))).2)
          (range I) z₀ :=
      ((Bundle.Trivialization.contMDiffWithinAt_iff
        (e := e)
        (f := fun y : E =>
          (⟨y, W y⟩ :
            TotalSpace E (TangentSpace 𝓘(𝕜, E) : E → Type _)))
        (s := range I) (x₀ := z₀) hzsrc).mp htotal).2
    have heq :
        (fun y : E =>
            (e (⟨y, W y⟩ :
              TotalSpace E (TangentSpace 𝓘(𝕜, E) : E → Type _))).2)
          =ᶠ[𝓝[range I] z₀] W := by
      filter_upwards with y
      simp [e]
    have heq₀ :
        (e (⟨z₀, W z₀⟩ :
          TotalSpace E (TangentSpace 𝓘(𝕜, E) : E → Type _))).2 = W z₀ := by
      simp [e]
    simpa [W, z₀] using hcoord.contDiffWithinAt.congr_of_eventuallyEq heq.symm heq₀.symm
  have hΓ :
      ContDiffWithinAt 𝕜 n
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
        (range I) (extChartAt I x₀ x₀) :=
    connectionEndomorphismInChart_contDiffWithinAt
      (𝕜 := 𝕜) (I := I) (M := M) (n := n) cov hcov X x₀
  have hx : extChartAt I x₀ x₀ ∈ range I :=
    extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)
  simpa [fixedChartNabla0SModel] using
    contDiffWithinAt_covariantDeriv_tensor0SModelWithin
      (𝕜 := 𝕜) (E := E) s hα hX hΓ I.uniqueDiffOn hmn hx
end SmoothVectorFieldRSNabla

end

end TensorLieDeriv
