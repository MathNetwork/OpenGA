import DifferentialGeometry.Tensor.RSTensor.Defs


noncomputable section

namespace Tensor0SBundle

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable {r s : ℕ}

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem tensor0SSpace_continuousLinearEquiv_norm_apply (s : ℕ) (b : M)
    (T : Tensor0SSpace s I b) :
    ‖tensor0SSpace_continuousLinearEquiv (𝕜 := 𝕜) (E := E) (I := I) (M := M) s b T‖
      = ‖T‖ := rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem tensor0SSpace_continuousLinearEquiv_symm_norm_apply (s : ℕ) (b : M)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :
    ‖(tensor0SSpace_continuousLinearEquiv (𝕜 := 𝕜) (E := E) (I := I)
        (M := M) s b).symm f‖ = ‖f‖ := rfl

theorem tensorRSSpace_norm_eq_carrier_opNorm {b : M} (T : TensorRSSpace r s I b) :
    ‖T‖ = sInf {c : ℝ | 0 ≤ c ∧
      ∀ x : Tensor0SSpace r I b,
        ‖(T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) x‖ ≤ c * ‖x‖} := by
  classical

  have hT_def : ‖T‖
      = ‖tensorRSSpace_continuousLinearEquiv
          (𝕜 := 𝕜) (E := E) (I := I) (M := M) r s b T‖ := rfl

  set e_r := tensor0SSpace_continuousLinearEquiv
    (𝕜 := 𝕜) (E := E) (I := I) (M := M) r b with he_r
  set e_s := tensor0SSpace_continuousLinearEquiv
    (𝕜 := 𝕜) (E := E) (I := I) (M := M) s b with he_s
  have hUnfold :
      tensorRSSpace_continuousLinearEquiv (𝕜 := 𝕜) (E := E) (I := I) (M := M) r s b T
        = e_r.arrowCongr e_s
            (T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) := rfl

  set Tcarrier : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b := T with hTcarrier
  have hSetEq :
      {c : ℝ | 0 ≤ c ∧
          ∀ x : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜,
            ‖e_r.arrowCongr e_s Tcarrier x‖ ≤ c * ‖x‖}
        = {c : ℝ | 0 ≤ c ∧
            ∀ x : Tensor0SSpace r I b, ‖Tcarrier x‖ ≤ c * ‖x‖} := by
    apply Set.eq_of_subset_of_subset
    · rintro c ⟨hc, hbd⟩
      refine ⟨hc, fun y => ?_⟩
      have hx := hbd (e_r y)
      have h1 : e_r.arrowCongr e_s Tcarrier (e_r y) = e_s (Tcarrier y) := by
        rw [ContinuousLinearEquiv.arrowCongr_apply,
            ContinuousLinearEquiv.symm_apply_apply]
      rw [h1] at hx
      have hLHS : ‖e_s (Tcarrier y)‖ = ‖Tcarrier y‖ :=
        tensor0SSpace_continuousLinearEquiv_norm_apply (𝕜 := 𝕜) (E := E)
          (I := I) (M := M) s b (Tcarrier y)
      have hRHS : ‖e_r y‖ = ‖y‖ :=
        tensor0SSpace_continuousLinearEquiv_norm_apply (𝕜 := 𝕜) (E := E)
          (I := I) (M := M) r b y
      rw [hLHS, hRHS] at hx
      exact hx
    · rintro c ⟨hc, hbd⟩
      refine ⟨hc, fun x => ?_⟩
      have hy := hbd (e_r.symm x)
      have h1 : e_r.arrowCongr e_s Tcarrier x = e_s (Tcarrier (e_r.symm x)) := by
        rw [ContinuousLinearEquiv.arrowCongr_apply]
      rw [h1]
      have hLHS : ‖e_s (Tcarrier (e_r.symm x))‖ = ‖Tcarrier (e_r.symm x)‖ :=
        tensor0SSpace_continuousLinearEquiv_norm_apply (𝕜 := 𝕜) (E := E)
          (I := I) (M := M) s b (Tcarrier (e_r.symm x))
      have hRHS : ‖e_r.symm x‖ = ‖x‖ :=
        tensor0SSpace_continuousLinearEquiv_symm_norm_apply (𝕜 := 𝕜) (E := E)
          (I := I) (M := M) r b x
      rw [hLHS, ← hRHS]
      exact hy

  have hnorm_def :
      ‖e_r.arrowCongr e_s Tcarrier‖
        = sInf {c : ℝ | 0 ≤ c ∧
            ∀ x : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜,
              ‖e_r.arrowCongr e_s Tcarrier x‖ ≤ c * ‖x‖} :=
    ContinuousLinearMap.norm_def _
  rw [hT_def, hUnfold, hnorm_def]
  exact congrArg sInf hSetEq

omit [FiniteDimensional 𝕜 E] in
private lemma _bounds_bddBelow_carrier {b : M} (T : TensorRSSpace r s I b) :
    BddBelow {c : ℝ | 0 ≤ c ∧
      ∀ x : Tensor0SSpace r I b,
        ‖(T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) x‖ ≤ c * ‖x‖} :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩

theorem tensorRSSpace_norm_apply_le {b : M} (T : TensorRSSpace r s I b)
    (x : Tensor0SSpace r I b) :
    ‖(T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) x‖ ≤ ‖T‖ * ‖x‖ := by
  set e_r := tensor0SSpace_continuousLinearEquiv
    (𝕜 := 𝕜) (E := E) (I := I) (M := M) r b with he_r
  set e_s := tensor0SSpace_continuousLinearEquiv
    (𝕜 := 𝕜) (E := E) (I := I) (M := M) s b with he_s

  have hbd_model :
      ‖(e_r.arrowCongr e_s
          (T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b)) (e_r x)‖
        ≤ ‖e_r.arrowCongr e_s
              (T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b)‖
          * ‖e_r x‖ :=
    ContinuousLinearMap.le_opNorm _ _

  have h1 :
      e_r.arrowCongr e_s
          (T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) (e_r x)
        = e_s ((T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) x) := by
    rw [ContinuousLinearEquiv.arrowCongr_apply,
        ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hLHS :
      ‖e_s ((T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) x)‖
        = ‖(T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) x‖ :=
    tensor0SSpace_continuousLinearEquiv_norm_apply (𝕜 := 𝕜) (E := E)
      (I := I) (M := M) s b _
  have hxNorm : ‖e_r x‖ = ‖x‖ :=
    tensor0SSpace_continuousLinearEquiv_norm_apply (𝕜 := 𝕜) (E := E)
      (I := I) (M := M) r b x
  have hT_norm :
      ‖e_r.arrowCongr e_s
          (T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b)‖ = ‖T‖ := rfl
  rw [h1, hLHS, hxNorm, hT_norm] at hbd_model
  exact hbd_model

theorem tensorRSSpace_opNorm_le_bound {b : M} (T : TensorRSSpace r s I b)
    {C : ℝ} (hCpos : 0 ≤ C)
    (hbd : ∀ x : Tensor0SSpace r I b,
      ‖(T : Tensor0SSpace r I b →L[𝕜] Tensor0SSpace s I b) x‖ ≤ C * ‖x‖) :
    ‖T‖ ≤ C := by
  rw [tensorRSSpace_norm_eq_carrier_opNorm]
  exact csInf_le (_bounds_bddBelow_carrier (𝕜 := 𝕜) (E := E) (I := I) (M := M) T)
    ⟨hCpos, hbd⟩

end Tensor0SBundle

end
