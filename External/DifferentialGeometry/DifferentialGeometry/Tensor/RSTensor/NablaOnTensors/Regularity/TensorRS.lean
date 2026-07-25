import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Tensor0S





namespace Tensor0SBundle

open Bundle Set TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem nablaRS_reg (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s) :
    NablaRSRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) r s
  letI := tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) r s
  letI := tensorRSBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) r s
  letI := tensorRSBundle_smooth (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) (n := (∞ : WithTop ℕ∞)) r s
  letI : FiniteDimensional 𝕜 (TensorRSModel r s 𝕜 E) := inferInstance
  let F : (p : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r s p :=
    fun p : M =>
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T p
  intro x₀
  rw [contMDiffAt_section]
  let e := trivializationAt (TensorRSModel r s 𝕜 E)
    (fun p : M => TensorRSSpace r s I p) x₀
  have hx₀ : x₀ ∈ e.baseSet := by
    simpa [e] using
      (mem_baseSet_trivializationAt
        (TensorRSModel r s 𝕜 E) (fun p : M => TensorRSSpace r s I p) x₀)
  let G : M -> TensorRSModel r s 𝕜 E := fun p => (e ⟨p, F p⟩).2
  let d := Module.finrank 𝕜 E
  let bE : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  have hG : ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E)
      (∞ : WithTop ℕ∞) G x₀ := by
    refine contMDiffAt_tensorRSModel_of_apply_basis_eval_basis
      (I := I) (bE := bE) (G := G) (x₀ := x₀)
      (n := (∞ : WithTop ℕ∞)) ?_
    intro ρ σ
    let eTan := trivializationAt E (TangentSpace I : M -> Type _) x₀
    let βρ : Tensor0SModel r 𝕜 E :=
      (continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) bE r) ρ
    let vσ : Fin s -> E := fun a => bE (σ a)
    have hintrinsic :
        ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
          (fun p : M =>
            (F p (Tensor0SSpace.constInChart
              (𝕜 := 𝕜) (I := I) (M := M) r x₀ βρ p))
              (fun a : Fin s => eTan.symmL 𝕜 p (vσ a))) x₀ := by
      let βsec : (p : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) r p :=
        fun p : M => Tensor0SSpace.constInChart
          (𝕜 := 𝕜) (I := I) (M := M) r x₀ βρ p
      let V : Fin s -> (p : M) -> TangentSpace I p :=
        fun a => tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (vσ a)
      let pair : M -> 𝕜 := fun p : M => (T p (βsec p)) (fun a : Fin s => V a p)
      let Xinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
        ⟨fun p : M => X p, X.contMDiff.of_le (by simp)⟩
      have hT : ContMDiffAt I (I.prod 𝓘(𝕜, TensorRSModel r s 𝕜 E))
          (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, T p⟩ :
              TotalSpace (TensorRSModel r s 𝕜 E)
                (fun p : M => TensorRSSpace r s I p))) x₀ :=
        (T.contMDiff x₀).of_le (by simp :
          (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
      have hβ : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
          (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, βsec p⟩ :
              TotalSpace (Tensor0SModel r 𝕜 E)
                (fun p : M => Tensor0SSpace r I p))) x₀ := by
        simpa [βsec] using
          tensor0SConstInChart_contMDiffAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) x₀ βρ
      have hV : ∀ a : Fin s,
          ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
            (fun p : M => (⟨p, V a p⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
            x₀ := by
        intro a
        have hx₀Tan : x₀ ∈ eTan.baseSet := by
          dsimp [eTan]
          exact mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x₀
        have hconst_on :
            CMDiff[eTan.baseSet] (∞ : WithTop ℕ∞) (T% (V a)) := by
          simpa [eTan, V, vσ] using
            (tangentConstInChart_contMDiffOn_baseSet
              (𝕜 := 𝕜) (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
              x₀ (vσ a))
        exact (hconst_on x₀ hx₀Tan).contMDiffAt (eTan.open_baseSet.mem_nhds hx₀Tan)
      have hpair : ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair x₀ := by
        simpa [pair] using
          tensorRS_eval_contMDiffAt
            (I := I) (T := fun p : M => T p) (β := βsec) (V := V) x₀ hT hβ hV
      have hderiv :
          ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
            (fun p : M => extDerivFun (I := I) pair p (X p)) x₀ := by
        simpa [Xinf] using DifferentialGeometry.extDerivFun_apply_contMDiffAt I hpair Xinf
      have hinput :
          ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
            (fun p : M =>
              (T p
                (localCovariantDerivTensor0SAt
                  (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X βsec p))
                (fun a : Fin s => V a p)) x₀ := by
        have hβcorr :
            ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
              (∞ : WithTop ℕ∞)
              (fun p : M =>
                (⟨p,
                  localCovariantDerivTensor0SAt
                    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X βsec p⟩ :
                  TotalSpace (Tensor0SModel r 𝕜 E)
                    (fun p : M => Tensor0SSpace r I p))) x₀ := by
          simpa [βsec] using
            localCovariantDerivTensor0SAt_constInChart_contMDiffAt
              (I := I) cov hcov X x₀ βρ
        exact tensorRS_eval_contMDiffAt
          (I := I) (T := fun p : M => T p)
          (β := fun p : M =>
            localCovariantDerivTensor0SAt
              (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X βsec p)
          (V := V) x₀ hT hβcorr hV
      have houtput :
          ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
            (fun p : M =>
              ∑ a : Fin s,
                (T p (βsec p))
                  (Function.update (fun b : Fin s => V b p) a
                    ((cov (V a) p) (X p)))) x₀ := by
        apply ContMDiffAt.sum
        intro a _
        let W : (p : M) -> TangentSpace I p := fun p : M => (cov (V a) p) (X p)
        have hW :
            ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
              (fun p : M => (⟨p, W p⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
              x₀ := by
          simpa [W, V] using
            tangentConst_covariantDeriv_apply_contMDiffAt
              (I := I) cov hcov X x₀ (vσ a)
        have hVupdate : ∀ i : Fin s,
            ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
              (fun p : M =>
                (⟨p, Function.update (fun b : Fin s => V b p) a (W p) i⟩ :
                  TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
          intro i
          by_cases hi : i = a
          · subst hi
            simpa using hW
          · simpa [Function.update, hi] using hV i
        exact tensorRS_eval_contMDiffAt
          (I := I) (T := fun p : M => T p) (β := βsec)
          (V := fun i : Fin s => fun p : M =>
            Function.update (fun b : Fin s => V b p) a (W p) i)
          x₀ hT hβ hVupdate
      have hmain :
          ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
            (fun p : M =>
              extDerivFun (I := I) pair p (X p) -
                (T p
                  (localCovariantDerivTensor0SAt
                    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X βsec p))
                  (fun a : Fin s => V a p) -
                ∑ a : Fin s,
                  (T p (βsec p))
                    (Function.update (fun b : Fin s => V b p) a
                      ((cov (V a) p) (X p)))) x₀ :=
        (hderiv.sub hinput).sub houtput
      refine hmain.congr_of_eventuallyEq ?_
      let eβ := trivializationAt (Tensor0SModel r 𝕜 E)
        (fun p : M => Tensor0SSpace r I p) x₀
      have hx₀Tan : x₀ ∈ eTan.baseSet := by
        dsimp [eTan]
        exact mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x₀
      have hx₀β : x₀ ∈ eβ.baseSet := by
        simpa [eβ] using
          (mem_baseSet_trivializationAt
            (Tensor0SModel r 𝕜 E) (fun p : M => Tensor0SSpace r I p) x₀)
      filter_upwards [eTan.open_baseSet.mem_nhds hx₀Tan,
        eβ.open_baseSet.mem_nhds hx₀β] with p hpTan hpβ
      have hT_p : ContMDiffAt I (I.prod 𝓘(𝕜, TensorRSModel r s 𝕜 E))
          (∞ : WithTop ℕ∞)
          (fun q : M =>
            (⟨q, T q⟩ :
              TotalSpace (TensorRSModel r s 𝕜 E)
                (fun q : M => TensorRSSpace r s I q))) p :=
        (T.contMDiff p).of_le (by simp :
          (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
      have hβ_p : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
          (∞ : WithTop ℕ∞)
          (fun q : M =>
            (⟨q, βsec q⟩ :
              TotalSpace (Tensor0SModel r 𝕜 E)
                (fun q : M => Tensor0SSpace r I q))) p := by
        simpa [βsec] using
          tensor0SConstInChart_contMDiffAt_of_mem
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) x₀ βρ hpβ
      have hV_p : ∀ a : Fin s,
          ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
            (fun q : M => (⟨q, V a q⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
            p := by
        intro a
        have hconst_on :
            CMDiff[eTan.baseSet] (∞ : WithTop ℕ∞) (T% (V a)) := by
          simpa [eTan, V, vσ] using
            (tangentConstInChart_contMDiffOn_baseSet
              (𝕜 := 𝕜) (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
              x₀ (vσ a))
        exact (hconst_on p hpTan).contMDiffAt (eTan.open_baseSet.mem_nhds hpTan)
      have hpair_md : MDifferentiableAt I 𝓘(𝕜, 𝕜) pair p := by
        have hpair_p : ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair p := by
          simpa [pair] using
            tensorRS_eval_contMDiffAt
              (I := I) (T := fun q : M => T q) (β := βsec) (V := V) p
              hT_p hβ_p hV_p
        exact hpair_p.mdifferentiableAt (by simp)
      have hβmodel_p :
          DifferentiableWithinAt 𝕜
            (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
              (M := M) r p βsec)
            (Set.range I) (extChartAt I p p) :=
        tensor0SModelInChart_differentiableWithinAt_center_of_contMDiffAt
          (I := I) βsec p hβ_p
      have hV_md : ∀ a : Fin s, MDiffAt (T% (V a)) p :=
        fun a => (hV_p a).mdifferentiableAt (by simp)
      have hVmodel_p : ∀ a : Fin s,
          DifferentiableWithinAt 𝕜
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) p (V a))
            (Set.range I) (extChartAt I p p) :=
        fun a =>
          tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
            (I := I) (V a) p (hV_p a)
      have hcoord_p : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
          MDifferentiableAt I 𝓘(𝕜, 𝕜)
            (fun q : M =>
              (Module.finBasis 𝕜 E).coord i
                (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) p (V a)
                  (extChartAt I p q))) p :=
        fun a i =>
          tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
            (I := I) (V a) p (hV_p a) i
      have hVeq :
          (fun a : Fin s => eTan.symmL 𝕜 p (vσ a)) =
            fun a : Fin s => V a p := by
        funext a
        simp [V, eTan]
      change ((nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T p) (βsec p))
          (fun a : Fin s => eTan.symmL 𝕜 p (vσ a)) =
        ((extDerivFun (I := I) pair p) (X p) -
            (T p (localCovariantDerivTensor0SAt
              (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X βsec p))
              (fun a : Fin s => V a p)) -
          ∑ a : Fin s,
            (T p (βsec p))
              (Function.update (fun b : Fin s => V b p) a ((cov (V a) p) (X p)))
      rw [hVeq]
      rw [nablaRSFun_eval_moving_raw
        (I := I) cov X T βsec V p hpair_md hβmodel_p hV_md hVmodel_p hcoord_p]
    refine hintrinsic.congr_of_eventuallyEq ?_
    have hx₀Tan : x₀ ∈ eTan.baseSet := by
      dsimp [eTan]
      exact mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x₀
    filter_upwards [eTan.open_baseSet.mem_nhds hx₀Tan] with p hp
    simpa [G, F, e, eTan, βρ, vσ] using
      (TensorRSSpace.trivializationAt_basis_coord
        (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := p)
        (bE := bE) (r := r) (s := s) hp (F p) ρ σ)
  simpa [G, F, e] using hG
end Tensor0SBundle
