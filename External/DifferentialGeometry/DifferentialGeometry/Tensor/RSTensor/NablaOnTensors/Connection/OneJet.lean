import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Derivation










namespace TensorLieDeriv

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section TangentOneJet

variable [IsManifold I 2 M] [T2Space M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]

omit [I.Boundaryless] [T2Space M] [IsManifold I ∞ M]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I] in
private theorem tangentFieldModelInChart_sum_tangentConst_model
    (x₀ : M) (F : E -> E) {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    tangentFieldModelInChart (𝕜 := Real) (I := I) x₀
        (fun x : M =>
          ∑ i : Fin (Module.finrank Real E),
            (Module.finBasis Real E).coord i (F (extChartAt I x₀ x)) •
              tangentConstInChart (𝕜 := Real) (I := I) x₀
                ((Module.finBasis Real E) i) x) y =
      F y := by
  classical
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let b := Module.finBasis Real E
  have hright : extChartAt I x₀ ((extChartAt I x₀).symm y) = y :=
    (extChartAt I x₀).right_inv hy
  have hconst (i : Fin (Module.finrank Real E)) :
      e.continuousLinearMapAt Real ((extChartAt I x₀).symm y)
          (tangentConstInChart (𝕜 := Real) (I := I) x₀ (b i)
            ((extChartAt I x₀).symm y)) =
        b i := by
    simpa [e, tangentFieldModelInChart] using
      tangentFieldModelInChart_tangentConstInChart_apply_of_mem
        (𝕜 := Real) (I := I) (M := M) x₀ hy (b i)
  unfold tangentFieldModelInChart
  rw [map_sum]
  change
    (∑ i : Fin (Module.finrank Real E),
      e.continuousLinearMapAt Real ((extChartAt I x₀).symm y)
        (b.coord i (F (extChartAt I x₀ ((extChartAt I x₀).symm y))) •
          tangentConstInChart (𝕜 := Real) (I := I) x₀ (b i)
            ((extChartAt I x₀).symm y))) = F y
  calc
    (∑ i : Fin (Module.finrank Real E),
      e.continuousLinearMapAt Real ((extChartAt I x₀).symm y)
        (b.coord i (F (extChartAt I x₀ ((extChartAt I x₀).symm y))) •
          tangentConstInChart (𝕜 := Real) (I := I) x₀ (b i)
            ((extChartAt I x₀).symm y)))
        = ∑ i : Fin (Module.finrank Real E), b.coord i (F y) • b i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [map_smul, hconst i, hright]
    _ = F y := b.sum_repr (F y)



omit [I.Boundaryless] in
theorem exists_cov_zero_at
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (_hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (x₀ : M) (v : TangentSpace I x₀) :
    ∃ V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
      V x₀ = v ∧ cov (fun x => V x) x₀ = 0 := by
  classical
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let b := Module.finBasis Real E
  let y₀ : E := extChartAt I x₀ x₀
  let v₀ : E := e.continuousLinearMapAt Real x₀ v
  let Γ : E →L[Real] E →L[Real] E :=
    connectionEndomorphismInChartL (𝕜 := Real) (I := I) cov x₀ y₀
  let A : E →L[Real] E := (ContinuousLinearMap.apply Real E v₀).comp Γ
  let z : E → E := fun y => v₀ - A (y - y₀)
  let Vloc : (x : M) -> TangentSpace I x :=
    fun x =>
      ∑ i : Fin (Module.finrank Real E),
        b.coord i (z (extChartAt I x₀ x)) •
          tangentConstInChart (𝕜 := Real) (I := I) x₀ (b i) x
  let coeff : Fin (Module.finrank Real E) -> M -> Real :=
    fun i x => b.coord i (z (extChartAt I x₀ x))
  have hcoeff : ∀ i : Fin (Module.finrank Real E),
      ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (coeff i) e.baseSet := by
    haveI : CompleteSpace E := FiniteDimensional.complete Real E
    intro i
    let c : E →L[Real] Real := LinearMap.toContinuousLinearMap (b.coord i)
    have hz :
        ContDiff Real (∞ : WithTop ℕ∞) (fun y : E => b.coord i (z y)) := by
      have hz' : ContDiff Real (∞ : WithTop ℕ∞) z := by
        unfold z
        fun_prop
      simpa [c] using c.contDiff.comp hz'
    have hchart :
        ContMDiffOn I 𝓘(Real, E) (∞ : WithTop ℕ∞)
          (extChartAt I x₀) e.baseSet := by
      simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using
        contMDiffOn_extChartAt (I := I) (x := x₀)
    simpa [coeff] using hz.contMDiff.comp_contMDiffOn hchart
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hVloc_val : Vloc x₀ = v := by
    have hconst_model (i : Fin (Module.finrank Real E)) :
        e.continuousLinearMapAt Real x₀
            (tangentConstInChart (𝕜 := Real) (I := I) x₀ (b i) x₀) =
          b i := by
      unfold tangentConstInChart
      exact e.continuousLinearMapAt_symmL (R := Real) hx₀ (b i)
    have hconst_linear (i : Fin (Module.finrank Real E)) :
        e.linearMapAt Real x₀
            (tangentConstInChart (𝕜 := Real) (I := I) x₀ (b i) x₀) =
          b i := by
      exact hconst_model i
    calc
      Vloc x₀ =
          e.symmL Real x₀ (e.continuousLinearMapAt Real x₀ (Vloc x₀)) := by
            symm
            exact e.symmL_continuousLinearMapAt (R := Real) hx₀ (Vloc x₀)
      _ = e.symmL Real x₀ v₀ := by
            congr 1
            calc
              e.continuousLinearMapAt Real x₀ (Vloc x₀)
                  = ∑ i : Fin (Module.finrank Real E), b.coord i v₀ • b i := by
                      dsimp [Vloc]
                      rw [map_sum]
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      rw [map_smul, hconst_linear]
                      simp [z, y₀]
              _ = v₀ := by
                      exact b.sum_repr v₀
      _ = v := by
            exact e.symmL_continuousLinearMapAt (R := Real) hx₀ v
  have hVloc_on : CMDiff[e.baseSet] (∞ : WithTop ℕ∞) (T% Vloc) := by
    let term : Fin (Module.finrank Real E) -> (x : M) -> TangentSpace I x :=
      fun i => coeff i • tangentConstInChart (𝕜 := Real) (I := I) x₀ (b i)
    have hconst : ∀ i : Fin (Module.finrank Real E),
        CMDiff[e.baseSet] (∞ : WithTop ℕ∞)
          (T% (tangentConstInChart (𝕜 := Real) (I := I) x₀ (b i) :
            (x : M) -> TangentSpace I x)) := by
      haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
        simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)
      haveI : IsManifold I (((∞ : WithTop ℕ∞) + 1) + 1) M := by
        simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)
      intro i
      simpa [e] using
        tangentConstInChart_contMDiffOn_baseSet
          (𝕜 := Real) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) x₀ (b i)
    have hterm : ∀ i : Fin (Module.finrank Real E),
        CMDiff[e.baseSet] (∞ : WithTop ℕ∞) (T% (term i)) := by
      intro i
      exact (hcoeff i).smul_section (hconst i)
    have hsum :
        CMDiff[e.baseSet] (∞ : WithTop ℕ∞)
          (T% ((Finset.univ : Finset (Fin (Module.finrank Real E))).sum term)) := by
      simpa using
        ContMDiffOn.sum_section
          (s := (Finset.univ : Finset (Fin (Module.finrank Real E))))
          (t := term) (fun i _ => hterm i)
    refine hsum.congr ?_
    intro x hx
    simp [Vloc, term, coeff]
  have hVloc_model {y : E} (hy : y ∈ (extChartAt I x₀).target) :
      tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ Vloc y = z y := by
    simpa [Vloc, b] using
      tangentFieldModelInChart_sum_tangentConst_model
        (I := I) (M := M) x₀ z hy
  have hzcoord : ∀ i : Fin (Module.finrank Real E),
      MDiffAt
        (fun p : M =>
          b.coord i
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ Vloc
              (extChartAt I x₀ p))) x₀ := by
    intro i
    have hlocal :
        (fun p : M =>
          b.coord i
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ Vloc
              (extChartAt I x₀ p))) =ᶠ[𝓝 x₀]
          coeff i := by
      filter_upwards [e.open_baseSet.mem_nhds hx₀] with p hp
      have hp_source : p ∈ (extChartAt I x₀).source := by
        simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp
      have hp_target : extChartAt I x₀ p ∈ (extChartAt I x₀).target :=
        (extChartAt I x₀).map_source hp_source
      change b.coord i
          (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ Vloc
            (extChartAt I x₀ p)) =
        b.coord i (z (extChartAt I x₀ p))
      rw [hVloc_model hp_target]
    have hsmooth :
        MDifferentiableAt I 𝓘(Real, Real) (coeff i) x₀ :=
      ((hcoeff i x₀ hx₀).contMDiffAt (e.open_baseSet.mem_nhds hx₀)).mdifferentiableAt
        (by simp)
    exact hsmooth.congr_of_eventuallyEq hlocal
  obtain ⟨Vglob, hVglob⟩ :=
    exists_contMDiffSection_eqOn_nhd
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := ⊤) (ι := Unit)
      (s := fun _ : Unit => Vloc) (u := e.baseSet) (p := x₀)
      (fun _ => hVloc_on) e.open_baseSet hx₀
  let V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Vglob Unit.unit
  have hV_ev : (fun x : M => V x) =ᶠ[𝓝 x₀] Vloc := by
    filter_upwards [hVglob] with x hx
    exact hx Unit.unit
  have hV_val : V x₀ = v := by
    have hxV := hV_ev.self_of_nhds
    change V x₀ = Vloc x₀ at hxV
    rw [hxV, hVloc_val]
  have hV_mdiff : MDiffAt (T% (fun x : M => V x)) x₀ :=
    V.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hVloc_mdiff : MDiffAt (T% Vloc) x₀ :=
    ((hVloc_on x₀ hx₀).contMDiffAt (e.open_baseSet.mem_nhds hx₀)).mdifferentiableAt
      (by simp)
  have hcov_congr : cov (fun x : M => V x) x₀ = cov Vloc x₀ :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hV_mdiff hVloc_mdiff (by simp) hV_ev
  have hcovVloc : cov Vloc x₀ = 0 := by
    ext W
    let W₀ : E := W
    obtain ⟨Xsec, hXsec⟩ :=
      ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
        (n := (⊤ : ℕ∞)) x₀ W
    let X : (x : M) -> TangentSpace I x := fun x => Xsec x
    have hX_mdiff :
        MDiffAt (T% X) x₀ :=
      Xsec.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hzRange : y₀ ∈ Set.range I :=
      extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)
    have hmodel_ev :
        tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ Vloc
          =ᶠ[𝓝[Set.range I] y₀] z := by
      filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
      exact hVloc_model hy
    have hz_diff :
        DifferentiableWithinAt Real z (Set.range I) y₀ := by
      unfold z
      fun_prop
    have hVmodel :
        DifferentiableWithinAt Real
          (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ Vloc)
          (Set.range I) y₀ := by
      exact (hmodel_ev.differentiableWithinAt_iff_of_mem hzRange).mpr hz_diff
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)
    have hformula :=
      covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
        (𝕜 := Real) (I := I) cov Xsec Vloc x₀ hVloc_mdiff hVmodel hzcoord
    have hXpull :
        VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x₀).symm
            X (Set.range I) y₀ = W₀ := by
      simp only [VectorField.mpullbackWithin_apply, X, W₀, y₀]
      rw [extChartAt_to_inv, hXsec]
      exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x₀) W
    have hXpull' :
        VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x₀).symm
            (fun x => Xsec x) (Set.range I) (extChartAt I x₀ x₀) = W₀ := by
      simpa [X, y₀] using hXpull
    have hmodel_center :
        tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ Vloc y₀ = v₀ := by
      have h := hVloc_model (mem_extChartAt_target (I := I) x₀)
      simpa [z, y₀] using h
    have hfd :
        fderivWithin Real z (Set.range I) y₀ W₀ = - A W₀ := by
      have hhas : HasFDerivAt z (-A) y₀ := by
        have hid : HasFDerivAt (fun y : E => y) (1 : E →L[Real] E) y₀ := by
          simpa using (hasFDerivAt_id y₀ : HasFDerivAt (fun y : E => y) 1 y₀)
        have hsub : HasFDerivAt (fun y : E => y - y₀) (1 : E →L[Real] E) y₀ := by
          simpa using hid.sub_const y₀
        have hA' :
            HasFDerivAt (fun y : E => A (y - y₀)) (A.comp (1 : E →L[Real] E)) y₀ :=
          A.hasFDerivAt.comp y₀ hsub
        have hA : HasFDerivAt (fun y : E => A (y - y₀)) A y₀ := by
          simpa using hA'
        have hconst : HasFDerivAt (fun _ : E => v₀) (0 : E →L[Real] E) y₀ := by
          fun_prop
        simpa [z] using hconst.sub hA
      have huniq : UniqueDiffWithinAt Real (Set.range I) y₀ :=
        I.uniqueDiffOn y₀ hzRange
      exact congrArg (fun L : E →L[Real] E => L W₀)
        (hhas.hasFDerivWithinAt.fderivWithin huniq)
    have hderiv :
        fderivWithin Real
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ Vloc)
            (Set.range I) y₀ W₀ = - A W₀ := by
      have hfd_eq :
          fderivWithin Real
              (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ Vloc)
              (Set.range I) y₀ =
            fderivWithin Real z (Set.range I) y₀ :=
        hmodel_ev.fderivWithin_eq_of_mem hzRange
      rw [hfd_eq]
      exact hfd
    have hconn :
        connectionEndomorphismInChart (𝕜 := Real) (I := I) cov X x₀ y₀
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ Vloc y₀) =
          Γ W₀ v₀ := by
      have h :=
        connectionEndomorphismInChartL_apply_center
          (𝕜 := Real) (I := I) cov X x₀ v₀
      have hX0 : X x₀ = W := by
        simpa [X] using hXsec
      rw [hX0] at h
      rw [hmodel_center]
      exact h.symm
    have hmodel_cov :
        tangentFieldModelInChart (𝕜 := Real) (I := I) x₀
            (fun p : M => (cov Vloc p) (X p)) y₀ = 0 := by
      calc
        tangentFieldModelInChart (𝕜 := Real) (I := I) x₀
            (fun p : M => (cov Vloc p) (X p)) y₀
            = fderivWithin Real
                (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ Vloc)
                (Set.range I) y₀
                (VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x₀).symm
                  (fun x => Xsec x) (Set.range I) (extChartAt I x₀ x₀)) +
              connectionEndomorphismInChart (𝕜 := Real) (I := I) cov X x₀ y₀
                (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ Vloc y₀) := by
                simpa [X, y₀] using hformula
        _ = fderivWithin Real
                (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ Vloc)
                (Set.range I) y₀ W₀ +
              connectionEndomorphismInChart (𝕜 := Real) (I := I) cov X x₀ y₀
                (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ Vloc y₀) := by
                rw [hXpull']
        _ = (- A W₀) + Γ W₀ v₀ := by
                rw [hderiv, hconn]
        _ = 0 := by
                simp [A, Γ]
    have hvec :
        (cov Vloc x₀) W = 0 := by
      have h := hmodel_cov
      unfold tangentFieldModelInChart at h
      rw [extChartAt_to_inv] at h
      have hX0 : X x₀ = W := by
        simpa [X] using hXsec
      rw [TangentBundle.continuousLinearMapAt_trivializationAt
        (I := I) (x₀ := x₀) (x := x₀) (mem_chart_source H x₀)] at h
      rw [mfderiv_extChartAt_self] at h
      simpa [y₀, hX0] using h
    exact hvec
  refine ⟨V, hV_val, ?_⟩
  rw [hcov_congr, hcovVloc]



omit [I.Boundaryless] in
theorem exists_cov_zero_at_apply
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (x₀ : M) (v : TangentSpace I x₀) :
    ∃ V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
      V x₀ = v ∧
        ∀ W : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
          ((cov (fun x => V x) x₀) (W x₀)) = 0 := by
  obtain ⟨V, hV, hcovV⟩ :=
    exists_cov_zero_at (I := I) cov hcov x₀ v
  refine ⟨V, hV, ?_⟩
  intro W
  rw [hcovV]
  rfl

end TangentOneJet

end

end TensorLieDeriv
