import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Tangent
import DifferentialGeometry.Tensor.RSTensor.Derivation.NablaOnTensors




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




private theorem contDiffWithinAt_clm_of_apply
    {D F : Type*} [NormedAddCommGroup D] [NormedSpace 𝕜 D]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : WithTop ℕ∞} {Γ : D → E →L[𝕜] F} {u : Set D} {y : D}
    (hΓ : ∀ v : E, ContDiffWithinAt 𝕜 n (fun z => Γ z v) u y) :
    ContDiffWithinAt 𝕜 n Γ u y := by
  classical
  let d := Module.finrank 𝕜 E
  have hd : d = Module.finrank 𝕜 (Fin d → 𝕜) :=
    (Module.finrank_fin_fun (R := 𝕜) (n := d)).symm
  let e₁ : E ≃L[𝕜] (Fin d → 𝕜) := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ : (E →L[𝕜] F) ≃L[𝕜] (Fin d → F) :=
    (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← id_comp Γ, ← e₂.symm_comp_self]
  refine e₂.symm.contDiff.comp_contDiffWithinAt ?_
  refine contDiffWithinAt_pi.mpr fun i => ?_
  simpa [e₁, e₂, Function.comp_def] using hΓ (e₁.symm (Pi.single i (1 : 𝕜)))

section ConnectionEndomorphism

variable [IsManifold I 2 M]

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
private theorem covariantDerivative_finset_sum
    {ι : Type*} (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (t : Finset ι) (σ : ι → (x : M) → TangentSpace I x)
    {x : M} (v : TangentSpace I x)
    (hσ : ∀ i, MDiffAt (T% (σ i)) x) :
    (cov (t.sum σ) x) v = t.sum (fun i => (cov (σ i) x) v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp [cov.isCovariantDerivativeOnUniv.zero]
  | insert i t hit ih =>
      have hσi : MDiffAt (T% (σ i)) x := hσ i
      have hsum : MDiffAt (T% (t.sum σ)) x := by
        have hsum_raw := MDifferentiableAt.sum_section (s := t) (t := σ) hσ
        simpa using hsum_raw
      calc
        (cov ((insert i t).sum σ) x) v
            = (cov (σ i + t.sum σ) x) v := by
              simp [Finset.sum_insert, hit]
        _ = ((cov (σ i) x + cov (t.sum σ) x) v) := by
              rw [cov.isCovariantDerivativeOnUniv.add hσi hsum]
        _ = (cov (σ i) x) v + (cov (t.sum σ) x) v := by
              simp
        _ = (insert i t).sum (fun j => (cov (σ j) x) v) := by
              rw [ih]
              simp [Finset.sum_insert, hit]

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in



omit [IsManifold I n M] in
lemma covariantDerivative_tangentConst_apply_contMDiffOn_baseSet
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov n)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (x₀ : M) (v : E) [IsManifold I (n + 1) M] [IsManifold I (n + 1 + 1) M] :
    CMDiff[(trivializationAt E (TangentSpace I) x₀).baseSet] n
      (T% (fun p : M =>
        (cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v) p) (X p))) := by
  let e := trivializationAt E (TangentSpace I) x₀
  have hσ :
      CMDiff[e.baseSet] (n + 1)
        (T% (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v :
          (p : M) → TangentSpace I p)) := by
    simpa [e] using
      (tangentConstInChart_contMDiffOn_baseSet (𝕜 := 𝕜) (I := I) (M := M)
        (n := n + 1) x₀ v)
  have hcovσ :
      ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] E)) n
        (fun p : M =>
          (⟨p, cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v) p⟩ :
            TotalSpace (E →L[𝕜] E)
              (fun p : M => TangentSpace I p →L[𝕜] TangentSpace I p)))
        e.baseSet := by
    exact (hcov e.open_baseSet).contMDiff hσ
  have hX :
      CMDiff[e.baseSet] n (T% (fun p : M => X p)) :=
    X.contMDiff.contMDiffOn
  simpa [e] using hcovσ.clm_bundle_apply hX



noncomputable def connectionEndomorphismInChartL
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x₀ : M) (y : E) : E →L[𝕜] E →L[𝕜] E := by
  classical
  let e := trivializationAt E (TangentSpace I) x₀
  let p := (extChartAt I x₀).symm y
  refine LinearMap.toContinuousLinearMap ?_
  refine
    { toFun := fun X =>
        LinearMap.toContinuousLinearMap
          { toFun := fun v =>
              if y ∈ (extChartAt I x₀).target then
                e.continuousLinearMapAt 𝕜 p
                  ((cov (tangentConstInChart x₀ v) p) (e.symmL 𝕜 p X))
              else
                0
            map_add' := ?_
            map_smul' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
  · intro v w
    by_cases hy : y ∈ (extChartAt I x₀).target
    · have hp_source : p ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
      have hp_base : p ∈ e.baseSet := by
        simpa [e, p, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
      have hv : MDiffAt
          (T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p :=
        mdifferentiableAt_tangentConstInChart_of_mem
          (x₀ := x₀) (p := p) v hp_base
      have hw : MDiffAt
          (T% (tangentConstInChart x₀ w : (p : M) → TangentSpace I p)) p :=
        mdifferentiableAt_tangentConstInChart_of_mem
          (x₀ := x₀) (p := p) w hp_base
      have hsection :
          (tangentConstInChart x₀ (v + w) : (p : M) → TangentSpace I p) =
            (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) +
              tangentConstInChart x₀ w :=
        tangentConstInChart_add x₀ v w
      have hcov :
          cov ((tangentConstInChart x₀ v : (p : M) → TangentSpace I p) +
              tangentConstInChart x₀ w) p =
            cov (tangentConstInChart x₀ v) p +
              cov (tangentConstInChart x₀ w) p :=
        cov.isCovariantDerivativeOnUniv.add hv hw
      rw [if_pos hy, if_pos hy, if_pos hy]
      rw [hsection, hcov]
      simp [map_add]
    · rw [if_neg hy, if_neg hy, if_neg hy]
      simp
  · intro a v
    by_cases hy : y ∈ (extChartAt I x₀).target
    · have hp_source : p ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
      have hp_base : p ∈ e.baseSet := by
        simpa [e, p, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
      have hv : MDiffAt
          (T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p :=
        mdifferentiableAt_tangentConstInChart_of_mem
          (x₀ := x₀) (p := p) v hp_base
      have hsection :
          (tangentConstInChart x₀ (a • v) : (p : M) → TangentSpace I p) =
            a • (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) :=
        tangentConstInChart_smul x₀ a v
      have hcov :
          cov (a • (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p =
            a • cov (tangentConstInChart x₀ v) p :=
        cov.isCovariantDerivativeOnUniv.smul_const a hv
      rw [if_pos hy, if_pos hy]
      rw [hsection, hcov]
      simp [map_smul]
    · rw [if_neg hy, if_neg hy]
      simp
  · intro X Y
    ext v
    change (if y ∈ (extChartAt I x₀).target then
        e.continuousLinearMapAt 𝕜 p
          ((cov (tangentConstInChart x₀ v) p) (e.symmL 𝕜 p (X + Y)))
      else 0) =
      (if y ∈ (extChartAt I x₀).target then
        e.continuousLinearMapAt 𝕜 p
          ((cov (tangentConstInChart x₀ v) p) (e.symmL 𝕜 p X))
      else 0) +
      (if y ∈ (extChartAt I x₀).target then
        e.continuousLinearMapAt 𝕜 p
          ((cov (tangentConstInChart x₀ v) p) (e.symmL 𝕜 p Y))
      else 0)
    by_cases hy : y ∈ (extChartAt I x₀).target
    · rw [if_pos hy, if_pos hy, if_pos hy]
      simp [map_add]
    · rw [if_neg hy, if_neg hy, if_neg hy]
      simp
  · intro a X
    ext v
    change (if y ∈ (extChartAt I x₀).target then
        e.continuousLinearMapAt 𝕜 p
          ((cov (tangentConstInChart x₀ v) p) (e.symmL 𝕜 p (a • X)))
      else 0) =
      a •
        (if y ∈ (extChartAt I x₀).target then
          e.continuousLinearMapAt 𝕜 p
            ((cov (tangentConstInChart x₀ v) p) (e.symmL 𝕜 p X))
        else 0)
    by_cases hy : y ∈ (extChartAt I x₀).target
    · rw [if_pos hy, if_pos hy]
      simp [map_smul]
    · rw [if_neg hy, if_neg hy]
      simp

@[simp] lemma connectionEndomorphismInChartL_apply_of_mem
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (X v : E) :
    connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x₀ y X v =
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜
        ((extChartAt I x₀).symm y)
        ((cov (tangentConstInChart x₀ v)
          ((extChartAt I x₀).symm y))
          ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜
            ((extChartAt I x₀).symm y) X)) := by
  classical
  change (if y ∈ (extChartAt I x₀).target then
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜
        ((extChartAt I x₀).symm y)
        ((cov (tangentConstInChart x₀ v) ((extChartAt I x₀).symm y))
          ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜
            ((extChartAt I x₀).symm y) X))
    else 0) =
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜
        ((extChartAt I x₀).symm y)
        ((cov (tangentConstInChart x₀ v) ((extChartAt I x₀).symm y))
          ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜
            ((extChartAt I x₀).symm y) X))
  rw [if_pos hy]

@[simp] lemma connectionEndomorphismInChartL_apply_of_notMem
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x₀ : M) {y : E}
    (hy : y ∉ (extChartAt I x₀).target) (X v : E) :
    connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x₀ y X v = 0 := by
  classical
  change (if y ∈ (extChartAt I x₀).target then
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜
        ((extChartAt I x₀).symm y)
        ((cov (tangentConstInChart x₀ v) ((extChartAt I x₀).symm y))
          ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜
            ((extChartAt I x₀).symm y) X))
    else 0) = 0
  rw [if_neg hy]

lemma connectionEndomorphismInChartL_apply_modelVector
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : (x : M) → TangentSpace I x) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (v : E) :
    connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x₀ y
        ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜
          ((extChartAt I x₀).symm y) (X ((extChartAt I x₀).symm y))) v =
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀ y v := by
  rw [connectionEndomorphismInChartL_apply_of_mem (𝕜 := 𝕜) (I := I) cov x₀ hy]
  rw [connectionEndomorphismInChart_apply_of_mem (𝕜 := 𝕜) (I := I) cov X x₀ hy]
  rw [(trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := 𝕜)
      (by
        have hp_source : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
          (extChartAt I x₀).map_target hy
        simpa [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source)
      (X ((extChartAt I x₀).symm y))]







lemma connectionEndomorphismInChartL_apply_center_modelVector
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : (x : M) → TangentSpace I x) (x : M) (v : E) :
    connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x (extChartAt I x x)
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜
          x (X x)) v =
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x
        (extChartAt I x x) v := by
  have h :=
    connectionEndomorphismInChartL_apply_modelVector
      (𝕜 := 𝕜) (I := I) cov X x (mem_extChartAt_target (I := I) x) v
  rw [extChartAt_to_inv] at h
  simpa using h




lemma connectionEndomorphismInChartL_apply_center
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : (x : M) → TangentSpace I x) (x : M) (v : E) :
    connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x (extChartAt I x x)
        (X x) v =
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x
        (extChartAt I x x) v := by
  have h :=
    connectionEndomorphismInChartL_apply_center_modelVector
      (𝕜 := 𝕜) (I := I) cov X x v
  rw [TangentBundle.continuousLinearMapAt_trivializationAt
    (I := I) (x₀ := x) (x := x) (mem_chart_source H x)] at h
  rw [mfderiv_extChartAt_self] at h
  simpa using h







theorem covariantDerivative_modelInChart_center_eq_sum
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X V : (x : M) → TangentSpace I x) (x₀ : M)
    (hV : MDiffAt (T% V) x₀)
    (hz : ∀ i : Fin (Module.finrank 𝕜 E),
      MDiffAt
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
              (extChartAt I x₀ p))) x₀) :
    let b := Module.finBasis 𝕜 E
    let zfun : Fin (Module.finrank 𝕜 E) → M → 𝕜 :=
      fun i p =>
        b.coord i
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
            (extChartAt I x₀ p))
    tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
        (fun p : M => (cov V p) (X p)) (extChartAt I x₀ x₀) =
      (∑ i : Fin (Module.finrank 𝕜 E),
        extDerivFun (I := I) (zfun i) x₀ (X x₀) • b i) +
        connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀
          (extChartAt I x₀ x₀)
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
            (extChartAt I x₀ x₀)) := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  let b := Module.finBasis 𝕜 E
  let zfun : Fin (Module.finrank 𝕜 E) → M → 𝕜 :=
    fun i p =>
      b.coord i
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V (extChartAt I x₀ p))
  let term : Fin (Module.finrank 𝕜 E) → (p : M) → TangentSpace I p :=
    fun i => zfun i • tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i)
  have hx_base : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hconst_diff (i : Fin (Module.finrank 𝕜 E)) :
      MDiffAt
        (T% (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i) :
          (p : M) → TangentSpace I p)) x₀ :=
    mdifferentiableAt_tangentConstInChart_of_mem
      (𝕜 := 𝕜) (I := I) (x₀ := x₀) (p := x₀) (b i) hx_base
  have hterm_diff : ∀ i : Fin (Module.finrank 𝕜 E), MDiffAt (T% (term i)) x₀ := by
    intro i
    exact (hz i).smul_section (hconst_diff i)
  have hsum_diff : MDiffAt (T% ((Finset.univ : Finset (Fin (Module.finrank 𝕜 E))).sum term)) x₀ := by
    simpa using MDifferentiableAt.sum_section
      (s := (Finset.univ : Finset (Fin (Module.finrank 𝕜 E)))) (t := term) hterm_diff
  have hV_ev :
      V =ᶠ[𝓝 x₀]
        fun p : M =>
          ∑ i : Fin (Module.finrank 𝕜 E),
            zfun i p • tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i) p := by
    simpa [zfun, b, term] using
      (tangentField_eq_sum_modelCoord_tangentConst_eventually
        (𝕜 := 𝕜) (I := I) x₀ V)
  have hcov_congr :
      cov V x₀ = cov ((Finset.univ : Finset (Fin (Module.finrank 𝕜 E))).sum term) x₀ :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hV hsum_diff
      (by simp) (by simpa [term] using hV_ev)
  have hcov_sum :
      (cov V x₀) (X x₀) =
        ∑ i : Fin (Module.finrank 𝕜 E),
          (extDerivFun (I := I) (zfun i) x₀ (X x₀) •
              tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i) x₀ +
            zfun i x₀ •
              (cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i)) x₀) (X x₀)) := by
    calc
      (cov V x₀) (X x₀)
          = (cov ((Finset.univ : Finset (Fin (Module.finrank 𝕜 E))).sum term) x₀)
              (X x₀) := by
            rw [hcov_congr]
      _ = ∑ i : Fin (Module.finrank 𝕜 E), (cov (term i) x₀) (X x₀) := by
            exact covariantDerivative_finset_sum (𝕜 := 𝕜) (I := I) cov
              (Finset.univ : Finset (Fin (Module.finrank 𝕜 E))) term (X x₀) hterm_diff
      _ = ∑ i : Fin (Module.finrank 𝕜 E),
            (extDerivFun (I := I) (zfun i) x₀ (X x₀) •
                tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i) x₀ +
              zfun i x₀ •
                (cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i)) x₀) (X x₀)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            have hleib := congr($(cov.isCovariantDerivativeOnUniv.leibniz
              (σ := tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i))
              (g := zfun i) (x := x₀)
              (hconst_diff i) (hz i)) (X x₀))
            simpa [term, zfun, Pi.smul_apply, add_comm] using hleib
  have hconst_model (i : Fin (Module.finrank 𝕜 E)) :
      e.continuousLinearMapAt 𝕜 x₀
          (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i) x₀) =
        b i := by
    unfold tangentConstInChart
    exact e.continuousLinearMapAt_symmL (R := 𝕜) hx_base (b i)
  have hΓ_basis (i : Fin (Module.finrank 𝕜 E)) :
      e.continuousLinearMapAt 𝕜 x₀
          ((cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i)) x₀) (X x₀)) =
        connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀
          (extChartAt I x₀ x₀) (b i) := by
    rw [connectionEndomorphismInChart_apply_of_mem
      (𝕜 := 𝕜) (I := I) cov X x₀ (mem_extChartAt_target (I := I) x₀) (b i)]
    rw [extChartAt_to_inv]
  have hcenter_model :
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀) =
        e.continuousLinearMapAt 𝕜 x₀ (V x₀) := by
    unfold tangentFieldModelInChart
    rw [extChartAt_to_inv]
  have hmodel_sum :
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀) =
        ∑ i : Fin (Module.finrank 𝕜 E), zfun i x₀ • b i := by
    calc
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀)
          = e.continuousLinearMapAt 𝕜 x₀ (V x₀) := hcenter_model
      _ = ∑ i : Fin (Module.finrank 𝕜 E),
            b.coord i (e.continuousLinearMapAt 𝕜 x₀ (V x₀)) • b i := by
            exact (b.sum_repr (e.continuousLinearMapAt 𝕜 x₀ (V x₀))).symm
      _ = ∑ i : Fin (Module.finrank 𝕜 E), zfun i x₀ • b i := by
            congr
            ext i
            rw [← hcenter_model]
  have hΓ_sum :
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀
          (extChartAt I x₀ x₀)
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
            (extChartAt I x₀ x₀)) =
        ∑ i : Fin (Module.finrank 𝕜 E),
          zfun i x₀ •
            connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀
              (extChartAt I x₀ x₀) (b i) := by
    rw [hmodel_sum, map_sum]
    simp_rw [map_smul]
  dsimp only
  unfold tangentFieldModelInChart
  rw [extChartAt_to_inv]
  change e.continuousLinearMapAt 𝕜 x₀ ((cov V x₀) (X x₀)) =
    (∑ i : Fin (Module.finrank 𝕜 E),
      extDerivFun (I := I) (zfun i) x₀ (X x₀) • b i) +
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀
        (extChartAt I x₀ x₀)
        (e.continuousLinearMapAt 𝕜 x₀ (V x₀))
  rw [hcov_sum]
  rw [map_sum]
  simp_rw [map_add, map_smul, hconst_model, hΓ_basis]
  rw [Finset.sum_add_distrib]
  rw [← hcenter_model]
  rw [hΓ_sum]







theorem covariantDerivative_modelInChart_eq_sum
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X V : (x : M) → TangentSpace I x) (x₀ p : M)
    (hp : p ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet)
    (hV : MDiffAt (T% V) p)
    (hz : ∀ i : Fin (Module.finrank 𝕜 E),
      MDiffAt
        (fun q : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
              (extChartAt I x₀ q))) p) :
    let b := Module.finBasis 𝕜 E
    let zfun : Fin (Module.finrank 𝕜 E) → M → 𝕜 :=
      fun i q =>
        b.coord i
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
            (extChartAt I x₀ q))
    tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
        (fun q : M => (cov V q) (X q)) (extChartAt I x₀ p) =
      (∑ i : Fin (Module.finrank 𝕜 E),
        extDerivFun (I := I) (zfun i) p (X p) • b i) +
        connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀
          (extChartAt I x₀ p)
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
            (extChartAt I x₀ p)) := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  let b := Module.finBasis 𝕜 E
  let zfun : Fin (Module.finrank 𝕜 E) → M → 𝕜 :=
    fun i q =>
      b.coord i
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V (extChartAt I x₀ q))
  let term : Fin (Module.finrank 𝕜 E) → (q : M) → TangentSpace I q :=
    fun i => zfun i • tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i)
  have hconst_diff (i : Fin (Module.finrank 𝕜 E)) :
      MDiffAt
        (T% (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i) :
          (q : M) → TangentSpace I q)) p :=
    mdifferentiableAt_tangentConstInChart_of_mem
      (𝕜 := 𝕜) (I := I) (x₀ := x₀) (p := p) (b i) hp
  have hterm_diff : ∀ i : Fin (Module.finrank 𝕜 E), MDiffAt (T% (term i)) p := by
    intro i
    exact (hz i).smul_section (hconst_diff i)
  have hsum_diff : MDiffAt (T% ((Finset.univ : Finset (Fin (Module.finrank 𝕜 E))).sum term)) p := by
    simpa using MDifferentiableAt.sum_section
      (s := (Finset.univ : Finset (Fin (Module.finrank 𝕜 E)))) (t := term) hterm_diff
  have hV_ev :
      V =ᶠ[𝓝 p]
        fun q : M =>
          ∑ i : Fin (Module.finrank 𝕜 E),
            zfun i q • tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i) q := by
    simpa [zfun, b, term] using
      (tangentField_eq_sum_modelCoord_tangentConst_eventually_of_mem
        (𝕜 := 𝕜) (I := I) x₀ V hp)
  have hcov_congr :
      cov V p = cov ((Finset.univ : Finset (Fin (Module.finrank 𝕜 E))).sum term) p :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hV hsum_diff
      (by simp) (by simpa [term] using hV_ev)
  have hcov_sum :
      (cov V p) (X p) =
        ∑ i : Fin (Module.finrank 𝕜 E),
          (extDerivFun (I := I) (zfun i) p (X p) •
              tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i) p +
            zfun i p •
              (cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i)) p) (X p)) := by
    calc
      (cov V p) (X p)
          = (cov ((Finset.univ : Finset (Fin (Module.finrank 𝕜 E))).sum term) p)
              (X p) := by
            rw [hcov_congr]
      _ = ∑ i : Fin (Module.finrank 𝕜 E), (cov (term i) p) (X p) := by
            exact covariantDerivative_finset_sum (𝕜 := 𝕜) (I := I) cov
              (Finset.univ : Finset (Fin (Module.finrank 𝕜 E))) term (X p) hterm_diff
      _ = ∑ i : Fin (Module.finrank 𝕜 E),
            (extDerivFun (I := I) (zfun i) p (X p) •
                tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i) p +
              zfun i p •
                (cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i)) p) (X p)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            have hleib := congr($(cov.isCovariantDerivativeOnUniv.leibniz
              (σ := tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i))
              (g := zfun i) (x := p)
              (hconst_diff i) (hz i)) (X p))
            simpa [term, zfun, Pi.smul_apply, add_comm] using hleib
  have hp_target : extChartAt I x₀ p ∈ (extChartAt I x₀).target := by
    have hp_source : p ∈ (extChartAt I x₀).source := by
      simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp
    exact (extChartAt I x₀).map_source hp_source
  have hleft : (extChartAt I x₀).symm (extChartAt I x₀ p) = p := by
    have hp_source : p ∈ (extChartAt I x₀).source := by
      simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp
    exact (extChartAt I x₀).left_inv hp_source
  have hconst_model (i : Fin (Module.finrank 𝕜 E)) :
      e.continuousLinearMapAt 𝕜 p
          (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i) p) =
        b i := by
    unfold tangentConstInChart
    exact e.continuousLinearMapAt_symmL (R := 𝕜) hp (b i)
  have hΓ_basis (i : Fin (Module.finrank 𝕜 E)) :
      e.continuousLinearMapAt 𝕜 p
          ((cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i)) p) (X p)) =
        connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀
          (extChartAt I x₀ p) (b i) := by
    rw [connectionEndomorphismInChart_apply_of_mem
      (𝕜 := 𝕜) (I := I) cov X x₀ hp_target (b i)]
    rw [hleft]
  have hcenter_model :
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ p) =
        e.continuousLinearMapAt 𝕜 p (V p) := by
    unfold tangentFieldModelInChart
    rw [hleft]
  have hmodel_sum :
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ p) =
        ∑ i : Fin (Module.finrank 𝕜 E), zfun i p • b i := by
    calc
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ p)
          = e.continuousLinearMapAt 𝕜 p (V p) := hcenter_model
      _ = ∑ i : Fin (Module.finrank 𝕜 E),
            b.coord i (e.continuousLinearMapAt 𝕜 p (V p)) • b i := by
            exact (b.sum_repr (e.continuousLinearMapAt 𝕜 p (V p))).symm
      _ = ∑ i : Fin (Module.finrank 𝕜 E), zfun i p • b i := by
            congr
            ext i
            rw [← hcenter_model]
  have hΓ_sum :
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀
          (extChartAt I x₀ p)
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
            (extChartAt I x₀ p)) =
        ∑ i : Fin (Module.finrank 𝕜 E),
          zfun i p •
            connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀
              (extChartAt I x₀ p) (b i) := by
    rw [hmodel_sum, map_sum]
    simp_rw [map_smul]
  dsimp only
  unfold tangentFieldModelInChart
  rw [hleft]
  change e.continuousLinearMapAt 𝕜 p ((cov V p) (X p)) =
    (∑ i : Fin (Module.finrank 𝕜 E),
      extDerivFun (I := I) (zfun i) p (X p) • b i) +
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀
        (extChartAt I x₀ p)
        (e.continuousLinearMapAt 𝕜 p (V p))
  rw [hcov_sum]
  rw [map_sum]
  simp_rw [map_add, map_smul, hconst_model, hΓ_basis]
  rw [Finset.sum_add_distrib]
  rw [← hcenter_model]
  rw [hΓ_sum]



omit [IsManifold I n M] in
lemma connectionEndomorphismInChart_apply_contDiffWithinAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov n)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (x₀ : M) (v : E) [IsManifold I (n + 1) M] [IsManifold I (n + 1 + 1) M] :
    ContDiffWithinAt 𝕜 n
      (fun y : E =>
        connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀ y v)
      (Set.range I) (extChartAt I x₀ x₀) := by
  let e := trivializationAt E (TangentSpace I) x₀
  haveI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  let σ : (p : M) → TangentSpace I p :=
    tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v
  let W : (p : M) → TangentSpace I p := fun p => (cov σ p) (X p)
  have hp₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hW_on :
      CMDiff[e.baseSet] n (T% W) := by
    simpa [e, σ, W] using
      (covariantDerivative_tangentConst_apply_contMDiffOn_baseSet
        (𝕜 := 𝕜) (I := I) (M := M) (n := n) cov hcov X x₀ v)
  have hW_at : CMDiffAt n (T% W) x₀ :=
    (hW_on x₀ hp₀).contMDiffAt (e.open_baseSet.mem_nhds hp₀)
  have hcoord :
      ContMDiffAt I 𝓘(𝕜, E) n
        (fun p : M => (e ⟨p, W p⟩).2) x₀ :=
    (e.contMDiffAt_section_iff hp₀).mp hW_at
  have hsymm :
      ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x₀).symm
        (Set.range I) (extChartAt I x₀ x₀) := by
    simpa using
      contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := n) x₀
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  have hcoord_center :
      ContMDiffAt I 𝓘(𝕜, E) n
        (fun p : M => (e ⟨p, W p⟩).2)
        ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    simpa [hcenter] using hcoord
  have hfixed :
      ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        ((fun p : M => (e ⟨p, W p⟩).2) ∘ (extChartAt I x₀).symm)
        (Set.range I) (extChartAt I x₀ x₀) :=
    hcoord_center.comp_contMDiffWithinAt (x := extChartAt I x₀ x₀) hsymm
  have hmdiff : ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
      (fun y : E =>
        connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀ y v)
      (Set.range I) (extChartAt I x₀ x₀) := by
    refine hfixed.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
      have hp_source : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
        (extChartAt I x₀).map_target hy
      have hp_base : (extChartAt I x₀).symm y ∈ e.baseSet := by
        simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
      have hcoe :
          ⇑(e.linearMapAt 𝕜 ((extChartAt I x₀).symm y)) =
            fun z => (e ⟨(extChartAt I x₀).symm y, z⟩).2 :=
        e.coe_linearMapAt_of_mem (R := 𝕜) hp_base
      rw [connectionEndomorphismInChart_apply_of_mem
        (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀ hy v]
      rw [Bundle.Trivialization.continuousLinearMapAt_apply]
      change (e.linearMapAt 𝕜 ((extChartAt I x₀).symm y))
          (W ((extChartAt I x₀).symm y)) =
        (e ⟨(extChartAt I x₀).symm y, W ((extChartAt I x₀).symm y)⟩).2
      rw [hcoe]
    · have hy : extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target :=
        mem_extChartAt_target (I := I) x₀
      have hp_source :
          (extChartAt I x₀).symm (extChartAt I x₀ x₀) ∈ (extChartAt I x₀).source :=
        (extChartAt I x₀).map_target hy
      have hp_base : (extChartAt I x₀).symm (extChartAt I x₀ x₀) ∈ e.baseSet := by
        simp [e, TangentBundle.trivializationAt_baseSet] at hp_source ⊢
      have hcoe :
          ⇑(e.linearMapAt 𝕜 ((extChartAt I x₀).symm (extChartAt I x₀ x₀))) =
            fun z => (e ⟨(extChartAt I x₀).symm (extChartAt I x₀ x₀), z⟩).2 :=
        e.coe_linearMapAt_of_mem (R := 𝕜) hp_base
      rw [connectionEndomorphismInChart_apply_of_mem
        (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀ hy v]
      rw [Bundle.Trivialization.continuousLinearMapAt_apply]
      change (e.linearMapAt 𝕜 ((extChartAt I x₀).symm (extChartAt I x₀ x₀)))
          (W ((extChartAt I x₀).symm (extChartAt I x₀ x₀))) =
        (e ⟨(extChartAt I x₀).symm (extChartAt I x₀ x₀),
          W ((extChartAt I x₀).symm (extChartAt I x₀ x₀))⟩).2
      rw [hcoe]
  exact hmdiff.contDiffWithinAt



omit [IsManifold I n M] in
lemma connectionEndomorphismInChart_contDiffWithinAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov n)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (x₀ : M) [IsManifold I (n + 1) M] [IsManifold I (n + 1 + 1) M] :
    ContDiffWithinAt 𝕜 n
      (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
      (Set.range I) (extChartAt I x₀ x₀) := by
  refine contDiffWithinAt_clm_of_apply (𝕜 := 𝕜) (E := E) ?_
  intro v
  exact connectionEndomorphismInChart_apply_contDiffWithinAt
    (𝕜 := 𝕜) (I := I) (M := M) (n := n) cov hcov X x₀ v

end ConnectionEndomorphism

end

end TensorLieDeriv
