import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Pointwise

noncomputable section

set_option autoImplicit false
set_option linter.style.longLine false

open Bundle Tensor0SBundle DifferentialGeometry.Integral.Connection
open scoped BigOperators Manifold ContDiff Topology

namespace DifferentialGeometry.Integral.Connection

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type _} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type _} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CovariantDerivative

omit [CompleteSpace E] in
theorem exists_contMDiffSection_eventuallyEq_tangentConstAt
    [T2Space M] (x : M) (v : TangentSpace I x) :
    ∃ V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
      (fun p : M => V p) =ᶠ[𝓝 x] tangentConstAt (I := I) x v ∧ V x = v := by
  classical
  let e := trivializationAt E (TangentSpace I) x
  let b := Module.finBasis Real E
  have he : x ∈ e.baseSet := by
    simp [e]
  have hframe := e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) b
  obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he
  let V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ∑ i, (b.repr v i) • s' i
  have hV : (fun p : M => V p) =ᶠ[𝓝 x] tangentConstAt (I := I) x v := by
    filter_upwards [hs', e.open_baseSet.mem_nhds he] with p hs'p hp
    have hbasis :
        (∑ i, (b.repr v i) • e.localFrame b i p) =
          tangentConstAt (I := I) x v p := by
      have hx_src : p ∈ (chartAt H x).source := by
        simpa [e, TangentBundle.trivializationAt_baseSet] using hp
      have hframe_apply (i) :
          e.localFrame b i p = e.symmL Real p (b i) := by
        rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) (i := i) hp]
        simp [e, Bundle.Trivialization.basisAt, Trivialization.symmL_apply]
      calc
        (∑ i, (b.repr v i) • e.localFrame b i p)
            = ∑ i, (b.repr v i) • e.symmL Real p (b i) := by
              exact Finset.sum_congr rfl (fun i _ => by rw [hframe_apply i])
        _ = e.symmL Real p (∑ i, (b.repr v i) • b i) := by
              rw [map_sum]
              simp
        _ = tangentConstAt (I := I) x v p := by
              rw [b.sum_repr]
              rfl
    calc
      V p = ∑ i, (b.repr v i) • s' i p := by
        simp [V, ContMDiffSection.finset_sum_apply_gen]
      _ = ∑ i, (b.repr v i) • e.localFrame b i p := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hs'p i]
      _ = tangentConstAt (I := I) x v p := hbasis
  refine ⟨V, hV, ?_⟩
  exact hV.self_of_nhds.trans (tangentConstAt_self (I := I) x v)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    {x : M} (X Y Z : TangentSpace I x)
    (Xs Ys Zs :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (hX : (fun p : M => Xs p) =ᶠ[𝓝 x] tangentConstAt (I := I) x X)
    (hY : (fun p : M => Ys p) =ᶠ[𝓝 x] tangentConstAt (I := I) x Y)
    (hZ : (fun p : M => Zs p) =ᶠ[𝓝 x] tangentConstAt (I := I) x Z) :
    connectionRiemannCurvatureField cov
        (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x =
      connectionRiemannCurvatureField cov
        (fun p : M => Xs p) (fun p : M => Ys p) (fun p : M => Zs p) x := by
  classical
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  have hX' : Xc =ᶠ[𝓝 x] fun p : M => Xs p := by
    simpa [Xc] using hX.symm
  have hY' : Yc =ᶠ[𝓝 x] fun p : M => Ys p := by
    simpa [Yc] using hY.symm
  have hZ' : Zc =ᶠ[𝓝 x] fun p : M => Zs p := by
    simpa [Zc] using hZ.symm
  have hXx : Xc x = Xs x := hX'.self_of_nhds
  have hYx : Yc x = Ys x := hY'.self_of_nhds
  have hbr :
      VectorField.mlieBracket I Xc Yc x =
        VectorField.mlieBracket I (fun p : M => Xs p) (fun p : M => Ys p) x := by
    exact hX'.mlieBracket_vectorField_eq (I := I) hY'
  have hZ_at :
      cov Zc x = cov (fun p : M => Zs p) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (by simpa [Zc] using mdifferentiableAt_tangentConstAt_self (I := I) x Z)
      (Zs.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      (by simp) hZ'
  let e := trivializationAt E (TangentSpace I) x
  have he : x ∈ e.baseSet := by
    simp [e]
  have hinnerY :
      (fun p : M => (cov Zc p) (Yc p)) =ᶠ[𝓝 x]
        (fun p : M => (cov (fun q : M => Zs q) p) (Ys p)) := by
    rcases mem_nhds_iff.mp (hZ' : {p : M | Zc p = Zs p} ∈ 𝓝 x) with
      ⟨U, hUsub, hUopen, hxU⟩
    filter_upwards [hUopen.mem_nhds hxU, hY', e.open_baseSet.mem_nhds he] with
      p hpU hYp hpE
    have hZp : Zc =ᶠ[𝓝 p] fun q : M => Zs q :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpU) fun q hq => hUsub hq
    have hZc_md : MDiffAt (T% Zc) p := by
      unfold Zc tangentConstAt
      exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
        (𝕜 := Real) (I := I) (x₀ := x) (p := p) Z (by simpa [e] using hpE)
    have hcovp :
        cov Zc p = cov (fun q : M => Zs q) p := by
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        hZc_md (Zs.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (by simp) hZp
    rw [hcovp, hYp]
  have hinnerX :
      (fun p : M => (cov Zc p) (Xc p)) =ᶠ[𝓝 x]
        (fun p : M => (cov (fun q : M => Zs q) p) (Xs p)) := by
    rcases mem_nhds_iff.mp (hZ' : {p : M | Zc p = Zs p} ∈ 𝓝 x) with
      ⟨U, hUsub, hUopen, hxU⟩
    filter_upwards [hUopen.mem_nhds hxU, hX', e.open_baseSet.mem_nhds he] with
      p hpU hXp hpE
    have hZp : Zc =ᶠ[𝓝 p] fun q : M => Zs q :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpU) fun q hq => hUsub hq
    have hZc_md : MDiffAt (T% Zc) p := by
      unfold Zc tangentConstAt
      exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
        (𝕜 := Real) (I := I) (x₀ := x) (p := p) Z (by simpa [e] using hpE)
    have hcovp :
        cov Zc p = cov (fun q : M => Zs q) p := by
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        hZc_md (Zs.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (by simp) hZp
    rw [hcovp, hXp]
  have hcovZY :
      cov (fun p : M => (cov Zc p) (Yc p)) x =
        cov (fun p : M => (cov (fun q : M => Zs q) p) (Ys p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (by
        simpa [Zc, Yc] using
          cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z Y)
      (cov_smooth_apply_mdiffAt (I := I) cov hcov Ys Zs x)
      (by simp) hinnerY
  have hcovZX :
      cov (fun p : M => (cov Zc p) (Xc p)) x =
        cov (fun p : M => (cov (fun q : M => Zs q) p) (Xs p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (by
        simpa [Zc, Xc] using
          cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z X)
      (cov_smooth_apply_mdiffAt (I := I) cov hcov Xs Zs x)
      (by simp) hinnerX
  have hXval : tangentConstAt (I := I) x X x = Xs x := by
    simpa [Xc] using hXx
  have hYval : tangentConstAt (I := I) x Y x = Ys x := by
    simpa [Yc] using hYx
  simp only [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField]
  rw [hcovZY, hcovZX, hZ_at, hbr]
  rw [hXval, hYval]







theorem riemannCurvatureAt_apply_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    riemannCurvatureAt cov hcov x α (vec3 (X x) (Y x) (Z x)) =
      cotangentToDual_gen α
        (connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x) := by
  obtain ⟨Xc, hXc, hXcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x (X x)
  obtain ⟨Yc, hYc, hYcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x (Y x)
  obtain ⟨Zc, hZc, hZcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x (Z x)
  have hraw :
      connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x (X x)) (tangentConstAt (I := I) x (Y x))
          (tangentConstAt (I := I) x (Z x)) x =
        connectionRiemannCurvatureField cov
          (fun p : M => Xc p) (fun p : M => Yc p) (fun p : M => Zc p) x :=
    connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst
      (I := I) cov hcov (X x) (Y x) (Z x) Xc Yc Zc hXc hYc hZc
  have hsmooth :
      connectionRiemannCurvatureField cov
          (fun p : M => Xc p) (fun p : M => Yc p) (fun p : M => Zc p) x =
        connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x :=
    connectionRiemannCurvatureField_congr_point
      (I := I) cov hcov Xc X Yc Y Zc Z hXcx hYcx hZcx
  rw [riemannCurvatureAt_apply_const]
  simpa [riemannCurvatureAux_eq_connectionRiemannCurvatureField] using
    congrArg (cotangentToDual_gen α) (hraw.trans hsmooth)



theorem riemannCurvature04At_apply_smooth
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (X Y Z W : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    riemannCurvature04At g cov hcov x (vec4 (X x) (Y x) (Z x) (W x)) =
      g.inner x (W x)
        (connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x) := by
  have h13 :=
    riemannCurvatureAt_apply_smooth (I := I) cov hcov X Y Z
      (dualToCotangent_gen (I := I) ((tangentFlatLinear_gen (I := I) g x) (W x)))
  rw [riemannCurvature04At_eq_lower_riemannCurvatureAt]
  simpa [tangentFlatLinear_apply_gen] using h13

set_option backward.isDefEq.respectTransparency false in
private theorem riemannCurvatureAt_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M] :
    letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 1 3
    letI := tensorRSBundle_fiber (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 1 3
    letI := tensorRSBundle_vector (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 1 3
    letI := tensorRSBundle_smooth (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (n := (∞ : WithTop ℕ∞)) 1 3
    ContMDiff I (I.prod 𝓘(Real, TensorRSModel 1 3 Real E)) (∞ : WithTop ℕ∞)
      (fun x : M =>
        (⟨x, riemannCurvatureAt (I := I) cov hcov x⟩ :
          TotalSpace (TensorRSModel 1 3 Real E)
            (fun x : M =>
              TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 3 x))) := by
  classical
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 1 3
  letI := tensorRSBundle_fiber (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 1 3
  letI := tensorRSBundle_vector (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 1 3
  letI := tensorRSBundle_smooth (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) (n := (∞ : WithTop ℕ∞)) 1 3
  letI : FiniteDimensional Real (TensorRSModel 1 3 Real E) := inferInstance
  intro x₀
  rw [contMDiffAt_section]
  let e := trivializationAt (TensorRSModel 1 3 Real E)
    (fun p : M => TensorRSSpace 1 3 I p) x₀
  have hx₀ : x₀ ∈ e.baseSet := by
    simpa [e] using
      (mem_baseSet_trivializationAt
        (TensorRSModel 1 3 Real E) (fun p : M => TensorRSSpace 1 3 I p) x₀)
  let G : M → TensorRSModel 1 3 Real E := fun p =>
    (e ⟨p, riemannCurvatureAt (I := I) cov hcov p⟩).2
  let d := Module.finrank Real E
  let bE : Module.Basis (Fin d) Real E := Module.finBasis Real E
  have hG : ContMDiffAt I 𝓘(Real, TensorRSModel 1 3 Real E)
      (∞ : WithTop ℕ∞) G x₀ := by
    refine contMDiffAt_tensorRSModel_of_apply_basis_eval_basis
      (I := I) (bE := bE) (G := G) (x₀ := x₀)
      (n := (∞ : WithTop ℕ∞)) ?_
    intro ρ σ
    let eTan := trivializationAt E (TangentSpace I : M → Type _) x₀
    let βρ : Tensor0SModel 1 Real E :=
      (continuousMultilinearMap_basis (𝕜 := Real) (F := E) bE 1) ρ
    let βsec : (p : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 1 p :=
      fun p : M => Tensor0SSpace.constInChart
        (𝕜 := Real) (I := I) (M := M) 1 x₀ βρ p
    let vσ : Fin 3 → E := fun a => bE (σ a)
    have hx₀Tan : x₀ ∈ eTan.baseSet := by
      dsimp [eTan]
      exact mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀
    have hframe := eTan.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) bE
    obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd eTan.open_baseSet hx₀Tan
    let Xs : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) := s' (σ 0)
    let Ys : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) := s' (σ 1)
    let Zs : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) := s' (σ 2)
    let Rsec : (p : M) → TangentSpace I p := fun p : M =>
      connectionRiemannCurvatureField cov
        (fun q : M => Xs q) (fun q : M => Ys q) (fun q : M => Zs q) p
    have hβ : ContMDiffAt I (I.prod 𝓘(Real, Tensor0SModel 1 Real E))
        (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, βsec p⟩ :
            TotalSpace (Tensor0SModel 1 Real E)
              (fun p : M => Tensor0SSpace 1 I p))) x₀ := by
      simpa [βsec] using
        tensor0SConstInChart_contMDiffAt
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) x₀ βρ
    have hR : ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, Rsec p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ := by
      simpa [Rsec] using
        curvField_contMDiffAt (I := I) cov hcov Xs Ys Zs x₀
    have hscalar : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun p : M => cotangentToDual_gen (I := I) (βsec p) (Rsec p)) x₀ := by
      have hEval := TensorMultilinear.contMDiffAt_section_apply_gen
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := 1) (x₀ := x₀) (T := βsec) hβ
        (v := fun _ : Fin 1 => Rsec) (fun _ => hR)
      simpa [cotangentToDual_apply_gen] using hEval
    refine hscalar.congr_of_eventuallyEq ?_
    filter_upwards [eTan.open_baseSet.mem_nhds hx₀Tan, hs'] with p hpTan hs'p
    have hbasis : ∀ i : Fin d,
        eTan.symmL Real p (bE i) = eTan.basisAt bE hpTan i := by
      intro i
      simp [Bundle.Trivialization.basisAt, Trivialization.symmL_apply]
    have hslots :
        (fun a : Fin 3 => eTan.symmL Real p (vσ a)) =
          vec3 (I := I) (Xs p) (Ys p) (Zs p) := by
      funext a
      fin_cases a <;>
        simp [vec3, Xs, Ys, Zs, vσ, eTan,
          hs'p (σ 0), hs'p (σ 1), hs'p (σ 2),
          hbasis,
          Bundle.Trivialization.localFrame_apply_of_mem_baseSet
            (e := eTan) (b := bE) (i := σ 0) hpTan,
          Bundle.Trivialization.localFrame_apply_of_mem_baseSet
            (e := eTan) (b := bE) (i := σ 1) hpTan,
          Bundle.Trivialization.localFrame_apply_of_mem_baseSet
            (e := eTan) (b := bE) (i := σ 2) hpTan]
    have hcoord := TensorRSSpace.trivializationAt_basis_coord
      (𝕜 := Real) (I := I) (x₀ := x₀) (x := p)
      (bE := bE) (r := 1) (s := 3) hpTan
      (riemannCurvatureAt (I := I) cov hcov p) ρ σ
    have hsmooth :=
      riemannCurvatureAt_apply_smooth (I := I) cov hcov Xs Ys Zs
        (βsec p)
    calc
      G p ((continuousMultilinearMap_basis (𝕜 := Real) (F := E) bE 1) ρ)
          (fun a : Fin 3 => bE (σ a))
          =
        (riemannCurvatureAt (I := I) cov hcov p (βsec p))
          (fun a : Fin 3 => eTan.symmL Real p (vσ a)) := by
          simpa [G, e, eTan, βρ, βsec, vσ] using hcoord
      _ = riemannCurvatureAt (I := I) cov hcov p (βsec p)
          (vec3 (I := I) (Xs p) (Ys p) (Zs p)) := by
          rw [hslots]
      _ = cotangentToDual_gen (I := I) (βsec p) (Rsec p) := by
          simpa [Rsec] using hsmooth
  simpa [G, e] using hG

set_option backward.isDefEq.respectTransparency false in






noncomputable def rm13Section
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M] :
    Tensor13Section (I := I) (M := M) :=
  by
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      simpa using (inferInstance : IsManifold I ∞ M)
    exact
      ⟨fun x => riemannCurvatureAt cov hcov x,
        riemannCurvatureAt_contMDiff (I := I) cov hcov⟩

@[simp]
theorem rm13Section_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (x : M) :
    rm13Section (I := I) (M := M) cov hcov x =
      riemannCurvatureAt cov hcov x := by
  rfl

@[simp]
theorem rm13Section_apply_const
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
    rm13Section (I := I) (M := M) cov hcov x α (vec3 X Y Z) =
      cotangentToDual_gen α
        (connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := by
  rw [rm13Section_apply, riemannCurvatureAt_apply_const]
  rfl








theorem rm13Section_apply_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    rm13Section (I := I) (M := M) cov hcov x α (vec3 (X x) (Y x) (Z x)) =
      cotangentToDual_gen α
        (connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x) := by
  rw [rm13Section_apply]
  exact riemannCurvatureAt_apply_smooth (I := I) cov hcov X Y Z α

set_option backward.isDefEq.respectTransparency false in
private theorem riemannCurvature04At_contMDiff
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M] :
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 4
    ContMDiff I (I.prod 𝓘(Real, Tensor0SModel 4 Real E)) (∞ : WithTop ℕ∞)
      (fun x : M =>
        (⟨x, riemannCurvature04At (I := I) g cov hcov x⟩ :
          TotalSpace (Tensor0SModel 4 Real E)
            (fun x : M =>
          Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x))) := by
  classical
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 4
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞))
  let d := Module.finrank Real E
  let b : Module.Basis (Fin d) Real E := Module.finBasis Real E
  let F : (p : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 p :=
    fun p : M => riemannCurvature04At (I := I) g cov hcov p
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  let eTan := trivializationAt E (TangentSpace I : M → Type _) x₀
  have hx₀Tan : x₀ ∈ eTan.baseSet := by
    dsimp [eTan]
    exact mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀
  have hframe := eTan.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) b
  obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd eTan.open_baseSet hx₀Tan
  let Xs : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := s' (σ 0)
  let Ys : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := s' (σ 1)
  let Zs : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := s' (σ 2)
  let Ws : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := s' (σ 3)
  let Rsec : (p : M) → TangentSpace I p := fun p : M =>
    connectionRiemannCurvatureField cov
      (fun q : M => Xs q) (fun q : M => Ys q) (fun q : M => Zs q) p
  have hW : ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
      (fun p : M => (⟨p, Ws p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ :=
    Ws.contMDiff.contMDiffAt
  have hR : ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
      (fun p : M => (⟨p, Rsec p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ := by
    simpa [Rsec] using
      curvField_contMDiffAt (I := I) cov hcov Xs Ys Zs x₀
  have hscalar : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : M => g.inner p (Ws p) (Rsec p)) x₀ :=
    metric_inner_contMDiffAt (I := I) g hW hR (by simp)
  refine hscalar.congr_of_eventuallyEq ?_
  filter_upwards [eTan.open_baseSet.mem_nhds hx₀Tan, hs'] with p hpTan hs'p
  have hbasis : ∀ i : Fin d,
      eTan.symmL Real p (b i) = eTan.basisAt b hpTan i := by
    intro i
    simp [Bundle.Trivialization.basisAt, Trivialization.symmL_apply]
  have hslots :
      (fun a : Fin 4 => eTan.symmL Real p (b (σ a))) =
        vec4 (I := I) (Xs p) (Ys p) (Zs p) (Ws p) := by
    funext a
    fin_cases a <;>
      simp [vec4, Ws, Xs, Ys, Zs,
        hs'p (σ 0), hs'p (σ 1), hs'p (σ 2), hs'p (σ 3), hbasis,
        Bundle.Trivialization.localFrame_apply_of_mem_baseSet
          (e := eTan) (b := b) (i := σ 0) hpTan,
        Bundle.Trivialization.localFrame_apply_of_mem_baseSet
          (e := eTan) (b := b) (i := σ 1) hpTan,
        Bundle.Trivialization.localFrame_apply_of_mem_baseSet
          (e := eTan) (b := b) (i := σ 2) hpTan,
        Bundle.Trivialization.localFrame_apply_of_mem_baseSet
          (e := eTan) (b := b) (i := σ 3) hpTan]
  rw [continuousMultilinearMap_basis_repr]
  change ((trivializationAt (Tensor0SModel 4 Real E)
      (Bundle.continuousMultilinearMap Real 4 E (TangentSpace I : M → Type _)) x₀
      ⟨p, F p⟩).2)
      (fun a : Fin 4 => b (σ a)) =
    g.inner p (Ws p) (Rsec p)
  change (F p).compContinuousLinearMap
      (fun _ : Fin 4 =>
        (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL Real p)
      (fun a : Fin 4 => b (σ a)) =
    g.inner p (Ws p) (Rsec p)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, hslots]
  simpa [F, Rsec] using
    riemannCurvature04At_apply_smooth (I := I) g cov hcov Xs Ys Zs Ws p

set_option backward.isDefEq.respectTransparency false in


noncomputable def rm04Section
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M] :
    Tensor04Section (I := I) (M := M) :=
  ⟨fun x => riemannCurvature04At g cov hcov x,
    riemannCurvature04At_contMDiff (I := I) g cov hcov⟩

@[simp]
theorem rm04Section_apply
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (x : M) :
    rm04Section (I := I) (M := M) g cov hcov x =
      riemannCurvature04At g cov hcov x := by
  rfl

@[simp]
theorem rm04Section_apply_const
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    {x : M}
    (X Y Z W : TangentSpace I x) :
    rm04Section (I := I) (M := M) g cov hcov x (vec4 X Y Z W) =
      g.inner x W
        (connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := by
  rw [rm04Section_apply, riemannCurvature04At_apply_const]
  rfl


theorem rm04Section_apply_smooth
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (X Y Z W : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    rm04Section (I := I) (M := M) g cov hcov x
        (vec4 (X x) (Y x) (Z x) (W x)) =
      g.inner x (W x)
        (connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x) := by
  rw [rm04Section_apply]
  exact riemannCurvature04At_apply_smooth (I := I) g cov hcov X Y Z W x

set_option backward.isDefEq.respectTransparency false in

noncomputable def ricciSection
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M] :
    Tensor02Section (I := I) (M := M) :=
  by
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      simpa using (inferInstance : IsManifold I ∞ M)
    exact tensorRSField_applyInput (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞
      (contract_TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := ∞) 0 2 (rm13Section (I := I) (M := M) cov hcov))
      (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞)

@[simp]
theorem ricciSection_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (x : M) :
    ricciSection (I := I) (M := M) cov hcov x =
      ricciCurvatureAt cov hcov x := by
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have hone :
      Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ x =
        scalarOne0S (I := I) x := by
    apply Tensor0SSpace.toModel_injective
    refine ContinuousMultilinearMap.ext fun v => ?_
    rw [Tensor0SField.one0_apply (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := ∞) x v]
    change (1 : Real) =
      (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => E) 1) v
    simp
  simp [ricciSection, ricciCurvatureAt, ricciFromRm13At, contract_TensorRSField,
    contract_TensorRSField_fun, hone]

@[simp]
theorem ricciSection_eq_trace
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (x : M) :
    ricciSection (I := I) (M := M) cov hcov x =
      ricciFromRm13At (I := I) (M := M)
        (rm13Section (I := I) (M := M) cov hcov x) := by
  rw [ricciSection_apply, rm13Section_apply, ricciCurvatureAt_eq_trace]

end CovariantDerivative

end DifferentialGeometry.Integral.Connection
