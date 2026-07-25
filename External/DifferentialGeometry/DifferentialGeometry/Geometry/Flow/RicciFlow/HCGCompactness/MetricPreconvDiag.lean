import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ComponentConvTower
import DifferentialGeometry.Geometry.Metric.SmoothMetricFromCoeff

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false














noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness
























theorem exists_diag_subseq
    (P : ℕ → (ℕ → ℕ) → Prop)
    (hstep : ∀ n : ℕ, ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P n (φ ∘ ψ))
    (hsub : ∀ n : ℕ, ∀ φ ψ : ℕ → ℕ, StrictMono ψ → P n φ → P n (φ ∘ ψ))
    (hextend : ∀ n : ℕ, ∀ φ : ℕ → ℕ, ∀ m : ℕ,
      P n (fun k => φ (k + m)) → P n φ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n : ℕ, P n φ := by
  classical

  let G : ℕ → {φ : ℕ → ℕ // StrictMono φ} := fun n =>
    Nat.rec ⟨id, strictMono_id⟩
      (fun m Gm => ⟨Gm.1 ∘ (hstep m Gm.1 Gm.2).choose,
        Gm.2.comp (hstep m Gm.1 Gm.2).choose_spec.1⟩) n
  set Gf : ℕ → (ℕ → ℕ) := fun n => (G n).1 with hGfdef
  have hGmono : ∀ n, StrictMono (Gf n) := fun n => (G n).2
  set ρ : ℕ → (ℕ → ℕ) := fun n => (hstep n (Gf n) (hGmono n)).choose with hρdef
  have hρmono : ∀ n, StrictMono (ρ n) := fun n => (hstep n (Gf n) (hGmono n)).choose_spec.1
  have hGstep : ∀ n, Gf (n + 1) = Gf n ∘ ρ n := fun n => rfl
  have hGP : ∀ n, P n (Gf (n + 1)) := fun n => by
    rw [hGstep]; exact (hstep n (Gf n) (hGmono n)).choose_spec.2
  set φ : ℕ → ℕ := fun n => Gf (n + 1) n with hφdef
  refine ⟨φ, ?_, ?_⟩
  ·
    apply strictMono_nat_of_lt_succ
    intro n
    have h1 : φ (n + 1) = Gf (n + 1) (ρ (n + 1) (n + 1)) := by
      show Gf (n + 2) (n + 1) = Gf (n + 1) (ρ (n + 1) (n + 1))
      rw [hGstep (n + 1)]; rfl
    show φ n < φ (n + 1)
    rw [h1]
    exact hGmono (n + 1) ((Nat.lt_succ_self n).trans_le (hρmono (n + 1)).le_apply)
  ·
    intro n

    let Q : ℕ → (ℕ → ℕ) := fun m =>
      Nat.rec id (fun j Qj => Qj ∘ ρ (n + 1 + j)) m
    have hQstep : ∀ m, Q (m + 1) = Q m ∘ ρ (n + 1 + m) := fun m => rfl
    have hQmono : ∀ m, StrictMono (Q m) := by
      intro m
      induction m with
      | zero => exact strictMono_id
      | succ j ih => exact ih.comp (hρmono (n + 1 + j))
    have hGcomp : ∀ m, Gf (n + 1 + m) = Gf (n + 1) ∘ Q m := by
      intro m
      induction m with
      | zero => rfl
      | succ j ih =>
        show Gf (n + 1 + j) ∘ ρ (n + 1 + j) = Gf (n + 1) ∘ Q (j + 1)
        rw [ih, hQstep]
        rfl

    set τ : ℕ → ℕ := fun m => Q m (n + m) with hτdef
    have hτmono : StrictMono τ := by
      apply strictMono_nat_of_lt_succ
      intro m
      show Q m (n + m) < Q (m + 1) (n + (m + 1))
      rw [hQstep]
      show Q m (n + m) < Q m (ρ (n + 1 + m) (n + (m + 1)))
      apply hQmono m
      exact (Nat.lt_succ_self (n + m)).trans_le
        (by rw [show n + (m + 1) = (n + m) + 1 from by ring]; exact (hρmono (n + 1 + m)).le_apply)
    have htail : (fun m => φ (n + m)) = Gf (n + 1) ∘ τ := by
      funext m
      show φ (n + m) = Gf (n + 1) (Q m (n + m))
      show Gf (n + m + 1) (n + m) = Gf (n + 1) (Q m (n + m))
      rw [show n + m + 1 = n + 1 + m from by ring, hGcomp m]
      rfl
    have hPtail : P n (fun m => φ (n + m)) := by
      rw [htail]; exact hsub n (Gf (n + 1)) τ hτmono (hGP n)
    refine hextend n φ n ?_
    have hcomm : (fun k => φ (k + n)) = (fun m => φ (n + m)) := by
      funext k; rw [Nat.add_comm]
    rw [hcomm]; exact hPtail



section Realization

open scoped Manifold ContDiff Topology
open Bundle Tensor0SBundle TensorLieDeriv
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]




omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
lemma frameVec_eq_tangentConst (x₀ : M) (i : Fin (Module.finrank Real E)) :
    Geometry.frameVec (I := I) x₀ i
      = tangentConstInChart (𝕜 := Real) (I := I) x₀ (Module.finBasis Real E i) := rfl







lemma exists_tendsto_clm_of_basis_eval {W : Type*} [NormedAddCommGroup W] [NormedSpace Real W]
    [FiniteDimensional Real W] {n : ℕ} (b : Module.Basis (Fin n) Real W)
    (L : ℕ → (W →L[Real] W →L[Real] Real))
    (h : ∀ i j : Fin n, ∃ cij : Real,
      Filter.Tendsto (fun k => L k (b i) (b j)) Filter.atTop (nhds cij)) :
    ∃ Linf : W →L[Real] W →L[Real] Real, Filter.Tendsto L Filter.atTop (nhds Linf) := by
  classical
  choose cval hcval using h
  set ev : (W →L[Real] W →L[Real] Real) →ₗ[Real] (Fin n × Fin n → Real) :=
    { toFun := fun φ p => φ (b p.1) (b p.2)
      map_add' := by intro φ ψ; funext p; simp
      map_smul' := by intro c φ; funext p; simp } with hevdef
  have hker : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro φ hφ
    have hzero : ∀ i j, φ (b i) (b j) = 0 := by
      intro i j; have := congrFun hφ (i, j); simpa [ev] using this
    have hcoe : φ.toLinearMap = 0 := by
      apply Module.Basis.ext b
      intro i
      have hrow : (φ (b i)).toLinearMap = 0 := by
        apply Module.Basis.ext b
        intro j
        simpa using hzero i j
      have : φ (b i) = 0 := by
        ext w; have := LinearMap.congr_fun hrow w; simpa using this
      simpa using this
    ext v w
    have hv : φ v = 0 := by
      have := LinearMap.congr_fun hcoe v
      simpa using this
    rw [hv]; simp
  have hcemb := LinearMap.isClosedEmbedding_of_injective (f := ev) hker
  have htpi : Filter.Tendsto (fun k => ev (L k)) Filter.atTop (nhds (fun p => cval p.1 p.2)) := by
    rw [tendsto_pi_nhds]; rintro ⟨i, j⟩; exact hcval i j
  have hmem : (fun p => cval p.1 p.2) ∈ Set.range ev :=
    hcemb.isClosed_range.mem_of_tendsto htpi
      (Filter.Eventually.of_forall fun k => ⟨L k, rfl⟩)
  obtain ⟨Linf, hLinf⟩ := hmem
  refine ⟨Linf, ?_⟩
  rw [hcemb.isEmbedding.tendsto_nhds_iff, hLinf]
  exact htpi

include I in





omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
lemma exists_chart_cover (hne : Nonempty M) :
    ∃ (c : ℕ → M) (K : ℕ → Set M),
      (∀ k, IsCompact (K k)) ∧ (∀ k, K k ⊆ (chartAt H (c k)).source) ∧
      (∀ x : M, ∃ k, x ∈ K k) := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have hcov : ∀ x : M, ∃ S, IsCompact S ∧ x ∈ interior S ∧ S ⊆ (chartAt H x).source :=
    fun x => exists_compact_subset (chartAt H x).open_source (mem_chart_source H x)
  choose Kf hKc hKint hKsub using hcov
  obtain ⟨s, hscount, hscov⟩ :=
    (isLindelof_univ (X := M)).elim_countable_subcover (fun x => interior (Kf x))
      (fun _ => isOpen_interior) (fun x _ => Set.mem_iUnion.2 ⟨x, hKint x⟩)
  have hsne : s.Nonempty := by
    obtain ⟨x0⟩ := hne
    obtain ⟨y, hy, -⟩ := Set.mem_iUnion₂.1 (hscov (Set.mem_univ x0))
    exact ⟨y, hy⟩
  obtain ⟨c, hcrange⟩ := hscount.exists_eq_range hsne
  refine ⟨c, fun k => Kf (c k), fun k => hKc (c k), fun k => hKsub (c k), ?_⟩
  intro x
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hscov (Set.mem_univ x))
  rw [hcrange] at hy
  obtain ⟨k, rfl⟩ := hy
  exact ⟨k, interior_subset hxy⟩

include I in




omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
lemma exists_gm_symm_pos
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M) (φ : ℕ → ℕ)
    (hconv : ∀ x : M, ∃ Lx : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real,
      Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop (nhds Lx))
    (hlow : ∃ c : Real, 0 < c ∧ ∀ (k : ℕ) (x : M) (v : TangentSpace I x),
      c * gRef.inner x v v ≤ (gSeq k).inner x v v) :
    ∃ gm : Π x : M, TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real,
      (∀ x, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop (nhds (gm x))) ∧
      (∀ (x : M) (v w : TangentSpace I x), gm x v w = gm x w v) ∧
      (∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < gm x v v) := by
  classical
  set gm : Π x : M, TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real :=
    fun x => (hconv x).choose with hgmdef
  have hgm : ∀ x, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop (nhds (gm x)) :=
    fun x => (hconv x).choose_spec
  have hev : ∀ (x : M) (a b : TangentSpace I x),
      Filter.Tendsto (fun m => (gSeq (φ m)).inner x a b) Filter.atTop (nhds (gm x a b)) := by
    intro x a b
    have hcont : Continuous
        (fun ψ : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real => ψ a b) :=
      ((ContinuousLinearMap.apply Real Real b).comp
        (ContinuousLinearMap.apply Real (TangentSpace I x →L[Real] Real) a)).continuous
    exact (hcont.tendsto (gm x)).comp (hgm x)
  refine ⟨gm, hgm, ?_, ?_⟩
  · intro x v w
    have h1 := hev x v w
    have h2 := hev x w v
    have heq : (fun m => (gSeq (φ m)).inner x v w) = (fun m => (gSeq (φ m)).inner x w v) := by
      funext m; exact (gSeq (φ m)).symm x v w
    rw [heq] at h1
    exact tendsto_nhds_unique h1 h2
  · obtain ⟨c, hc, hcle⟩ := hlow
    intro x v hv
    have hle : c * gRef.inner x v v ≤ gm x v v :=
      ge_of_tendsto (hev x v v) (Filter.Eventually.of_forall (fun m => hcle (φ m) x v))
    exact lt_of_lt_of_le (mul_pos hc (gRef.pos x v hv)) hle


omit [I.Boundaryless] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
lemma covDerivOfField_zero (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2) :
    covDerivOfField (I := I) gRef A0 0 = A0 := rfl

include I in




omit [IsManifold I 2 M] in
lemma exists_engine_frameConv
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (i j : Fin (Module.finrank Real E)) (φ : ℕ → ℕ) :
    ∃ (ψ : ℕ → ℕ) (Φinf : E → Real), StrictMono ψ ∧ ContDiff Real (∞ : WithTop ℕ∞) Φinf ∧
      ∀ x ∈ K₀, Filter.Tendsto (fun m => (gSeq (φ (ψ m))).inner x
        (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x))
        Filter.atTop (nhds (Φinf (extChartAt I x₀ x))) := by
  obtain ⟨σi, hσi⟩ :=
    exists_section_eqOn_compact (I := I) x₀ (Module.finBasis Real E i) hK₀ hK₀chart
  obtain ⟨σj, hσj⟩ :=
    exists_section_eqOn_compact (I := I) x₀ (Module.finBasis Real E j) hK₀ hK₀chart
  have hbdd' : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q ((gSeq ∘ φ) k) gRef z ≤ C := by
    intro q K hK; obtain ⟨C, hC⟩ := hbdd q K hK; exact ⟨C, fun k z hz => hC (φ k) z hz⟩
  obtain ⟨ψ, Φinf, χ, hψ, hΦinf, hχ1, hconv⟩ :=
    exists_chart_cInfConv (I := I) gRef (gSeq ∘ φ) hbdd' x₀ ![σi, σj] hK₀ hK₀chart
  refine ⟨ψ, Φinf, hψ, hΦinf, fun x hx => ?_⟩
  have htend := tendsto_of_cInf hconv (Set.mem_univ (extChartAt I x₀ x))
  have hxsrc : x ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source]; exact hK₀chart hx
  have hxi : σi x = Geometry.frameVec (I := I) x₀ i x :=
    (hσi.self_of_nhdsSet x hx).trans (congrFun (frameVec_eq_tangentConst (I := I) x₀ i).symm x)
  have hxj : σj x = Geometry.frameVec (I := I) x₀ j x :=
    (hσj.self_of_nhdsSet x hx).trans (congrFun (frameVec_eq_tangentConst (I := I) x₀ j).symm x)
  have hfun : (fun m => χ (extChartAt I x₀ x) * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef
          (Tensor0SBundle.metricTensorField (I := I) ((gSeq ∘ φ) (ψ m))) 0) w
            (fun a => (![σi, σj] : Fin 2 → _) a w)) (extChartAt I x₀ x))
      = (fun m => (gSeq (φ (ψ m))).inner x
          (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x)) := by
    funext m
    rw [hχ1 x hx, one_mul, writtenInExtChartAt_real_apply,
      PartialEquiv.left_inv _ hxsrc, covDerivOfField_zero,
      Tensor0SBundle.metricTensorField_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Function.comp_apply]
    rw [hxi, hxj]
  rw [hfun] at htend
  exact htend

include I in

omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
lemma exists_frame_refs
    (gBase : SmoothRiemannianMetric I M)
    (gRef : ℕ → SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ r q : ℕ, q ≤ r → ∀ K : Set M, IsCompact K → ∃ C : Real,
      ∀ k : ℕ, ∀ z ∈ K, metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C)
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (i j : Fin (Module.finrank Real E)) (φ : ℕ → ℕ) :
    ∃ (ψ : ℕ → ℕ) (Φinf : E → Real), StrictMono ψ ∧ ContDiff Real (∞ : WithTop ℕ∞) Φinf ∧
      ∀ x ∈ K₀, Filter.Tendsto (fun m => (gSeq (φ (ψ m))).inner x
        (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x))
        Filter.atTop (nhds (Φinf (extChartAt I x₀ x))) := by
  obtain ⟨σi, hσi⟩ :=
    exists_section_eqOn_compact (I := I) x₀ (Module.finBasis Real E i) hK₀ hK₀chart
  obtain ⟨σj, hσj⟩ :=
    exists_section_eqOn_compact (I := I) x₀ (Module.finBasis Real E j) hK₀ hK₀chart
  have hbdd' : ∀ r q : ℕ, q ≤ r → ∀ K : Set M, IsCompact K → ∃ C : Real,
      ∀ k : ℕ, ∀ z ∈ K,
        metricCovDerivNorm (I := I) q ((gSeq ∘ φ) k) (gRef r) z ≤ C := by
    intro r q hqr K hK
    obtain ⟨C, hC⟩ := hbdd r q hqr K hK
    exact ⟨C, fun k z hz => hC (φ k) z hz⟩
  obtain ⟨ψ, Φinf, χ, hψ, hΦinf, hχ1, hconv⟩ :=
    exists_chart_refs (I := I) gBase gRef (gSeq ∘ φ) hbdd' x₀ ![σi, σj] hK₀ hK₀chart
  refine ⟨ψ, Φinf, hψ, hΦinf, fun x hx => ?_⟩
  have htend := tendsto_of_cInf hconv (Set.mem_univ (extChartAt I x₀ x))
  have hxsrc : x ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source]
    exact hK₀chart hx
  have hxi : σi x = Geometry.frameVec (I := I) x₀ i x :=
    (hσi.self_of_nhdsSet x hx).trans
      (congrFun (frameVec_eq_tangentConst (I := I) x₀ i).symm x)
  have hxj : σj x = Geometry.frameVec (I := I) x₀ j x :=
    (hσj.self_of_nhdsSet x hx).trans
      (congrFun (frameVec_eq_tangentConst (I := I) x₀ j).symm x)
  have hfun : (fun m => χ (extChartAt I x₀ x) * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gBase
          (Tensor0SBundle.metricTensorField (I := I) ((gSeq ∘ φ) (ψ m))) 0) w
            (fun a => (![σi, σj] : Fin 2 → _) a w)) (extChartAt I x₀ x))
      = (fun m => (gSeq (φ (ψ m))).inner x
          (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x)) := by
    funext m
    rw [hχ1 x hx, one_mul, writtenInExtChartAt_real_apply,
      PartialEquiv.left_inv _ hxsrc, covDerivOfField_zero,
      Tensor0SBundle.metricTensorField_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Function.comp_apply]
    rw [hxi, hxj]
  rw [hfun] at htend
  exact htend

include I in







omit [IsManifold I 2 M] in
lemma exists_engine_frameCInfConv
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (i j : Fin (Module.finrank Real E)) (φ : ℕ → ℕ) :
    ∃ (ψ : ℕ → ℕ) (Φinf χ : E → Real)
      (σi σj : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      StrictMono ψ ∧ ContDiff Real (∞ : WithTop ℕ∞) Φinf ∧
      (∀ x ∈ K₀, σi x = Geometry.frameVec (I := I) x₀ i x) ∧
      (∀ x ∈ K₀, σj x = Geometry.frameVec (I := I) x₀ j x) ∧
      (∀ x ∈ K₀, χ (extChartAt I x₀ x) = 1) ∧
      MapCInfConvOnCompacts (Set.univ : Set E)
        (fun k => fun x : E => χ x * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (gSeq (φ (ψ k))).inner w (σi w) (σj w)) x) Φinf := by
  obtain ⟨σi, hσi⟩ :=
    exists_section_eqOn_compact (I := I) x₀ (Module.finBasis Real E i) hK₀ hK₀chart
  obtain ⟨σj, hσj⟩ :=
    exists_section_eqOn_compact (I := I) x₀ (Module.finBasis Real E j) hK₀ hK₀chart
  have hbdd' : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q ((gSeq ∘ φ) k) gRef z ≤ C := by
    intro q K hK; obtain ⟨C, hC⟩ := hbdd q K hK; exact ⟨C, fun k z hz => hC (φ k) z hz⟩
  obtain ⟨ψ, Φinf, χ, hψ, hΦinf, hχ1, hconv⟩ :=
    exists_chart_cInfConv (I := I) gRef (gSeq ∘ φ) hbdd' x₀ ![σi, σj] hK₀ hK₀chart
  have hxi : ∀ x ∈ K₀, σi x = Geometry.frameVec (I := I) x₀ i x := fun x hx =>
    (hσi.self_of_nhdsSet x hx).trans (congrFun (frameVec_eq_tangentConst (I := I) x₀ i).symm x)
  have hxj : ∀ x ∈ K₀, σj x = Geometry.frameVec (I := I) x₀ j x := fun x hx =>
    (hσj.self_of_nhdsSet x hx).trans (congrFun (frameVec_eq_tangentConst (I := I) x₀ j).symm x)
  have hinner : ∀ (g : SmoothRiemannianMetric I M) (w : M),
      (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) g) 0) w
          (fun a => (![σi, σj] : Fin 2 → _) a w)
        = g.inner w (σi w) (σj w) := by
    intro g w
    rw [covDerivOfField_zero, Tensor0SBundle.metricTensorField_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [hinner, Function.comp_apply] at hconv
  exact ⟨ψ, Φinf, χ, σi, σj, hψ, hΦinf, hxi, hxj, hχ1, hconv⟩

include I in






omit [IsManifold I 2 M] in
lemma exists_engine_frameCInfConv_eq_gm
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (φ : ℕ → ℕ)
    (gm : Π x : M, TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real)
    (hgm : ∀ x, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop (nhds (gm x)))
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (i j : Fin (Module.finrank Real E)) :
    ∃ (ψ : ℕ → ℕ) (Φinf χ : E → Real)
      (σi σj : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      StrictMono ψ ∧ ContDiff Real (∞ : WithTop ℕ∞) Φinf ∧
      (∀ x ∈ K₀, σi x = Geometry.frameVec (I := I) x₀ i x) ∧
      (∀ x ∈ K₀, σj x = Geometry.frameVec (I := I) x₀ j x) ∧
      (∀ x ∈ K₀, χ (extChartAt I x₀ x) = 1) ∧
      (∀ x ∈ K₀, Φinf (extChartAt I x₀ x)
        = gm x (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x)) ∧
      MapCInfConvOnCompacts (Set.univ : Set E)
        (fun k => fun x : E => χ x * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (gSeq (φ (ψ k))).inner w (σi w) (σj w)) x) Φinf := by
  obtain ⟨ψ, Φinf, χ, σi, σj, hψ, hΦinf, hxi, hxj, hχ1, hconv⟩ :=
    exists_engine_frameCInfConv (I := I) gRef gSeq hbdd x₀ hK₀ hK₀chart i j φ
  refine ⟨ψ, Φinf, χ, σi, σj, hψ, hΦinf, hxi, hxj, hχ1, fun x hx => ?_, hconv⟩
  have hxsrc : x ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hK₀chart hx
  have hA : Filter.Tendsto (fun k => (gSeq (φ (ψ k))).inner x
      (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x))
      Filter.atTop (nhds (Φinf (extChartAt I x₀ x))) := by
    have htend := tendsto_of_cInf hconv (Set.mem_univ (extChartAt I x₀ x))
    have hfun : (fun k => χ (extChartAt I x₀ x) * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (gSeq (φ (ψ k))).inner w (σi w) (σj w)) (extChartAt I x₀ x))
        = (fun k => (gSeq (φ (ψ k))).inner x
            (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x)) := by
      funext k
      rw [hχ1 x hx, one_mul, writtenInExtChartAt_real_apply, PartialEquiv.left_inv _ hxsrc,
        hxi x hx, hxj x hx]
    rw [hfun] at htend; exact htend
  have hcont : Continuous (fun η : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real =>
      η (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x)) :=
    ((ContinuousLinearMap.apply Real Real (Geometry.frameVec (I := I) x₀ j x)).comp
      (ContinuousLinearMap.apply Real (TangentSpace I x →L[Real] Real)
        (Geometry.frameVec (I := I) x₀ i x))).continuous
  have hB := ((hcont.tendsto (gm x)).comp (hgm x)).comp hψ.tendsto_atTop
  exact (tendsto_nhds_unique hB hA).symm

include I in


omit [IsManifold I 2 M] in
lemma exists_refine_componentConv
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (i j : Fin (Module.finrank Real E)) (φ : ℕ → ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ x ∈ K₀, ∃ L : Real,
      Filter.Tendsto (fun m => (gSeq (φ (ψ m))).inner x
        (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x))
        Filter.atTop (nhds L) := by
  obtain ⟨ψ, Φinf, hψ, _, hconv⟩ :=
    exists_engine_frameConv (I := I) gRef gSeq hbdd x₀ hK₀ hK₀chart i j φ
  exact ⟨ψ, hψ, fun x hx => ⟨Φinf (extChartAt I x₀ x), hconv x hx⟩⟩

include I in

omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
lemma exists_comp_refs
    (gBase : SmoothRiemannianMetric I M)
    (gRef : ℕ → SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ r q : ℕ, q ≤ r → ∀ K : Set M, IsCompact K → ∃ C : Real,
      ∀ k : ℕ, ∀ z ∈ K, metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C)
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (i j : Fin (Module.finrank Real E)) (φ : ℕ → ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ x ∈ K₀, ∃ L : Real,
      Filter.Tendsto (fun m => (gSeq (φ (ψ m))).inner x
        (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x))
        Filter.atTop (nhds L) := by
  obtain ⟨ψ, Φinf, hψ, _, hconv⟩ :=
    exists_frame_refs (I := I) gBase gRef gSeq hbdd x₀ hK₀ hK₀chart i j φ
  exact ⟨ψ, hψ, fun x hx => ⟨Φinf (extChartAt I x₀ x), hconv x hx⟩⟩

include I in



omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [IsManifold I 2 M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
lemma exists_frameVec_basis (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet) :
    ∃ b : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x),
      ∀ i, b i = Geometry.frameVec (I := I) x₀ i x := by
  refine ⟨(Module.finBasis Real E).map
    ((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt Real x
      hx).symm.toLinearEquiv, fun i => ?_⟩
  rw [Module.Basis.map_apply]
  rfl

include I in



omit [IsManifold I 2 M] in
lemma exists_refine_allComponents
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (φ : ℕ → ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ i j : Fin (Module.finrank Real E), ∀ x ∈ K₀,
      ∃ L : Real, Filter.Tendsto (fun m => (gSeq (φ (ψ m))).inner x
        (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x))
        Filter.atTop (nhds L) := by
  have key : ∀ s : Finset (Fin (Module.finrank Real E) × Fin (Module.finrank Real E)),
      ∀ φ' : ℕ → ℕ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ p ∈ s, ∀ x ∈ K₀, ∃ L : Real,
        Filter.Tendsto (fun m => (gSeq (φ' (ψ m))).inner x
          (Geometry.frameVec (I := I) x₀ p.1 x) (Geometry.frameVec (I := I) x₀ p.2 x))
          Filter.atTop (nhds L) := by
    intro s
    induction s using Finset.induction with
    | empty => exact fun φ' => ⟨id, strictMono_id, by simp⟩
    | @insert p s hps ih =>
      intro φ'
      obtain ⟨ψ₀, hψ₀, hs⟩ := ih φ'
      obtain ⟨ψ₁, hψ₁, hp⟩ :=
        exists_refine_componentConv (I := I) gRef gSeq hbdd x₀ hK₀ hK₀chart p.1 p.2 (φ' ∘ ψ₀)
      refine ⟨ψ₀ ∘ ψ₁, hψ₀.comp hψ₁, fun q hq x hx => ?_⟩
      rcases Finset.mem_insert.1 hq with rfl | hqs
      · obtain ⟨L, hL⟩ := hp x hx
        exact ⟨L, by simpa [Function.comp] using hL⟩
      · obtain ⟨L, hL⟩ := hs q hqs x hx
        exact ⟨L, hL.comp hψ₁.tendsto_atTop⟩
  obtain ⟨ψ, hψ, hψspec⟩ := key Finset.univ φ
  exact ⟨ψ, hψ, fun i j x hx => hψspec (i, j) (Finset.mem_univ _) x hx⟩

include I in

omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
lemma exists_allcomp_refs
    (gBase : SmoothRiemannianMetric I M)
    (gRef : ℕ → SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ r q : ℕ, q ≤ r → ∀ K : Set M, IsCompact K → ∃ C : Real,
      ∀ k : ℕ, ∀ z ∈ K, metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C)
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (φ : ℕ → ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ i j : Fin (Module.finrank Real E), ∀ x ∈ K₀,
      ∃ L : Real, Filter.Tendsto (fun m => (gSeq (φ (ψ m))).inner x
        (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x))
        Filter.atTop (nhds L) := by
  have key : ∀ s : Finset (Fin (Module.finrank Real E) × Fin (Module.finrank Real E)),
      ∀ φ' : ℕ → ℕ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ p ∈ s, ∀ x ∈ K₀, ∃ L : Real,
        Filter.Tendsto (fun m => (gSeq (φ' (ψ m))).inner x
          (Geometry.frameVec (I := I) x₀ p.1 x) (Geometry.frameVec (I := I) x₀ p.2 x))
          Filter.atTop (nhds L) := by
    intro s
    induction s using Finset.induction with
    | empty => exact fun φ' => ⟨id, strictMono_id, by simp⟩
    | @insert p s hps ih =>
      intro φ'
      obtain ⟨ψ₀, hψ₀, hs⟩ := ih φ'
      obtain ⟨ψ₁, hψ₁, hp⟩ :=
        exists_comp_refs (I := I) gBase gRef gSeq hbdd x₀ hK₀ hK₀chart
          p.1 p.2 (φ' ∘ ψ₀)
      refine ⟨ψ₀ ∘ ψ₁, hψ₀.comp hψ₁, fun q hq x hx => ?_⟩
      rcases Finset.mem_insert.1 hq with rfl | hqs
      · obtain ⟨L, hL⟩ := hp x hx
        exact ⟨L, by simpa [Function.comp] using hL⟩
      · obtain ⟨L, hL⟩ := hs q hqs x hx
        exact ⟨L, hL.comp hψ₁.tendsto_atTop⟩
  obtain ⟨ψ, hψ, hψspec⟩ := key Finset.univ φ
  exact ⟨ψ, hψ, fun i j x hx => hψspec (i, j) (Finset.mem_univ _) x hx⟩

include I in




omit [IsManifold I 2 M] in
lemma exists_limit_gm (hne : Nonempty M)
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (hlow : ∃ c : Real, 0 < c ∧ ∀ (k : ℕ) (x : M) (v : TangentSpace I x),
      c * gRef.inner x v v ≤ (gSeq k).inner x v v) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ gm : Π x : M, TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real,
        (∀ x, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop (nhds (gm x))) ∧
        (∀ (x : M) (v w : TangentSpace I x), gm x v w = gm x w v) ∧
        (∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < gm x v v) := by
  obtain ⟨c, K, hKc, hKchart, hcover⟩ := exists_chart_cover (I := I) (M := M) hne
  set P : ℕ → (ℕ → ℕ) → Prop := fun k ξ => ∀ i j : Fin (Module.finrank Real E), ∀ x ∈ K k,
    ∃ L : Real, Filter.Tendsto (fun m => (gSeq (ξ m)).inner x
      (Geometry.frameVec (I := I) (c k) i x) (Geometry.frameVec (I := I) (c k) j x))
      Filter.atTop (nhds L) with hPdef
  obtain ⟨φ, hφmono, hφP⟩ := exists_diag_subseq P
    (fun k φ' _ => by
      obtain ⟨ψ, hψ, hspec⟩ :=
        exists_refine_allComponents (I := I) gRef gSeq hbdd (c k) (hKc k) (hKchart k) φ'
      exact ⟨ψ, hψ, hspec⟩)
    (fun k φ' ψ hψ hP i j x hx => by
      obtain ⟨L, hL⟩ := hP i j x hx
      exact ⟨L, hL.comp hψ.tendsto_atTop⟩)
    (fun k φ' a hP i j x hx => by
      obtain ⟨L, hL⟩ := hP i j x hx
      exact ⟨L, (Filter.tendsto_add_atTop_iff_nat a).mp hL⟩)
  have hconv : ∀ x : M, ∃ Lx : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real,
      Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop (nhds Lx) := by
    intro x
    obtain ⟨k, hxK⟩ := hcover x
    have hxbase : x ∈ (trivializationAt E (TangentSpace I : M → Type _) (c k)).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hKchart k hxK
    obtain ⟨b, hb⟩ := exists_frameVec_basis (I := I) (c k) hxbase
    refine exists_tendsto_clm_of_basis_eval b (fun m => (gSeq (φ m)).inner x) ?_
    intro i j
    obtain ⟨L, hL⟩ := hφP k i j x hxK
    refine ⟨L, ?_⟩
    rw [hb i, hb j]; exact hL
  obtain ⟨gm, hgm, hsymm, hpos⟩ := exists_gm_symm_pos (I := I) gRef gSeq φ hconv hlow
  exact ⟨φ, hφmono, gm, hgm, hsymm, hpos⟩

include I in

omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
lemma exists_limit_refs (hne : Nonempty M)
    (gBase : SmoothRiemannianMetric I M)
    (gRef : ℕ → SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ r q : ℕ, q ≤ r → ∀ K : Set M, IsCompact K → ∃ C : Real,
      ∀ k : ℕ, ∀ z ∈ K, metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C)
    (hlow : ∃ c : Real, 0 < c ∧ ∀ (k : ℕ) (x : M) (v : TangentSpace I x),
      c * gBase.inner x v v ≤ (gSeq k).inner x v v) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ gm : Π x : M, TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real,
        (∀ x, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop (nhds (gm x))) ∧
        (∀ (x : M) (v w : TangentSpace I x), gm x v w = gm x w v) ∧
        (∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < gm x v v) := by
  obtain ⟨c, K, hKc, hKchart, hcover⟩ := exists_chart_cover (I := I) (M := M) hne
  set P : ℕ → (ℕ → ℕ) → Prop := fun k ξ => ∀ i j : Fin (Module.finrank Real E), ∀ x ∈ K k,
    ∃ L : Real, Filter.Tendsto (fun m => (gSeq (ξ m)).inner x
      (Geometry.frameVec (I := I) (c k) i x) (Geometry.frameVec (I := I) (c k) j x))
      Filter.atTop (nhds L) with hPdef
  obtain ⟨φ, hφmono, hφP⟩ := exists_diag_subseq P
    (fun k φ' _ => by
      obtain ⟨ψ, hψ, hspec⟩ :=
        exists_allcomp_refs (I := I) gBase gRef gSeq hbdd
          (c k) (hKc k) (hKchart k) φ'
      exact ⟨ψ, hψ, hspec⟩)
    (fun k φ' ψ hψ hP i j x hx => by
      obtain ⟨L, hL⟩ := hP i j x hx
      exact ⟨L, hL.comp hψ.tendsto_atTop⟩)
    (fun k φ' a hP i j x hx => by
      obtain ⟨L, hL⟩ := hP i j x hx
      exact ⟨L, (Filter.tendsto_add_atTop_iff_nat a).mp hL⟩)
  have hconv : ∀ x : M, ∃ Lx : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real,
      Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop (nhds Lx) := by
    intro x
    obtain ⟨k, hxK⟩ := hcover x
    have hxbase : x ∈ (trivializationAt E (TangentSpace I : M → Type _) (c k)).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hKchart k hxK
    obtain ⟨b, hb⟩ := exists_frameVec_basis (I := I) (c k) hxbase
    refine exists_tendsto_clm_of_basis_eval b (fun m => (gSeq (φ m)).inner x) ?_
    intro i j
    obtain ⟨L, hL⟩ := hφP k i j x hxK
    refine ⟨L, ?_⟩
    rw [hb i, hb j]
    exact hL
  obtain ⟨gm, hgm, hsymm, hpos⟩ :=
    exists_gm_symm_pos (I := I) gBase gSeq φ hconv hlow
  exact ⟨φ, hφmono, gm, hgm, hsymm, hpos⟩

include I in





omit [IsManifold I 2 M] in
lemma frameComp_contMDiffOn
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (φ : ℕ → ℕ)
    (gm : Π x : M, TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real)
    (hgm : ∀ x, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop (nhds (gm x)))
    (x₀ : M) (i j : Fin (Module.finrank Real E)) :
    ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun x => gm x (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x))
      (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  intro z hz
  have hzsrc : z ∈ (chartAt H x₀).source := by
    have hz' := hz; rwa [TangentBundle.trivializationAt_baseSet] at hz'
  obtain ⟨K₀, hK₀c, hzint, hK₀sub⟩ := exists_compact_subset (chartAt H x₀).open_source hzsrc
  obtain ⟨ψ, Φinf, hψ, hΦcd, heng⟩ :=
    exists_engine_frameConv (I := I) gRef gSeq hbdd x₀ hK₀c hK₀sub i j φ
  have hid : ∀ x ∈ K₀, gm x (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x)
      = Φinf (extChartAt I x₀ x) := by
    intro x hx
    have hcont : Continuous (fun η : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real =>
        η (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x)) :=
      ((ContinuousLinearMap.apply Real Real (Geometry.frameVec (I := I) x₀ j x)).comp
        (ContinuousLinearMap.apply Real (TangentSpace I x →L[Real] Real)
          (Geometry.frameVec (I := I) x₀ i x))).continuous
    have hB := ((hcont.tendsto (gm x)).comp (hgm x)).comp hψ.tendsto_atTop
    exact tendsto_nhds_unique hB (heng x hx)
  have hsmooth : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun x => Φinf (extChartAt I x₀ x)) z :=
    (contMDiff_iff_contDiff.mpr hΦcd).contMDiffAt.comp z (contMDiffAt_extChartAt' hzsrc)
  have hK₀nhds : K₀ ∈ nhds z :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hzint) interior_subset
  have heq : (fun x => gm x (Geometry.frameVec (I := I) x₀ i x)
        (Geometry.frameVec (I := I) x₀ j x)) =ᶠ[nhds z] (fun x => Φinf (extChartAt I x₀ x)) := by
    filter_upwards [hK₀nhds] with x hx using hid x hx
  exact (hsmooth.congr_of_eventuallyEq heq).contMDiffWithinAt

include I in

omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
lemma frame_smooth_refs
    (gBase : SmoothRiemannianMetric I M)
    (gRef : ℕ → SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ r q : ℕ, q ≤ r → ∀ K : Set M, IsCompact K → ∃ C : Real,
      ∀ k : ℕ, ∀ z ∈ K, metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C)
    (φ : ℕ → ℕ)
    (gm : Π x : M, TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real)
    (hgm : ∀ x, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop (nhds (gm x)))
    (x₀ : M) (i j : Fin (Module.finrank Real E)) :
    ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun x => gm x (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x))
      (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  intro z hz
  have hzsrc : z ∈ (chartAt H x₀).source := by
    have hz' := hz
    rwa [TangentBundle.trivializationAt_baseSet] at hz'
  obtain ⟨K₀, hK₀c, hzint, hK₀sub⟩ :=
    exists_compact_subset (chartAt H x₀).open_source hzsrc
  obtain ⟨ψ, Φinf, hψ, hΦcd, heng⟩ :=
    exists_frame_refs (I := I) gBase gRef gSeq hbdd x₀ hK₀c hK₀sub i j φ
  have hid : ∀ x ∈ K₀,
      gm x (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x)
        = Φinf (extChartAt I x₀ x) := by
    intro x hx
    have hcont : Continuous
        (fun η : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real =>
          η (Geometry.frameVec (I := I) x₀ i x) (Geometry.frameVec (I := I) x₀ j x)) :=
      ((ContinuousLinearMap.apply Real Real (Geometry.frameVec (I := I) x₀ j x)).comp
        (ContinuousLinearMap.apply Real (TangentSpace I x →L[Real] Real)
          (Geometry.frameVec (I := I) x₀ i x))).continuous
    have hB := ((hcont.tendsto (gm x)).comp (hgm x)).comp hψ.tendsto_atTop
    exact tendsto_nhds_unique hB (heng x hx)
  have hsmooth : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun x => Φinf (extChartAt I x₀ x)) z :=
    (contMDiff_iff_contDiff.mpr hΦcd).contMDiffAt.comp z (contMDiffAt_extChartAt' hzsrc)
  have hK₀nhds : K₀ ∈ nhds z :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hzint) interior_subset
  have heq : (fun x => gm x (Geometry.frameVec (I := I) x₀ i x)
        (Geometry.frameVec (I := I) x₀ j x)) =ᶠ[nhds z]
      (fun x => Φinf (extChartAt I x₀ x)) := by
    filter_upwards [hK₀nhds] with x hx using hid x hx
  exact (hsmooth.congr_of_eventuallyEq heq).contMDiffWithinAt

include I in




omit [IsManifold I 2 M] in
theorem metricPreconv_gInf (hne : Nonempty M)
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (hlow : ∃ c : Real, 0 < c ∧ ∀ (k : ℕ) (x : M) (v : TangentSpace I x),
      c * gRef.inner x v v ≤ (gSeq k).inner x v v) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ gInf : SmoothRiemannianMetric I M,
      ∀ x : M, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop (nhds (gInf.inner x)) := by
  obtain ⟨φ, hφ, gm, hgm, hsymm, hpos⟩ := exists_limit_gm (I := I) hne gRef gSeq hbdd hlow
  obtain ⟨gInf, hgInf⟩ :=
    Geometry.smoothMetric_of_localCoeff gm hsymm hpos
      (fun x₀ i j => frameComp_contMDiffOn (I := I) gRef gSeq hbdd φ gm hgm x₀ i j)
  refine ⟨φ, hφ, gInf, fun x => ?_⟩
  have hx : gInf.inner x = gm x := by ext v w; exact hgInf x v w
  rw [hx]; exact hgm x

include I in

omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem metricPreconv_refs (hne : Nonempty M)
    (gBase : SmoothRiemannianMetric I M)
    (gRef : ℕ → SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ r q : ℕ, q ≤ r → ∀ K : Set M, IsCompact K → ∃ C : Real,
      ∀ k : ℕ, ∀ z ∈ K, metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C)
    (hlow : ∃ c : Real, 0 < c ∧ ∀ (k : ℕ) (x : M) (v : TangentSpace I x),
      c * gBase.inner x v v ≤ (gSeq k).inner x v v) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ gInf : SmoothRiemannianMetric I M,
      ∀ x : M, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop
        (nhds (gInf.inner x)) := by
  obtain ⟨φ, hφ, gm, hgm, hsymm, hpos⟩ :=
    exists_limit_refs (I := I) hne gBase gRef gSeq hbdd hlow
  obtain ⟨gInf, hgInf⟩ :=
    Geometry.smoothMetric_of_localCoeff gm hsymm hpos
      (fun x₀ i j => frame_smooth_refs (I := I) gBase gRef gSeq hbdd φ gm hgm x₀ i j)
  refine ⟨φ, hφ, gInf, fun x => ?_⟩
  have hx : gInf.inner x = gm x := by
    ext v w
    exact hgInf x v w
  rw [hx]
  exact hgm x

include I in









omit [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
lemma componentConv_covDeriv_zero
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (φ : ℕ → ℕ) (gInf : SmoothRiemannianMetric I M)
    (hconv : ∀ x : M, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop
      (nhds (gInf.inner x)))
    (x : M) (b : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x))
    (I0 : Fin 2 → Fin (Module.finrank Real E)) :
    Filter.Tendsto (fun m => Tensor0SBundle.component0S (I := I) b
        (metricCovDeriv (I := I) (gSeq (φ m)) gRef 0 x) I0) Filter.atTop
      (nhds (Tensor0SBundle.component0S (I := I) b
        (metricCovDeriv (I := I) gInf gRef 0 x) I0)) := by
  have hkey : ∀ g : SmoothRiemannianMetric I M,
      Tensor0SBundle.component0S (I := I) b (metricCovDeriv (I := I) g gRef 0 x) I0
        = g.inner x (b (I0 0)) (b (I0 1)) := by
    intro g
    simp only [Tensor0SBundle.component0S_apply, metricCovDeriv_eq_covDerivOfField,
      covDerivOfField_zero]
    rw [Tensor0SBundle.metricTensorField_apply]
  simp only [hkey]
  have hcont : Continuous (fun η : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real =>
      η (b (I0 0)) (b (I0 1))) :=
    ((ContinuousLinearMap.apply Real Real (b (I0 1))).comp
      (ContinuousLinearMap.apply Real (TangentSpace I x →L[Real] Real) (b (I0 0)))).continuous
  exact (hcont.tendsto (gInf.inner x)).comp (hconv x)

end Realization

end HCGCompactness
end DifferentialGeometry
