import DifferentialGeometry.Geometry.Flow.MetricTrace


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
private lemma exists_bump_tsupport_subset {U : Set M} (hU : IsOpen U) {x₀ : M}
    (hx₀ : x₀ ∈ U) :
    ∃ χ : SmoothBumpFunction I x₀, tsupport (χ : M → ℝ) ⊆ U := by
  have hUnhds : U ∈ 𝓝 x₀ := hU.mem_nhds hx₀
  exact (SmoothBumpFunction.nhds_basis_support (I := I) (c := x₀) hUnhds).ex_mem

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connDiff_contMDiffOn_local (g g' : SmoothRiemannianMetric I M)
    {U : Set M} (hU : IsOpen U) {σ τ : Π x : M, TangentSpace I x}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ) U)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% τ) U) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x (σ x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) U := by
  classical
  intro x₀ hx₀
  obtain ⟨χ, hχ_tsupport⟩ := exists_bump_tsupport_subset (I := I) hU hx₀
  set ψ : M → ℝ := (χ : M → ℝ) with hψ_def
  have hψ_smooth : ContMDiffOn I 𝓘(ℝ) ∞ ψ U :=
    χ.contMDiff.contMDiffOn
  have hcut : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (ψ • σ)) :=
    ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (n := ∞)
      (V := fun x : M => TangentSpace I x) hψ_smooth hU hχ_tsupport hσ
  have hConn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x ((ψ • σ) x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) U :=
    connDiff_contMDiffOn (I := I) g g' hcut hτ
  have hConnAt : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x ((ψ • σ) x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) x₀ :=
    (hConn x₀ hx₀).contMDiffAt (hU.mem_nhds hx₀)
  have hψ_one : ψ =ᶠ[𝓝 x₀] (1 : M → ℝ) := χ.eventuallyEq_one
  have heventuallyEq :
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x (σ x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) =ᶠ[𝓝 x₀]
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x ((ψ • σ) x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) := by
    refine hψ_one.mono (fun x hx => ?_)
    have hx1 : ψ x = 1 := by simpa using hx
    have hσx : (ψ • σ) x = σ x := by
      change ψ x • σ x = σ x
      rw [hx1, one_smul]
    change (⟨x, connDiff (I := I) g g' x (σ x) (τ x)⟩ : TotalSpace E (TangentSpace I)) =
      ⟨x, connDiff (I := I) g g' x ((ψ • σ) x) (τ x)⟩
    rw [hσx]
  have hGoalAt : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x (σ x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) x₀ :=
    hConnAt.congr_of_eventuallyEq heventuallyEq
  exact hGoalAt.contMDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma connDiff_chartBasis_contMDiffOn (g g' : SmoothRiemannianMetric I M)
    (α : M) (j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x
            (chartBasisVecFiber (I := I) α j x)
            (chartBasisVecFiber (I := I) α k x)⟩ :
          TotalSpace E (TangentSpace I)))
      (chartAt H α).source := by
  have hopen : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
  have hbase : (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    trivializationAt_baseSet_eq_chartAt_source α
  have hframe : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun x : M => chartBasisVecFiber (I := I) α i x))
        (chartAt H α).source := by
    intro i
    have h := chartBasisVec_contMDiffOn (I := I) α i
    rw [hbase] at h
    exact h
  exact connDiff_contMDiffOn_local (I := I) g g' hopen (hframe j) (hframe k)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartInvGramMatrix_entry_contMDiffOn_source
    (g : SmoothRiemannianMetric I M) (α : M)
    (j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix (I := I) g α x j k)
      (chartAt H α).source := by
  have h := chartInvGramMatrix_entry_contMDiffOn (I := I) g α j k
  rwa [trivializationAt_baseSet_eq_chartAt_source] at h

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckChartLocal_contMDiffOn (g g' : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (deTurckChartLocal (I := I) g g' α x))
      (chartAt H α).source := by
  classical
  have hcoeff : ∀ j k : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun x : M => chartInvGramMatrix (I := I) g α x j k)
        (chartAt H α).source :=
    fun j k => chartInvGramMatrix_entry_contMDiffOn_source (I := I) g α j k
  have hterm : ∀ j k : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M =>
          (⟨x, connDiff (I := I) g g' x
              (chartBasisVecFiber (I := I) α j x)
              (chartBasisVecFiber (I := I) α k x)⟩ :
            TotalSpace E (TangentSpace I)))
        (chartAt H α).source :=
    fun j k => connDiff_chartBasis_contMDiffOn (I := I) g g' α j k
  have hsmul : ∀ j k : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E x
          (chartInvGramMatrix (I := I) g α x j k •
            connDiff (I := I) g g' x
              (chartBasisVecFiber (I := I) α j x)
              (chartBasisVecFiber (I := I) α k x)))
        (chartAt H α).source :=
    fun j k => (hcoeff j k).smul_section (hterm j k)
  have hinner : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E x
          (∑ k : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α x j k •
              connDiff (I := I) g g' x
                (chartBasisVecFiber (I := I) α j x)
                (chartBasisVecFiber (I := I) α k x)))
        (chartAt H α).source :=
    fun j => ContMDiffOn.sum_section (fun k _ => hsmul j k)
  have houter : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x
        (∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α x j k •
              connDiff (I := I) g g' x
                (chartBasisVecFiber (I := I) α j x)
                (chartBasisVecFiber (I := I) α k x)))
      (chartAt H α).source :=
    ContMDiffOn.sum_section (fun j _ => hinner j)
  refine houter.congr (fun x _hx => ?_)
  rw [deTurckChartLocal_def]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckFun_contMDiff_total (g g' : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (deTurckFun (I := I) g g' x)) := by
  intro x
  have hx_src : x ∈ (chartAt H x).source := mem_chart_source H x
  have hsrc_open : IsOpen ((chartAt H x).source) := (chartAt H x).open_source
  have hsmooth_local : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (deTurckChartLocal (I := I) g g' x y))
      (chartAt H x).source :=
    deTurckChartLocal_contMDiffOn (I := I) g g' x
  have hsmooth_local2 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (deTurckFun (I := I) g g' y))
      (chartAt H x).source := by
    refine hsmooth_local.congr (fun y hy => ?_)
    have h := deTurckChartLocal_eq_deTurckFun_of_mem_source (I := I) g g' x hy
    change TotalSpace.mk' E y (deTurckFun (I := I) g g' y) =
      TotalSpace.mk' E y (deTurckChartLocal (I := I) g g' x y)
    rw [h]
  exact (hsmooth_local2 x hx_src).contMDiffAt (hsrc_open.mem_nhds hx_src)

end DeTurck
end PDE
end DifferentialGeometry
