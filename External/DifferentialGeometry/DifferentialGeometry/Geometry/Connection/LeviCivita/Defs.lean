import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartTorsion
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartMetric
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartSmooth
import DifferentialGeometry.Geometry.Connection.LeviCivita.Torsion


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
lemma self_mem_chartLeviCivitaGoodSet (α : M) :
    α ∈ chartLeviCivitaGoodSet (I := I) α := by
  classical
  refine mem_chartLeviCivitaGoodSet_iff.mpr ⟨?_, ?_, ?_⟩
  · exact mem_extChartAt_source α
  · exact FiberBundle.mem_baseSet_trivializationAt' α
  · have hint : I.IsInteriorPoint α := BoundarylessManifold.isInteriorPoint
    exact (ModelWithCorners.isInteriorPoint_iff).mp hint

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
lemma iUnion_chartLeviCivitaGoodSet :
    (⋃ α : M, chartLeviCivitaGoodSet (I := I) α) = (Set.univ : Set M) := by
  classical
  refine Set.eq_univ_of_forall ?_
  intro x
  refine mem_iUnion.mpr ⟨x, ?_⟩
  exact self_mem_chartLeviCivitaGoodSet (I := I) (α := x)

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartLeviCivita_chart_overlap
    (g : SmoothRiemannianMetric I M) (α β : M)
    {Y : Π x : M, TangentSpace I x} {x : M}
    (hxα : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hxβ : x ∈ chartLeviCivitaGoodSet (I := I) β)
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    chartLeviCivita (I := I) g α Y x v =
      chartLeviCivita (I := I) g β Y x v := by
  classical
  obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v
  have hX : MDiffAt (T% fun y => X y) x := X.mdifferentiableAt
  set s : Set M := {x} with hs
  have hxs : x ∈ s := rfl
  have hTFα : ∀ ⦃A B : Π y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDiffAt (T% A) y → MDiffAt (T% B) y → y ∈ s →
      chartLeviCivita (I := I) g α B y (A y) -
        chartLeviCivita (I := I) g α A y (B y) =
        VectorField.mlieBracket I A B y := by
    intro A B y hA hB hy
    have hyx : y = x := hy
    subst hyx
    exact chartLeviCivita_torsion_free_on (I := I) g α hA hB hxα
  have hTFβ : ∀ ⦃A B : Π y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDiffAt (T% A) y → MDiffAt (T% B) y → y ∈ s →
      chartLeviCivita (I := I) g β B y (A y) -
        chartLeviCivita (I := I) g β A y (B y) =
        VectorField.mlieBracket I A B y := by
    intro A B y hA hB hy
    have hyx : y = x := hy
    subst hyx
    exact chartLeviCivita_torsion_free_on (I := I) g β hA hB hxβ
  have hMCα : IsMetricCompatibleOn (chartLeviCivita (I := I) g α) g s :=
    (chartLeviCivita_isMetricCompatibleOn (I := I) g α).mono
      (by intro y hy; have : y = x := hy; subst this; exact hxα)
  have hMCβ : IsMetricCompatibleOn (chartLeviCivita (I := I) g β) g s :=
    (chartLeviCivita_isMetricCompatibleOn (I := I) g β).mono
      (by intro y hy; have : y = x := hy; subst this; exact hxβ)
  have hloc :
      chartLeviCivita (I := I) g α Y x (X x) =
        chartLeviCivita (I := I) g β Y x (X x) :=
    koszul_local_uniqueness (s := s)
      hTFα hTFβ hMCα hMCβ hX hY hxs
  simpa [hXx] using hloc

def leviCivitaStitched (g : SmoothRiemannianMetric I M) :
    (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x) :=
  fun σ x => chartLeviCivita (I := I) g x σ x

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma leviCivitaStitched_eq_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    {Y : Π x : M, TangentSpace I x} {x : M}
    (hxα : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    leviCivitaStitched (I := I) g Y x v =
      chartLeviCivita (I := I) g α Y x v := by
  unfold leviCivitaStitched
  exact chartLeviCivita_chart_overlap (I := I) g x α
    (self_mem_chartLeviCivitaGoodSet (I := I) (α := x)) hxα hY v

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma leviCivitaStitched_add_on_goodSet
    (g : SmoothRiemannianMetric I M) (α : M)
    {σ σ' : Π x : M, TangentSpace I x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    leviCivitaStitched (I := I) g (σ + σ') x =
      leviCivitaStitched (I := I) g σ x + leviCivitaStitched (I := I) g σ' x := by
  classical
  have hsum_at : MDiffAt (T% (σ + σ')) x :=
    mdifferentiableAt_add_section hσ hσ'
  apply ContinuousLinearMap.ext
  intro v
  rw [leviCivitaStitched_eq_chart (I := I) g α hx hsum_at v]
  rw [(chartLeviCivita_isCovariantDerivativeOn (I := I) g α).add hσ hσ' hx]
  rw [ContinuousLinearMap.add_apply,
      ← leviCivitaStitched_eq_chart (I := I) g α hx hσ v,
      ← leviCivitaStitched_eq_chart (I := I) g α hx hσ' v]
  rfl

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma leviCivitaStitched_leibniz_on_goodSet
    (g : SmoothRiemannianMetric I M) (α : M)
    {σ : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M}
    (hσ : MDiffAt (T% σ) x) (hf : MDiffAt f x)
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    leviCivitaStitched (I := I) g (f • σ) x =
      f x • leviCivitaStitched (I := I) g σ x +
        (extDerivFun f x).smulRight (σ x) := by
  classical
  have hsmul_at : MDiffAt (T% (f • σ)) x :=
    hf.smul_section hσ
  apply ContinuousLinearMap.ext
  intro v
  rw [leviCivitaStitched_eq_chart (I := I) g α hx hsmul_at v]
  rw [(chartLeviCivita_isCovariantDerivativeOn (I := I) g α).leibniz hσ hf hx]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply,
      ← leviCivitaStitched_eq_chart (I := I) g α hx hσ v]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma leviCivitaStitched_isCovariantDerivativeOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (leviCivitaStitched (I := I) g) (chartLeviCivitaGoodSet (I := I) α) where
  add hσ hσ' hx := leviCivitaStitched_add_on_goodSet (I := I) g α hσ hσ' hx
  leibniz hσ hf hx := leviCivitaStitched_leibniz_on_goodSet (I := I) g α hσ hf hx

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma leviCivitaStitched_isCovariantDerivativeOn_univ
    (g : SmoothRiemannianMetric I M) :
    IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (leviCivitaStitched (I := I) g) Set.univ := by
  classical
  rw [← iUnion_chartLeviCivitaGoodSet (I := I) (M := M)]
  exact IsCovariantDerivativeOn.iUnion (s := fun α => chartLeviCivitaGoodSet (I := I) α)
    (fun α => leviCivitaStitched_isCovariantDerivativeOn (I := I) g α)

def LeviCivita (g : SmoothRiemannianMetric I M) :
    CovariantDerivative I E (TangentSpace I : M → Type _) :=
  leviCivitaConnectionOfMetric (I := I) g

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in


omit [SigmaCompactSpace M] [T2Space M] in
theorem LeviCivita_eq_leviCivitaConnectionOfMetric (g : SmoothRiemannianMetric I M) :
    LeviCivita (I := I) g = leviCivitaConnectionOfMetric (I := I) g := rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem LeviCivita_chart_apply (g : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {σ : Π x : M, TangentSpace I x} (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    (LeviCivita (I := I) g).toFun σ x v = chartLeviCivita (I := I) g α σ x v := by
  classical
  obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v
  have hX : MDiffAt (T% fun y => X y) x := X.mdifferentiableAt
  set s : Set M := {x} with hs
  have hxs : x ∈ s := rfl
  have htor0 : (leviCivitaConnectionOfMetric (I := I) g).torsion = 0 :=
    funext fun y => leviCivitaConnectionOfMetric_isTorsionFree (I := I) g y
  have hTF₁ : ∀ ⦃A B : Π y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDiffAt (T% A) y → MDiffAt (T% B) y → y ∈ s →
      (leviCivitaConnectionOfMetric (I := I) g).toFun B y (A y) -
        (leviCivitaConnectionOfMetric (I := I) g).toFun A y (B y) =
        VectorField.mlieBracket I A B y := by
    intro A B y hA hB _
    exact (CovariantDerivative.torsion_eq_zero_iff
      (leviCivitaConnectionOfMetric (I := I) g)).mp htor0 hA hB
  have hTF₂ : ∀ ⦃A B : Π y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDiffAt (T% A) y → MDiffAt (T% B) y → y ∈ s →
      chartLeviCivita (I := I) g α B y (A y) -
        chartLeviCivita (I := I) g α A y (B y) =
        VectorField.mlieBracket I A B y := by
    intro A B y hA hB hy
    have hyx : y = x := hy
    subst hyx
    exact chartLeviCivita_torsion_free_on (I := I) g α hA hB hx
  have hMC₁ : IsMetricCompatibleOn (leviCivitaConnectionOfMetric (I := I) g).toFun g s := by
    intro Y Z y hY hZ _ v
    obtain ⟨W, hWy⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) y v
    have hW : MDiffAt (T% fun b => W b) y := W.mdifferentiableAt
    have hgen := leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g y W Y Z hW hY hZ
    rw [hWy] at hgen
    exact hgen
  have hMC₂ : IsMetricCompatibleOn (chartLeviCivita (I := I) g α) g s :=
    (chartLeviCivita_isMetricCompatibleOn (I := I) g α).mono
      (by intro y hy; have : y = x := hy; subst this; exact hx)
  have hloc :=
    koszul_local_uniqueness (s := s) hTF₁ hTF₂ hMC₁ hMC₂ hX hσ hxs
  simpa [hXx] using hloc

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem LeviCivita_torsion_eq_zero (g : SmoothRiemannianMetric I M) :
    (LeviCivita (I := I) g).torsion = 0 := by
  classical
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  have hx : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  rw [LeviCivita_chart_apply (I := I) g x hx hY (X x),
      LeviCivita_chart_apply (I := I) g x hx hX (Y x)]
  exact chartLeviCivita_torsion_free_on (I := I) g x hX hY hx

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem LeviCivita_isMetricCompatible (g : SmoothRiemannianMetric I M) :
    IsMetricCompatible (LeviCivita (I := I) g) g := by
  classical
  change IsMetricCompatibleOn (LeviCivita (I := I) g).toFun g Set.univ
  rw [show (Set.univ : Set M) = ⋃ α : M, chartLeviCivitaGoodSet (I := I) α from
    (iUnion_chartLeviCivitaGoodSet (I := I) (M := M)).symm]
  refine IsMetricCompatibleOn.iUnion (s := fun α => chartLeviCivitaGoodSet (I := I) α) ?_
  intro α Y Z x hY hZ hxα v
  rw [LeviCivita_chart_apply (I := I) g α hxα hY v,
      LeviCivita_chart_apply (I := I) g α hxα hZ v]
  exact chartLeviCivita_isMetricCompatibleOn (I := I) g α hY hZ hxα v

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma LeviCivita_section_contMDiffOn_univ (g : SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) Set.univ) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g).toFun σ x⟩ :
          TotalSpace (E →L[ℝ] E) (fun x : M =>
            TangentSpace I x →L[ℝ] TangentSpace I x))) Set.univ := by
  classical
  apply contMDiffOn_of_locally_contMDiffOn
  intro x _hx
  refine ⟨chartLeviCivitaGoodSet (I := I) x,
    chartLeviCivitaGoodSet_isOpen (I := I) x,
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x), ?_⟩
  have hσ_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ)
      (chartLeviCivitaGoodSet (I := I) x) :=
    hσ.mono (Set.subset_univ _)
  have hchart :=
    (chartLeviCivita_contMDiffCovariantDerivativeOn (I := I) g x).contMDiff
      (σ := σ) hσ_on
  rw [Set.univ_inter]
  refine hchart.congr ?_
  intro y hy
  have hσ_at : MDiffAt (T% σ) y := by
    have h1 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) y :=
      hσ.contMDiffAt Filter.univ_mem
    have h2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (T% σ) y := by
      have h_le : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) + 1 := by
        rw [ENat.coe_top_add_one]
      exact h1.of_le h_le
    exact h2.mdifferentiableAt (by simp)
  have hfib :
      (LeviCivita (I := I) g).toFun σ y = chartLeviCivita (I := I) g x σ y := by
    apply ContinuousLinearMap.ext
    intro v
    exact LeviCivita_chart_apply (I := I) g x hy hσ_at v
  simp [hfib]

instance LeviCivita_isContMDiff (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivative (LeviCivita (I := I) g) ∞ where
  contMDiff :=
    { contMDiff := fun hσ => LeviCivita_section_contMDiffOn_univ (I := I) g hσ }

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem LeviCivita_unique (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (htor : cov.torsion = 0) (hmc : IsMetricCompatible cov g)
    {σ : Π x : M, TangentSpace I x} {x : M} (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    cov.toFun σ x v = (LeviCivita (I := I) g).toFun σ x v :=
  koszul_levi_civita_unique_of_torsionFree_metricCompatible cov (LeviCivita (I := I) g)
    htor (LeviCivita_torsion_eq_zero (I := I) g)
    hmc (LeviCivita_isMetricCompatible (I := I) g)
    hσ v

end Connection
end Integral
end DifferentialGeometry
