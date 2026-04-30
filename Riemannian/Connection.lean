import Riemannian.Connection.Koszul
import Riemannian.Connection.LeviCivita
import Riemannian.Connection.Bianchi

/-!
# Riemannian.Connection — facade

Re-exports the two sub-modules that together construct the Levi-Civita
connection on a Riemannian manifold $M$:

- `Connection/Koszul.lean` — `directionalDeriv`, `koszulFunctional`,
  the 8 algebraic identities (`koszul_antisymm`, `koszul_metric_compat_sum`,
  `koszul_smul_*`, `koszul_add_*`), and `koszulFunctional_local`.
- `Connection/LeviCivita.lean` — Riesz extraction (`koszulCovDeriv`),
  `koszulLeviCivita_exists` (closed via `TensorialAt.mkHom` + Riesz
  uniqueness), `leviCivitaConnection_exists`, the `leviCivitaConnection`
  def, torsion / metric-compat properties, and the `covDeriv` public-API
  wrapper.

**Ground truth**: do Carmo 1992 §2 Theorem 3.6 (Levi-Civita theorem,
existence + uniqueness via the Koszul formula).
-/

open Bundle VectorField OpenGALib
open scoped ContDiff Manifold


/-! ## UXTest

Self-test verifying the Levi-Civita connection + `covDeriv` resolve
their typeclass cascade. Regression guard against signature drift. -/
section UXTest

open Riemannian OpenGALib

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [RiemannianMetric I M]
    (X Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x := covDeriv X Y x

/-! ## Self-test: Koszul functional typeclass + identities -/

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    ℝ := koszulFunctional X Y Z x

example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    koszulFunctional X Y Z x - koszulFunctional Y X Z x
      = 2 * metricInner x (mlieBracket I X Y x) (Z x) :=
  koszul_antisymm X Y Z x

example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    koszulFunctional X Y Z x + koszulFunctional X Z Y x
      = 2 * directionalDeriv (fun y => metricInner y (Y y) (Z y)) x (X x) :=
  koszul_metric_compat_sum X Y Z x

/-! ## Self-test: Koszul $C^\infty(M)$-linearity in $Z$ -/

example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (X Y Z : Π x : M, TangentSpace I x) (f : M → ℝ) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hYZ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z y)) x)
    (hZX : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Z y) (X y)) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Z y⟩ : TangentBundle I M)) x) :
    koszulFunctional X Y (fun y => f y • Z y) x = f x * koszulFunctional X Y Z x :=
  koszul_smul_right X Y Z f x hf hYZ hZX hZ

/-! ## Self-test: koszulCovDeriv + Riesz defining property -/

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [RiemannianMetric I M]
    (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, X y⟩ : TangentBundle I M)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Y y⟩ : TangentBundle I M)) x) :
    TangentSpace I x := koszulCovDeriv X Y x hX hY

example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [RiemannianMetric I M]
    (X Y Z : Π x : M, TangentSpace I x) (x : M)
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, X y⟩ : TangentBundle I M)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Y y⟩ : TangentBundle I M)) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Z y⟩ : TangentBundle I M)) x) :
    metricInner x (koszulCovDeriv X Y x hX hY) (Z x)
      = (1/2 : ℝ) * koszulFunctional X Y Z x :=
  koszulCovDeriv_inner_eq X Y Z x hX hY hZ

/-! ## Self-test: 5 koszul algebraic identities -/

example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (X Y Z₁ Z₂ : Π x : M, TangentSpace I x) (x : M)
    (h_YZ₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z₁ y)) x)
    (h_YZ₂ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z₂ y)) x)
    (h_Z₁X : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Z₁ y) (X y)) x)
    (h_Z₂X : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Z₂ y) (X y)) x)
    (h_Z₁ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Z₁ y⟩ : TangentBundle I M)) x)
    (h_Z₂ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Z₂ y⟩ : TangentBundle I M)) x) :
    koszulFunctional X Y (Z₁ + Z₂) x
      = koszulFunctional X Y Z₁ x + koszulFunctional X Y Z₂ x :=
  koszul_add_right X Y Z₁ Z₂ x h_YZ₁ h_YZ₂ h_Z₁X h_Z₂X h_Z₁ h_Z₂

example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (X₁ X₂ Y Z : Π x : M, TangentSpace I x) (x : M)
    (h_ZX₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Z y) (X₁ y)) x)
    (h_ZX₂ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Z y) (X₂ y)) x)
    (h_X₁Y : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (X₁ y) (Y y)) x)
    (h_X₂Y : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (X₂ y) (Y y)) x)
    (h_X₁ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, X₁ y⟩ : TangentBundle I M)) x)
    (h_X₂ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, X₂ y⟩ : TangentBundle I M)) x) :
    koszulFunctional (X₁ + X₂) Y Z x
      = koszulFunctional X₁ Y Z x + koszulFunctional X₂ Y Z x :=
  koszul_add_left X₁ X₂ Y Z x h_ZX₁ h_ZX₂ h_X₁Y h_X₂Y h_X₁ h_X₂

example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (X Y₁ Y₂ Z : Π x : M, TangentSpace I x) (x : M)
    (h_Y₁Z : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y₁ y) (Z y)) x)
    (h_Y₂Z : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y₂ y) (Z y)) x)
    (h_XY₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (X y) (Y₁ y)) x)
    (h_XY₂ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (X y) (Y₂ y)) x)
    (h_Y₁ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Y₁ y⟩ : TangentBundle I M)) x)
    (h_Y₂ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Y₂ y⟩ : TangentBundle I M)) x) :
    koszulFunctional X (Y₁ + Y₂) Z x
      = koszulFunctional X Y₁ Z x + koszulFunctional X Y₂ Z x :=
  koszul_add_middle X Y₁ Y₂ Z x h_Y₁Z h_Y₂Z h_XY₁ h_XY₂ h_Y₁ h_Y₂

example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (X Y Z : Π x : M, TangentSpace I x) (f : M → ℝ) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (h_ZX : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Z y) (X y)) x)
    (h_XY : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (X y) (Y y)) x)
    (h_X : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, X y⟩ : TangentBundle I M)) x) :
    koszulFunctional (fun y => f y • X y) Y Z x = f x * koszulFunctional X Y Z x :=
  koszul_smul_left X Y Z f x hf h_ZX h_XY h_X

example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (X Y Z : Π x : M, TangentSpace I x) (f : M → ℝ) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (h_YZ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z y)) x)
    (h_XY : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (X y) (Y y)) x)
    (h_Y : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Y y⟩ : TangentBundle I M)) x) :
    koszulFunctional X (fun y => f y • Y y) Z x
      = f x * koszulFunctional X Y Z x
        + 2 * directionalDeriv f x (X x) * metricInner x (Y x) (Z x) :=
  koszul_smul_middle X Y Z f x hf h_YZ h_XY h_Y

end UXTest
