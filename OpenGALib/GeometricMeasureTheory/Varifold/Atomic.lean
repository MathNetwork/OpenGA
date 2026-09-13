import OpenGALib.GeometricMeasureTheory.Varifold.Convergence

/-!
# Atomic varifolds

Point masses on positions and planes are legitimate general varifolds. They
provide simple examples showing why weight measures alone cannot determine
a varifold. These are not asserted to be rectifiable varifolds of positive dimension.
-/

noncomputable section

open MeasureTheory Topology
open scoped CompactlySupported

namespace OpenGA.Varifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ}

/-- Unit mass at one position and one unoriented plane. -/
def dirac (x : E) (P : Grassmannian E k) : Varifold E k :=
  ⟨Measure.dirac (x, P), inferInstance⟩

@[simp] theorem weightMeasure_dirac (x : E) (P : Grassmannian E k) :
    (dirac x P).weightMeasure = Measure.dirac x :=
  Measure.map_dirac' measurable_fst _

@[simp] theorem mass_dirac (x : E) (P : Grassmannian E k) : (dirac x P).mass = 1 := by
  simp [mass, dirac]

@[simp] theorem testIntegral_dirac (x : E) (P : Grassmannian E k)
    (φ : C_c(E × Grassmannian E k, ℝ)) : (dirac x P).testIntegral φ = φ (x, P) :=
  integral_dirac _ _

/-- Changing only the plane changes the varifold, although its weight measure is unchanged. -/
theorem dirac_ne_of_plane_ne (x : E) {P Q : Grassmannian E k} (hPQ : P ≠ Q) :
    dirac x P ≠ dirac x Q := by
  intro h
  have heq : Measure.dirac (x, P) = Measure.dirac (x, Q) := congrArg measure h
  exact hPQ (congrArg Prod.snd (dirac_eq_dirac_iff.mp heq))

theorem continuous_dirac :
    Continuous (fun z : E × Grassmannian E k => dirac z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_iff_testIntegral.mpr
  intro φ
  simp only [testIntegral_dirac]
  exact φ.continuous.continuousAt

end OpenGA.Varifold
