import OpenGALib.Riemannian.Surface.Sweepout
import OpenGALib.Riemannian.Surface.DirichletEnergy
import Mathlib.Topology.Homotopy.Basic

/-!
# Min--max energy in a smooth-slice sweepout class

The energy is the geometric Dirichlet integral of each map, not an arbitrary
energy profile. Homotopies preserve constant endpoint slices and smoothness
of every slice. They are jointly continuous in the ordinary topology.

This is the smooth-slice precursor to CM's width. It does not impose joint
continuity in C0 intersection W1,2 and does not identify this infimum with
the CM Sobolev width. That mapping-space comparison, finiteness, and positivity
for nontrivial classes remain separate theorems.
-/

noncomputable section
open Set
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry

namespace OpenGA.RicciFlow.SmoothSweepout

variable {N : Type*} [TopologicalSpace N] [ChartedSpace Surface.Model N]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def toContinuousMap (W : SmoothSweepout (N := N) (I := I) (M := M)) :
    C(Icc (0 : ℝ) 1 × N, M) := ⟨fun p => W.map p.1 p.2, W.continuous_joint⟩

/-- Endpoint values may move during the homotopy, but each endpoint slice
remains a constant map. -/
def IsSmoothSweepoutMap (F : C(Icc (0 : ℝ) 1 × N, M)) : Prop :=
  (∃ c : M, ∀ x, F (⟨0, ⟨le_rfl, zero_le_one⟩⟩, x) = c) ∧
  (∃ c : M, ∀ x, F (⟨1, ⟨zero_le_one, le_rfl⟩⟩, x) = c) ∧
  ∀ u, ContMDiff 𝓘(ℝ, Surface.Model) I ∞ (fun x => F (u, x))

def Homotopic (W V : SmoothSweepout (N := N) (I := I) (M := M)) : Prop :=
  W.toContinuousMap.HomotopicWith V.toContinuousMap (IsSmoothSweepoutMap (I := I))

theorem homotopic_refl (W : SmoothSweepout (N := N) (I := I) (M := M)) :
    W.Homotopic W :=
  ContinuousMap.HomotopicWith.refl W.toContinuousMap
    ⟨W.endpoint_zero_constant, W.endpoint_one_constant, W.smooth⟩

theorem Homotopic.symm {W V : SmoothSweepout (N := N) (I := I) (M := M)}
    (h : W.Homotopic V) : V.Homotopic W := ContinuousMap.HomotopicWith.symm h

theorem Homotopic.trans {W V U : SmoothSweepout (N := N) (I := I) (M := M)}
    (h : W.Homotopic V) (k : V.Homotopic U) : W.Homotopic U :=
  ContinuousMap.HomotopicWith.trans h k

variable [IsManifold 𝓘(ℝ, Surface.Model) ∞ N] [T2Space N] [SigmaCompactSpace N]
  [IsManifold I ∞ M]

/-- Supremum of the energies of a single family. -/
def maxEnergy (q : SmoothRiemannianMetric 𝓘(ℝ, Surface.Model) N)
    (g : SmoothRiemannianMetric I M) (W : SmoothSweepout (N := N) (I := I) (M := M)) :
    ℝ≥0∞ := ⨆ u, Surface.dirichletEnergy q g (W.map u)

/-- Infimum over all smooth-slice sweepouts homotopic through smooth-slice
sweepouts to the given representative. Infinite values are retained. -/
def homotopyWidth (q : SmoothRiemannianMetric 𝓘(ℝ, Surface.Model) N)
    (g : SmoothRiemannianMetric I M) (W : SmoothSweepout (N := N) (I := I) (M := M)) :
    ℝ≥0∞ := ⨅ (V : SmoothSweepout (N := N) (I := I) (M := M)),
      ⨅ (_ : W.Homotopic V), maxEnergy q g V

theorem homotopyWidth_le_maxEnergy (q : SmoothRiemannianMetric 𝓘(ℝ, Surface.Model) N)
    (g : SmoothRiemannianMetric I M)
    {W V : SmoothSweepout (N := N) (I := I) (M := M)} (h : W.Homotopic V) :
    homotopyWidth q g W ≤ maxEnergy q g V :=
  iInf_le_of_le V (iInf_le_of_le h le_rfl)

theorem homotopyWidth_eq_of_homotopic (q : SmoothRiemannianMetric 𝓘(ℝ, Surface.Model) N)
    (g : SmoothRiemannianMetric I M)
    {W V : SmoothSweepout (N := N) (I := I) (M := M)} (h : W.Homotopic V) :
    homotopyWidth q g W = homotopyWidth q g V := by
  apply le_antisymm
  · exact le_iInf fun U => le_iInf fun hVU => homotopyWidth_le_maxEnergy q g (h.trans hVU)
  · exact le_iInf fun U => le_iInf fun hWU => homotopyWidth_le_maxEnergy q g (h.symm.trans hWU)

/-- Any strict upper bound on the infimum is attained as a strict upper
bound by some representative. No minimizing surface is asserted. -/
theorem exists_maxEnergy_lt (q : SmoothRiemannianMetric 𝓘(ℝ, Surface.Model) N)
    (g : SmoothRiemannianMetric I M) (W : SmoothSweepout (N := N) (I := I) (M := M))
    {a : ℝ≥0∞} (h : homotopyWidth q g W < a) :
    ∃ V, W.Homotopic V ∧ maxEnergy q g V < a := by
  obtain ⟨V, hV⟩ := iInf_lt_iff.mp h
  obtain ⟨hWV, henergy⟩ := iInf_lt_iff.mp hV
  exact ⟨V, hWV, henergy⟩

@[simp] theorem maxEnergy_const (q : SmoothRiemannianMetric 𝓘(ℝ, Surface.Model) N)
    (g : SmoothRiemannianMetric I M) (c : M) :
    maxEnergy q g (SmoothSweepout.const (N := N) (I := I) c) = 0 := by
  simp [maxEnergy, SmoothSweepout.const]

@[simp] theorem homotopyWidth_const (q : SmoothRiemannianMetric 𝓘(ℝ, Surface.Model) N)
    (g : SmoothRiemannianMetric I M) (c : M) :
    homotopyWidth q g (SmoothSweepout.const (N := N) (I := I) c) = 0 := by
  apply le_antisymm _ bot_le
  simpa using homotopyWidth_le_maxEnergy q g
    (homotopic_refl (SmoothSweepout.const (N := N) (I := I) c))

end OpenGA.RicciFlow.SmoothSweepout
