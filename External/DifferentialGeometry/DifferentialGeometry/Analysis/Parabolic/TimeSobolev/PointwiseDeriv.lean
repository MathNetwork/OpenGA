import DifferentialGeometry.Analysis.Sobolev.Embedding.TensorSobolevEmbeddingCm
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem maxreg_l2deriv_to_pointwise_hasderivwithinat
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] {T : ℝ} (u : timeH1 X T) {g : ℝ → X}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) T))
    (hrep : u.deriv =ᵐ[timeMeasure T] g) :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt u.toFun (g t) (Set.Ici (0 : ℝ)) t := by
  intro t ht
  have ht_icc : t ∈ Set.Icc (0 : ℝ) T :=
    ⟨ht.1, le_of_lt ht.2⟩
  have hderivIcc : HasDerivWithinAt u.toFun (g t) (Set.Icc (0 : ℝ) T) t :=
    u.hasDerivWithinAt_toFun_of_continuousOn hg hrep ht_icc
  have hIic : Set.Iic T ∈ nhds t := Iic_mem_nhds ht.2
  have hmem : Set.Icc (0 : ℝ) T ∈ nhdsWithin t (Set.Ici (0 : ℝ)) := by
    have : Set.Ici (0 : ℝ) ∩ Set.Iic T ∈ nhdsWithin t (Set.Ici (0 : ℝ)) :=
      inter_mem_nhdsWithin _ hIic
    simpa [Set.Ici_inter_Iic] using this
  exact hderivIcc.mono_of_mem_nhdsWithin hmem

theorem hasDerivAt_clm_apply_from_h1_time
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : ℝ → X →L[ℝ] Y) (L' : ℝ → X →L[ℝ] Y) (u : ℝ → X) (u' : ℝ → X)
    (t : ℝ) (_x : X)
    (hL : HasDerivAt L (L' t) t) (hu : HasDerivAt u (u' t) t) :
    HasDerivAt (fun s : ℝ => L s (u s)) (L' t (u t) + L t (u' t)) t :=
  hL.clm_apply hu

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
