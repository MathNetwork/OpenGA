import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import Mathlib.Geometry.Manifold.VectorBundle.Hom

















noncomputable section
open Set Function Filter Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]









omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] in
theorem slice_mfderiv_continuousAt_of_jointFlow
    (Φg : M → ℝ → M) {O : Set ℝ} (hO : IsOpen O) {s₀ : ℝ} (hs₀ : s₀ ∈ O)
    (hΦg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φg q.2 q.1) (O ×ˢ Set.univ))
    (y : M) (u : TangentSpace I y) :
    ContinuousAt (fun s : ℝ => (TotalSpace.mk' E (Φg y s)
      (mfderiv I I (fun x => Φg x s) y u) : TangentBundle I M)) s₀ := by
  have hf : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞
      (Function.uncurry (fun s x => Φg x s)) (O ×ˢ Set.univ) (s₀, y) :=
    hΦg (s₀, y) ⟨hs₀, Set.mem_univ _⟩
  have hg : ContMDiffWithinAt (𝓘(ℝ, ℝ)) I ∞ (fun _ : ℝ => y) O s₀ := contMDiffWithinAt_const
  have hmf := ContMDiffWithinAt.mfderivWithin (J := 𝓘(ℝ, ℝ)) (I := I) (I' := I)
    (n := ∞) (m := ∞) (f := fun s x => Φg x s) (g := fun _ : ℝ => y) (t := O) (u := Set.univ)
    hf hg hs₀ (Set.mapsTo_univ _ _) (le_refl _) uniqueMDiffOn_univ
  have hmfAt := hmf.contMDiffAt (hO.mem_nhds hs₀)
  have hb₂ : ContMDiffAt (𝓘(ℝ, ℝ)) I ∞ (fun s : ℝ => Φg y s) s₀ := by
    have hcomp : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞ (fun s : ℝ => (s, y)) s₀ :=
      contMDiffAt_id.prodMk contMDiffAt_const
    exact ((hΦg.contMDiffAt ((hO.prod isOpen_univ).mem_nhds ⟨hs₀, Set.mem_univ _⟩)).comp s₀ hcomp)
  have hv : ContMDiffAt (𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun _ : ℝ => (TotalSpace.mk' E y u : TangentBundle I M)) s₀ := contMDiffAt_const
  have happ := ContMDiffAt.clm_apply_of_inCoordinates
    (F₁ := E) (E₁ := TangentSpace I (M := M)) (F₂ := E) (E₂ := TangentSpace I (M := M))
    (IB₁ := I) (IB₂ := I) (IM := 𝓘(ℝ, ℝ)) (n := ∞)
    (b₁ := fun _ : ℝ => y) (b₂ := fun s : ℝ => Φg y s) (m₀ := s₀)
    (ϕ := fun s : ℝ => mfderivWithin I I (fun x => Φg x s) Set.univ y)
    (v := fun _ : ℝ => u)
    hmfAt hv hb₂
  have hcont := happ.continuousAt
  simp only [mfderivWithin_univ] at hcont
  exact hcont

end DifferentialGeometry.PDE.RicciFlow.ODE
