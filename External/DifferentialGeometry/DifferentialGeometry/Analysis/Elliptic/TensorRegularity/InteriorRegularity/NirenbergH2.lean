import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.WeakSolution.WeakSolutionHeadline
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SmoothWeakSolutionH2


noncomputable section

open Bundle Manifold Set Filter MeasureTheory Topology
open scoped Manifold Topology ContDiff BigOperators Matrix InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in

omit [FiniteDimensional ℝ E] in
private lemma memLp_two_contDiff_hasCompactSupport_restrict
    {f : EuclN → ℝ} (hf_cd : ContDiff ℝ ∞ f) (hf_cs : HasCompactSupport f)
    (Ω' : Set EuclN) :
    MemLp f 2 ((volume : Measure EuclN).restrict Ω') :=
  (hf_cd.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2)
    hf_cs).restrict _

theorem tensor_h2_loc_chartComp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_supp : tsupport F.toFun ⊆ (chartAt H α).source)
    (hT_K : tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun)
    {Ω'' : Set EuclN} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    ∀ i k : Fin (Module.finrank ℝ E), ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (fun y : EuclN =>
          (fderiv ℝ (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) y)
            (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set EuclN, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧
        closure Ω' ⊆ (Set.univ : Set EuclN) ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g_ik x ^ 2 ∂(volume : Measure EuclN) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin (Module.finrank ℝ E),
                    ((fderiv ℝ
                      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) x)
                        (EuclideanSpace.single j 1)) ^ 2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω',
                  (tensorComponentEuclid (I := I) (M := M) g r s T α P₀ x) ^ 2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω',
                  (tensorComponentWeakRHS (I := I) (M := M)
                    g r s T F α hK hK_target P₀ x) ^ 2
                ∂(volume : Measure EuclN)) := by
  classical
  have h_weak :
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).IsSmoothWeakSolution
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀)
        (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀) :=
    tensorComponent_isSmoothWeakSolution (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_supp hF_supp hT_K hweak
  have hRHS_cd : ContDiff ℝ ∞
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀) :=
    tensorComponentWeakRHS_contDiff (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_supp hF_supp
  have hRHS_cs : HasCompactSupport
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀) :=
    tensorComponentWeakRHS_hasCompactSupport (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_supp hF_supp hT_K hweak
  have hf_l2_loc : ∀ {Ω' : Set EuclN}, IsCompact (closure Ω') →
      MemLp (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀)
        2 ((volume : Measure EuclN).restrict Ω') := by
    intro Ω' _
    exact memLp_two_contDiff_hasCompactSupport_restrict (E := E)
      hRHS_cd hRHS_cs Ω'
  have h_closure_in :
      closure Ω'' ⊆ (Set.univ : Set EuclN) := fun y _ => Set.mem_univ y
  have h_room :
      Metric.cthickening 2 (closure Ω'') ⊆ (Set.univ : Set EuclN) :=
    fun y _ => Set.mem_univ y
  obtain ⟨C, hC_nn, h_eng⟩ := loc_smooth_solution
    (d := Module.finrank ℝ E)
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target)
    hΩ'' hΩ''_compact_closure h_closure_in h_room
  intro i k
  obtain ⟨g_ik, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, hbound⟩ := h_eng h_weak hf_l2_loc i k
  exact ⟨g_ik, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, C, hC_nn, hbound⟩

theorem tensor_h2_loc_chartComp_all
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_supp : tsupport F.toFun ⊆ (chartAt H α).source)
    (hT_K : ∀ P₀ : CompIdx E r s,
      tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun)
    {Ω'' : Set EuclN} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    ∀ (P₀ : CompIdx E r s) (i k : Fin (Module.finrank ℝ E)),
      ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (fun y : EuclN =>
          (fderiv ℝ (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) y)
            (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set EuclN, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧
        closure Ω' ⊆ (Set.univ : Set EuclN) ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g_ik x ^ 2 ∂(volume : Measure EuclN) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin (Module.finrank ℝ E),
                    ((fderiv ℝ
                      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) x)
                        (EuclideanSpace.single j 1)) ^ 2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω',
                  (tensorComponentEuclid (I := I) (M := M) g r s T α P₀ x) ^ 2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω',
                  (tensorComponentWeakRHS (I := I) (M := M)
                    g r s T F α hK hK_target P₀ x) ^ 2
                ∂(volume : Measure EuclN)) :=
  fun P₀ => tensor_h2_loc_chartComp (I := I) (M := M)
    g r s T F α hK hK_target P₀ hT_supp hF_supp (hT_K P₀) hweak hΩ'' hΩ''_compact_closure

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
