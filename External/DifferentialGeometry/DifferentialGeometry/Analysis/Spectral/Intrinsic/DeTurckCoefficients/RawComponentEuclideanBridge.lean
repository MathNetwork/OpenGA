import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartGramRealizeDiffJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.IteratedCovGradChartJetPeel


noncomputable section

set_option maxHeartbeats 1600000

open Manifold Set Filter Topology
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma rawPullR_eq_rawCompOnE_comp (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx =
      tensorChartComponentOnModel (I := I) (M := M) g S α Jdx ∘ (toEuclidean (E := E)).symm := by
  funext y
  rw [tensorComponentEuclideanChart, Function.comp_apply, Function.comp_apply, Function.comp_apply, tensorChartComponentOnModel]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma norm_iteratedFDeriv_rawPullR_le_iteratedFDerivWithin_rawCompOnE
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m : ℕ) {y : EuclN}
    (hy : (toEuclidean (E := E)).symm y ∈ interior (extChartAt I α).target) :
    ‖iteratedFDeriv ℝ m (tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α
        (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) y‖ ≤
      ‖((toEuclidean (E := E)).symm : EuclN →L[ℝ] E)‖ ^ m *
        ‖iteratedFDerivWithin ℝ m (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx)
          (interior (extChartAt I α).target) ((toEuclidean (E := E)).symm y)‖ := by
  classical
  set e : EuclN ≃L[ℝ] E := (toEuclidean (E := E)).symm with he_def
  set O : Set E := interior (extChartAt I α).target with hO_def
  have hO_open : IsOpen O := isOpen_interior
  have hUD : UniqueDiffOn ℝ O := hO_open.uniqueDiffOn

  rw [rawPullR_eq_rawCompOnE_comp (I := I) (M := M) g S α Jdx]

  have hpre_open : IsOpen (e ⁻¹' O) := hO_open.preimage e.continuous
  have hy_pre : y ∈ e ⁻¹' O := hy

  have hplain : iteratedFDeriv ℝ m (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx ∘ ⇑e) y =
      iteratedFDerivWithin ℝ m (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx ∘ ⇑e) (e ⁻¹' O) y :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
      (f := tensorChartComponentOnModel (I := I) (M := M) g S α Jdx ∘ ⇑e) m hpre_open hy_pre).symm
  rw [hplain]

  have hcomp := e.iteratedFDerivWithin_comp_right (f := tensorChartComponentOnModel (I := I) (M := M) g S α Jdx)
    hUD (x := y) hy m
  rw [hcomp]

  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

  have he_norm : ‖(e : EuclN →L[ℝ] E)‖ = ‖((toEuclidean (E := E)).symm : EuclN →L[ℝ] E)‖ := rfl
  rw [he_norm, mul_comm]




omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma rawCompJet_le
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m : ℕ) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    ‖iteratedFDerivWithin ℝ m (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx)
        (interior (extChartAt I α).target) y‖ ≤
      ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ m *
        ‖iteratedFDeriv ℝ m (tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α
          (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
          (toEuclidean (E := E) y)‖ := by
  classical
  set e : E ≃L[ℝ] EuclN := toEuclidean (E := E) with he_def
  set O : Set E := interior (extChartAt I α).target with hO_def
  have hO_open : IsOpen O := isOpen_interior
  have hcompose : tensorChartComponentOnModel (I := I) (M := M) g S α Jdx =
      tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α
        (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx ∘ ⇑e := by
    have h := rawPullR_eq_rawCompOnE_comp (I := I) (M := M) g S α Jdx
    funext z
    have hz := congrFun h (e z)
    simp only [Function.comp_apply, he_def] at hz ⊢
    rw [hz, ContinuousLinearEquiv.symm_apply_apply]
  rw [hcompose]
  set Oe : Set EuclN := e '' O with hOe_def
  have hOe_open : IsOpen Oe := e.isOpenMap O hO_open
  have hUDe : UniqueDiffOn ℝ Oe := hOe_open.uniqueDiffOn
  have hpre : (⇑e) ⁻¹' Oe = O := by
    rw [hOe_def, Set.preimage_image_eq _ e.injective]
  have hey : e y ∈ Oe := ⟨y, hy, rfl⟩
  have hcr := e.iteratedFDerivWithin_comp_right
    (f := tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
    hUDe (x := y) hey m
  rw [hpre] at hcr
  rw [hcr]
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m hOe_open hey]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]




omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem bareOnE_le_bare
    (g : SmoothRiemannianMetric I M) (α : M) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensor g 0 2) {y : E},
      y ∈ interior (extChartAt I α).target →
      chartComponentJetSeminormSum (I := I) (M := M) g S α N y ≤
        C * bareChartJetContent (I := I) (M := M) g 0 2 S α N
          (toEuclidean (E := E) y) := by
  classical
  let A : ℝ := ∑ m ∈ Finset.range (N + 1),
    ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ m
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _
  let C : ℝ :=
    ∑ _Jdx : Fin 2 → Fin (Module.finrank ℝ E),
      ∑ _m ∈ Finset.range (N + 1), A
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hA
  refine ⟨C, hC, ?_⟩
  intro S y hy
  set B : ℝ := bareChartJetContent (I := I) (M := M) g 0 2 S α N
    (toEuclidean (E := E) y) with hB_def
  have hB : 0 ≤ B := by
    rw [hB_def]
    exact bareChartJetContent_nonneg (I := I) (M := M) g 0 2 S α N _
  have hterm : ∀ (Jdx : Fin 2 → Fin (Module.finrank ℝ E))
      (m : ℕ), m ∈ Finset.range (N + 1) →
      ‖iteratedFDerivWithin ℝ m (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx)
          (interior (extChartAt I α).target) y‖ ≤ A * B := by
    intro Jdx m hm
    have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hpow : ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ m ≤ A := by
      dsimp [A]
      exact Finset.single_le_sum
        (fun q _ => pow_nonneg (norm_nonneg _) q) hm
    have hraw := iteratedFDeriv_rawPullR_le_bareChartJetContent
      (I := I) (M := M) g 0 2 S α
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx hmN
      (toEuclidean (E := E) y)
    refine (rawCompJet_le (I := I) (M := M) g S α Jdx m hy).trans ?_
    exact mul_le_mul hpow (hB_def ▸ hraw) (norm_nonneg _) hA
  unfold chartComponentJetSeminormSum
  calc
    (∑ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
        ∑ m ∈ Finset.range (N + 1),
          ‖iteratedFDerivWithin ℝ m (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx)
            (interior (extChartAt I α).target) y‖)
        ≤ ∑ _Jdx : Fin 2 → Fin (Module.finrank ℝ E),
            ∑ _m ∈ Finset.range (N + 1), A * B :=
      Finset.sum_le_sum fun Jdx _ =>
        Finset.sum_le_sum fun m hm => hterm Jdx m hm
    _ = ∑ _Jdx : Fin 2 → Fin (Module.finrank ℝ E),
          (∑ _m ∈ Finset.range (N + 1), A) * B := by
      refine Finset.sum_congr rfl fun _ _ => ?_
      dsimp [A]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    _ = C * B := by
      dsimp [C]
      simp only [Finset.sum_const, Finset.card_range, Finset.card_univ,
        nsmul_eq_mul]
      ring
    _ = C * bareChartJetContent (I := I) (M := M) g 0 2 S α N
          (toEuclidean (E := E) y) := by rw [hB_def]

end DifferentialGeometry.PDE.RicciFlow
