import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifold
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuant
import DifferentialGeometry.Analysis.Sobolev.Tools.StrictStrongSupport
import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.Approximation.ContMDiffDenseLemmas


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] in
private lemma wkpNorm_eta_target_le_split
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (_hp_top : p ≠ (⊤ : ℝ≥0∞))
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {η : EuclN → ℝ} (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    {C0 C1 : ℝ} (hC0_nn : 0 ≤ C0) (_hC1_nn : 0 ≤ C1)
    (hη0 : ∀ x ∈ Ω, ‖η x‖ ≤ C0)
    (hη1 : ∀ x ∈ Ω, ‖fderiv ℝ η x‖ ≤ C1)
    {u : EuclN → ℝ}
    (hu : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) 1 p u Ω) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p (fun x => η x * u x) Ω ≤
      ENNReal.ofReal C0 *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p u Ω +
      ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) * ENNReal.ofReal C1 *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p u Ω := by
  classical
  letI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  have hLHS_unfold : DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 p (fun x => η x * u x) Ω =
        eLpNorm (fun x => η x * u x) p (volume.restrict Ω) +
        ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
              (d := Module.finrank ℝ E) p 1 α' (fun x => η x * u x) Ω) p
            (volume.restrict Ω) := by
    unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
    rw [show (1 : ℕ) + 1 = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
    have h0_unique : ∀ α' : Fin 0 → Fin (Module.finrank ℝ E),
        α' = (fun i : Fin 0 => i.elim0) := fun α' => by funext i; exact i.elim0
    haveI : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
      { default := fun i : Fin 0 => i.elim0
        uniq := fun α' => (h0_unique α').symm ▸ rfl }
    rw [Fintype.sum_unique
          (f := fun α' : Fin 0 → Fin (Module.finrank ℝ E) =>
            eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
                (d := Module.finrank ℝ E) p 0 α' (fun x => η x * u x) Ω) p
              (volume.restrict Ω))]
    simp [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
  have hRHS_unfold : DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 p u Ω =
        eLpNorm u p (volume.restrict Ω) +
        ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
              (d := Module.finrank ℝ E) p 1 α' u Ω) p
            (volume.restrict Ω) := by
    unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
    rw [show (1 : ℕ) + 1 = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
    have h0_unique : ∀ α' : Fin 0 → Fin (Module.finrank ℝ E),
        α' = (fun i : Fin 0 => i.elim0) := fun α' => by funext i; exact i.elim0
    haveI : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
      { default := fun i : Fin 0 => i.elim0
        uniq := fun α' => (h0_unique α').symm ▸ rfl }
    rw [Fintype.sum_unique
          (f := fun α' : Fin 0 → Fin (Module.finrank ℝ E) =>
            eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
                (d := Module.finrank ℝ E) p 0 α' u Ω) p
              (volume.restrict Ω))]
    simp [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
  have hIter1_eta_u : ∀ α' : Fin 1 → Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
          (d := Module.finrank ℝ E) p 1 α' (fun x => η x * u x) Ω =
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p (α' 0) (fun x => η x * u x) Ω := by
    intro α'
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_succ]; rfl
  have hIter1_u : ∀ α' : Fin 1 → Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
          (d := Module.finrank ℝ E) p 1 α' u Ω =
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p (α' 0) u Ω := by
    intro α'
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_succ]; rfl
  have hLHS_unfold' : DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 p (fun x => η x * u x) Ω =
        eLpNorm (fun x => η x * u x) p (volume.restrict Ω) +
        ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p (α' 0) (fun x => η x * u x) Ω) p
            (volume.restrict Ω) := by
    rw [hLHS_unfold]
    refine congrArg (eLpNorm (fun x => η x * u x) p (volume.restrict Ω) + ·) ?_
    refine Finset.sum_congr rfl (fun α' _ => ?_)
    rw [hIter1_eta_u α']
  have hRHS_unfold' : DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 p u Ω =
        eLpNorm u p (volume.restrict Ω) +
        ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p (α' 0) u Ω) p
            (volume.restrict Ω) := by
    rw [hRHS_unfold]
    refine congrArg (eLpNorm u p (volume.restrict Ω) + ·) ?_
    refine Finset.sum_congr rfl (fun α' _ => ?_)
    rw [hIter1_u α']
  have hLp_bound : eLpNorm (fun x => η x * u x) p (volume.restrict Ω) ≤
      ENNReal.ofReal C0 * eLpNorm u p (volume.restrict Ω) := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := u) (c := C0) ?_ p
    refine (ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    calc
      ‖η x * u x‖ = ‖η x‖ * ‖u x‖ := norm_mul _ _
      _ ≤ C0 * ‖u x‖ := by gcongr; exact hη0 x hx
  have hu_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p u Ω := hu.memW1p
  set Cmax : ℝ := max C0 C1 with hCmax_def
  have hCmax_nn : 0 ≤ Cmax := le_max_of_le_left hC0_nn
  have hη0_max : ∀ x ∈ Ω, ‖η x‖ ≤ Cmax := fun x hx =>
    (hη0 x hx).trans (le_max_left _ _)
  have hη1_max : ∀ x ∈ Ω, ‖fderiv ℝ η x‖ ≤ Cmax := fun x hx =>
    (hη1 x hx).trans (le_max_right _ _)
  have h_chosen_bnd : ∀ i : Fin (Module.finrank ℝ E),
      eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) p i (fun x => η x * u x) Ω) p
          (volume.restrict Ω) ≤
        ENNReal.ofReal C0 *
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p i u Ω) p (volume.restrict Ω) +
        ENNReal.ofReal C1 * eLpNorm u p (volume.restrict Ω) := by
    intro i
    classical
    have hae := DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_smul_smooth_bounded_ae
      (d := Module.finrank ℝ E) hp_one hΩ_open hη_smooth hη0_max hη1_max hu_W1p i
    have hηcwp_meas : AEStronglyMeasurable
        (fun x => η x * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p i u Ω x)
        (volume.restrict Ω) :=
      hη_smooth.continuous.aestronglyMeasurable.mul
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
          hu_W1p i).aestronglyMeasurable
    have hderiv_cont : Continuous
        (fun x : EuclN => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ))) :=
      (hη_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const
    have hdηu_meas : AEStronglyMeasurable
        (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x)
        (volume.restrict Ω) :=
      hderiv_cont.aestronglyMeasurable.mul hu.memLp.aestronglyMeasurable
    rw [eLpNorm_congr_ae hae]
    have hSumEq :
        (fun x => η x * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p i u Ω x +
          (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x) =
        (fun x => η x * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) p i u Ω x) +
        (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x) := by
      funext x
      simp [Pi.add_apply]
    rw [hSumEq]
    have htriangle :
        eLpNorm
            ((fun x => η x * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p i u Ω x) +
              fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x)
            p (volume.restrict Ω)
          ≤ eLpNorm (fun x => η x * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p i u Ω x) p (volume.restrict Ω) +
            eLpNorm
              (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x)
              p (volume.restrict Ω) :=
      eLpNorm_add_le hηcwp_meas hdηu_meas hp_one
    refine htriangle.trans ?_
    have hbnd1 :
        eLpNorm (fun x => η x * DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p i u Ω x) p (volume.restrict Ω) ≤
          ENNReal.ofReal C0 *
            eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) p i u Ω) p (volume.restrict Ω) :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_eta_mul_le
        (d := Module.finrank ℝ E) hΩ_open hη0
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' p i u Ω)
    have hbnd2 :
        eLpNorm (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x) p
            (volume.restrict Ω) ≤
          ENNReal.ofReal C1 * eLpNorm u p (volume.restrict Ω) :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_partial_eta_mul_le
        (d := Module.finrank ℝ E) hΩ_open hη1 i u
    exact add_le_add hbnd1 hbnd2
  rw [hLHS_unfold', hRHS_unfold']
  have hGrad_LHS_bnd :
      ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) p (α' 0) (fun x => η x * u x) Ω) p
          (volume.restrict Ω) ≤
      ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
        (ENNReal.ofReal C0 *
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p (α' 0) u Ω) p (volume.restrict Ω) +
        ENNReal.ofReal C1 * eLpNorm u p (volume.restrict Ω)) :=
    Finset.sum_le_sum (fun α' _ => h_chosen_bnd (α' 0))
  refine (add_le_add hLp_bound hGrad_LHS_bnd).trans ?_
  have hSum_split :
      ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
        (ENNReal.ofReal C0 *
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p (α' 0) u Ω) p (volume.restrict Ω) +
        ENNReal.ofReal C1 * eLpNorm u p (volume.restrict Ω)) =
        (∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
          ENNReal.ofReal C0 *
            eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) p (α' 0) u Ω) p (volume.restrict Ω)) +
        ∑ _α' : Fin 1 → Fin (Module.finrank ℝ E),
          ENNReal.ofReal C1 * eLpNorm u p (volume.restrict Ω) := Finset.sum_add_distrib
  rw [hSum_split]
  have hCard : (Finset.univ : Finset (Fin 1 → Fin (Module.finrank ℝ E))).card =
      Module.finrank ℝ E := by
    rw [Finset.card_univ]; simp
  have hSum_const :
      ∑ _α' : Fin 1 → Fin (Module.finrank ℝ E),
        ENNReal.ofReal C1 * eLpNorm u p (volume.restrict Ω) =
        ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal C1 * eLpNorm u p (volume.restrict Ω)) := by
    rw [Finset.sum_const, hCard, nsmul_eq_mul]
  rw [hSum_const]
  have hSum_factor :
      ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
        ENNReal.ofReal C0 *
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) p (α' 0) u Ω) p (volume.restrict Ω) =
      ENNReal.ofReal C0 * ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) p (α' 0) u Ω) p (volume.restrict Ω) := by
    rw [Finset.mul_sum]
  rw [hSum_factor]
  set Au : ℝ≥0∞ := eLpNorm u p (volume.restrict Ω) with hAu_def
  set SBu : ℝ≥0∞ := ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
    eLpNorm
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p (α' 0) u Ω) p (volume.restrict Ω) with hSBu_def
  set OC0 : ℝ≥0∞ := ENNReal.ofReal C0 with hOC0_def
  set OC1 : ℝ≥0∞ := ENNReal.ofReal C1 with hOC1_def
  set Nat_d : ℝ≥0∞ := ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) with hNd_def
  change OC0 * Au + (OC0 * SBu + Nat_d * (OC1 * Au)) ≤
    OC0 * (Au + SBu) + Nat_d * OC1 * (Au + SBu)
  rw [mul_add OC0 Au SBu, mul_add (Nat_d * OC1) Au SBu]
  have hAssoc : Nat_d * (OC1 * Au) = Nat_d * OC1 * Au := by ring
  rw [hAssoc]
  have hRearrange : OC0 * Au + (OC0 * SBu + Nat_d * OC1 * Au) =
      OC0 * Au + OC0 * SBu + Nat_d * OC1 * Au := by ring
  rw [hRearrange]
  refine add_le_add (le_refl _) ?_
  exact le_self_add

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
