import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSMemWkp
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderLimits
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderWkpNormBoundsProductSumEstimates
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderWkpNormBoundsLimitVanishingOffKernel

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section LowerOrderWkpNormBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

omit [CompleteSpace E] in
theorem wkpNorm_covPrincipalRotationCoeffLimit_le_unconditional
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (K : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s i α P₀ : EuclN → ℝ)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((partialLpLimit (I := I) (M := M)
                    g r s i α P k :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set partAtom : (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E))
      → EuclN → ℝ := fun pk y =>
    ((partialLpLimit (I := I) (M := M) g r s i α pk.1 pk.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  set F : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (principalRotationFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s i α x.1 x.2.2.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have h_data : ∀ x ∈ (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))),
      MemWkp (d := Module.finrank ℝ E) K 2 (F x) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F x) Ω
            ≤ ENNReal.ofReal C *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (partAtom (x.1, x.2.2.1)) Ω := by
    intro x _
    exact wkpNorm_indicatorFactor_mul_atom_le (I := I) (M := M) α K
      (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2)
      (partialLpLimit_memWkp (I := I) (M := M)
        g r s i α x.1 x.2.2.1 K h_pou)
      (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.1 x.2.2.1 K h_pou)
  obtain ⟨Csum, hCsum_nn, hCsum_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds (I := I) (M := M)
      (α := α) (K := K) F partAtom (fun x => (x.1, x.2.2.1))
      (fun x => (h_data x (Finset.mem_univ x)).2)
  have h_bound :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E), F x y) Ω
        ≤ ENNReal.ofReal (Csum * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
          * ∑ pk : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (partAtom pk) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ F partAtom
      (fun x => (x.1, x.2.2.1)) (fun x _ => Finset.mem_univ _)
      Csum hCsum_nn
      (fun x hx => (h_data x hx).1)
      (fun x _ => hCsum_bd x)
  have h_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E), F x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (principalRotationFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s i α P k :
                    EuclN → ℝ) y) := by
    funext y
    rw [hF_def]
    simp only [Fintype.sum_prod_type]
  have h_atom_eq : ∑ pk : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (partAtom pk) Ω
      = ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [Fintype.sum_prod_type]
  refine ⟨Csum * (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card,
    by positivity, ?_⟩
  rw [show (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s i α P₀ : EuclN → ℝ)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (principalRotationFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s i α P k :
                    EuclN → ℝ) y) from rfl]
  rw [← h_eq, hΩ_def, ← h_atom_eq]
  exact h_bound

omit [CompleteSpace E] in
theorem wkpNorm_covLowerOrderRotationValueCoeffLimit_le_unconditional
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (K : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s i α P₀ : EuclN → ℝ)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          ((∑ P : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((partialLpLimit (I := I) (M := M)
                      g r s i α P k :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) α))
            + (∑ p : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((componentLpLimit (I := I) (M := M)
                      g r s i α p :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set partAtom : (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E))
      → EuclN → ℝ := fun pk y =>
    ((partialLpLimit (I := I) (M := M) g r s i α pk.1 pk.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  set compAtom : TensorCompIdx (E := E) r s → EuclN → ℝ := fun p y =>
    ((componentLpLimit (I := I) (M := M) g r s i α p :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hcompAtom_def
  set Fpart : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valuePartialFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s i α x.1 x.2.2.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFpart_def
  set Fcomp : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valueComponentFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) y *
        ((componentLpLimit (I := I) (M := M) g r s i α x.2.2.2.2 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFcomp_def
  have h_part_data : ∀ x ∈ (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))),
      MemWkp (d := Module.finrank ℝ E) K 2 (Fpart x) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Fpart x) Ω
            ≤ ENNReal.ofReal C *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (partAtom (x.1, x.2.2.1)) Ω := by
    intro x _
    exact wkpNorm_indicatorFactor_mul_atom_le (I := I) (M := M) α K
      (valuePartialFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2)
      (partialLpLimit_memWkp (I := I) (M := M)
        g r s i α x.1 x.2.2.1 K h_pou)
      (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.1 x.2.2.1 K h_pou)
  have h_comp_data : ∀ x ∈ (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s)),
      MemWkp (d := Module.finrank ℝ E) K 2 (Fcomp x) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Fcomp x) Ω
            ≤ ENNReal.ofReal C *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (compAtom x.2.2.2.2) Ω := by
    intro x _
    exact wkpNorm_indicatorFactor_mul_atom_le (I := I) (M := M) α K
      (valueComponentFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (componentLpLimit_memWkp (I := I) (M := M)
        g r s i α x.2.2.2.2 K h_pou)
      (componentLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.2.2.2.2)
  obtain ⟨Cpart, hCpart_nn, hCpart_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds (I := I) (M := M)
      (α := α) (K := K) Fpart partAtom (fun x => (x.1, x.2.2.1))
      (fun x => (h_part_data x (Finset.mem_univ x)).2)
  obtain ⟨Ccomp, hCcomp_nn, hCcomp_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds (I := I) (M := M)
      (α := α) (K := K) Fcomp compAtom (fun x => x.2.2.2.2)
      (fun x => (h_comp_data x (Finset.mem_univ x)).2)
  have h_part_bound :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E), Fpart x y) Ω
        ≤ ENNReal.ofReal (Cpart * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
          * ∑ pk : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (partAtom pk) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ Fpart partAtom
      (fun x => (x.1, x.2.2.1)) (fun x _ => Finset.mem_univ _)
      Cpart hCpart_nn
      (fun x hx => (h_part_data x hx).1)
      (fun x _ => hCpart_bd x)
  have h_comp_bound :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
            Fcomp x y) Ω
        ≤ ENNReal.ofReal (Ccomp * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
              × TensorCompIdx (E := E) r s)).card)
          * ∑ p : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (compAtom p) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ Fcomp compAtom
      (fun x => x.2.2.2.2) (fun x _ => Finset.mem_univ _)
      Ccomp hCcomp_nn
      (fun x hx => (h_comp_data x hx).1)
      (fun x _ => hCcomp_bd x)
  have h_part_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E), Fpart x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (valuePartialFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s i α P k :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFpart_def]
    simp only [Fintype.sum_prod_type]
  have h_comp_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, Fcomp x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (valueComponentFactor (I := I) (M := M)
                        g r s α P₀ P Q k l p) y *
                    (componentLpLimit (I := I) (M := M) g r s i α p :
                      EuclN → ℝ) y) := by
    funext y
    rw [hFcomp_def]
    simp only [Fintype.sum_prod_type]
  have h_part_atom_eq : ∑ pk : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (partAtom pk) Ω
      = ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [Fintype.sum_prod_type]
  refine ⟨max
      (Cpart * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
      (Ccomp * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s)).card),
    le_trans (by positivity) (le_max_left _ _), ?_⟩
  set Cmax : ℝ := max
      (Cpart * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
      (Ccomp * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s)).card) with hCmax_def
  have hpart : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E), Fpart x y) Ω
      ≤ ENNReal.ofReal Cmax *
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [← h_part_atom_eq]
    refine h_part_bound.trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) (zero_le _)
  have hcomp : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
          Fcomp x y) Ω
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            Ω := by
    refine h_comp_bound.trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_right _ _)) (zero_le _)
  have h_part_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × Fin (Module.finrank ℝ E), Fpart x y) Ω :=
    memWkp_finsetSum (I := I) (M := M) _ (fun x hx => (h_part_data x hx).1)
  have h_comp_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
        Fcomp x y) Ω :=
    memWkp_finsetSum (I := I) (M := M) _ (fun x hx => (h_comp_data x hx).1)
  rw [show (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s i α P₀ : EuclN → ℝ)
      = (fun y => (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (valuePartialFactor (I := I) (M := M)
                        g r s α P₀ P Q k l) y *
                    (partialLpLimit (I := I) (M := M) g r s i α P k :
                      EuclN → ℝ) y)
          + ∑ P : TensorCompIdx (E := E) r s,
              ∑ Q : TensorCompIdx (E := E) r s,
                ∑ k : Fin (Module.finrank ℝ E),
                  ∑ l : Fin (Module.finrank ℝ E),
                    ∑ p : TensorCompIdx (E := E) r s,
                      Set.indicator (chartPouKernel (I := I) (M := M) α)
                          (valueComponentFactor (I := I) (M := M)
                            g r s α P₀ P Q k l p) y *
                        (componentLpLimit (I := I) (M := M)
                          g r s i α p : EuclN → ℝ) y) from rfl]
  have h_bridge : (fun y => (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (valuePartialFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s i α P k :
                    EuclN → ℝ) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ∑ p : TensorCompIdx (E := E) r s,
                    Set.indicator (chartPouKernel (I := I) (M := M) α)
                        (valueComponentFactor (I := I) (M := M)
                          g r s α P₀ P Q k l p) y *
                      (componentLpLimit (I := I) (M := M)
                        g r s i α p : EuclN → ℝ) y)
      = (fun y => (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E), Fpart x y)
          + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
              × TensorCompIdx (E := E) r s, Fcomp x y) := by
    funext y
    rw [← congrFun h_part_eq y, ← congrFun h_comp_eq y]
  rw [h_bridge]
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => (∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E), Fpart x y)
        + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
            × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, Fcomp x y) Ω
        ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ x : TensorCompIdx (E := E) r s
                × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
                × Fin (Module.finrank ℝ E), Fpart x y) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ x : TensorCompIdx (E := E) r s
                × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
                × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
                Fcomp x y) Ω :=
        wkpNorm_add_le (d := Module.finrank ℝ E)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_part_memWkp h_comp_memWkp
    _ ≤ ENNReal.ofReal Cmax *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((partialLpLimit (I := I) (M := M)
                    g r s i α P k :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω)
        + ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((componentLpLimit (I := I) (M := M)
                  g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y) Ω) :=
        add_le_add hpart hcomp
    _ = ENNReal.ofReal Cmax *
          ((∑ P : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((partialLpLimit (I := I) (M := M)
                      g r s i α P k :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) Ω)
            + (∑ p : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((componentLpLimit (I := I) (M := M)
                      g r s i α p :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) Ω)) := by
      rw [mul_add]

omit [CompleteSpace E] in
theorem wkpNorm_weightedGradCoeffDivLimit_le_unconditional
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (K : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l : EuclN → ℝ)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          ((∑ p : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((componentLpLimit (I := I) (M := M)
                    g r s i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) α))
            + (∑ p : TensorCompIdx (E := E) r s,
                ∑ l' : Fin (Module.finrank ℝ E),
                  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                    (fun y => ((partialLpLimit (I := I) (M := M)
                        g r s i α p l' :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set compAtom : TensorCompIdx (E := E) r s → EuclN → ℝ := fun p y =>
    ((componentLpLimit (I := I) (M := M) g r s i α p :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hcompAtom_def
  set partAtom : (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E))
      → EuclN → ℝ := fun pl y =>
    ((partialLpLimit (I := I) (M := M) g r s i α pl.1 pl.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  set Fcomp : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (euclidPartial (E := E) l
            (weightedGradFactor (I := I) (M := M)
              g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)) y *
        ((componentLpLimit (I := I) (M := M) g r s i α x.2.2.2 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFcomp_def
  set Fpart : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (weightedGradFactor (I := I) (M := M)
            g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s i α x.2.2.2 l :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFpart_def
  have h_comp_data : ∀ x ∈ (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)),
      MemWkp (d := Module.finrank ℝ E) K 2 (Fcomp x) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Fcomp x) Ω
            ≤ ENNReal.ofReal C *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (compAtom x.2.2.2) Ω := by
    intro x _
    exact wkpNorm_indicatorFactor_mul_atom_le (I := I) (M := M) α K
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)
      (componentLpLimit_memWkp (I := I) (M := M)
        g r s i α x.2.2.2 K h_pou)
      (componentLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.2.2.2)
  have h_part_data : ∀ x ∈ (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)),
      MemWkp (d := Module.finrank ℝ E) K 2 (Fpart x) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Fpart x) Ω
            ≤ ENNReal.ofReal C *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (partAtom (x.2.2.2, l)) Ω := by
    intro x _
    exact wkpNorm_indicatorFactor_mul_atom_le (I := I) (M := M) α K
      (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)
      (partialLpLimit_memWkp (I := I) (M := M)
        g r s i α x.2.2.2 l K h_pou)
      (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.2.2.2 l K h_pou)
  obtain ⟨Ccomp, hCcomp_nn, hCcomp_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds (I := I) (M := M)
      (α := α) (K := K) Fcomp compAtom (fun x => x.2.2.2)
      (fun x => (h_comp_data x (Finset.mem_univ x)).2)
  obtain ⟨Cpart, hCpart_nn, hCpart_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds (I := I) (M := M)
      (α := α) (K := K) Fpart partAtom (fun x => (x.2.2.2, l))
      (fun x => (h_part_data x (Finset.mem_univ x)).2)
  have h_comp_bound :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, Fcomp x y) Ω
        ≤ ENNReal.ofReal (Ccomp * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
          * ∑ p : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (compAtom p) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ Fcomp compAtom
      (fun x => x.2.2.2) (fun x _ => Finset.mem_univ _)
      Ccomp hCcomp_nn
      (fun x hx => (h_comp_data x hx).1)
      (fun x _ => hCcomp_bd x)
  have h_part_bound :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, Fpart x y) Ω
        ≤ ENNReal.ofReal (Cpart * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
          * ∑ pl : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (partAtom pl) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ Fpart partAtom
      (fun x => (x.2.2.2, l)) (fun x _ => Finset.mem_univ _)
      Cpart hCpart_nn
      (fun x hx => (h_part_data x hx).1)
      (fun x _ => hCpart_bd x)
  have h_comp_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s, Fcomp x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (euclidPartial (E := E) l
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p)) y *
                  (componentLpLimit (I := I) (M := M) g r s i α p :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFcomp_def]
    simp only [Fintype.sum_prod_type]
  have h_part_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s, Fpart x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (weightedGradFactor (I := I) (M := M)
                      g r s α P₀ l P Q k p) y *
                  (partialLpLimit (I := I) (M := M) g r s i α p l :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFpart_def]
    simp only [Fintype.sum_prod_type]
  have h_part_atom_eq : ∑ pl : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (partAtom pl) Ω
      = ∑ p : TensorCompIdx (E := E) r s,
          ∑ l' : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α p l' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [Fintype.sum_prod_type]
  refine ⟨max
      (Ccomp * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
      (Cpart * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card),
    le_trans (by positivity) (le_max_left _ _), ?_⟩
  set Cmax : ℝ := max
      (Ccomp * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
      (Cpart * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
    with hCmax_def
  have hcomp : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s, Fcomp x y) Ω
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            Ω := by
    refine h_comp_bound.trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) (zero_le _)
  have hpart : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s, Fpart x y) Ω
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          ∑ l' : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α p l' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [← h_part_atom_eq]
    refine h_part_bound.trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_right _ _)) (zero_le _)
  have h_comp_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s, Fcomp x y) Ω :=
    memWkp_finsetSum (I := I) (M := M) _ (fun x hx => (h_comp_data x hx).1)
  have h_part_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s, Fpart x y) Ω :=
    memWkp_finsetSum (I := I) (M := M) _ (fun x hx => (h_part_data x hx).1)
  rw [show (weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l : EuclN → ℝ)
      = (fun y => (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (euclidPartial (E := E) l
                        (weightedGradFactor (I := I) (M := M)
                          g r s α P₀ l P Q k p)) y *
                    (componentLpLimit (I := I) (M := M) g r s i α p :
                      EuclN → ℝ) y)
          + ∑ P : TensorCompIdx (E := E) r s,
              ∑ Q : TensorCompIdx (E := E) r s,
                ∑ k : Fin (Module.finrank ℝ E),
                  ∑ p : TensorCompIdx (E := E) r s,
                    Set.indicator (chartPouKernel (I := I) (M := M) α)
                        (weightedGradFactor (I := I) (M := M)
                          g r s α P₀ l P Q k p) y *
                      (partialLpLimit (I := I) (M := M) g r s i α p l :
                        EuclN → ℝ) y) from rfl]
  have h_bridge : (fun y => (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (euclidPartial (E := E) l
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p)) y *
                  (componentLpLimit (I := I) (M := M) g r s i α p :
                    EuclN → ℝ) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p) y *
                    (partialLpLimit (I := I) (M := M) g r s i α p l :
                      EuclN → ℝ) y)
      = (fun y => (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, Fcomp x y)
          + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
              Fpart x y) := by
    funext y
    rw [← congrFun h_comp_eq y, ← congrFun h_part_eq y]
  rw [h_bridge]
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => (∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s, Fcomp x y)
        + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
            × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
            Fpart x y) Ω
        ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ x : TensorCompIdx (E := E) r s
                × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
                × TensorCompIdx (E := E) r s, Fcomp x y) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ x : TensorCompIdx (E := E) r s
                × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
                × TensorCompIdx (E := E) r s, Fpart x y) Ω :=
        wkpNorm_add_le (d := Module.finrank ℝ E)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_comp_memWkp h_part_memWkp
    _ ≤ ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((componentLpLimit (I := I) (M := M)
                  g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y) Ω)
        + ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            ∑ l' : Fin (Module.finrank ℝ E),
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((partialLpLimit (I := I) (M := M)
                    g r s i α p l' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω) :=
        add_le_add hcomp hpart
    _ = ENNReal.ofReal Cmax *
          ((∑ p : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((componentLpLimit (I := I) (M := M)
                    g r s i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω)
            + (∑ p : TensorCompIdx (E := E) r s,
                ∑ l' : Fin (Module.finrank ℝ E),
                  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                    (fun y => ((partialLpLimit (I := I) (M := M)
                        g r s i α p l' :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y) Ω)) := by
      rw [mul_add]

end LowerOrderWkpNormBoundsUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
