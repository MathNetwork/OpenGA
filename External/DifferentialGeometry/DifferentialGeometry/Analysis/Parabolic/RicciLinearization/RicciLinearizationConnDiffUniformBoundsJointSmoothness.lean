import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CorrFieldChristoffelCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovDerivConnDiffQuadraticBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseMetricPerturbationFibreBound
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Geometry.Metric.MetricBounds
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffUniformBoundsSlotPermutations


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators Matrix Interval

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section JointSmoothness

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem jointField_add {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact ((e.linear ℝ hx).map_add (A p) (B p)).symm
  · exact ((e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem jointField_sub {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact ((e.linear ℝ hx).map_sub (A p) (B p)).symm
  · exact ((e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem jointField_smul {d : ℕ} {S : Set ℝ} (a : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (a • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := a)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact ((e.linear ℝ hx).map_smul a (A p)).symm
  · exact ((e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      a (A p₀)).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem jointField_neg {d : ℕ} {S : Set ℝ}
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (-A p))
      ((Set.univ : Set M) ×ˢ S) := by
  have h := jointField_smul (I := I) (M := M) (d := d) (S := S) (-1 : ℝ) A hA
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 t) ?_
  rw [neg_one_smul]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem slotPermField_jointContMDiffOn {d : ℕ} (ρ : Equiv.Perm (Fin d)) {S : Set ℝ}
    (Z : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (Z p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1
        (slotPermCLM (I := I) ρ p.1 (Z p)))
      ((Set.univ : Set M) ×ˢ S) := by
  have h := domDomCongrField_jointContMDiffOn (I := I) ρ (S := S) Z hZ
  refine h.congr (fun p _ => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 t)
    (slotPermCLM_apply (I := I) ρ p.1 (Z p))

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem tensorProdField_jointContMDiffOn (m k : ℕ) {S : Set ℝ}
    (P : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace m I p.1)
    (Q : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace k I p.1)
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel m ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel m ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace m I z) p.1 (P p))
      ((Set.univ : Set M) ×ˢ S))
    (hQ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel k ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel k ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace k I z) p.1 (Q p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (m + k) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + k) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + k) I z) p.1
        (tensorProdWithCLM (I := I) m k p.1 (P p) (Q p)))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) m
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) k
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (m + k)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hP' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel m ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace m I z)).mp (hP p₀ hp₀)
  have hQ' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel k ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace k I z)).mp (hQ p₀ hp₀)
  have h_combine : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.Tensor0SModel (m + k) ℝ E) ∞
      (fun p : M × ℝ => Bundle.continuousMultilinearMap.modelProductL (𝕜 := ℝ) (F := E) m k
        ((trivializationAt (Tensor0SBundle.Tensor0SModel m ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace m I z) x₀ ⟨p.1, P p⟩).2)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀ ⟨p.1, Q p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    ((contMDiffWithinAt_const (c := Bundle.continuousMultilinearMap.modelProductL
        (𝕜 := ℝ) (F := E) m k)).clm_apply hP'.2).clm_apply hQ'.2
  have hpointwise : ∀ p : M × ℝ,
      p.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
      (trivializationAt (Tensor0SBundle.Tensor0SModel (m + k) ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace (m + k) I z) x₀
        ⟨p.1, tensorProdWithCLM (I := I) m k p.1 (P p) (Q p)⟩).2 =
      Bundle.continuousMultilinearMap.modelProductL (𝕜 := ℝ) (F := E) m k
        ((trivializationAt (Tensor0SBundle.Tensor0SModel m ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace m I z) x₀ ⟨p.1, P p⟩).2)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀ ⟨p.1, Q p⟩).2) := by
    intro p hx
    apply ContinuousMultilinearMap.ext
    intro v
    rw [Bundle.continuousMultilinearMap.modelProductL_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    set symmL := (trivializationAt E (TangentSpace I) x₀).symmL ℝ p.1 with hsymmL
    change (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
        (Tensor0SBundle.Tensor0SSpace.toModel (P p))
        (Tensor0SBundle.Tensor0SSpace.toModel (Q p)))
        (fun i => symmL (v i)) = _
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rfl
  refine h_combine.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact hpointwise p hx
  · exact hpointwise p₀ (by rw [← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem connContrField_jointContMDiffOn (m k : ℕ) {S : Set ℝ}
    (Bf : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace 1 (k + 1) I p.1)
    (hBf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (k + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (k + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (k + 1) I z) p.1 (Bf p))
      ((Set.univ : Set M) ×ˢ S))
    (Df : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (m + 1) I p.1)
    (hDf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (m + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1) I z) p.1 (Df p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (m + 1 + k) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + 1 + k) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1 + k) I z) p.1
        (connContrCLM (I := I) m k p.1 (Bf p) (Df p)))
      ((Set.univ : Set M) ×ˢ S) := by
  have hΨ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (m + 1 + k + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (m + 1 + k + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I z) p.1
        (show Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I p.1 from
          (tensorProdWithCLM (I := I) (m + 1) (k + 1) p.1 (Df p)).comp
            (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (k + 1) I p.1 from Bf p)))
      ((Set.univ : Set M) ×ˢ S) := by
    apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
      (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E)
      (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z)
      (F₂ := Tensor0SBundle.Tensor0SModel (m + 1 + k + 1) ℝ E)
      (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1 + k + 1) I z)
      (φ := fun p : M × ℝ =>
        (tensorProdWithCLM (I := I) (m + 1) (k + 1) p.1 (Df p)).comp
          (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (k + 1) I p.1 from Bf p))
      (S := S)
    intro om
    have homj : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) p.1 (om p.1))
        ((Set.univ : Set M) ×ˢ S) :=
      om.contMDiff.comp_contMDiffOn contMDiffOn_fst
    have hBom : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (k + 1) ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (k + 1) ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace (k + 1) I z) p.1
          ((show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (k + 1) I p.1 from Bf p) (om p.1)))
        ((Set.univ : Set M) ×ˢ S) :=
      ContMDiffOn.clm_bundle_apply (b := Prod.fst) hBf homj
    have hprod := tensorProdField_jointContMDiffOn (I := I) (M := M) (m + 1) (k + 1) (S := S)
      (fun p => Df p)
      (fun p => (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (k + 1) I p.1 from Bf p) (om p.1))
      hDf hBom
    refine hprod.congr (fun p _ => ?_)
    exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + 1 + k + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1 + k + 1) I z) p.1 t) rfl
  have hTr := contractTraceField_jointContMDiffOn (I := I) 0 (m + 1 + k) (S := S)
    (fun p : M × ℝ =>
      (show Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I p.1 from
        (tensorProdWithCLM (I := I) (m + 1) (k + 1) p.1 (Df p)).comp
          (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (k + 1) I p.1 from Bf p)))
    hΨ
  have hunit : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) p.1
        (Integral.Connection.unitZeroSec (I := I) (M := M) p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    (Integral.Connection.unitZeroSec (I := I) (M := M)).contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hEval := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hTr hunit
  refine hEval.congr (fun p _ => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + 1 + k) ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1 + k) I z) p.1 t) rfl

set_option backward.isDefEq.respectTransparency false in

private theorem connDiffSection_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 2 I z) p.1
        ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  let φ : ∀ p : M × ℝ,
      Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I p.1 :=
    fun p =>
      (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        raisedKoszulFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1).comp
          ((g0FlatCLM (I := I) g₀ p.1).comp
            (inverseMetricSharpFib (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
  have happly : ∀ om : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 1 ℝ E,
      (fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z)⟯,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (φ p (om p.1)))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    intro om
    have homj : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) p.1 (om p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
      om.contMDiff.comp_contMDiffOn contMDiffOn_fst
    have hsharpom := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
      (inverseMetricSharpField_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ') homj
    have hflatj : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)
          (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 1 I z) p.1
          (g0FlatCLM (I := I) g₀ p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
      (g0FlatField_contMDiff (I := I) g₀).comp_contMDiffOn contMDiffOn_fst
    have hflatom := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hflatj hsharpom
    have hkosom := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
      (corrField_raisedKoszulFib_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ') hflatom
    refine hkosom.congr (fun p _ => ?_)
    rfl
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := φ)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    happly
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 2 I z) p.1 t) ?_
  dsimp only [φ]
  rw [connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' p.2)]
  rw [appCcRS_toSection, raisedKoszul_toSection, sharpFlatEndoCc_toSection]
  rfl

private theorem covGradConnDiff_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 3 I z) p.1
        ((covGrad (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀)).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have h := covGrad_step_jointContMDiffOn (I := I) (M := M) g₀ 1 2
    (fun s => connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)
    (realizedSmallSet (δ := δ) (δ' := δ'))
    (connDiffSection_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ')
  exact h

set_option backward.isDefEq.respectTransparency false in

private theorem order1CLM_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Z : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 3 I p.1)
    (hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Z p))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1
        (linearizedRicciConnDiffOrder1CLM (I := I) p.1
          ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀).toSection p.1)
          (Z p)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  set S := realizedSmallSet (δ := δ) (δ' := δ') with hS
  set Af : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace 1 2 I p.1 :=
    fun p => (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀).toSection p.1
    with hAf
  have hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 2 I z) p.1 (Af p))
      ((Set.univ : Set M) ×ˢ S) :=
    connDiffSection_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hpre102 := slotPermField_jointContMDiffOn (I := I) cdPerm3_102 (S := S) Z hZ
  have hpre120 := slotPermField_jointContMDiffOn (I := I) cdPerm3_120 (S := S) Z hZ
  have h₁ := slotPermField_jointContMDiffOn (I := I) cdPerm4_0312 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => slotPermCLM (I := I) cdPerm3_102 p.1 (Z p)) hpre102)
  have h₂ := slotPermField_jointContMDiffOn (I := I) cdPerm4_0213 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => slotPermCLM (I := I) cdPerm3_120 p.1 (Z p)) hpre120)
  have h₃ := slotPermField_jointContMDiffOn (I := I) cdPerm4_2301 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA (fun p => Z p) hZ)
  have h₄ := slotPermField_jointContMDiffOn (I := I) cdPerm4_1302 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => slotPermCLM (I := I) cdPerm3_102 p.1 (Z p)) hpre102)
  have h₅ := slotPermField_jointContMDiffOn (I := I) cdPerm4_1203 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => slotPermCLM (I := I) cdPerm3_120 p.1 (Z p)) hpre120)
  have hsum := jointField_neg (I := I) (M := M) (d := 4) (S := S) _
    (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _
      (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _
        (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _
          (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _ h₁ h₂) h₃) h₄) h₅)
  refine hsum.congr (fun p _ => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1 t) rfl

set_option backward.isDefEq.respectTransparency false in

private theorem order0CLM_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Z : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 2 I p.1)
    (hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Z p))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1
        (linearizedRicciConnDiffOrder0CLM (I := I) p.1
          ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀).toSection p.1)
          ((covGrad (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀)).toSection p.1)
          (Z p)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  set S := realizedSmallSet (δ := δ) (δ' := δ') with hS
  set Af : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace 1 2 I p.1 :=
    fun p => (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀).toSection p.1
    with hAf
  set DAf : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace 1 3 I p.1 :=
    fun p => (covGrad (I := I) (M := M) g₀ 1 2
      (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀)).toSection p.1
    with hDAf
  have hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 2 I z) p.1 (Af p))
      ((Set.univ : Set M) ×ˢ S) :=
    connDiffSection_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hDA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 3 I z) p.1 (DAf p))
      ((Set.univ : Set M) ×ˢ S) :=
    covGradConnDiff_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hZswap := slotPermField_jointContMDiffOn (I := I) cdPerm2_10 (S := S) Z hZ
  have hinnJ := connContrField_jointContMDiffOn (I := I) 1 1 (S := S) Af hA (fun p => Z p) hZ
  have hinnJ' := connContrField_jointContMDiffOn (I := I) 1 1 (S := S) Af hA
    (fun p => slotPermCLM (I := I) cdPerm2_10 p.1 (Z p)) hZswap
  have hu₃ := slotPermField_jointContMDiffOn (I := I) cdPerm4_3201 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => slotPermCLM (I := I) cdPerm3_102 p.1
        (connContrCLM (I := I) 1 1 p.1 (Af p) (Z p)))
      (slotPermField_jointContMDiffOn (I := I) cdPerm3_102 (S := S) _ hinnJ))
  have hu₄ := slotPermField_jointContMDiffOn (I := I) cdPerm4_2301 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => slotPermCLM (I := I) cdPerm3_102 p.1
        (connContrCLM (I := I) 1 1 p.1 (Af p) (slotPermCLM (I := I) cdPerm2_10 p.1 (Z p))))
      (slotPermField_jointContMDiffOn (I := I) cdPerm3_102 (S := S) _ hinnJ'))
  have hu₅ := slotPermField_jointContMDiffOn (I := I) cdPerm4_3102 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => slotPermCLM (I := I) cdPerm3_120 p.1
        (connContrCLM (I := I) 1 1 p.1 (Af p) (Z p)))
      (slotPermField_jointContMDiffOn (I := I) cdPerm3_120 (S := S) _ hinnJ))
  have hu₆ := slotPermField_jointContMDiffOn (I := I) cdPerm4_1302 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => connContrCLM (I := I) 1 1 p.1 (Af p) (slotPermCLM (I := I) cdPerm2_10 p.1 (Z p)))
      hinnJ')
  have hu₇ := slotPermField_jointContMDiffOn (I := I) cdPerm4_1203 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => connContrCLM (I := I) 1 1 p.1 (Af p) (Z p))
      hinnJ)
  have hu₈ := slotPermField_jointContMDiffOn (I := I) cdPerm4_2103 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 2 1 (S := S) Af hA
      (fun p => slotPermCLM (I := I) cdPerm3_120 p.1
        (connContrCLM (I := I) 1 1 p.1 (Af p) (slotPermCLM (I := I) cdPerm2_10 p.1 (Z p))))
      (slotPermField_jointContMDiffOn (I := I) cdPerm3_120 (S := S) _ hinnJ'))
  have hu₁ := slotPermField_jointContMDiffOn (I := I) cdPerm4_3012 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 1 2 (S := S) DAf hDA (fun p => Z p) hZ)
  have hu₂ := slotPermField_jointContMDiffOn (I := I) cdPerm4_2013 (S := S) _
    (connContrField_jointContMDiffOn (I := I) 1 2 (S := S) DAf hDA
      (fun p => slotPermCLM (I := I) cdPerm2_10 p.1 (Z p)) hZswap)
  have hsum := jointField_sub (I := I) (M := M) (d := 4) (S := S) _ _
    (jointField_sub (I := I) (M := M) (d := 4) (S := S) _ _
      (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _
        (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _
          (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _
            (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _
              (jointField_add (I := I) (M := M) (d := 4) (S := S) _ _ hu₃ hu₄) hu₅) hu₆) hu₇)
        hu₈) hu₁) hu₂
  refine hsum.congr (fun p _ => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1 t) rfl

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] in
private theorem fourTrace_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Z : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 4 I p.1)
    (hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1 (Z p))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (ricciCometricFourTraceCLM (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Z p)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  set S := realizedSmallSet (δ := δ) (δ' := δ') with hS
  have ha := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p => slotPermCLM (I := I) cdPerm4_0231 p.1 (Z p))
    (slotPermField_jointContMDiffOn (I := I) cdPerm4_0231 (S := S) Z hZ)
  have hb := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p => slotPermCLM (I := I) cdPerm4_0321 p.1 (Z p))
    (slotPermField_jointContMDiffOn (I := I) cdPerm4_0321 (S := S) Z hZ)
  have hc := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p => Z p) hZ
  have hd := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p => slotPermCLM (I := I) cdPerm4_2301 p.1 (Z p))
    (slotPermField_jointContMDiffOn (I := I) cdPerm4_2301 (S := S) Z hZ)
  have hcomb := jointField_smul (I := I) (M := M) (d := 2) (S := S) ((1 : ℝ) / 2) _
    (jointField_sub (I := I) (M := M) (d := 2) (S := S) _ _
      (jointField_sub (I := I) (M := M) (d := 2) (S := S) _ _
        (jointField_add (I := I) (M := M) (d := 2) (S := S) _ _ ha hb) hc) hd)
  refine hcomb.congr (fun p _ => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) rfl

set_option backward.isDefEq.respectTransparency false in

theorem linearizedRicciConnDiffOrder1Fib_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1
        (linearizedRicciConnDiffOrder1CometricTracedCLM (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun p : M × ℝ => linearizedRicciConnDiffOrder1CometricTracedCLM (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  have hYj : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hE1 := order1CLM_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    (fun p => Y p.1) hYj
  have hCK := fourTrace_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    (fun p => linearizedRicciConnDiffOrder1CLM (I := I) p.1
      ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀).toSection p.1)
      (Y p.1))
    hE1
  refine hCK.congr (fun p _ => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 8000 in

theorem linearizedRicciConnDiffOrder0Fib_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        (linearizedRicciConnDiffOrder0CometricTracedCLM (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun p : M × ℝ => linearizedRicciConnDiffOrder0CometricTracedCLM (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  have hYj : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hE0 := order0CLM_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    (fun p => Y p.1) hYj
  have hCK := fourTrace_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    (fun p => linearizedRicciConnDiffOrder0CLM (I := I) p.1
      ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀).toSection p.1)
      ((covGrad (I := I) (M := M) g₀ 1 2
          (connDiffSection (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀)).toSection p.1)
      (Y p.1))
    hE0
  refine hCK.congr (fun p _ => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) rfl


theorem linearizedRicciConnDiffOrder0Coeff_jointContMDiffOn_smallPerturbationSet
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ') (δ := δ) (δ' := δ') := by
  have h := linearizedRicciConnDiffOrder0Fib_realizedFam_jointContMDiffOn
    (I := I) g₀ T T' hδ hδ'
  refine h.congr (fun p _ => ?_)
  rfl


theorem linearizedRicciConnDiffOrder1Coeff_jointContMDiffOn_smallPerturbationSet
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ') (δ := δ) (δ' := δ') := by
  have h := linearizedRicciConnDiffOrder1Fib_realizedFam_jointContMDiffOn
    (I := I) g₀ T T' hδ hδ'
  refine h.congr (fun p _ => ?_)
  rfl

end JointSmoothness

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
