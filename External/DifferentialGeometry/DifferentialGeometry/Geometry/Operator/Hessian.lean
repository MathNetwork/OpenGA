import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Operator.Laplacian
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

theorem bilinForm_trace_sq_le_card_mul_frobenius_sq
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι : Type*} [Fintype ι]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v : ι → V) :
    (∑ i : ι, B (v i) (v i))^2 ≤
      (Fintype.card ι : ℝ) * ∑ i : ι, ∑ j : ι, (B (v i) (v j))^2 := by
  classical
  have h_diag :
      (∑ i : ι, B (v i) (v i))^2 ≤
        (Fintype.card ι : ℝ) * ∑ i : ι, (B (v i) (v i))^2 := by
    have h := sq_sum_le_card_mul_sum_sq (α := ℝ) (s := (Finset.univ : Finset ι))
      (f := fun i => B (v i) (v i))
    simpa [Finset.card_univ] using h
  have h_row : ∀ i : ι,
      (B (v i) (v i))^2 ≤ ∑ j : ι, (B (v i) (v j))^2 := by
    intro i
    have h_mem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
    have h_nonneg : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ (B (v i) (v j))^2 :=
      fun j _ => sq_nonneg _
    exact Finset.single_le_sum (f := fun j => (B (v i) (v j))^2) h_nonneg h_mem
  have h_sum :
      ∑ i : ι, (B (v i) (v i))^2 ≤ ∑ i : ι, ∑ j : ι, (B (v i) (v j))^2 :=
    Finset.sum_le_sum (fun i _ => h_row i)
  have h_card_nonneg : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Nat.zero_le _
  calc (∑ i : ι, B (v i) (v i))^2
      ≤ (Fintype.card ι : ℝ) * ∑ i : ι, (B (v i) (v i))^2 := h_diag
    _ ≤ (Fintype.card ι : ℝ) * ∑ i : ι, ∑ j : ι, (B (v i) (v j))^2 := by
        exact mul_le_mul_of_nonneg_left h_sum h_card_nonneg

theorem bilinForm_trace_sq_le_dim_mul_frobenius_sq
    {V : Type*} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V) :
    (∑ i : Fin (Module.finrank ℝ V), B (b i) (b i))^2 ≤
      (Module.finrank ℝ V : ℝ) *
        ∑ i : Fin (Module.finrank ℝ V),
          ∑ j : Fin (Module.finrank ℝ V), (B (b i) (b j))^2 := by
  have h := bilinForm_trace_sq_le_card_mul_frobenius_sq (V := V)
    (ι := Fin (Module.finrank ℝ V)) B (fun i => b i)
  simpa [Fintype.card_fin] using h

variable (I) in

abbrev pointwiseBilin :=
  ∀ x : M, TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ

def IsPointwiseSymm (B : pointwiseBilin (M := M) I) : Prop :=
  ∀ x : M, ∀ v w : TangentSpace I x, B x v w = B x w v

def frobeniusSqFun (B : pointwiseBilin (M := M) I) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      (B x ((chartModelBasis E) i) ((chartModelBasis E) j))^2

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
@[simp] lemma frobeniusSqFun_def (B : pointwiseBilin (M := M) I) (x : M) :
    frobeniusSqFun (I := I) (M := M) B x =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (B x ((chartModelBasis E) i) ((chartModelBasis E) j))^2 := rfl

def traceFun (B : pointwiseBilin (M := M) I) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    B x ((chartModelBasis E) i) ((chartModelBasis E) i)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
@[simp] lemma traceFun_def (B : pointwiseBilin (M := M) I) (x : M) :
    traceFun (I := I) (M := M) B x =
      ∑ i : Fin (Module.finrank ℝ E),
        B x ((chartModelBasis E) i) ((chartModelBasis E) i) := rfl

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
lemma frobeniusSqFun_nonneg (B : pointwiseBilin (M := M) I) (x : M) :
    0 ≤ frobeniusSqFun (I := I) (M := M) B x := by
  unfold frobeniusSqFun
  exact Finset.sum_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
theorem traceFun_sq_le_dim_mul_frobeniusSqFun
    (B : pointwiseBilin (M := M) I) (x : M) :
    (traceFun (I := I) (M := M) B x)^2 ≤
      (Module.finrank ℝ E : ℝ) * frobeniusSqFun (I := I) (M := M) B x := by
  have h := bilinForm_trace_sq_le_dim_mul_frobenius_sq
    (V := TangentSpace I x) (B := B x) (b := chartModelBasis E)
  simp only [traceFun_def, frobeniusSqFun_def]
  exact h

omit [IsManifold I ∞ M] in
theorem traceFun_sq_div_dim_le_frobeniusSqFun
    (B : pointwiseBilin (M := M) I) (x : M) :
    (traceFun (I := I) (M := M) B x)^2 / (Module.finrank ℝ E : ℝ) ≤
      frobeniusSqFun (I := I) (M := M) B x := by
  have hne : (Module.finrank ℝ E : ℕ) ≠ 0 := NeZero.ne _
  have hpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    have : (0 : ℕ) < Module.finrank ℝ E := Nat.pos_of_ne_zero hne
    exact_mod_cast this
  have hbound := traceFun_sq_le_dim_mul_frobeniusSqFun (I := I) (M := M) B x
  exact (div_le_iff₀ hpos).mpr (by linarith [hbound])

def chartGramOnE (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => chartGramMatrix (I := I) g α ((extChartAt I α).symm y) i j

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartGramOnE_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) g α i j y =
      chartGramMatrix (I := I) g α ((extChartAt I α).symm y) i j := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma chartGramOnE_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) g α i j y = chartGramOnE (I := I) g α j i y := by
  unfold chartGramOnE
  rw [chartGramMatrix_apply, chartGramMatrix_apply]
  exact g.symm _ _ _

def chartChristoffel (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k l *
      (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
       partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
       partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartChristoffel_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g α i j k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k l *
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
           partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
           partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffel_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g α i j k y =
      chartChristoffel (I := I) g α j i k y := by
  classical
  rw [chartChristoffel_def, chartChristoffel_def]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro l _
  congr 1
  have hsym : chartGramOnE (I := I) g α i j =
      chartGramOnE (I := I) g α j i :=
    funext (fun y' => chartGramOnE_symm (I := I) g α i j y')
  rw [show partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y =
        partialDeriv (E := E) l (chartGramOnE (I := I) g α j i) y from by
    rw [hsym]]
  ring

def chartIteratedPartialDeriv
    (α : M) (f : M → ℝ) (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) i (partialDeriv (E := E) j (scalarOnE (I := I) α f)) y

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
@[simp] lemma chartIteratedPartialDeriv_def
    (α : M) (f : M → ℝ) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartIteratedPartialDeriv (I := I) α f i j y =
      partialDeriv (E := E) i
        (partialDeriv (E := E) j (scalarOnE (I := I) α f)) y := rfl

def chartHessianTensor (g : SmoothRiemannianMetric I M)
    (α : M) (f : M → ℝ) (i j : Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  chartIteratedPartialDeriv (I := I) α f i j (extChartAt I α x) -
    ∑ k : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g α i j k (extChartAt I α x) *
        partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartHessianTensor_def
    (g : SmoothRiemannianMetric I M)
    (α : M) (f : M → ℝ) (i j : Fin (Module.finrank ℝ E)) (x : M) :
    chartHessianTensor (I := I) g α f i j x =
      chartIteratedPartialDeriv (I := I) α f i j (extChartAt I α x) -
        ∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j k (extChartAt I α x) *
            partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma chartIteratedPartialDeriv_symm_of_contDiff
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartIteratedPartialDeriv (I := I) α f i j y =
      chartIteratedPartialDeriv (I := I) α f j i y := by
  classical
  unfold chartIteratedPartialDeriv partialDeriv
  have hsmooth_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hsmooth_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (interior (extChartAt I α).target) := hsmooth_target.mono interior_subset
  have hopen_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hcontDiffAt : ContDiffAt ℝ ∞ (scalarOnE (I := I) α f) y :=
    hsmooth_int.contDiffAt (hopen_int.mem_nhds hy)
  have hsymm_2 :
      IsSymmSndFDerivAt ℝ (scalarOnE (I := I) α f) y := by
    refine ContDiffAt.isSymmSndFDerivAt hcontDiffAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    decide
  have hg_diff : DifferentiableAt ℝ (fderiv ℝ (scalarOnE (I := I) α f)) y := by
    have hfderiv_smooth : ContDiffOn ℝ ∞
        (fderiv ℝ (scalarOnE (I := I) α f))
        (interior (extChartAt I α).target) :=
      hsmooth_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
    have hcontDiff_at_fderiv :
        ContDiffAt ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f)) y :=
      hfderiv_smooth.contDiffAt (hopen_int.mem_nhds hy)
    exact hcontDiff_at_fderiv.differentiableAt (by simp)
  have hkey : ∀ a b : Fin (Module.finrank ℝ E),
      fderiv ℝ
          (fun z => fderiv ℝ (scalarOnE (I := I) α f) z ((chartModelBasis E) b))
          y ((chartModelBasis E) a) =
        (fderiv ℝ (fderiv ℝ (scalarOnE (I := I) α f)) y
          ((chartModelBasis E) a)) ((chartModelBasis E) b) := by
    intro a b
    set L : (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ ((chartModelBasis E) b)
    have hcomp_eq : (fun z : E =>
          fderiv ℝ (scalarOnE (I := I) α f) z ((chartModelBasis E) b)) =
        L ∘ (fderiv ℝ (scalarOnE (I := I) α f)) := by
      funext z; rfl
    rw [hcomp_eq, fderiv_comp y L.differentiableAt hg_diff]
    rw [L.fderiv]
    rfl
  rw [hkey i j, hkey j i]
  exact hsymm_2 _ _

omit [NeZero (Module.finrank ℝ E)] in
theorem chartHessianTensor_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i j : Fin (Module.finrank ℝ E))
    {x : M} (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) :
    chartHessianTensor (I := I) g α f i j x =
      chartHessianTensor (I := I) g α f j i x := by
  classical
  rw [chartHessianTensor_def, chartHessianTensor_def]
  rw [chartIteratedPartialDeriv_symm_of_contDiff (I := I) α hf i j hx_int]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [chartChristoffel_symm (I := I) g α i j k]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartHessianTensor_symm_of_boundaryless [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i j : Fin (Module.finrank ℝ E))
    {x : M} (hx : x ∈ (chartAt H α).source) :
    chartHessianTensor (I := I) g α f i j x =
      chartHessianTensor (I := I) g α f j i x := by
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hx_target : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_target
  exact chartHessianTensor_symm (I := I) g α hf i j hx_int

def hessFun (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    pointwiseBilin (M := M) I :=
  fun x => LinearMap.mk₂ ℝ
    (fun v w =>
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) i *
            ((chartModelBasis E).repr w) j *
            chartHessianTensor (I := I) g x f i j x)
    (fun v₁ v₂ w => by
      classical
      dsimp only
      have hrepr : (chartModelBasis E).repr (v₁ + v₂) =
          (chartModelBasis E).repr v₁ + (chartModelBasis E).repr v₂ := map_add _ _ _
      rw [hrepr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finsupp.coe_add, Pi.add_apply]
      ring)
    (fun c v w => by
      classical
      dsimp only
      have hrepr : (chartModelBasis E).repr (c • v) =
          c • (chartModelBasis E).repr v := map_smul _ _ _
      rw [hrepr]
      simp only [smul_eq_mul, Finsupp.coe_smul, Pi.smul_apply]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring)
    (fun v w₁ w₂ => by
      classical
      dsimp only
      have hrepr : (chartModelBasis E).repr (w₁ + w₂) =
          (chartModelBasis E).repr w₁ + (chartModelBasis E).repr w₂ := map_add _ _ _
      rw [hrepr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finsupp.coe_add, Pi.add_apply]
      ring)
    (fun c v w => by
      classical
      dsimp only
      have hrepr : (chartModelBasis E).repr (c • w) =
          c • (chartModelBasis E).repr w := map_smul _ _ _
      rw [hrepr]
      simp only [smul_eq_mul, Finsupp.coe_smul, Pi.smul_apply]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring)

omit [NeZero (Module.finrank ℝ E)] in
@[simp]
lemma hessFun_apply (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v w : TangentSpace I x) :
    hessFun (I := I) g f x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) i *
            ((chartModelBasis E).repr w) j *
            chartHessianTensor (I := I) g x f i j x := by
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem hessFun_symm_of_boundaryless [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    IsPointwiseSymm (hessFun (I := I) (M := M) g f) := by
  intro x v w
  classical
  rw [hessFun_apply, hessFun_apply]
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hsymm : ∀ i j, chartHessianTensor (I := I) g x f i j x =
      chartHessianTensor (I := I) g x f j i x := fun i j =>
    chartHessianTensor_symm_of_boundaryless (I := I) g x hf i j hxsrc
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hsymm j i]
  ring

def chartHessFrobeniusSq (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
  ∑ j : Fin (Module.finrank ℝ E),
  ∑ k : Fin (Module.finrank ℝ E),
  ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g x x i k *
      chartInvGramMatrix (I := I) g x x j l *
        chartHessianTensor (I := I) g x f i j x *
          chartHessianTensor (I := I) g x f k l x

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartHessFrobeniusSq_def (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (x : M) :
    chartHessFrobeniusSq (I := I) g f x =
      ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x i k *
          chartInvGramMatrix (I := I) g x x j l *
            chartHessianTensor (I := I) g x f i j x *
              chartHessianTensor (I := I) g x f k l x := rfl

def chartHessTrace (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
  ∑ j : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g x x i j *
      chartHessianTensor (I := I) g x f i j x

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartHessTrace_def (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (x : M) :
    chartHessTrace (I := I) g f x =
      ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x i j *
          chartHessianTensor (I := I) g x f i j x := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma hessFun_basis_apply
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    hessFun (I := I) g f x
        ((chartModelBasis E) i) ((chartModelBasis E) j) =
      chartHessianTensor (I := I) g x f i j x := by
  classical
  rw [hessFun_apply]
  conv_lhs => rw [show
      (∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr ((chartModelBasis E) i)) i' *
            ((chartModelBasis E).repr ((chartModelBasis E) j)) j' *
            chartHessianTensor (I := I) g x f i' j' x) =
      (∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          (if i = i' then (1 : ℝ) else 0) *
            (if j = j' then (1 : ℝ) else 0) *
            chartHessianTensor (I := I) g x f i' j' x) from
      Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun j' _ => by
        rw [Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]))]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'_ne
      have hjj' : ¬ j = j' := fun h => hj'_ne h.symm
      simp [hjj']
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · intro i' _ hi'_ne
    apply Finset.sum_eq_zero
    intro j' _
    have hii' : ¬ i = i' := fun h => hi'_ne h.symm
    simp [hii']
  · intro hi
    exact absurd (Finset.mem_univ i) hi

omit [NeZero (Module.finrank ℝ E)] in
lemma traceFun_hessFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      ∑ i : Fin (Module.finrank ℝ E), chartHessianTensor (I := I) g x f i i x := by
  unfold traceFun
  refine Finset.sum_congr rfl ?_
  intro i _
  exact hessFun_basis_apply (I := I) g f x i i

omit [NeZero (Module.finrank ℝ E)] in
lemma frobeniusSqFun_hessFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    frobeniusSqFun (I := I) (M := M) (hessFun (I := I) g f) x =
      ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (chartHessianTensor (I := I) g x f i j x)^2 := by
  unfold frobeniusSqFun
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hessFun_basis_apply]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartHess_trace_sq_le_dim_mul_frobenius_sq
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E), chartHessianTensor (I := I) g x f i i x)^2 ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartHessianTensor (I := I) g x f i j x)^2 := by
  classical
  have hbound :=
    traceFun_sq_le_dim_mul_frobeniusSqFun
      (I := I) (M := M) (hessFun (I := I) g f) x
  rw [traceFun_hessFun (I := I) g f x,
      frobeniusSqFun_hessFun (I := I) g f x] at hbound
  exact hbound

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacian_sq_le_dim_mul_frobenius_sq_of_trace_eq
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (htr : traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
        Δ_g (I := I) g hf x) :
    (Δ_g (I := I) g hf x)^2 ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartHessianTensor (I := I) g x f i j x)^2 := by
  classical
  have hbound := chartHess_trace_sq_le_dim_mul_frobenius_sq (I := I) g f x
  rw [traceFun_hessFun (I := I) g f x] at htr
  rw [← htr]
  exact hbound

theorem laplacian_sq_div_dim_le_frobenius_sq_of_trace_eq
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (htr : traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
        Δ_g (I := I) g hf x) :
    (Δ_g (I := I) g hf x)^2 / (Module.finrank ℝ E : ℝ) ≤
      ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (chartHessianTensor (I := I) g x f i j x)^2 := by
  classical
  have hne : (Module.finrank ℝ E : ℕ) ≠ 0 := NeZero.ne _
  have hpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    have : (0 : ℕ) < Module.finrank ℝ E := Nat.pos_of_ne_zero hne
    exact_mod_cast this
  have hbound :=
    laplacian_sq_le_dim_mul_frobenius_sq_of_trace_eq (I := I) g hf x htr
  exact (div_le_iff₀ hpos).mpr (by linarith [hbound])

omit [NeZero (Module.finrank ℝ E)] in
theorem traceFun_hessFun_sq_le_dim_mul_frobeniusSqFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    (traceFun (I := I) (M := M) (hessFun (I := I) g f) x)^2 ≤
      (Module.finrank ℝ E : ℝ) *
        frobeniusSqFun (I := I) (M := M) (hessFun (I := I) g f) x :=
  traceFun_sq_le_dim_mul_frobeniusSqFun
    (I := I) (M := M) (hessFun (I := I) g f) x

end DivergenceTheorem
end Integral
end DifferentialGeometry
