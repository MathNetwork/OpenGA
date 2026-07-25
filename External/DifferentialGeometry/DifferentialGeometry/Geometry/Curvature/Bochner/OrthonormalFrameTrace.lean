import DifferentialGeometry.Geometry.Connection.Laplacian.ConnectionLaplacian
import DifferentialGeometry.Geometry.Connection.ChartBridge.Laplacian
import DifferentialGeometry.Geometry.Connection.ChartBridge.HessFrobenius
import DifferentialGeometry.Geometry.Operator.NormGradSq

set_option linter.unnecessarySimpa false


noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

section OrthonormalFrameTrace

variable (g : SmoothRiemannianMetric I M) (x : M)

private noncomputable def coBchange
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i k => (chartModelBasis E).repr (B i) k

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] private lemma coBchange_apply
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (i k : Fin (Module.finrank ℝ E)) :
    coBchange (I := I) (x := x) B i k =
      (chartModelBasis E).repr (B i) k := rfl

private noncomputable def modelGramMatrix :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun k l =>
    g.inner x ((chartModelBasis E) k) ((chartModelBasis E) l)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] private lemma modelGramMatrix_apply
    (k l : Fin (Module.finrank ℝ E)) :
    modelGramMatrix (I := I) g x k l =
      g.inner x ((chartModelBasis E) k) ((chartModelBasis E) l) := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma modelGramMatrix_eq_chartGramMatrix :
    modelGramMatrix (I := I) g x = chartGramMatrix (I := I) g x x := by
  classical
  ext k l
  rw [modelGramMatrix_apply, chartGramMatrix_apply]
  rw [chartBasisVecFiber_self (I := I) x k]
  rw [chartBasisVecFiber_self (I := I) x l]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma decompose_in_modelBasis
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (i : Fin (Module.finrank ℝ E)) :
    B i = ∑ k : Fin (Module.finrank ℝ E),
      coBchange (I := I) (x := x) B i k •
        ((chartModelBasis E) k : TangentSpace I x) := by
  classical
  have h := (chartModelBasis E).sum_repr (B i)
  exact h.symm

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma bilin_expand_modelBasis
    (Hb : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (i j : Fin (Module.finrank ℝ E)) :
    Hb (B i) (B j) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        coBchange (I := I) (x := x) B i k *
          coBchange (I := I) (x := x) B j l *
            Hb ((chartModelBasis E) k) ((chartModelBasis E) l) := by
  classical
  have hHb_first : Hb (B i) =
      ∑ k : Fin (Module.finrank ℝ E),
        coBchange (I := I) (x := x) B i k •
          Hb ((chartModelBasis E) k) := by
    have hi := decompose_in_modelBasis (I := I) (x := x) B i
    rw [show Hb (B i) = Hb (∑ k : Fin (Module.finrank ℝ E),
            coBchange (I := I) (x := x) B i k •
              ((chartModelBasis E) k : TangentSpace I x))
          from congrArg Hb hi]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    exact Hb.map_smul (coBchange (I := I) (x := x) B i k)
      ((chartModelBasis E) k : TangentSpace I x)
  rw [hHb_first]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hHb_second : Hb ((chartModelBasis E) k) (B j) =
      ∑ l : Fin (Module.finrank ℝ E),
        coBchange (I := I) (x := x) B j l *
          Hb ((chartModelBasis E) k) ((chartModelBasis E) l) := by
    have hj := decompose_in_modelBasis (I := I) (x := x) B j
    rw [show Hb ((chartModelBasis E) k) (B j) =
          Hb ((chartModelBasis E) k)
            (∑ l : Fin (Module.finrank ℝ E),
              coBchange (I := I) (x := x) B j l •
                ((chartModelBasis E) l : TangentSpace I x))
        from congrArg (Hb ((chartModelBasis E) k)) hj]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    have hsmul : Hb ((chartModelBasis E) k)
        (coBchange (I := I) (x := x) B j l •
          ((chartModelBasis E) l : TangentSpace I x)) =
        coBchange (I := I) (x := x) B j l •
          Hb ((chartModelBasis E) k)
            ((chartModelBasis E) l : TangentSpace I x) :=
      (Hb ((chartModelBasis E) k)).map_smul
        (coBchange (I := I) (x := x) B j l)
        ((chartModelBasis E) l : TangentSpace I x)
    rw [hsmul, smul_eq_mul]
  rw [hHb_second]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma gram_expand_modelBasis
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner x (B i) (B j) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        coBchange (I := I) (x := x) B i k *
          coBchange (I := I) (x := x) B j l *
            modelGramMatrix (I := I) g x k l := by
  classical
  have h := bilin_expand_modelBasis (I := I) (x := x) (g.inner x) B i j
  refine h.trans ?_
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [modelGramMatrix_apply]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma orthonormal_matrix_form
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    coBchange (I := I) (x := x) B *
        modelGramMatrix (I := I) g x *
          (coBchange (I := I) (x := x) B).transpose =
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) := by
  classical
  ext i j
  have hg := gram_expand_modelBasis (I := I) g x B i j
  rw [hB i j] at hg
  rw [Matrix.mul_apply]
  have h_inner : ∀ k : Fin (Module.finrank ℝ E),
      (coBchange (I := I) (x := x) B *
          modelGramMatrix (I := I) g x) i k *
        (coBchange (I := I) (x := x) B).transpose k j =
      ∑ l : Fin (Module.finrank ℝ E),
        coBchange (I := I) (x := x) B i l *
          modelGramMatrix (I := I) g x l k *
          coBchange (I := I) (x := x) B j k := by
    intro k
    rw [Matrix.mul_apply]
    rw [Matrix.transpose_apply]
    rw [Finset.sum_mul]
  rw [show (∑ k, (coBchange (I := I) (x := x) B *
        modelGramMatrix (I := I) g x) i k *
      (coBchange (I := I) (x := x) B).transpose k j) =
    ∑ k, ∑ l,
      coBchange (I := I) (x := x) B i l *
          modelGramMatrix (I := I) g x l k *
          coBchange (I := I) (x := x) B j k from
    Finset.sum_congr rfl (fun k _ => h_inner k)]
  rw [show (1 : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ) i j =
      (if i = j then (1 : ℝ) else 0) from by
    rw [Matrix.one_apply]]
  rw [hg]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l₀ _
  refine Finset.sum_congr rfl ?_
  intro k₀ _
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma orthonormal_matrix_inverse
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    (coBchange (I := I) (x := x) B).transpose *
        coBchange (I := I) (x := x) B =
      (modelGramMatrix (I := I) g x)⁻¹ := by
  classical
  have hAGA := orthonormal_matrix_form (I := I) g x B hB
  set A : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ := coBchange (I := I) (x := x) B with hA_def
  set G : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ := modelGramMatrix (I := I) g x with hG_def
  have hAGA_right : A * (G * A.transpose) = 1 := by
    rw [← Matrix.mul_assoc]; exact hAGA
  have hG_At_eq_inv : G * A.transpose = A⁻¹ :=
    (Matrix.inv_eq_right_inv hAGA_right).symm
  have hA_left_inv : (G * A.transpose) * A = 1 :=
    (mul_eq_one_comm).mp hAGA_right
  rw [Matrix.mul_assoc] at hA_left_inv
  exact (Matrix.inv_eq_right_inv hA_left_inv).symm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma sum_coBchange_eq_invGram
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0)
    (k l : Fin (Module.finrank ℝ E)) :
    ∑ i : Fin (Module.finrank ℝ E),
      coBchange (I := I) (x := x) B i k *
        coBchange (I := I) (x := x) B i l =
      chartInvGramMatrix (I := I) g x x k l := by
  classical
  have h := orthonormal_matrix_inverse (I := I) g x B hB
  have heq : (coBchange (I := I) (x := x) B).transpose *
      coBchange (I := I) (x := x) B =
        (chartGramMatrix (I := I) g x x)⁻¹ := by
    rw [h]
    rw [modelGramMatrix_eq_chartGramMatrix (I := I) g x]
  have heval : ((coBchange (I := I) (x := x) B).transpose *
      coBchange (I := I) (x := x) B) k l =
        (chartGramMatrix (I := I) g x x)⁻¹ k l := by
    rw [heq]
  rw [Matrix.mul_apply] at heval
  rw [show ∑ i, (coBchange (I := I) (x := x) B).transpose k i *
            coBchange (I := I) (x := x) B i l =
         ∑ i, coBchange (I := I) (x := x) B i k *
            coBchange (I := I) (x := x) B i l from by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Matrix.transpose_apply]] at heval
  rw [heval]
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem orthonormal_basis_bilin_trace
    (Hb : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ i : Fin (Module.finrank ℝ E), Hb (B i) (B i) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          Hb ((chartModelBasis E) k) ((chartModelBasis E) l) := by
  classical
  have h_expand : ∀ i : Fin (Module.finrank ℝ E),
      Hb (B i) (B i) =
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          coBchange (I := I) (x := x) B i k *
            coBchange (I := I) (x := x) B i l *
              Hb ((chartModelBasis E) k) ((chartModelBasis E) l) :=
    fun i => bilin_expand_modelBasis (I := I) (x := x) Hb B i i
  rw [show ∑ i : Fin (Module.finrank ℝ E), Hb (B i) (B i) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          coBchange (I := I) (x := x) B i k *
            coBchange (I := I) (x := x) B i l *
              Hb ((chartModelBasis E) k) ((chartModelBasis E) l) from
    Finset.sum_congr rfl (fun i _ => h_expand i)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        coBchange (I := I) (x := x) B i k *
          coBchange (I := I) (x := x) B i l *
            Hb ((chartModelBasis E) k) ((chartModelBasis E) l)) =
      (∑ i : Fin (Module.finrank ℝ E),
        coBchange (I := I) (x := x) B i k *
          coBchange (I := I) (x := x) B i l) *
        Hb ((chartModelBasis E) k) ((chartModelBasis E) l) from by
    rw [Finset.sum_mul]]
  rw [sum_coBchange_eq_invGram (I := I) g x B hB k l]

end OrthonormalFrameTrace

section TraceIdentity

variable (g : SmoothRiemannianMetric I M) (x : M)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma finBasis_repr_eq_invGram_inner_sum
    (X : TangentSpace I x) (k : Fin (Module.finrank ℝ E)) :
    (chartModelBasis E).repr X k =
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          g.inner x X ((chartModelBasis E) l) := by
  classical
  have hX_decomp : X = ∑ p : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr X p •
        ((chartModelBasis E) p : TangentSpace I x) :=
    ((chartModelBasis E).sum_repr X).symm
  have h_inner_decomp : ∀ l : Fin (Module.finrank ℝ E),
      g.inner x X ((chartModelBasis E) l) =
        ∑ p : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr X p *
            chartGramMatrix (I := I) g x x p l := by
    intro l
    rw [g.symm x X ((chartModelBasis E) l)]
    rw [show g.inner x ((chartModelBasis E) l) X =
          g.inner x ((chartModelBasis E) l) (∑ p : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr X p •
              ((chartModelBasis E) p : TangentSpace I x)) from
      congrArg (g.inner x ((chartModelBasis E) l)) hX_decomp]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    show g.inner x ((chartModelBasis E) l)
        (((chartModelBasis E).repr X) p •
          ((chartModelBasis E) p : TangentSpace I x)) =
      ((chartModelBasis E).repr X) p *
        chartGramMatrix (I := I) g x x p l
    rw [show g.inner x ((chartModelBasis E) l)
            (((chartModelBasis E).repr X) p •
              ((chartModelBasis E) p : TangentSpace I x)) =
        ((chartModelBasis E).repr X) p •
          g.inner x ((chartModelBasis E) l)
            ((chartModelBasis E) p) from
      ContinuousLinearMap.map_smul (g.inner x ((chartModelBasis E) l)) _ _]
    rw [smul_eq_mul]
    rw [g.symm x ((chartModelBasis E) l) ((chartModelBasis E) p)]
    rw [show g.inner x ((chartModelBasis E) p) ((chartModelBasis E) l) =
          chartGramMatrix (I := I) g x x p l from by
      rw [← modelGramMatrix_apply (I := I) g x p l,
          modelGramMatrix_eq_chartGramMatrix (I := I) g x]]
  rw [show (∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          g.inner x X ((chartModelBasis E) l)) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          (∑ p : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr X p *
              chartGramMatrix (I := I) g x x p l) from
    Finset.sum_congr rfl (fun l _ => by rw [h_inner_decomp])]
  rw [show (∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          (∑ p : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr X p *
              chartGramMatrix (I := I) g x x p l)) =
      ∑ l : Fin (Module.finrank ℝ E),
        ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            ((chartModelBasis E).repr X p *
              chartGramMatrix (I := I) g x x p l) from by
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [Finset.mul_sum]]
  rw [Finset.sum_comm]
  rw [show (∑ p : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            ((chartModelBasis E).repr X p *
              chartGramMatrix (I := I) g x x p l)) =
      ∑ p : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr X p *
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x k l *
              chartGramMatrix (I := I) g x x p l from by
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    ring]
  have h_invGram_gram_eq : ∀ p : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          chartGramMatrix (I := I) g x x p l =
      if k = p then (1 : ℝ) else 0 := by
    intro p
    have h_gram_symm : ∀ l : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g x x p l =
        chartGramMatrix (I := I) g x x l p := by
      intro l
      rw [chartGramMatrix_apply, chartGramMatrix_apply, g.symm]
    rw [show (∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          chartGramMatrix (I := I) g x x p l) =
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            chartGramMatrix (I := I) g x x l p from by
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [h_gram_symm]]
    have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' x
    have hmul := chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hx_base
    have heval : (chartInvGramMatrix (I := I) g x x *
        chartGramMatrix (I := I) g x x) k p =
        (1 : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) k p := by
      rw [hmul]
    rw [Matrix.mul_apply] at heval
    rw [heval, Matrix.one_apply]
  rw [show (∑ p : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr X p *
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x k l *
              chartGramMatrix (I := I) g x x p l) =
      ∑ p : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr X p *
          (if k = p then (1 : ℝ) else 0) from by
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [h_invGram_gram_eq]]
  rw [show (∑ p : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr X p *
          (if k = p then (1 : ℝ) else 0)) =
      (chartModelBasis E).repr X k from by
    rw [Finset.sum_eq_single k]
    · simp
    · intro p _ hpk
      rw [if_neg (fun h => hpk h.symm)]; ring
    · intro hk
      exact absurd (Finset.mem_univ k) hk]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma linearMap_trace_eq_invGram_bilin_sum
    (T : TangentSpace I x →ₗ[ℝ] TangentSpace I x) :
    LinearMap.trace ℝ (TangentSpace I x) T =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            g.inner x (T ((chartModelBasis E) k))
              ((chartModelBasis E) l) := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  rw [LinearMap.trace_eq_matrix_trace ℝ
        (chartModelBasis (TangentSpace I x)) T]
  unfold Matrix.trace
  refine Finset.sum_congr rfl ?_
  intro k _
  simp only [Matrix.diag_apply]
  rw [LinearMap.toMatrix_apply]
  exact finBasis_repr_eq_invGram_inner_sum (I := I) g x
    (T ((chartModelBasis E) k)) k

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem trace_eq_ortho_sum
    (T : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    LinearMap.trace ℝ (TangentSpace I x) T =
      ∑ i : Fin (Module.finrank ℝ E), g.inner x (T (B i)) (B i) := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · have htang : Module.finrank ℝ (TangentSpace I x) = 0 := hdim
    letI : Subsingleton (TangentSpace I x) := Module.finrank_zero_iff.1 htang
    rw [Subsingleton.elim T 0]
    simp
  · letI : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    let D := (Tensor0SBundle.tangentMetricData_gen (I := I) g x).metric
    letI : InnerProductSpace.Core ℝ (TangentSpace I x) := D.toCore
    letI : NormedAddCommGroup (TangentSpace I x) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I x) _ _ _ D.toCore
    letI : InnerProductSpace ℝ (TangentSpace I x) :=
      @InnerProductSpace.ofCore ℝ (TangentSpace I x) _ _ _ D.toCore.toCore
    have hg : ∀ v w : TangentSpace I x,
        g.inner x v w = Inner.inner ℝ v w := by
      intro v w
      rw [← Tensor0SBundle.TangentMetricData_gen.inner_eq_gen
        (Tensor0SBundle.tangentMetricData_gen (I := I) g x) v w]
      change D.inner v w = Inner.inner ℝ v w
      exact (Tensor0SBundle.MetricFiberData.toCore_inner D v w).symm
    have hON : Orthonormal ℝ B := by
      rw [orthonormal_iff_ite]
      intro i j
      rw [← hg]
      exact hB i j
    have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
        Module.finrank ℝ (TangentSpace I x) := by
      rw [Fintype.card_fin]
      rfl
    have hspan : ⊤ ≤ Submodule.span ℝ (Set.range B) :=
      ge_of_eq (hON.linearIndependent.span_eq_top_of_card_eq_finrank hcard)
    let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
      OrthonormalBasis.mk hON hspan
    have hb : ∀ i, b i = B i := by
      intro i
      show (OrthonormalBasis.mk hON hspan) i = B i
      rw [OrthonormalBasis.coe_mk]
    rw [LinearMap.trace_eq_sum_inner T b]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb i, ← hg (B i) (T (B i)), g.symm x (B i) (T (B i))]

end TraceIdentity

section RicciOrthonormalTrace

variable (g : SmoothRiemannianMetric I M) (x : M)

private def riemannCurvatureEndo
    (v w : TangentSpace I x) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun Z := riemannOp (LeviCivita (I := I) g) x Z v w
  map_add' Z Z' := by
    have h := (riemannOp (LeviCivita (I := I) g) x).map_add Z Z'
    simpa using h
  map_smul' c Z := by
    have h := (riemannOp (LeviCivita (I := I) g) x).map_smul c Z
    simpa using h

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] private lemma riemannCurvatureEndo_apply
    (v w Z : TangentSpace I x) :
    riemannCurvatureEndo (I := I) g x v w Z =
      riemannOp (LeviCivita (I := I) g) x Z v w := rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciTensor_eq_orthonormal_trace
    (v w : TangentSpace I x)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ricciTensor (I := I) g x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) v w) (B i) := by
  classical
  have hRic : ricciTensor (I := I) g x v w =
      LinearMap.trace ℝ (TangentSpace I x)
        (riemannCurvatureEndo (I := I) g x v w) := by
    rw [ricciTensor_apply]
    rfl
  rw [hRic]
  rw [trace_eq_ortho_sum (I := I) g x
    (riemannCurvatureEndo (I := I) g x v w) B hB]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [riemannCurvatureEndo_apply]

omit [SigmaCompactSpace M] in
theorem heart_curvature_orthonormal_sum_eq_ricci
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (_hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (w : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (riemannOp (LeviCivita (I := I) g) x
        (smoothOrthoFrame (I := I) g x i x) w (gradFun (I := I) g f x))
        (smoothOrthoFrame (I := I) g x i x) =
      ricciTensor (I := I) g x (gradFun (I := I) g f x) w := by
  classical
  rw [ricciTensor_symm (I := I) g x (gradFun (I := I) g f x) w]
  rw [ricciTensor_eq_orthonormal_trace (I := I) g x w
        (gradFun (I := I) g f x)
        (fun i => smoothOrthoFrame (I := I) g x i x)
        (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)]

end RicciOrthonormalTrace

section OrthonormalFrameSkewDerivative

variable (g : SmoothRiemannianMetric I M) (x : M)

omit [SigmaCompactSpace M] in
theorem smoothOrthoFrame_cov_skew
    (i j : Fin (Module.finrank ℝ E))
    (v : TangentSpace I x) :
    g.inner x ((LeviCivita (I := I) g).toFun
        (smoothOrthoFrame (I := I) g x i) x v)
        (smoothOrthoFrame (I := I) g x j x) =
      - g.inner x (smoothOrthoFrame (I := I) g x i x)
          ((LeviCivita (I := I) g).toFun
            (smoothOrthoFrame (I := I) g x j) x v) := by
  classical
  have hBi := smoothOrthoFrame_smooth (I := I) g x i
  have hBj := smoothOrthoFrame_smooth (I := I) g x j
  have h_constant_on_nbhd : ∀ᶠ b in 𝓝 x,
      g.inner b (smoothOrthoFrame (I := I) g x i b)
        (smoothOrthoFrame (I := I) g x j b) =
      (if i = j then (1 : ℝ) else 0) := by
    have h_open : smoothOrthoFrameNbhd (I := I) (M := M) x ∈ 𝓝 x :=
      smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x
    filter_upwards [h_open] with b hb
    exact smoothOrthoFrame_orthonormal (I := I) g x hb i j
  have h_eq : (fun b : M => g.inner b
        (smoothOrthoFrame (I := I) g x i b)
        (smoothOrthoFrame (I := I) g x j b)) =ᶠ[𝓝 x]
      (fun _ : M => (if i = j then (1 : ℝ) else 0)) := h_constant_on_nbhd
  have h_mfderiv : mfderiv I 𝓘(ℝ) (fun b : M =>
        g.inner b (smoothOrthoFrame (I := I) g x i b)
          (smoothOrthoFrame (I := I) g x j b)) x =
      mfderiv I 𝓘(ℝ) (fun _ : M => (if i = j then (1 : ℝ) else 0)) x :=
    Filter.EventuallyEq.mfderiv_eq h_eq
  have h_const_zero : mfderiv I 𝓘(ℝ)
      (fun _ : M => (if i = j then (1 : ℝ) else 0)) x = 0 :=
    mfderiv_const ..
  have hBi_at : MDiffAt (T% (smoothOrthoFrame (I := I) g x i)) x :=
    (hBi x).mdifferentiableAt (by simp)
  have hBj_at : MDiffAt (T% (smoothOrthoFrame (I := I) g x j)) x :=
    (hBj x).mdifferentiableAt (by simp)
  have hmc :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hBi_at hBj_at v
  have h_zero : (mfderiv I 𝓘(ℝ) (fun b : M =>
        g.inner b (smoothOrthoFrame (I := I) g x i b)
          (smoothOrthoFrame (I := I) g x j b)) x) v = 0 := by
    rw [h_mfderiv, h_const_zero]
    rfl
  rw [h_zero] at hmc
  exact eq_neg_of_add_eq_zero_left hmc.symm

end OrthonormalFrameSkewDerivative

section OrthonormalRiesz

variable (g : SmoothRiemannianMetric I M) (x : M)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem g_inner_eq_orthonormal_parseval_sum
    (X Y : TangentSpace I x)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    g.inner x X Y =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner x X (B i) * g.inner x (B i) Y := by
  classical
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  set T : TangentSpace I x →ₗ[ℝ] TangentSpace I x :=
    { toFun := fun Z => g.inner x X Z • Y
      map_add' := fun Z Z' => by
        rw [(g.inner x X).map_add Z Z', add_smul]
      map_smul' := fun c Z => by
        rw [(g.inner x X).map_smul c Z, smul_eq_mul,
            show (c * g.inner x X Z) • Y = c • (g.inner x X Z) • Y from by
              rw [smul_smul]]
        rfl } with hT_def
  have hT_apply : ∀ Z : TangentSpace I x, T Z = g.inner x X Z • Y := fun _ => rfl
  have hT_pair : ∀ Z W : TangentSpace I x,
      g.inner x (T Z) W = g.inner x X Z * g.inner x W Y := by
    intro Z W
    rw [hT_apply]
    rw [show g.inner x (g.inner x X Z • Y) W =
          g.inner x X Z * g.inner x Y W from by
      rw [(g.inner x).map_smul (g.inner x X Z) Y]
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul]]
    rw [g.symm x Y W]
  have hT_trace_orthonormal :
      LinearMap.trace ℝ (TangentSpace I x) T =
        ∑ i : Fin (Module.finrank ℝ E), g.inner x (T (B i)) (B i) :=
    trace_eq_ortho_sum (I := I) g x T B hB
  have hT_trace_xy : LinearMap.trace ℝ (TangentSpace I x) T = g.inner x X Y := by
    rw [linearMap_trace_eq_invGram_bilin_sum (I := I) g x T]
    rw [show (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x k l *
              g.inner x (T ((chartModelBasis E) k))
                ((chartModelBasis E) l)) =
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x k l *
              (g.inner x X ((chartModelBasis E) k) *
                g.inner x ((chartModelBasis E) l) Y) from by
      refine Finset.sum_congr rfl ?_
      intro k _
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [hT_pair]]
    rw [show (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x k l *
              (g.inner x X ((chartModelBasis E) k) *
                g.inner x ((chartModelBasis E) l) Y)) =
        ∑ k : Fin (Module.finrank ℝ E),
          g.inner x X ((chartModelBasis E) k) *
            (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x k l *
                g.inner x ((chartModelBasis E) l) Y) from by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro l _
      ring]
    rw [show (∑ k : Fin (Module.finrank ℝ E),
          g.inner x X ((chartModelBasis E) k) *
            (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x k l *
                g.inner x ((chartModelBasis E) l) Y)) =
        ∑ k : Fin (Module.finrank ℝ E),
          g.inner x X ((chartModelBasis E) k) *
            (chartModelBasis E).repr Y k from by
      refine Finset.sum_congr rfl ?_
      intro k _
      have h := finBasis_repr_eq_invGram_inner_sum (I := I) g x Y k
      have h' : (chartModelBasis E).repr Y k =
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x k l *
              g.inner x ((chartModelBasis E) l) Y := by
        rw [h]
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [g.symm x Y ((chartModelBasis E) l)]
      rw [h']]
    have hY_decomp : Y = ∑ k : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr Y k •
          ((chartModelBasis E) k : TangentSpace I x) :=
      ((chartModelBasis E).sum_repr Y).symm
    rw [show g.inner x X Y = g.inner x X
            (∑ k : Fin (Module.finrank ℝ E),
              (chartModelBasis E).repr Y k •
                ((chartModelBasis E) k : TangentSpace I x)) from
      congrArg (g.inner x X) hY_decomp]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [show g.inner x X
            ((chartModelBasis E).repr Y k •
              ((chartModelBasis E) k : TangentSpace I x)) =
          (chartModelBasis E).repr Y k *
            g.inner x X ((chartModelBasis E) k) from by
      rw [show ((g.inner x) X)
              (((chartModelBasis E).repr Y k) •
                ((chartModelBasis E) k : TangentSpace I x)) =
            ((chartModelBasis E).repr Y k) •
              ((g.inner x) X) ((chartModelBasis E) k) from
        ContinuousLinearMap.map_smul ((g.inner x) X) _ _]
      rw [smul_eq_mul]]
    ring
  rw [← hT_trace_xy, hT_trace_orthonormal]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [hT_pair]

end OrthonormalRiesz

end Connection
end Integral
end DifferentialGeometry
