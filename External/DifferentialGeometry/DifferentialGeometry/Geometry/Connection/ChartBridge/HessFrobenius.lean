import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Connection
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization


noncomputable section

open Bundle Manifold Set FiberBundle Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor.Coordinates


noncomputable def leviHessSec
    (g : SmoothRiemannianMetric I M)
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f) :
    TwoTensorSection (I := I) (M := M) :=
  hessianSec (I := I)
    (leviCivitaConnectionOfMetric (I := I) g)
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g)
    f hf



omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem hessSec_abs
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (x : M) (v w : TangentSpace I x) :
    leviHessSec (I := I) g f hf x (vec2 (I := I) v w) =
      abstractHessian (I := I) g f x v w := by
  classical
  change hessianSec (I := I)
      (leviCivitaConnectionOfMetric (I := I) g)
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
      f hf x (vec2 (I := I) v w) = _
  let cov := leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  obtain ⟨X, hX⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v
  obtain ⟨Y, hY⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x w
  have hsec := (hessianSec_nabla (I := I) cov hcov f hf) x X (Y x)
  have heval := nabla0SFun_one_eval_smooth_slots
    (I := I) cov X Y (duSec (I := I) f hf) x
  have htheta : MDiffAtCotangent (extDerivFun (I := I) f) x :=
    ((cotangentCov_extDerivFun_smooth (I := I) hf) x).mdifferentiableAt (by simp)
  have hYmd : MDiffAt (T% (fun p : M => Y p)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hpair := cotangentCov_dualPairing cov htheta hYmd (X x)
  have hdufun :
      (fun p : M => duSec (I := I) f hf p (fun _ : Fin 1 => Y p)) =
        fun p : M => extDerivFun (I := I) f p (Y p) := by
    funext p
    rw [duSec_apply]
    exact differential1FormFun_apply_eq_extDerivFun (I := I) f p (Y p)
  rw [← hX, ← hY]
  rw [hsec]
  change
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 cov X (duSec (I := I) f hf) x) (fun _ : Fin 1 => Y x) = _
  rw [heval, hdufun, duSec_apply,
    differential1FormFun_apply_eq_extDerivFun]
  change
    extDerivFun (I := I) (fun p : M => extDerivFun (I := I) f p (Y p)) x (X x) -
        extDerivFun (I := I) f x ((cov (fun p : M => Y p) x) (X x)) =
      ((cotangentCov cov).toFun (extDerivFun (I := I) f) x (X x)) (Y x)
  linarith



omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem hessSec_chart_comp
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (x : M) (hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (i j : Fin (Module.finrank Real E)) :
    leviHessSec (I := I) g f hf x
        (fun a : Fin 2 => if a = 0 then
          chartBasisFamily (I := I) x hx i else
            chartBasisFamily (I := I) x hx j) =
      chartHessianTensor (I := I) g x f i j x := by
  have hslots :
      (fun a : Fin 2 => if a = 0 then
        chartBasisFamily (I := I) x hx i else
          chartBasisFamily (I := I) x hx j) =
        vec2 (I := I) (chartBasisFamily (I := I) x hx i)
          (chartBasisFamily (I := I) x hx j) := by
    funext a
    fin_cases a <;> simp [vec2]
  rw [hslots, hessSec_abs (I := I) g hf]
  rw [show chartBasisFamily (I := I) x hx i = (chartModelBasis E) i by
      simp only [chartBasisFamily_apply, chartBasisVecFiber_self],
    show chartBasisFamily (I := I) x hx j = (chartModelBasis E) j by
      simp only [chartBasisFamily_apply, chartBasisVecFiber_self]]
  exact chartHessianMatrixIdentity_holds (I := I) g hf x i j

omit [NeZero (Module.finrank Real E)] in

omit [SigmaCompactSpace M] in
private theorem hessSec_norm_coord
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (x : M) (hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    normSq0S (I := I) g x 2 (leviHessSec (I := I) g f hf x) =
      ∑ i : Fin (Module.finrank Real E),
      ∑ j : Fin (Module.finrank Real E),
      ∑ k : Fin (Module.finrank Real E),
      ∑ l : Fin (Module.finrank Real E),
        chartInvGramMatrix (I := I) g x x i k *
          chartInvGramMatrix (I := I) g x x j l *
            leviHessSec (I := I) g f hf x
              (fun a : Fin 2 => if a = 0 then
                chartBasisFamily (I := I) x hx i else
                  chartBasisFamily (I := I) x hx j) *
            leviHessSec (I := I) g f hf x
              (fun a : Fin 2 => if a = 0 then
                chartBasisFamily (I := I) x hx k else
                  chartBasisFamily (I := I) x hx l) := by
  have hinv : MetricInverseInBasis (I := I) g x
      (chartBasisFamily (I := I) x hx)
      (fun i j => chartInvGramMatrix (I := I) g x x i j) := by
    intro i j
    refine ⟨?_, ?_⟩
    · have hmul := chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hx
      have hentry :
          (chartInvGramMatrix (I := I) g x x *
            chartGramMatrix (I := I) g x x) i j =
              (1 : Matrix _ _ Real) i j := by
        rw [hmul]
      rw [Matrix.mul_apply, Matrix.one_apply] at hentry
      rw [← hentry]
      exact Finset.sum_congr rfl fun k _ => by
        rw [chartGramMatrix_apply, chartBasisFamily_apply, chartBasisFamily_apply]
    · have hmul := chartGramMatrix_mul_chartInvGramMatrix (I := I) g x hx
      have hentry :
          (chartGramMatrix (I := I) g x x *
            chartInvGramMatrix (I := I) g x x) i j =
              (1 : Matrix _ _ Real) i j := by
        rw [hmul]
      rw [Matrix.mul_apply, Matrix.one_apply] at hentry
      rw [← hentry]
      exact Finset.sum_congr rfl fun k _ => by
        rw [chartGramMatrix_apply, chartBasisFamily_apply, chartBasisFamily_apply]
  exact normSq0S_two_eq_coord (I := I) g x
    (chartBasisFamily (I := I) x hx)
    (fun i j => chartInvGramMatrix (I := I) g x x i j)
    hinv (leviHessSec (I := I) g f hf x)


omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
theorem chartHessFrobeniusSq_eq_frobeniusSqFun_hessFun_of_orthonormal
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    chartHessFrobeniusSq (I := I) g f x =
      frobeniusSqFun (I := I) (M := M) (hessFun (I := I) g f) x := by
  classical
  rw [chartHessFrobeniusSq_def, frobeniusSqFun_hessFun]
  have hLHS_eq :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i k *
            chartInvGramMatrix (I := I) g x x j l *
              chartHessianTensor (I := I) g x f i j x *
                chartHessianTensor (I := I) g x f k l x) =
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          (if i = k then (1 : ℝ) else 0) *
            (if j = l then (1 : ℝ) else 0) *
              chartHessianTensor (I := I) g x f i j x *
                chartHessianTensor (I := I) g x f k l x) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [h_orth i k, h_orth j l]
  rw [hLHS_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hl : ∀ k : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        (if i = k then (1 : ℝ) else 0) *
          (if j = l then (1 : ℝ) else 0) *
            chartHessianTensor (I := I) g x f i j x *
              chartHessianTensor (I := I) g x f k l x =
        (if i = k then (1 : ℝ) else 0) *
          chartHessianTensor (I := I) g x f i j x *
          chartHessianTensor (I := I) g x f k j x := by
    intro k
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]
      ring
    · intro l _ hlj
      have hjl : ¬ j = l := fun h => hlj h.symm
      rw [if_neg hjl]
      ring
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [show
      (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          (if i = k then (1 : ℝ) else 0) *
            (if j = l then (1 : ℝ) else 0) *
              chartHessianTensor (I := I) g x f i j x *
                chartHessianTensor (I := I) g x f k l x) =
      ∑ k : Fin (Module.finrank ℝ E),
        (if i = k then (1 : ℝ) else 0) *
          chartHessianTensor (I := I) g x f i j x *
          chartHessianTensor (I := I) g x f k j x from
    Finset.sum_congr rfl (fun k _ => hl k)]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
    ring
  · intro k _ hki
    have hik : ¬ i = k := fun h => hki h.symm
    rw [if_neg hik]
    ring
  · intro hi
    exact absurd (Finset.mem_univ i) hi

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartHessFrobeniusSq_eq_metric_hessian_norm_sq [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    chartHessFrobeniusSq (I := I) g f x =
      frobeniusSqFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x := by
  classical
  have h1 : chartHessFrobeniusSq (I := I) g f x =
      frobeniusSqFun (I := I) (M := M) (hessFun (I := I) g f) x :=
    chartHessFrobeniusSq_eq_frobeniusSqFun_hessFun_of_orthonormal
      (I := I) g f x h_orth
  have hM : chartHessianMatrixIdentity (I := I) g f x :=
    chartHessianMatrixIdentity_holds (I := I) g hf x
  have h2 : frobeniusSqFun (I := I) (M := M) (hessFun (I := I) g f) x =
      frobeniusSqFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x :=
    frobeniusSqFun_hessFun_eq_frobeniusSqFun_abstractHessianBilin_of_matrix_identity
      (I := I) g f x hM
  exact h1.trans h2



omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hessSec_normSq [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f) (x : M) :
    normSq0S (I := I) g x 2 (leviHessSec (I := I) g f hf x) =
      chartHessFrobeniusSq (I := I) g f x := by
  classical
  let hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x
  rw [hessSec_norm_coord (I := I) g hf x hx]
  rw [chartHessFrobeniusSq_def]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hessSec_chart_comp (I := I) g hf x hx i j,
    hessSec_chart_comp (I := I) g hf x hx k l]

end Connection
end Integral
end DifferentialGeometry
