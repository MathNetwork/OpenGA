import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.PosDefPerturbation
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpVWFactorBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpHigherRankParseval
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Geometry.Metric.MetricBounds


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


private lemma sum_fun_fin_four_eval_zero_one {n : ℕ} (F : Fin n → Fin n → ℝ) :
    ∑ K : Fin 4 → Fin n, F (K 0) (K 1) =
      ((n : ℝ) ^ 2) * ∑ k : Fin n, ∑ l : Fin n, F k l := by
  classical
  have h1 : ∑ p : Fin n × (Fin 3 → Fin n), F p.1 (p.2 0) =
      ∑ K : Fin 4 → Fin n, F (K 0) (K 1) :=
    Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin 4 => Fin n))
      (fun p => F p.1 (p.2 0)) (fun K => F (K 0) (K 1)) (fun p => rfl)
  rw [← h1, Fintype.sum_prod_type]
  have h2 : ∀ k : Fin n, ∑ f : Fin 3 → Fin n, F k (f 0) =
      ((n : ℝ) ^ 2) * ∑ l : Fin n, F k l := by
    intro k
    have h3 : ∑ q : Fin n × (Fin 2 → Fin n), F k q.1 =
        ∑ f : Fin 3 → Fin n, F k (f 0) :=
      Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin 3 => Fin n))
        (fun q => F k q.1) (fun f => F k (f 0)) (fun q => rfl)
    rw [← h3, Fintype.sum_prod_type]
    have h4 : ∀ l : Fin n, ∑ _r : Fin 2 → Fin n, F k l = ((n : ℝ) ^ 2) * F k l := by
      intro l
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun l _ => h4 l), ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun k _ => h2 k), ← Finset.mul_sum]


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metric_inner_right_sum (g : SmoothRiemannianMetric I M) (x : M)
    (u : TangentSpace I x) {d : ℕ} (c : Fin d → ℝ) (v : Fin d → TangentSpace I x) :
    g.inner x u (∑ b, c b • v b) = ∑ b, c b * g.inner x u (v b) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun b _ => by rw [map_smul, smul_eq_mul])


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metric_inner_left_sum (g : SmoothRiemannianMetric I M) (x : M)
    {d : ℕ} (c : Fin d → ℝ) (v : Fin d → TangentSpace I x) (u : TangentSpace I x) :
    g.inner x (∑ a, c a • v a) u = ∑ a, c a * g.inner x (v a) u := by
  have h1 : g.inner x (∑ a, c a • v a) = ∑ a, c a • g.inner x (v a) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun a _ => by rw [map_smul])
  rw [h1, ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun a _ => by
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul])


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metric_inner_orthonormal_pair (g₁ : SmoothRiemannianMetric I M) (x : M)
    {d : ℕ} (B : Fin d → TangentSpace I x)
    (hB : ∀ a b, g₁.inner x (B a) (B b) = if a = b then (1 : ℝ) else 0)
    (c c' : Fin d → ℝ) :
    g₁.inner x (∑ a, c a • B a) (∑ b, c' b • B b) = ∑ a, c a * c' a := by
  rw [metric_inner_left_sum (I := I) (M := M) g₁ x c B]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [metric_inner_right_sum (I := I) (M := M) g₁ x (B a) c' B]
  congr 1
  rw [Finset.sum_congr rfl (fun b _ => by rw [hB a b, mul_ite, mul_one, mul_zero])]
  rw [Finset.sum_ite_eq]
  exact if_pos (Finset.mem_univ a)


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma sum_sq_component_le_of_orthonormal
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) {δ : ℝ} (h1mδ : (0 : ℝ) < 1 - δ)
    (hcomp : ∀ u : TangentSpace I x,
      (1 - δ) * g₀.inner x u u ≤ g₁.inner x u u)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hpars : ∀ v : TangentSpace I x, ∑ i, g₀.inner x (e i) v ^ 2 = g₀.inner x v v)
    {d : ℕ} (B : Fin d → TangentSpace I x)
    (hB : ∀ a b, g₁.inner x (B a) (B b) = if a = b then (1 : ℝ) else 0)
    (c : Fin d → ℝ) :
    ∑ k, (∑ a, c a * g₀.inner x (e k) (B a)) ^ 2 ≤
      (1 / (1 - δ)) * ∑ a, (c a) ^ 2 := by
  have h1 : ∀ k, (∑ a, c a * g₀.inner x (e k) (B a)) =
      g₀.inner x (e k) (∑ a, c a • B a) := by
    intro k
    rw [metric_inner_right_sum (I := I) (M := M) g₀ x (e k) c B]
  rw [Finset.sum_congr rfl (fun k _ => by rw [h1 k])]
  rw [hpars (∑ a, c a • B a)]
  have h2 := hcomp (∑ a, c a • B a)
  rw [metric_inner_orthonormal_pair (I := I) (M := M) g₁ x B hB c c] at h2
  have h3 : ∀ a, c a * c a = (c a) ^ 2 := fun a => (sq (c a)).symm
  rw [Finset.sum_congr rfl (fun a _ => h3 a)] at h2
  have h4 : g₀.inner x (∑ a, c a • B a) (∑ a, c a • B a) * (1 - δ) ≤
      ∑ a, (c a) ^ 2 := by nlinarith [h2]
  calc g₀.inner x (∑ a, c a • B a) (∑ a, c a • B a)
      ≤ (∑ a, (c a) ^ 2) / (1 - δ) := (le_div_iff₀ h1mδ).mpr h4
    _ = (1 / (1 - δ)) * ∑ a, (c a) ^ 2 := by ring


private lemma div_pow_div_arith {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    (u / t) ^ 2 / t = u ^ 2 / t ^ 3 := by
  field_simp


private lemma one_div_mul_pow_arith {t : ℝ} (ht : t ≠ 0) (D u : ℝ) :
    (1 / t) * (D * (u / t ^ 3)) = D * (u / t ^ 4) := by
  field_simp


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma weight_row_g0norm_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) {δ δW : ℝ}
    (h1mδ : (0 : ℝ) < 1 - δ) (hδW0 : 0 ≤ δW)
    (hcomp : ∀ u : TangentSpace I x,
      (1 - δ) * g₀.inner x u u ≤ g₁.inner x u u)
    {d : ℕ} (B : Fin d → TangentSpace I x)
    (hB : ∀ a b, g₁.inner x (B a) (B b) = if a = b then (1 : ℝ) else 0)
    (hB0 : ∀ a, g₀.inner x (B a) (B a) ≤ 1 / (1 - δ))
    (Wx : Tensor0SSpace 2 I x)
    (hWx : ∀ v w : TangentSpace I x,
      |Tensor0SSpace.toModel (𝕜 := ℝ) Wx ![(v : E), (w : E)]| ≤
        δW * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w))
    (a : Fin d) :
    g₀.inner x
        (∑ b, (Tensor0SSpace.toModel (𝕜 := ℝ) Wx ![(B a : E), (B b : E)]) • B b)
        (∑ b, (Tensor0SSpace.toModel (𝕜 := ℝ) Wx ![(B a : E), (B b : E)]) • B b) ≤
      δW ^ 2 / (1 - δ) ^ 3 := by
  classical
  set c : Fin d → ℝ :=
    fun b => Tensor0SSpace.toModel (𝕜 := ℝ) Wx ![(B a : E), (B b : E)] with hc_def
  set w : TangentSpace I x := ∑ b, c b • B b with hw_def
  set X : ℝ := g₁.inner x w w with hX_def
  have hX_sum : X = ∑ b, c b * c b := by
    rw [hX_def, hw_def]
    exact metric_inner_orthonormal_pair (I := I) (M := M) g₁ x B hB c c
  have hX0 : 0 ≤ X := by
    rw [hX_sum]
    exact Finset.sum_nonneg (fun b _ => mul_self_nonneg _)
  have hupd : ∀ z : E, (![(B a : E), z] : Fin 2 → E) =
      Function.update ![(B a : E), (B a : E)] 1 z := by
    intro z
    funext i
    fin_cases i <;> simp [Function.update]
  have hWaw : Tensor0SSpace.toModel (𝕜 := ℝ) Wx ![(B a : E), (w : E)] = X := by
    rw [hupd (w : E)]
    have hsum_coe : (w : E) = ∑ b, c b • (B b : E) := rfl
    rw [hsum_coe]
    have hms : (Tensor0SSpace.toModel (𝕜 := ℝ) Wx)
        (Function.update ![(B a : E), (B a : E)] 1 (∑ b, c b • (B b : E))) =
        ∑ b, (Tensor0SSpace.toModel (𝕜 := ℝ) Wx)
          (Function.update ![(B a : E), (B a : E)] 1 (c b • (B b : E))) :=
      (Tensor0SSpace.toModel (𝕜 := ℝ) Wx).toMultilinearMap.map_update_sum
        Finset.univ (1 : Fin 2) (fun b => c b • (B b : E)) ![(B a : E), (B a : E)]
    rw [hms]
    have hterm : ∀ b : Fin d,
        (Tensor0SSpace.toModel (𝕜 := ℝ) Wx)
            (Function.update ![(B a : E), (B a : E)] 1 (c b • (B b : E))) =
          c b * c b := by
      intro b
      rw [(Tensor0SSpace.toModel (𝕜 := ℝ) Wx).map_update_smul
        ![(B a : E), (B a : E)] (1 : Fin 2) (c b) ((B b : E)), ← hupd ((B b : E)),
        smul_eq_mul]
    rw [Finset.sum_congr rfl (fun b _ => hterm b), ← hX_sum]
  have hg0w : g₀.inner x w w ≤ X / (1 - δ) := by
    have h1 := hcomp w
    rw [← hX_def] at h1
    rw [le_div_iff₀ h1mδ]
    nlinarith [h1]
  have hkey : X ≤ (δW / (1 - δ)) * Real.sqrt X := by
    have h1 : |Tensor0SSpace.toModel (𝕜 := ℝ) Wx ![(B a : E), (w : E)]| ≤
        δW * Real.sqrt (g₀.inner x (B a) (B a)) * Real.sqrt (g₀.inner x w w) :=
      hWx (B a) w
    rw [hWaw, abs_of_nonneg hX0] at h1
    have h2 : Real.sqrt (g₀.inner x (B a) (B a)) ≤ Real.sqrt (1 / (1 - δ)) :=
      Real.sqrt_le_sqrt (hB0 a)
    have h3 : Real.sqrt (g₀.inner x w w) ≤ Real.sqrt (X * (1 / (1 - δ))) := by
      refine Real.sqrt_le_sqrt ?_
      rw [mul_one_div]
      exact hg0w
    have h4 : Real.sqrt (X * (1 / (1 - δ))) =
        Real.sqrt X * Real.sqrt (1 / (1 - δ)) := Real.sqrt_mul hX0 _
    have h1mδ_inv_nonneg : (0 : ℝ) ≤ 1 / (1 - δ) := by positivity
    have h5 : X ≤ δW * Real.sqrt (1 / (1 - δ)) *
        (Real.sqrt X * Real.sqrt (1 / (1 - δ))) := by
      calc X ≤ δW * Real.sqrt (g₀.inner x (B a) (B a)) * Real.sqrt (g₀.inner x w w) := h1
        _ ≤ δW * Real.sqrt (1 / (1 - δ)) * Real.sqrt (g₀.inner x w w) := by
            have h6 := mul_le_mul_of_nonneg_left h2 hδW0
            exact mul_le_mul_of_nonneg_right h6 (Real.sqrt_nonneg _)
        _ ≤ δW * Real.sqrt (1 / (1 - δ)) *
            (Real.sqrt X * Real.sqrt (1 / (1 - δ))) := by
            rw [← h4]
            exact mul_le_mul_of_nonneg_left h3
              (mul_nonneg hδW0 (Real.sqrt_nonneg _))
    calc X ≤ δW * Real.sqrt (1 / (1 - δ)) *
          (Real.sqrt X * Real.sqrt (1 / (1 - δ))) := h5
      _ = δW * (Real.sqrt (1 / (1 - δ)) * Real.sqrt (1 / (1 - δ))) * Real.sqrt X := by
          ring
      _ = δW * (1 / (1 - δ)) * Real.sqrt X := by
          rw [Real.mul_self_sqrt h1mδ_inv_nonneg]
      _ = (δW / (1 - δ)) * Real.sqrt X := by ring
  have hXle : X ≤ (δW / (1 - δ)) ^ 2 := by
    have hc_nn : (0 : ℝ) ≤ δW / (1 - δ) := div_nonneg hδW0 (le_of_lt h1mδ)
    nlinarith [hkey, Real.sq_sqrt hX0, Real.sqrt_nonneg X,
      sq_nonneg (Real.sqrt X - δW / (1 - δ))]
  calc g₀.inner x w w ≤ X / (1 - δ) := hg0w
    _ ≤ (δW / (1 - δ)) ^ 2 / (1 - δ) := by gcongr
    _ = δW ^ 2 / (1 - δ) ^ 3 := div_pow_div_arith (ne_of_gt h1mδ) δW

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_smul (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  classical
  obtain ⟨n, e, hn, horth, hpars, hrfns⟩ :=
    exists_orthonormal_frame_riemannianFiberNormSq (I := I) (M := M) g r s x
  rw [hrfns (c • v), hrfns v, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [fiberNormSqSummand_eq_component_sq, fiberNormSqSummand_eq_component_sq,
    fiberNormSqComponent_smul]
  ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_curvatureRefoldMonomialBiContrFib_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    {δ : ℝ} (hδ1 : δ < 1)
    (hδP : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (W : Π b : M, Tensor0SSpace 2 I b) {δW : ℝ} (hδW0 : 0 ≤ δW)
    (hW : ∀ (y : M) (v w : TangentSpace I y),
      |Tensor0SSpace.toModel (𝕜 := ℝ) (W y) ![(v : E), (w : E)]| ≤
        δW * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w))
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        (show TensorRSSpace 4 2 I x from
          TensorRSSpace.ofCLM
            (curvatureActionMonomialTrace (I := I) (M := M) g₁ W σ x)) ≤
      (deTurckArmFibreConst (Module.finrank ℝ E) * (δW / (1 - δ) ^ 2)) ^ 2 := by
  classical
  have h1mδ : (0 : ℝ) < 1 - δ := by linarith
  obtain ⟨n, e, hn, horth, hpars, hrfns⟩ :=
    exists_orthonormal_frame_riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
  have hnE : n = Module.finrank ℝ E := hn
  subst hnE
  have hcomp : ∀ u : TangentSpace I x,
      (1 - δ) * g₀.inner x u u ≤ g₁.inner x u u := by
    intro u
    have h := hδP x u u
    have huu : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have heq : δ * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x u u) =
        δ * g₀.inner x u u := by
      rw [mul_assoc, Real.mul_self_sqrt huu]
    rw [heq] at h
    have hlb := (abs_le.mp h).1
    have hti := htie x u u
    nlinarith [hlb, hti]
  have hBg1 : ∀ a b : Fin (Module.finrank ℝ E),
      g₁.inner x (smoothOrthoFrame (I := I) g₁ x a x)
        (smoothOrthoFrame (I := I) g₁ x b x) = if a = b then (1 : ℝ) else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ x a b
  have hB0 : ∀ a : Fin (Module.finrank ℝ E),
      g₀.inner x (smoothOrthoFrame (I := I) g₁ x a x)
        (smoothOrthoFrame (I := I) g₁ x a x) ≤ 1 / (1 - δ) := by
    intro a
    have h1 := hcomp (smoothOrthoFrame (I := I) g₁ x a x)
    have h2 : g₁.inner x (smoothOrthoFrame (I := I) g₁ x a x)
        (smoothOrthoFrame (I := I) g₁ x a x) = 1 := by
      rw [hBg1 a a]
      simp
    have h0 : 0 ≤ g₀.inner x (smoothOrthoFrame (I := I) g₁ x a x)
        (smoothOrthoFrame (I := I) g₁ x a x) :=
      metric_inner_self_nonneg (I := I) (M := M) g₀ x _
    rw [le_div_iff₀ h1mδ]
    nlinarith [h1, h2]
  set Wm : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a b => Tensor0SSpace.toModel (𝕜 := ℝ) (W x)
      ![(smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] with hWm_def
  set A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun k a => g₀.inner x (e k) (smoothOrthoFrame (I := I) g₁ x a x) with hA_def
  set V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun k l => ∑ a, ∑ b, Wm a b * (A k a * A l b) with hV_def
  have hcomp_eq : ∀ (K : Fin 4 → Fin (Module.finrank ℝ E))
      (J : Fin 2 → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            TensorRSSpace.ofCLM
              (curvatureActionMonomialTrace (I := I) (M := M) g₁ W σ x))
          (Module.finrank ℝ E) e K J =
        V (K (σ.symm 0)) (K (σ.symm 1)) *
          ((if K (σ.symm 2) = J 0 then (1 : ℝ) else 0) *
            (if K (σ.symm 3) = J 1 then (1 : ℝ) else 0)) := by
    intro K J
    have hcomp_toModel : fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          TensorRSSpace.ofCLM
            (curvatureActionMonomialTrace (I := I) (M := M) g₁ W σ x))
        (Module.finrank ℝ E) e K J =
        Tensor0SSpace.toModel
          ((curvatureActionMonomialTrace (I := I) (M := M) g₁ W σ x)
            (coframeS (I := I) (M := M) g₀ x 4 e K))
          (fun i => (e (J i) : E)) := by
      unfold fiberNormSqComponent coframeS
      rfl
    rw [hcomp_toModel]
    rw [show curvatureActionMonomialTrace (I := I) (M := M) g₁ W σ x =
        curvatureActionMonomialFrameTrace (I := I) (M := M) W σ
          (smoothOrthoFrame (I := I) g₁ x) x from rfl]
    rw [curvatureRefoldMonomialFibFixedFrame_toModel]
    have hterm : ∀ a b : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel (𝕜 := ℝ)
            (coframeS (I := I) (M := M) g₀ x 4 e K)
            (fun i => (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : E))
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : E))
                (fun i => (e (J i) : E))) : Fin 4 → E) (σ i)) =
          (A (K (σ.symm 0)) a * A (K (σ.symm 1)) b) *
            ((if K (σ.symm 2) = J 0 then (1 : ℝ) else 0) *
              (if K (σ.symm 3) = J 1 then (1 : ℝ) else 0)) := by
      intro a b
      set tup : Fin 4 → E :=
        (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : E))
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : E))
            (fun i => (e (J i) : E))) : Fin 4 → E) with htup_def
      have step1 : Tensor0SSpace.toModel (𝕜 := ℝ)
          (coframeS (I := I) (M := M) g₀ x 4 e K) (fun i => tup (σ i)) =
          ∏ k : Fin 4, g₀.inner x (e (K k)) ((tup (σ k) : TangentSpace I x)) :=
        coframeS_apply (I := I) (M := M) g₀ x 4 e K
          (fun i => (tup (σ i) : TangentSpace I x))
      set f : Fin 4 → ℝ :=
        fun j => g₀.inner x (e (K (σ.symm j))) ((tup j : TangentSpace I x)) with hf_def
      have step2 : (∏ k : Fin 4, g₀.inner x (e (K k)) ((tup (σ k) : TangentSpace I x))) =
          ∏ i : Fin 4, f (σ i) :=
        Finset.prod_congr rfl (fun k _ => by
          simp only [hf_def, Equiv.symm_apply_apply])
      have step3 : (∏ i : Fin 4, f (σ i)) = ∏ j : Fin 4, f j := Equiv.prod_comp σ f
      have step4 : (∏ j : Fin 4, f j) = f 0 * f 1 * f 2 * f 3 := Fin.prod_univ_four f
      have hf0 : f 0 = A (K (σ.symm 0)) a := by
        simp only [hf_def]
        rfl
      have hf1 : f 1 = A (K (σ.symm 1)) b := by
        simp only [hf_def]
        rfl
      have hf2 : f 2 = if K (σ.symm 2) = J 0 then (1 : ℝ) else 0 := by
        simp only [hf_def]
        rw [show ((tup 2 : TangentSpace I x)) = e (J 0) from rfl]
        exact horth (K (σ.symm 2)) (J 0)
      have hf3 : f 3 = if K (σ.symm 3) = J 1 then (1 : ℝ) else 0 := by
        simp only [hf_def]
        rw [show ((tup 3 : TangentSpace I x)) = e (J 1) from rfl]
        exact horth (K (σ.symm 3)) (J 1)
      rw [step1, step2, step3, step4, hf0, hf1, hf2, hf3]
      ring
    have hsum_split : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel (𝕜 := ℝ) (W x)
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          Tensor0SSpace.toModel (𝕜 := ℝ)
            (coframeS (I := I) (M := M) g₀ x 4 e K)
            (fun i => (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : E))
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : E))
                (fun i => (e (J i) : E))) : Fin 4 → E) (σ i))) =
        V (K (σ.symm 0)) (K (σ.symm 1)) *
          ((if K (σ.symm 2) = J 0 then (1 : ℝ) else 0) *
            (if K (σ.symm 3) = J 1 then (1 : ℝ) else 0)) := by
      have hper : ∀ a b : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel (𝕜 := ℝ) (W x)
              ![(smoothOrthoFrame (I := I) g₁ x a x : E),
                (smoothOrthoFrame (I := I) g₁ x b x : E)] *
            Tensor0SSpace.toModel (𝕜 := ℝ)
              (coframeS (I := I) (M := M) g₀ x 4 e K)
              (fun i => (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : E))
                (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : E))
                  (fun i => (e (J i) : E))) : Fin 4 → E) (σ i)) =
          (Wm a b * (A (K (σ.symm 0)) a * A (K (σ.symm 1)) b)) *
            ((if K (σ.symm 2) = J 0 then (1 : ℝ) else 0) *
              (if K (σ.symm 3) = J 1 then (1 : ℝ) else 0)) := by
        intro a b
        rw [hterm a b]
        rw [show Tensor0SSpace.toModel (𝕜 := ℝ) (W x)
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] = Wm a b from rfl]
        ring
      rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl
        (fun b _ => hper a b))]
      rw [show V (K (σ.symm 0)) (K (σ.symm 1)) =
          ∑ a, ∑ b, Wm a b * (A (K (σ.symm 0)) a * A (K (σ.symm 1)) b) from rfl]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a _ => by rw [Finset.sum_mul])
    exact hsum_split
  have hJcollapse : ∀ K : Fin 4 → Fin (Module.finrank ℝ E),
      ∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        (fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            TensorRSSpace.ofCLM
              (curvatureActionMonomialTrace (I := I) (M := M) g₁ W σ x))
          (Module.finrank ℝ E) e K J) ^ 2 =
        (V (K (σ.symm 0)) (K (σ.symm 1))) ^ 2 := by
    intro K
    have h1 : ∀ J : Fin 2 → Fin (Module.finrank ℝ E),
        (fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            TensorRSSpace.ofCLM
              (curvatureActionMonomialTrace (I := I) (M := M) g₁ W σ x))
          (Module.finrank ℝ E) e K J) ^ 2 =
        (V (K (σ.symm 0)) (K (σ.symm 1))) ^ 2 *
          ((if K (σ.symm 2) = J 0 then (1 : ℝ) else 0) *
            (if K (σ.symm 3) = J 1 then (1 : ℝ) else 0)) := by
      intro J
      rw [hcomp_eq K J]
      by_cases h2 : K (σ.symm 2) = J 0 <;> by_cases h3 : K (σ.symm 3) = J 1 <;>
        simp [h2, h3]
    rw [Finset.sum_congr rfl (fun J _ => h1 J), ← Finset.mul_sum]
    have hcount : ∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        ((if K (σ.symm 2) = J 0 then (1 : ℝ) else 0) *
          (if K (σ.symm 3) = J 1 then (1 : ℝ) else 0)) = 1 := by
      have h4 : ∑ J : Fin 2 → Fin (Module.finrank ℝ E),
          ((if K (σ.symm 2) = J 0 then (1 : ℝ) else 0) *
            (if K (σ.symm 3) = J 1 then (1 : ℝ) else 0)) =
          ∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ((if K (σ.symm 2) = p.1 then (1 : ℝ) else 0) *
              (if K (σ.symm 3) = p.2 then (1 : ℝ) else 0)) :=
        Fintype.sum_equiv (piFinTwoEquiv (fun _ : Fin 2 => Fin (Module.finrank ℝ E)))
          _ _ (fun J => rfl)
      rw [h4, Fintype.sum_prod_type]
      have h5 : ∀ j0 : Fin (Module.finrank ℝ E),
          (∑ j1 : Fin (Module.finrank ℝ E),
            (if K (σ.symm 2) = j0 then (1 : ℝ) else 0) *
              (if K (σ.symm 3) = j1 then (1 : ℝ) else 0)) =
          (if K (σ.symm 2) = j0 then (1 : ℝ) else 0) := by
        intro j0
        rw [← Finset.mul_sum, Finset.sum_ite_eq, if_pos (Finset.mem_univ _), mul_one]
      rw [Finset.sum_congr rfl (fun j0 _ => h5 j0), Finset.sum_ite_eq,
        if_pos (Finset.mem_univ _)]
    rw [hcount, mul_one]
  have hKcollapse : ∑ K : Fin 4 → Fin (Module.finrank ℝ E),
      (V (K (σ.symm 0)) (K (σ.symm 1))) ^ 2 =
      ((Module.finrank ℝ E : ℝ) ^ 2) * ∑ k, ∑ l, (V k l) ^ 2 := by
    have h1 : ∑ K : Fin 4 → Fin (Module.finrank ℝ E),
        (V (K (σ.symm 0)) (K (σ.symm 1))) ^ 2 =
        ∑ K : Fin 4 → Fin (Module.finrank ℝ E), (V (K 0) (K 1)) ^ 2 :=
      Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin (Module.finrank ℝ E))))
        (fun K => (V (K (σ.symm 0)) (K (σ.symm 1))) ^ 2)
        (fun K => (V (K 0) (K 1)) ^ 2) (fun K => rfl)
    rw [h1]
    exact sum_fun_fin_four_eval_zero_one (fun k l => (V k l) ^ 2)
  have hVsum : ∑ k, ∑ l, (V k l) ^ 2 ≤
      (Module.finrank ℝ E : ℝ) * (δW ^ 2 / (1 - δ) ^ 4) := by
    have hq_eq : ∀ (a l : Fin (Module.finrank ℝ E)),
        (∑ b, Wm a b * A l b) =
          g₀.inner x (e l) (∑ b, Wm a b • smoothOrthoFrame (I := I) g₁ x b x) := by
      intro a l
      rw [metric_inner_right_sum (I := I) (M := M) g₀ x (e l) (Wm a)
        (fun b => smoothOrthoFrame (I := I) g₁ x b x)]
    have hV_swap : ∀ k l, V k l = ∑ a, (∑ b, Wm a b * A l b) * A k a := by
      intro k l
      rw [show V k l = ∑ a, ∑ b, Wm a b * (A k a * A l b) from rfl]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      ring
    have hcol : ∀ l : Fin (Module.finrank ℝ E),
        ∑ k, (V k l) ^ 2 ≤ (1 / (1 - δ)) * ∑ a, (∑ b, Wm a b * A l b) ^ 2 := by
      intro l
      rw [Finset.sum_congr rfl (fun k _ => by rw [hV_swap k l])]
      exact sum_sq_component_le_of_orthonormal (I := I) (M := M) g₀ g₁ x h1mδ hcomp
        e hpars (fun a => smoothOrthoFrame (I := I) g₁ x a x) hBg1
        (fun a => ∑ b, Wm a b * A l b)
    have hrow_col : ∀ a : Fin (Module.finrank ℝ E),
        ∑ l, (∑ b, Wm a b * A l b) ^ 2 ≤ δW ^ 2 / (1 - δ) ^ 3 := by
      intro a
      rw [Finset.sum_congr rfl (fun l _ => by rw [hq_eq a l])]
      rw [hpars (∑ b, Wm a b • smoothOrthoFrame (I := I) g₁ x b x)]
      exact weight_row_g0norm_le (I := I) (M := M) g₀ g₁ x h1mδ hδW0 hcomp
        (fun a => smoothOrthoFrame (I := I) g₁ x a x) hBg1 hB0 (W x) (hW x) a
    calc ∑ k, ∑ l, (V k l) ^ 2 = ∑ l, ∑ k, (V k l) ^ 2 := Finset.sum_comm
      _ ≤ ∑ l : Fin (Module.finrank ℝ E),
            (1 / (1 - δ)) * ∑ a, (∑ b, Wm a b * A l b) ^ 2 :=
          Finset.sum_le_sum (fun l _ => hcol l)
      _ = (1 / (1 - δ)) * ∑ a, ∑ l, (∑ b, Wm a b * A l b) ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (1 / (1 - δ)) * ∑ _a : Fin (Module.finrank ℝ E), δW ^ 2 / (1 - δ) ^ 3 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.sum_le_sum (fun a _ => hrow_col a)
      _ = (Module.finrank ℝ E : ℝ) * (δW ^ 2 / (1 - δ) ^ 4) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          exact one_div_mul_pow_arith (ne_of_gt h1mδ) _ _
  have hrfns_eq := hrfns
    (show TensorRSSpace 4 2 I x from
      TensorRSSpace.ofCLM
        (curvatureActionMonomialTrace (I := I) (M := M) g₁ W σ x))
  rw [hrfns_eq]
  have hsummand : ∀ (K : Fin 4 → Fin (Module.finrank ℝ E))
      (J : Fin 2 → Fin (Module.finrank ℝ E)),
      fiberNormSqSummand (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          TensorRSSpace.ofCLM
            (curvatureActionMonomialTrace (I := I) (M := M) g₁ W σ x))
        (Module.finrank ℝ E) e K J =
      (fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          TensorRSSpace.ofCLM
            (curvatureActionMonomialTrace (I := I) (M := M) g₁ W σ x))
        (Module.finrank ℝ E) e K J) ^ 2 :=
    fun K J => fiberNormSqSummand_eq_component_sq (I := I) (M := M) g₀ x 4 2 _ _ e K J
  calc ∑ K : Fin 4 → Fin (Module.finrank ℝ E),
        ∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        fiberNormSqSummand (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            TensorRSSpace.ofCLM
              (curvatureActionMonomialTrace (I := I) (M := M) g₁ W σ x))
          (Module.finrank ℝ E) e K J
      = ∑ K : Fin 4 → Fin (Module.finrank ℝ E),
          (V (K (σ.symm 0)) (K (σ.symm 1))) ^ 2 := by
        refine Finset.sum_congr rfl (fun K _ => ?_)
        rw [Finset.sum_congr rfl (fun J _ => hsummand K J)]
        exact hJcollapse K
    _ = ((Module.finrank ℝ E : ℝ) ^ 2) * ∑ k, ∑ l, (V k l) ^ 2 := hKcollapse
    _ ≤ ((Module.finrank ℝ E : ℝ) ^ 2) *
          ((Module.finrank ℝ E : ℝ) * (δW ^ 2 / (1 - δ) ^ 4)) := by
        refine mul_le_mul_of_nonneg_left hVsum (by positivity)
    _ = (deTurckArmFibreConst (Module.finrank ℝ E) * (δW / (1 - δ) ^ 2)) ^ 2 := by
        rw [mul_pow, sq_deTurckArmFibreConst, div_pow]
        ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
