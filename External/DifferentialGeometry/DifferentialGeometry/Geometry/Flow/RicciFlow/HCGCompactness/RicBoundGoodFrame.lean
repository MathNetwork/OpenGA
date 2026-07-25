import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.Claim1Wiring
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.QuadraticForm.Basic

set_option autoImplicit false
set_option linter.style.longLine false





















noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]



omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem gramInv_inverse
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    {y : M} (hy : y ∈ e₀.baseSet) :
    Tensor0SBundle.MetricInverseInBasis_gen (I := I) g y
      ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hy)
      (fun i j => (gramE (I := I) e₀ g basisE y)⁻¹ i j) := by
  classical
  have hdet : IsUnit (gramE (I := I) e₀ g basisE y).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (gramE_posDef (I := I) e₀ g basisE hy).det_pos)
  have hco : ∀ k l : Idx,
      g.inner y
        (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hy) k)
        (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hy) l) =
      gramE (I := I) e₀ g basisE y k l := by
    intro k l
    rw [IsLocalFrameOn.toBasisAt_coe, IsLocalFrameOn.toBasisAt_coe]
    rfl
  intro i j
  constructor
  · have h := congrArg (fun A : Matrix Idx Idx Real => A i j)
      (Matrix.nonsing_inv_mul (gramE (I := I) e₀ g basisE y) hdet)
    simp only [Matrix.mul_apply, Matrix.one_apply] at h
    calc (∑ k : Idx, (gramE (I := I) e₀ g basisE y)⁻¹ i k *
            g.inner y
              (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hy) k)
              (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hy) j))
        = ∑ k : Idx, (gramE (I := I) e₀ g basisE y)⁻¹ i k *
            gramE (I := I) e₀ g basisE y k j :=
          Finset.sum_congr rfl fun k _ => by rw [hco]
      _ = if i = j then 1 else 0 := h
  · have h := congrArg (fun A : Matrix Idx Idx Real => A i j)
      (Matrix.mul_nonsing_inv (gramE (I := I) e₀ g basisE y) hdet)
    simp only [Matrix.mul_apply, Matrix.one_apply] at h
    calc (∑ k : Idx,
            g.inner y
              (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hy) i)
              (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hy) k) *
            (gramE (I := I) e₀ g basisE y)⁻¹ k j)
        = ∑ k : Idx, gramE (I := I) e₀ g basisE y i k *
            (gramE (I := I) e₀ g basisE y)⁻¹ k j :=
          Finset.sum_congr rfl fun k _ => by rw [hco]
      _ = if i = j then 1 else 0 := h


omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem gramInv_symm
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E) (y : M)
    (i j : Idx) :
    (gramE (I := I) e₀ g basisE y)⁻¹ i j = (gramE (I := I) e₀ g basisE y)⁻¹ j i := by
  have h := congr_fun (congr_fun ((gramE_herm (I := I) e₀ g basisE y).inv.eq) i) j
  simpa [Matrix.conjTranspose_apply] using h.symm



omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] [Fintype Idx] in
theorem gramE_eq_one
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E) {x : M}
    (hON : ∀ i j : Idx,
      g.inner x (e₀.localFrame basisE i x) (e₀.localFrame basisE j x) =
        if i = j then 1 else 0) :
    gramE (I := I) e₀ g basisE x = 1 := by
  ext i j
  simp only [gramE, Matrix.of_apply, Matrix.one_apply]
  exact hON i j




omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem gramInv_near_id
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    {x : M} (hx : x ∈ e₀.baseSet)
    (hONx : gramE (I := I) e₀ g basisE x = 1)
    {ε : Real} (hε : 0 < ε) :
    ∃ u' : Set M, IsOpen u' ∧ x ∈ u' ∧ u' ⊆ e₀.baseSet ∧
      ∀ z ∈ u', ∀ i j : Idx,
        |(gramE (I := I) e₀ g basisE z)⁻¹ i j - (if i = j then 1 else 0)| ≤ ε ∧
        |gramE (I := I) e₀ g basisE z i j - (if i = j then 1 else 0)| ≤ ε := by
  classical

  have hentry : ∀ i j : Idx, ContinuousWithinAt
      (fun z => gramE (I := I) e₀ g basisE z i j) e₀.baseSet x := by
    intro i j
    have h := (gCompField_mdiffOn (I := I) e₀ g basisE
      (Fin.snoc (fun _ : Fin 1 => i) j)).continuousOn
    have heq : ∀ z : M,
        gramE (I := I) e₀ g basisE z i j =
          frameComp0S (I := I) (metricTensorField (I := I) g)
            (fun a y' => e₀.localFrame basisE a y') z
            (Fin.snoc (fun _ : Fin 1 => i) j) := by
      intro z
      have h0 : (Fin.snoc (fun _ : Fin 1 => i) j : Fin 2 → Idx) 0 = i := by simp [Fin.snoc]
      have h1 : (Fin.snoc (fun _ : Fin 1 => i) j : Fin 2 → Idx) 1 = j := by simp [Fin.snoc]
      rw [frameComp0S_apply, metricTensorField_apply, h0, h1]
      rfl
    exact ((h.congr fun z _ => (heq z)).continuousWithinAt hx)

  have hmat : ContinuousWithinAt
      (fun z => gramE (I := I) e₀ g basisE z) e₀.baseSet x := by
    have hpi : ContinuousWithinAt
        (fun z => (fun i j => gramE (I := I) e₀ g basisE z i j : Idx → Idx → Real))
        e₀.baseSet x := by
      rw [continuousWithinAt_pi]
      intro i
      rw [continuousWithinAt_pi]
      intro j
      exact hentry i j
    exact hpi

  have hdet1 : (gramE (I := I) e₀ g basisE x).det = 1 := by
    rw [hONx, Matrix.det_one]
  have hinvc : ContinuousAt Inv.inv (gramE (I := I) e₀ g basisE x) := by
    apply continuousAt_matrix_inv
    rw [hdet1, Ring.inverse_eq_inv']
    exact continuousAt_inv₀ one_ne_zero
  have hinv_cwa : ContinuousWithinAt
      (fun z => (gramE (I := I) e₀ g basisE z)⁻¹) e₀.baseSet x :=
    hinvc.comp_continuousWithinAt hmat
  have hone : (gramE (I := I) e₀ g basisE x)⁻¹ = 1 := by
    rw [hONx]
    exact Matrix.inv_eq_left_inv (by rw [one_mul])

  have hev1 : ∀ i j : Idx, ∀ᶠ z in nhdsWithin x e₀.baseSet,
      |(gramE (I := I) e₀ g basisE z)⁻¹ i j - (if i = j then 1 else 0)| ≤ ε := by
    intro i j
    have hcwa : ContinuousWithinAt
        (fun z => (gramE (I := I) e₀ g basisE z)⁻¹ i j) e₀.baseSet x := by
      have h1 := (continuousWithinAt_pi.mp hinv_cwa) i
      exact (continuousWithinAt_pi.mp h1) j
    have hval : (gramE (I := I) e₀ g basisE x)⁻¹ i j = (if i = j then (1 : Real) else 0) := by
      rw [hone, Matrix.one_apply]
    have hb : ∀ᶠ t in nhds ((gramE (I := I) e₀ g basisE x)⁻¹ i j),
        |t - (if i = j then (1 : Real) else 0)| ≤ ε := by
      rw [hval]
      have hball := Metric.closedBall_mem_nhds (x := (if i = j then (1 : Real) else 0)) hε
      refine Filter.eventually_of_mem hball fun t ht => ?_
      simpa [Metric.mem_closedBall, Real.dist_eq] using ht
    exact hcwa.eventually hb

  have hevG1 : ∀ i j : Idx, ∀ᶠ z in nhdsWithin x e₀.baseSet,
      |gramE (I := I) e₀ g basisE z i j - (if i = j then 1 else 0)| ≤ ε := by
    intro i j
    have hval : gramE (I := I) e₀ g basisE x i j = (if i = j then (1 : Real) else 0) := by
      rw [hONx, Matrix.one_apply]
    have hb : ∀ᶠ t in nhds (gramE (I := I) e₀ g basisE x i j),
        |t - (if i = j then (1 : Real) else 0)| ≤ ε := by
      rw [hval]
      have hball := Metric.closedBall_mem_nhds (x := (if i = j then (1 : Real) else 0)) hε
      refine Filter.eventually_of_mem hball fun t ht => ?_
      simpa [Metric.mem_closedBall, Real.dist_eq] using ht
    exact (hentry i j).eventually hb

  have hev : ∀ᶠ z in nhdsWithin x e₀.baseSet, ∀ i j : Idx,
      |(gramE (I := I) e₀ g basisE z)⁻¹ i j - (if i = j then 1 else 0)| ≤ ε ∧
      |gramE (I := I) e₀ g basisE z i j - (if i = j then 1 else 0)| ≤ ε := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact (hev1 i j).and (hevG1 i j)
  obtain ⟨t, htopen, hxt, hsub⟩ := mem_nhdsWithin.mp hev
  exact ⟨t ∩ e₀.baseSet, htopen.inter e₀.open_baseSet, ⟨hxt, hx⟩,
    Set.inter_subset_right, fun z hz => hsub hz⟩





private theorem exists_orthonormalBasis_of_posDef
    {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    (B : LinearMap.BilinForm Real V) (hsymm : LinearMap.IsSymm B)
    (hpos : ∀ v : V, v ≠ 0 → 0 < B v v) :
    ∃ b : Module.Basis (Fin (Module.finrank Real V)) Real V,
      ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
  classical
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B) hsymm
  have hdpos : ∀ i, 0 < B (v i) (v i) := fun i => hpos (v i) (v.ne_zero i)
  set w : Fin (Module.finrank Real V) → Real :=
    fun i => (Real.sqrt (B (v i) (v i)))⁻¹ with hw
  have hwunit : ∀ i, IsUnit (w i) := by
    intro i
    refine isUnit_iff_ne_zero.mpr ?_
    simp only [hw]
    exact inv_ne_zero (Real.sqrt_pos.mpr (hdpos i)).ne'
  refine ⟨v.isUnitSMul hwunit, ?_⟩
  intro i j
  have hreduce :
      B ((v.isUnitSMul hwunit) i) ((v.isUnitSMul hwunit) j) =
        (w i * w j) * B (v i) (v j) := by
    simp only [Module.Basis.isUnitSMul_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    ring
  rw [hreduce]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hd : 0 < B (v i) (v i) := hdpos i
    have hroot :
        Real.sqrt (B (v i) (v i)) * Real.sqrt (B (v i) (v i)) = B (v i) (v i) :=
      Real.mul_self_sqrt hd.le
    simp only [hw]
    rw [← mul_inv, hroot, inv_mul_cancel₀ hd.ne']
  · rw [if_neg hij]
    have horth : B (v i) (v j) = 0 := (LinearMap.isOrthoᵢ_def.mp hv) i j hij
    rw [horth, mul_zero]






omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem exists_trivONBasis
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ basisE : Module.Basis (Fin (Module.finrank Real E)) Real E,
      ∀ i j : Fin (Module.finrank Real E),
        g.inner x
          ((trivializationAt E (TangentSpace I : M → Type _) x).localFrame basisE i x)
          ((trivializationAt E (TangentSpace I : M → Type _) x).localFrame basisE j x) =
        if i = j then 1 else 0 := by
  classical
  set e₀ := trivializationAt E (TangentSpace I : M → Type _) x with he₀
  have hxu0 : x ∈ e₀.baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x
  let Q : LinearMap.BilinForm Real E :=
    LinearMap.mk₂ Real
      (fun v w => g.inner x (e₀.symmL Real x v) (e₀.symmL Real x w))
      (fun _ _ _ => by simp [map_add, ContinuousLinearMap.add_apply])
      (fun _ _ _ => by simp [map_smul, ContinuousLinearMap.smul_apply])
      (fun _ _ _ => by simp [map_add])
      (fun _ _ _ => by simp [map_smul])
  have hsymm : LinearMap.IsSymm Q :=
    ⟨fun v w => by
      simp only [Q, LinearMap.mk₂_apply, RingHom.id_apply]
      exact g.symm x (e₀.symmL Real x v) (e₀.symmL Real x w)⟩
  have hpos : ∀ v : E, v ≠ 0 → 0 < Q v v := by
    intro v hv
    have hSv : e₀.symmL Real x v ≠ 0 := by
      intro h0
      apply hv
      have hself := e₀.continuousLinearMapAt_symmL (R := Real) hxu0 v
      rw [h0, map_zero] at hself
      exact hself.symm
    simp only [Q, LinearMap.mk₂_apply]
    exact g.pos x (e₀.symmL Real x v) hSv
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_of_posDef Q hsymm hpos
  have hsymmL : ∀ k, e₀.symmL Real x (b k) = e₀.localFrame b k x := fun k => by
    rw [e₀.localFrame_apply_of_mem_baseSet (b := b) hxu0]
    simp [Bundle.Trivialization.basisAt]
  refine ⟨b, fun i j => ?_⟩
  rw [← hsymmL i, ← hsymmL j]
  simpa [Q, LinearMap.mk₂_apply] using hb i j









omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem exists_goodFrame_compBound
    (gRef : SmoothRiemannianMetric I M) (x : M) :
    ∃ basisE : Module.Basis (Fin (Module.finrank Real E)) Real E,
      ∃ u' : Set M, ∃ ε : Real, IsOpen u' ∧ x ∈ u' ∧
        u' ⊆ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet ∧
        0 ≤ ε ∧
        (Fintype.card (Fin (Module.finrank Real E)) : Real) * ε ≤ 1 / 2 ∧
        (∀ z ∈ u', ∀ i j : Fin (Module.finrank Real E),
          |gramE (I := I) (trivializationAt E (TangentSpace I : M → Type _) x)
              gRef basisE z i j - (if i = j then 1 else 0)| ≤ ε) ∧
        (∀ i j : Fin (Module.finrank Real E),
          gRef.inner x
            ((trivializationAt E (TangentSpace I : M → Type _) x).localFrame basisE i x)
            ((trivializationAt E (TangentSpace I : M → Type _) x).localFrame basisE j x) =
          if i = j then 1 else 0) ∧
        (∀ z, ∀ hz : z ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet,
          z ∈ u' → ∀ (s : ℕ) (A : Tensor0SSpace s I z),
            (∑ I0 : Fin s → Fin (Module.finrank Real E),
              Tensor0SBundle.component0S (I := I)
                (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).toBasisAt hz) A I0 ^ 2) ≤
              2 ^ s * Tensor0SBundle.normSq0S (I := I) gRef z s A) ∧
        ∀ z, ∀ hz : z ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet,
          z ∈ u' → ∀ (s : ℕ) (A : Tensor0SSpace s I z),
            Tensor0SBundle.normSq0S (I := I) gRef z s A ≤
              ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ s *
              (∑ I0 : Fin s → Fin (Module.finrank Real E),
                Tensor0SBundle.component0S (I := I)
                  (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                      I 1 basisE).toBasisAt hz) A I0 ^ 2) := by
  classical
  obtain ⟨basisE, hONraw⟩ := exists_trivONBasis (I := I) gRef x
  set e₀ := trivializationAt E (TangentSpace I : M → Type _) x with he₀
  have hxbase : x ∈ e₀.baseSet := mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x
  have hONx : gramE (I := I) e₀ gRef basisE x = 1 :=
    gramE_eq_one (I := I) e₀ gRef basisE hONraw

  set n : ℕ := Fintype.card (Fin (Module.finrank Real E)) with hn
  set ε : Real := 1 / (2 * ((n : Real) + 1)) with hε_def
  have hε : 0 < ε := by
    rw [hε_def]
    positivity
  have hsmall : (n : Real) * ε ≤ 1 / 2 := by
    rw [hε_def, mul_one_div, div_le_iff₀ (by positivity : (0 : Real) < 2 * ((n : Real) + 1))]
    have : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
    linarith
  obtain ⟨u', hopen, hxu', hsub, hnear⟩ :=
    gramInv_near_id (I := I) e₀ gRef basisE hxbase hONx hε
  refine ⟨basisE, u', ε, hopen, hxu', hsub, hε.le, hsmall,
    (fun z hz i j => (hnear z hz i j).2), hONraw, ?_, ?_⟩
  · intro z hz hzu' s A

    have hQlb := quad_lb_of_near_id
      (fun i j => (gramE (I := I) e₀ gRef basisE z)⁻¹ i j) ε hε.le
      (fun i j => (hnear z hzu' i j).1) hsmall

    have hkey := Tensor0SBundle.sum_comp_sq_le_pow_normSq0S (I := I) gRef z s
      (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE)).toBasisAt hz)
      (fun i j => (gramE (I := I) e₀ gRef basisE z)⁻¹ i j) 2 two_pos
      (gramInv_inverse (I := I) e₀ gRef basisE hz)
      (fun i j => gramInv_symm (I := I) e₀ gRef basisE z i j)
      hQlb A

    calc (∑ I0 : Fin s → Fin (Module.finrank Real E),
          Tensor0SBundle.component0S (I := I)
            (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE)).toBasisAt hz) A I0 ^ 2)
        = ∑ I0 : Fin s → Fin (Module.finrank Real E),
            Tensor0SBundle.tensor0SComponent (I := I) A
              (fun i => ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE)).toBasisAt hz i)
              I0 ^ 2 := by
          refine Finset.sum_congr rfl fun I0 _ => ?_
          rw [Tensor0SBundle.component0S_apply, Tensor0SBundle.tensor0SComponent_apply]
      _ ≤ 2 ^ s * Tensor0SBundle.normSq0S (I := I) gRef z s A := hkey
  · intro z hz hzu' s A
    have hε12 : ε ≤ 1 / 2 := by
      rw [hε_def]
      have h2 : (2 : Real) ≤ 2 * ((n : Real) + 1) := by
        have hn0 : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
        linarith
      exact one_div_le_one_div_of_le two_pos h2
    have hub := Tensor0SBundle.normSq0S_le_pow_sum_comp_sq (I := I) gRef z s
      (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE)).toBasisAt hz)
      (fun i j => (gramE (I := I) e₀ gRef basisE z)⁻¹ i j) ε hε.le
      (gramInv_inverse (I := I) e₀ gRef basisE hz)
      (fun i j => (hnear z hzu' i j).1) A
    have hbridge : (∑ I0 : Fin s → Fin (Module.finrank Real E),
          Tensor0SBundle.tensor0SComponent (I := I) A
            (fun i => ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE)).toBasisAt hz i)
            I0 ^ 2)
        = ∑ I0 : Fin s → Fin (Module.finrank Real E),
            Tensor0SBundle.component0S (I := I)
              (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE)).toBasisAt hz) A I0 ^ 2 := by
      refine Finset.sum_congr rfl fun I0 _ => ?_
      rw [Tensor0SBundle.component0S_apply, Tensor0SBundle.tensor0SComponent_apply]
    have hcomp0 : (0 : Real) ≤ ∑ I0 : Fin s → Fin (Module.finrank Real E),
        Tensor0SBundle.component0S (I := I)
          (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE)).toBasisAt hz) A I0 ^ 2 :=
      Finset.sum_nonneg fun I0 _ => sq_nonneg _
    have hmono : ((1 + ε) * (Fintype.card (Fin (Module.finrank Real E)) : Real)) ^ s
        ≤ ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ s := by
      have hcard0 : (0 : Real) ≤ (Fintype.card (Fin (Module.finrank Real E)) : Real) :=
        Nat.cast_nonneg _
      have hbase : (1 + ε) * (Fintype.card (Fin (Module.finrank Real E)) : Real)
          ≤ (3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1) := by
        nlinarith [hε.le, hε12]
      exact pow_le_pow_left₀ (by positivity) hbase s
    calc Tensor0SBundle.normSq0S (I := I) gRef z s A
        ≤ ((1 + ε) * (Fintype.card (Fin (Module.finrank Real E)) : Real)) ^ s *
            ∑ I0 : Fin s → Fin (Module.finrank Real E),
              Tensor0SBundle.tensor0SComponent (I := I) A
                (fun i => ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE)).toBasisAt hz i)
                I0 ^ 2 := hub
      _ = ((1 + ε) * (Fintype.card (Fin (Module.finrank Real E)) : Real)) ^ s *
            ∑ I0 : Fin s → Fin (Module.finrank Real E),
              Tensor0SBundle.component0S (I := I)
                (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE)).toBasisAt hz) A I0 ^ 2 := by
          rw [hbridge]
      _ ≤ ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ s *
            ∑ I0 : Fin s → Fin (Module.finrank Real E),
              Tensor0SBundle.component0S (I := I)
                (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE)).toBasisAt hz) A I0 ^ 2 :=
          mul_le_mul_of_nonneg_right hmono hcomp0







omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [I.Boundaryless] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem compL2_tower_le
    (gM gRef : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u)
    {y : M} (hy : y ∈ u)
    (hcomp : ∀ (s : ℕ) (A : Tensor0SSpace s I y),
      (∑ I0 : Fin s → Idx,
        Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hy) A I0 ^ 2) ≤
        2 ^ s * Tensor0SBundle.normSq0S (I := I) gRef y s A)
    (j : ℕ) :
    compL2 (iterCovComp (I := I) frame
        (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gM)
          frame hframe y')
        (frameComp0S (I := I) T frame) j y) ≤
      2 ^ (r + j) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (r + j)
          (iterCov (I := I) gM r T j y)) := by

  have hsq : compL2Sq (iterCovComp (I := I) frame
      (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gM)
        frame hframe y')
      (frameComp0S (I := I) T frame) j y) =
      ∑ I0 : Fin (r + j) → Idx,
        Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hy)
          (iterCov (I := I) gM r T j y) I0 ^ 2 := by
    simp only [compL2Sq]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [iterCovComp_eq_iterCov (I := I) gM T frame hframe hu j hy n]
    congr 1
    rw [Tensor0SBundle.component0S_apply]
    congr 1
    funext q
    rw [IsLocalFrameOn.toBasisAt_coe]
    rfl

  have hbound := hcomp (r + j) (iterCov (I := I) gM r T j y)
  have hs : Real.sqrt ((2 : Real) ^ (r + j)) ≤ (2 : Real) ^ (r + j) := by
    have h2 : ((2 : Real) ^ (r + j)) ≤ ((2 : Real) ^ (r + j)) ^ 2 := by
      have h1 : (1 : Real) ≤ (2 : Real) ^ (r + j) := one_le_pow₀ one_le_two
      nlinarith
    calc Real.sqrt ((2 : Real) ^ (r + j))
        ≤ Real.sqrt (((2 : Real) ^ (r + j)) ^ 2) := Real.sqrt_le_sqrt h2
      _ = (2 : Real) ^ (r + j) := Real.sqrt_sq (by positivity)
  calc compL2 (iterCovComp (I := I) frame
        (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gM)
          frame hframe y')
        (frameComp0S (I := I) T frame) j y)
      = Real.sqrt (compL2Sq (iterCovComp (I := I) frame
          (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gM)
            frame hframe y')
          (frameComp0S (I := I) T frame) j y)) := rfl
    _ = Real.sqrt (∑ I0 : Fin (r + j) → Idx,
          Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hy)
            (iterCov (I := I) gM r T j y) I0 ^ 2) := by rw [hsq]
    _ ≤ Real.sqrt (2 ^ (r + j) *
          Tensor0SBundle.normSq0S (I := I) gRef y (r + j)
            (iterCov (I := I) gM r T j y)) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt ((2 : Real) ^ (r + j)) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (r + j)
            (iterCov (I := I) gM r T j y)) := Real.sqrt_mul (by positivity) _
    _ ≤ 2 ^ (r + j) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (r + j)
            (iterCov (I := I) gM r T j y)) :=
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)






omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [I.Boundaryless] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem metricComp_le
    (g gRef : SmoothRiemannianMetric I M)
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u)
    {y : M} (hy : y ∈ u)
    (hcomp : ∀ (s : ℕ) (A : Tensor0SSpace s I y),
      (∑ I0 : Fin s → Idx,
        Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hy) A I0 ^ 2) ≤
        2 ^ s * Tensor0SBundle.normSq0S (I := I) gRef y s A)
    (j : ℕ) {eps : Real}
    (hbound : Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (2 + j)
      (iterCov (I := I) gRef 2 (Tensor0SBundle.metricTensorField (I := I) g) j y)) ≤ eps) :
    compL2 (iterCovComp (I := I) frame
        (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
          frame hframe y')
        (frameComp0S (I := I) (Tensor0SBundle.metricTensorField (I := I) g) frame) j y) ≤
      2 ^ (2 + j) * eps := by
  have h := compL2_tower_le (I := I) (gM := gRef) (gRef := gRef) (r := 2)
    (T := Tensor0SBundle.metricTensorField (I := I) g) frame hframe hu hy hcomp j
  exact le_trans h
    (mul_le_mul_of_nonneg_left hbound (by positivity : (0 : Real) ≤ 2 ^ (2 + j)))




omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [I.Boundaryless] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem metricComp_mul
    (g gRef : SmoothRiemannianMetric I M)
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u)
    {y : M} (hy : y ∈ u)
    (hcomp : ∀ (s : ℕ) (A : Tensor0SSpace s I y),
      (∑ I0 : Fin s → Idx,
        Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hy) A I0 ^ 2) ≤
        2 ^ s * Tensor0SBundle.normSq0S (I := I) g y s A)
    (C : Real) (hC1 : 1 ≤ C) (hC2 : C ≤ 2)
    (hequiv : ∀ v : TangentSpace I y,
      C⁻¹ * gRef.inner y v v ≤ g.inner y v v ∧
        g.inner y v v ≤ C * gRef.inner y v v)
    (p j : ℕ) (hj : j ≤ p) {eps : Real} (heps0 : 0 ≤ eps)
    (hbound : Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (2 + j)
      (iterCov (I := I) gRef 2 (Tensor0SBundle.metricTensorField (I := I) g) j y)) ≤ eps) :
    compL2 (iterCovComp (I := I) frame
        (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
          frame hframe y')
        (frameComp0S (I := I) (Tensor0SBundle.metricTensorField (I := I) g) frame) j y) ≤
      4 ^ (2 + p) * eps := by
  let A := iterCov (I := I) gRef 2 (Tensor0SBundle.metricTensorField (I := I) g) j y
  have htow := compL2_tower_le (I := I) (gM := gRef) (gRef := g) (r := 2)
    (T := Tensor0SBundle.metricTensorField (I := I) g) frame hframe hu hy hcomp j
  have hconv := Tensor0SBundle.sqrt_normSq0S_le_of_metric_equiv
    (I := I) gRef g y (2 + j) hC1 hequiv A
  have hC0 : (0 : Real) ≤ C := le_trans zero_le_one hC1
  have hCp1 : (1 : Real) ≤ C ^ (2 + j) := one_le_pow₀ hC1
  have hsqrt : Real.sqrt (C ^ (2 + j)) ≤ C ^ (2 + j) := by
    have hsq : C ^ (2 + j) ≤ (C ^ (2 + j)) ^ 2 := by nlinarith
    calc
      Real.sqrt (C ^ (2 + j)) ≤ Real.sqrt ((C ^ (2 + j)) ^ 2) :=
        Real.sqrt_le_sqrt hsq
      _ = C ^ (2 + j) := Real.sqrt_sq (by positivity)
  have hCpow : C ^ (2 + j) ≤ (2 : Real) ^ (2 + j) :=
    pow_le_pow_left₀ hC0 hC2 (2 + j)
  have hsqrt2 : Real.sqrt (C ^ (2 + j)) ≤ (2 : Real) ^ (2 + j) :=
    le_trans hsqrt hCpow
  have hcoef : (2 : Real) ^ (2 + j) * Real.sqrt (C ^ (2 + j)) ≤
      (4 : Real) ^ (2 + j) := by
    calc
      (2 : Real) ^ (2 + j) * Real.sqrt (C ^ (2 + j))
          ≤ (2 : Real) ^ (2 + j) * (2 : Real) ^ (2 + j) :=
        mul_le_mul_of_nonneg_left hsqrt2 (by positivity)
      _ = (4 : Real) ^ (2 + j) := by rw [← mul_pow]; norm_num
  have hpow : (4 : Real) ^ (2 + j) ≤ 4 ^ (2 + p) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    compL2 (iterCovComp (I := I) frame
        (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
          frame hframe y')
        (frameComp0S (I := I) (Tensor0SBundle.metricTensorField (I := I) g) frame) j y)
        ≤ 2 ^ (2 + j) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y (2 + j) A) :=
      htow
    _ ≤ 2 ^ (2 + j) *
        (Real.sqrt (C ^ (2 + j)) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (2 + j) A)) :=
      mul_le_mul_of_nonneg_left hconv (by positivity)
    _ ≤ 2 ^ (2 + j) * (Real.sqrt (C ^ (2 + j)) * eps) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _)) (by positivity)
    _ = (2 ^ (2 + j) * Real.sqrt (C ^ (2 + j))) * eps := by ring
    _ ≤ 4 ^ (2 + j) * eps := mul_le_mul_of_nonneg_right hcoef heps0
    _ ≤ 4 ^ (2 + p) * eps := mul_le_mul_of_nonneg_right hpow heps0





omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [I.Boundaryless] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem sqrt_tower_le_compL2
    (gRef : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u)
    {y : M} (hy : y ∈ u)
    (Cu : Real) (hCu : 1 ≤ Cu)
    (hub : ∀ (s : ℕ) (A : Tensor0SSpace s I y),
      Tensor0SBundle.normSq0S (I := I) gRef y s A ≤
        Cu ^ s * (∑ I0 : Fin s → Idx,
          Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hy) A I0 ^ 2))
    (j : ℕ) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (r + j)
        (iterCov (I := I) gRef r T j y)) ≤
      Cu ^ (r + j) * compL2 (iterCovComp (I := I) frame
        (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
          frame hframe y')
        (frameComp0S (I := I) T frame) j y) := by
  have hsq : compL2Sq (iterCovComp (I := I) frame
      (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
        frame hframe y')
      (frameComp0S (I := I) T frame) j y) =
      ∑ I0 : Fin (r + j) → Idx,
        Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hy)
          (iterCov (I := I) gRef r T j y) I0 ^ 2 := by
    simp only [compL2Sq]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [iterCovComp_eq_iterCov (I := I) gRef T frame hframe hu j hy n]
    congr 1
    rw [Tensor0SBundle.component0S_apply]
    congr 1
    funext q
    rw [IsLocalFrameOn.toBasisAt_coe]
    rfl
  have hbound := hub (r + j) (iterCov (I := I) gRef r T j y)
  have hCp : (1 : Real) ≤ Cu ^ (r + j) := one_le_pow₀ hCu
  have hs : Real.sqrt (Cu ^ (r + j)) ≤ Cu ^ (r + j) := by
    have h2 : (Cu ^ (r + j)) ≤ (Cu ^ (r + j)) ^ 2 := by nlinarith
    calc Real.sqrt (Cu ^ (r + j))
        ≤ Real.sqrt ((Cu ^ (r + j)) ^ 2) := Real.sqrt_le_sqrt h2
      _ = Cu ^ (r + j) := Real.sqrt_sq (by linarith)
  calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (r + j)
        (iterCov (I := I) gRef r T j y))
      ≤ Real.sqrt (Cu ^ (r + j) *
          ∑ I0 : Fin (r + j) → Idx,
            Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hy)
              (iterCov (I := I) gRef r T j y) I0 ^ 2) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt (Cu ^ (r + j)) *
          Real.sqrt (∑ I0 : Fin (r + j) → Idx,
            Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hy)
              (iterCov (I := I) gRef r T j y) I0 ^ 2) :=
        Real.sqrt_mul (by positivity) _
    _ ≤ Cu ^ (r + j) *
          Real.sqrt (∑ I0 : Fin (r + j) → Idx,
            Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hy)
              (iterCov (I := I) gRef r T j y) I0 ^ 2) :=
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
    _ = Cu ^ (r + j) * compL2 (iterCovComp (I := I) frame
          (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
            frame hframe y')
          (frameComp0S (I := I) T frame) j y) := by
        rw [show compL2 (iterCovComp (I := I) frame
            (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
              frame hframe y')
            (frameComp0S (I := I) T frame) j y) =
          Real.sqrt (compL2Sq (iterCovComp (I := I) frame
            (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
              frame hframe y')
            (frameComp0S (I := I) T frame) j y)) from rfl, hsq]

set_option backward.isDefEq.respectTransparency false in




omit [I.Boundaryless] [IsManifold I 2 M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem ricCompField_mdiffOn
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    (k : Fin 2 → Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => frameComp0S (I := I)
        (DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
          (I := I) (M := M) (leviCivitaConnectionOfMetric (I := I) g)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) (M := M) g))
        (fun a y' => e₀.localFrame basisE a y') y k) e₀.baseSet := by
  intro y hy
  have hT : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun x : M => Tensor0SSpace 2 I x) b
        ((DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
          (I := I) (M := M) (leviCivitaConnectionOfMetric (I := I) g)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) (M := M) g))
          b)) y :=
    (DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
      (I := I) (M := M) (leviCivitaConnectionOfMetric (I := I) g)
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)).contMDiff.contMDiffAt
  have hv : ∀ i : Fin 2,
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b
          (e₀.localFrame basisE (k i) b)) y :=
    fun i => (frame_e_mdiffOn e₀ basisE (k i)).contMDiffAt (e₀.open_baseSet.mem_nhds hy)
  have h := TensorMultilinear.contMDiffAt_section_apply_gen
    (T := fun b : M =>
      (DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
        (I := I) (M := M) (leviCivitaConnectionOfMetric (I := I) g)
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) (M := M) g)) b) hT
    (v := fun (i : Fin 2) (b : M) => e₀.localFrame basisE (k i) b) hv
  exact h.contMDiffWithinAt




omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] [Fintype Idx] [DecidableEq Idx] in
theorem chrInFrame_mono
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (frame : Idx → (x : M) → TangentSpace I x) {u u' : Set M}
    (hframe : IsLocalFrameOn I E 1 frame u) (hsub : u' ⊆ u)
    {z : M} (hz : z ∈ u') (d i j : Idx) :
    christoffelSymbolInFrame cov frame (hframe.mono hsub) z d i j =
      christoffelSymbolInFrame cov frame hframe z d i j := by
  unfold christoffelSymbolInFrame
  simp only [IsLocalFrameOn.coeff, dif_pos hz, dif_pos (hsub hz)]
  rfl





omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem movingGinv_le
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g gRef : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    {z : M}
    (Beq : Real) (hBeq : 0 < Beq)
    (hlow : ∀ v : TangentSpace I z, Beq⁻¹ * gRef.inner z v v ≤ g.inner z v v)
    (ε : Real) (hε0 : 0 ≤ ε)
    (hsmall : (Fintype.card Idx : Real) * ε ≤ 1 / 2)
    (hGnear : ∀ i j : Idx,
      |gramE (I := I) e₀ gRef basisE z i j - (if i = j then 1 else 0)| ≤ ε) :
    compL2 (ginvCompField (I := I) e₀ g basisE z) ≤
      Real.sqrt (Fintype.card Idx) * (2 * Beq) := by
  classical
  have hdot : ∀ (G : Matrix Idx Idx Real) (w : Idx → Real),
      w ⬝ᵥ G.mulVec w = ∑ i : Idx, ∑ j : Idx, G i j * (w i * w j) := by
    intro G w
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  have hquadRef := DifferentialGeometry.HCGCompactness.quad_lb_of_near_id
    (fun i j => gramE (I := I) e₀ gRef basisE z i j) ε hε0 hGnear hsmall
  have hquadG : ∀ v : Idx → Real,
      (1 / (2 * Beq)) * (v ⬝ᵥ v) ≤
        v ⬝ᵥ (gramE (I := I) e₀ g basisE z).mulVec v := by
    intro v
    have hsq : v ⬝ᵥ v = ∑ i : Idx, v i ^ 2 := by
      simp only [dotProduct]
      exact Finset.sum_congr rfl fun i _ => (pow_two (v i)).symm
    have hRef : (1 / 2) * ∑ i : Idx, v i ^ 2 ≤
        v ⬝ᵥ (gramE (I := I) e₀ gRef basisE z).mulVec v := by
      rw [hdot]
      exact hquadRef v
    have hg : v ⬝ᵥ (gramE (I := I) e₀ g basisE z).mulVec v =
        g.inner z (∑ i, v i • e₀.localFrame basisE i z)
          (∑ j, v j • e₀.localFrame basisE j z) :=
      gramE_dotVec (I := I) e₀ g basisE z v
    have hgRef : v ⬝ᵥ (gramE (I := I) e₀ gRef basisE z).mulVec v =
        gRef.inner z (∑ i, v i • e₀.localFrame basisE i z)
          (∑ j, v j • e₀.localFrame basisE j z) :=
      gramE_dotVec (I := I) e₀ gRef basisE z v
    have hlow' := hlow (∑ i, v i • e₀.localFrame basisE i z)
    have hBeqinv : (0 : Real) < Beq⁻¹ := inv_pos.mpr hBeq
    rw [hsq, hg]
    calc (1 / (2 * Beq)) * ∑ i : Idx, v i ^ 2
        = Beq⁻¹ * ((1 / 2) * ∑ i : Idx, v i ^ 2) := by
          field_simp
      _ ≤ Beq⁻¹ * (v ⬝ᵥ (gramE (I := I) e₀ gRef basisE z).mulVec v) :=
          mul_le_mul_of_nonneg_left hRef hBeqinv.le
      _ = Beq⁻¹ * gRef.inner z (∑ i, v i • e₀.localFrame basisE i z)
            (∑ j, v j • e₀.localFrame basisE j z) := by rw [hgRef]
      _ ≤ g.inner z (∑ i, v i • e₀.localFrame basisE i z)
            (∑ j, v j • e₀.localFrame basisE j z) := hlow'
  have h := ginv_compL2_le (I := I) e₀ g basisE (1 / (2 * Beq)) (by positivity) hquadG
  calc compL2 (ginvCompField (I := I) e₀ g basisE z)
      ≤ Real.sqrt (Fintype.card Idx) / (1 / (2 * Beq)) := h
    _ = Real.sqrt (Fintype.card Idx) * (2 * Beq) := by
        rw [one_div, div_eq_mul_inv, inv_inv]

end DifferentialGeometry.PDE.RicciFlow
