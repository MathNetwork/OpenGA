import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in

theorem orthonormal_tangent_expansion
    (g : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i j, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (u : TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E), g.inner x (e i) u • e i) = u := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  haveI : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, NeZero.pos _⟩⟩
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  have hON : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinner_eq (e i) (e j)]
    exact horth i j
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfOrthonormalOfCardEqFinrank hON hcard
  have hb_coe : ⇑b = e := coe_basisOfOrthonormalOfCardEqFinrank hON hcard
  have hb_on : Orthonormal ℝ ⇑b := by rw [hb_coe]; exact hON
  let ob : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    b.toOrthonormalBasis hb_on
  have hob : ∀ i, ob i = e i := by
    intro i
    have h1 : ob i = b i := by
      have := Module.Basis.coe_toOrthonormalBasis b hb_on
      exact congrFun this i
    rw [h1, show b i = e i from congrFun hb_coe i]
  have hrepr := ob.sum_repr' u
  calc
    (∑ i : Fin (Module.finrank ℝ E), g.inner x (e i) u • e i)
        = ∑ i : Fin (Module.finrank ℝ E), (inner ℝ (ob i) u : ℝ) • ob i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hob i, hinner_eq (e i) u]
    _ = u := hrepr

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [BoundarylessManifold I M] in

theorem parseval_family_inner_mul_sum
    (g : SmoothRiemannianMetric I M) (x : M)
    {N : ℕ} (W : Fin N → TangentSpace I x)
    (hW : ∀ u : TangentSpace I x, (∑ a : Fin N, g.inner x (W a) u • W a) = u)
    (u v : TangentSpace I x) :
    (∑ a : Fin N, g.inner x (W a) u * g.inner x (W a) v) = g.inner x u v := by
  classical
  have h := congrArg (fun w : TangentSpace I x => g.inner x w v) (hW u)
  simp only at h
  rw [show g.inner x (∑ a : Fin N, g.inner x (W a) u • W a) v =
      ∑ a : Fin N, g.inner x (W a) u * g.inner x (W a) v from ?_] at h
  · exact h
  · rw [map_sum (g.inner x) (fun a : Fin N => g.inner x (W a) u • W a) Finset.univ,
      ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_smul (g.inner x) (g.inner x (W a) u) (W a), ContinuousLinearMap.smul_apply,
      smul_eq_mul]

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in

theorem parseval_family_sum_bilin_eq
    (g : SmoothRiemannianMetric I M) (x : M)
    {N : ℕ} (W : Fin N → TangentSpace I x)
    (hW : ∀ u : TangentSpace I x, (∑ a : Fin N, g.inner x (W a) u • W a) = u)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i j, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    {Z : Type*} [AddCommMonoid Z] [Module ℝ Z]
    (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] Z) :
    (∑ a : Fin N, B (W a) (W a)) =
      ∑ i : Fin (Module.finrank ℝ E), B (e i) (e i) := by
  classical
  have hexp : ∀ u : TangentSpace I x,
      (∑ i : Fin (Module.finrank ℝ E), g.inner x (e i) u • e i) = u :=
    orthonormal_tangent_expansion (I := I) (M := M) g x e horth
  have hdual : ∀ i j : Fin (Module.finrank ℝ E),
      (∑ a : Fin N, g.inner x (e i) (W a) * g.inner x (e j) (W a)) =
        if i = j then (1 : ℝ) else 0 := by
    intro i j
    have h1 : (∑ a : Fin N, g.inner x (W a) (e j) • W a) = e j := hW (e j)
    have h2 : g.inner x (e i) (e j) =
        ∑ a : Fin N, g.inner x (W a) (e j) * g.inner x (e i) (W a) := by
      conv_lhs => rw [← h1]
      rw [map_sum (g.inner x (e i)) (fun a : Fin N => g.inner x (W a) (e j) • W a)
        Finset.univ]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_smul (g.inner x (e i)) (g.inner x (W a) (e j)) (W a), smul_eq_mul]
    rw [← horth i j, h2]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [g.symm x (W a) (e j)]
    ring
  calc
    (∑ a : Fin N, B (W a) (W a))
        = ∑ a : Fin N, ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (g.inner x (e i) (W a) * g.inner x (e j) (W a)) • B (e i) (e j) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          conv_lhs => rw [← hexp (W a)]
          rw [map_sum B (fun i : Fin (Module.finrank ℝ E) => g.inner x (e i) (W a) • e i)
            Finset.univ, LinearMap.coe_sum, Finset.sum_apply]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [map_smul B (g.inner x (e i) (W a)) (e i), LinearMap.smul_apply]
          rw [map_sum (B (e i)) (fun j : Fin (Module.finrank ℝ E) =>
            g.inner x (e j) (W a) • e j) Finset.univ, Finset.smul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [map_smul (B (e i)) (g.inner x (e j) (W a)) (e j), smul_smul]
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (∑ a : Fin N, g.inner x (e i) (W a) * g.inner x (e j) (W a)) • B (e i) (e j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.sum_smul]
    _ = ∑ i : Fin (Module.finrank ℝ E), B (e i) (e i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_congr rfl (fun j _ => by
            rw [hdual i j, ite_smul, one_smul, zero_smul])]
          rw [Finset.sum_ite_eq (Finset.univ : Finset (Fin (Module.finrank ℝ E))) i
            (fun j => B (e i) (e j))]
          simp

variable [CompactSpace M]

omit [BoundarylessManifold I M] in
theorem exists_smooth_parseval_frame_family (g : SmoothRiemannianMetric I M) :
    ∃ (N : ℕ) (W : Fin N → Π b : M, TangentSpace I b),
      (∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (W a))) ∧
      ∀ (x : M) (u : TangentSpace I x),
        (∑ a : Fin N, g.inner x (W a x) u • W a x) = u := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set U : M → Set M := fun α => interior (smoothOrthoFrameNbhd (I := I) (M := M) α) with hU_def
  have hU_open : ∀ α : M, IsOpen (U α) := fun _ => isOpen_interior
  have hU_mem : ∀ α : M, α ∈ U α := fun α =>
    mem_interior_iff_mem_nhds.mpr (smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) α)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU_open
    (fun x _ => mem_iUnion.mpr ⟨x, hU_mem x⟩)
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := I) isClosed_univ
    (fun k : ↥t => U (k : M)) (fun _ => isOpen_interior)
    (by
      intro x _
      rcases mem_iUnion₂.mp (ht (mem_univ x)) with ⟨α, hαt, hαx⟩
      exact mem_iUnion.mpr ⟨⟨α, hαt⟩, hαx⟩)
  set ρ : M → ℝ := fun x => ∑ k : ↥t, (f k x) ^ 2 with hρ_def
  have hρ_pos : ∀ x : M, 0 < ρ x := by
    intro x
    obtain ⟨k, hk⟩ := f.exists_pos_of_mem (mem_univ x)
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨k, Finset.mem_univ k, pow_pos hk 2⟩
  have hρ_smooth : ContMDiff I 𝓘(ℝ) ∞ ρ := by
    have hgen : ∀ s : Finset ↥t,
        ContMDiff I 𝓘(ℝ) ∞ (fun x : M => ∑ k ∈ s, (f k x) ^ 2) := by
      intro s
      induction s using Finset.induction with
      | empty => simpa using contMDiff_const (c := (0 : ℝ))
      | insert k s hk ih =>
          have hsq : ContMDiff I 𝓘(ℝ) ∞ (fun x : M => (f k x) ^ 2) := by
            have h := (f k).contMDiff
            simpa [pow_two] using h.mul h
          simpa [Finset.sum_insert hk] using hsq.add ih
    exact hgen Finset.univ
  set c : ↥t → M → ℝ := fun k x => (Real.sqrt (ρ x))⁻¹ * f k x with hc_def
  have hc_smooth : ∀ k : ↥t, ContMDiff I 𝓘(ℝ) ∞ (c k) := by
    intro k x
    have hsq : ContMDiffAt I 𝓘(ℝ) ∞ (fun y : M => Real.sqrt (ρ y)) x := by
      have h1 : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ Real.sqrt (ρ x) :=
        (Real.contDiffAt_sqrt (ne_of_gt (hρ_pos x))).contMDiffAt
      exact h1.comp x (hρ_smooth x)
    have hinv : ContMDiffAt I 𝓘(ℝ) ∞ (fun y : M => (Real.sqrt (ρ y))⁻¹) x :=
      hsq.inv₀ (ne_of_gt (Real.sqrt_pos.mpr (hρ_pos x)))
    exact hinv.mul ((f k).contMDiff x)
  set W0 : ↥t × Fin n → Π b : M, TangentSpace I b :=
    fun p => fun b => c p.1 b • smoothOrthoFrame (I := I) g (p.1 : M) p.2 b with hW0_def
  have hW0_smooth : ∀ p : ↥t × Fin n,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (W0 p)) := by
    intro p
    have h := ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (n := ∞)
      (V := TangentSpace I) (ψ := c p.1) (s := smoothOrthoFrame (I := I) g (p.1 : M) p.2)
      ((hc_smooth p.1).contMDiffOn (s := univ)) isOpen_univ (subset_univ _)
      ((smoothOrthoFrame_smooth (I := I) g (p.1 : M) p.2).contMDiffOn (s := univ))
    exact h
  have hrepr : ∀ (x : M) (u : TangentSpace I x),
      (∑ p : ↥t × Fin n, g.inner x (W0 p x) u • W0 p x) = u := by
    intro x u
    rw [Fintype.sum_prod_type]
    have hperk : ∀ k : ↥t,
        (∑ i : Fin n, g.inner x (W0 (k, i) x) u • W0 (k, i) x) =
          ((f k x) ^ 2 * (ρ x)⁻¹) • u := by
      intro k
      by_cases hfk : f k x = 0
      · have hc0 : c k x = 0 := by rw [hc_def]; simp [hfk]
        rw [hfk]
        simp only [hW0_def, hc0, zero_smul, map_zero, ContinuousLinearMap.zero_apply,
          smul_zero, Finset.sum_const_zero]
        rw [show (0 : ℝ) ^ 2 * (ρ x)⁻¹ = 0 by ring, zero_smul]
      · have hx_mem : x ∈ smoothOrthoFrameNbhd (I := I) (M := M) (k : M) := by
          have h1 : x ∈ tsupport (f k) := subset_closure (Function.mem_support.mpr hfk)
          exact interior_subset (hf k h1)
        have horth : ∀ i j : Fin n,
            g.inner x (smoothOrthoFrame (I := I) g (k : M) i x)
              (smoothOrthoFrame (I := I) g (k : M) j x) = if i = j then (1 : ℝ) else 0 :=
          fun i j => smoothOrthoFrame_orthonormal (I := I) g (k : M) hx_mem i j
        have hstep : ∀ i : Fin n,
            g.inner x (W0 (k, i) x) u • W0 (k, i) x =
              (c k x) ^ 2 • (g.inner x (smoothOrthoFrame (I := I) g (k : M) i x) u •
                smoothOrthoFrame (I := I) g (k : M) i x) := by
          intro i
          rw [hW0_def]
          simp only
          rw [map_smul (g.inner x) (c k x) (smoothOrthoFrame (I := I) g (k : M) i x),
            ContinuousLinearMap.smul_apply, smul_eq_mul, smul_smul, smul_smul]
          congr 1
          ring
        rw [Finset.sum_congr rfl (fun i _ => hstep i), ← Finset.smul_sum,
          orthonormal_tangent_expansion (I := I) (M := M) g x
            (fun i => smoothOrthoFrame (I := I) g (k : M) i x) horth u]
        congr 1
        rw [hc_def]
        simp only
        rw [mul_pow]
        have hsq : ((Real.sqrt (ρ x))⁻¹) ^ 2 = (ρ x)⁻¹ := by
          rw [← Real.sqrt_inv, Real.sq_sqrt (inv_nonneg.mpr (le_of_lt (hρ_pos x)))]
        rw [hsq]
        ring
    rw [Finset.sum_congr rfl (fun k _ => hperk k), ← Finset.sum_smul, ← Finset.sum_mul]
    rw [show (∑ k : ↥t, (f k x) ^ 2) = ρ x from rfl]
    rw [mul_inv_cancel₀ (ne_of_gt (hρ_pos x)), one_smul]
  refine ⟨Fintype.card (↥t × Fin n), fun a => W0 ((Fintype.equivFin (↥t × Fin n)).symm a),
    fun a => hW0_smooth _, ?_⟩
  intro x u
  conv_rhs => rw [← hrepr x u]
  exact Equiv.sum_comp (Fintype.equivFin (↥t × Fin n)).symm
    (fun p => g.inner x (W0 p x) u • W0 p x)

end Connection
end Integral
end DifferentialGeometry

end
