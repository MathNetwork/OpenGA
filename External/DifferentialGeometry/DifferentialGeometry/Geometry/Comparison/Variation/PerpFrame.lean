import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Connection.ParallelTransport.ParallelTransport
import DifferentialGeometry.Geometry.Connection.ParallelTransport.ParallelTransportSmooth
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic


noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace PerpFrameAux

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private noncomputable def bGramSchmidt
    (B : F →L[ℝ] F →L[ℝ] ℝ) {m : ℕ} (v : Fin m → F) (i : Fin m) : F :=
  let raw : F :=
    v i - ∑ j : Fin i.val,
      (B (v i) (bGramSchmidt B v ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
        bGramSchmidt B v ⟨j.val, lt_trans j.isLt i.isLt⟩
  (Real.sqrt (B raw raw))⁻¹ • raw
termination_by i.val
decreasing_by exact j.isLt

private noncomputable def bGramSchmidtRaw
    (B : F →L[ℝ] F →L[ℝ] ℝ) {m : ℕ} (v : Fin m → F) (i : Fin m) : F :=
  v i - ∑ j : Fin i.val,
    (B (v i) (bGramSchmidt B v ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
      bGramSchmidt B v ⟨j.val, lt_trans j.isLt i.isLt⟩

private lemma bGramSchmidt_eq
    (B : F →L[ℝ] F →L[ℝ] ℝ) {m : ℕ} (v : Fin m → F) (i : Fin m) :
    bGramSchmidt B v i =
      (Real.sqrt (B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i)))⁻¹ •
        bGramSchmidtRaw B v i := by
  unfold bGramSchmidt bGramSchmidtRaw
  rfl

private lemma B_sum_right
    (B : F →L[ℝ] F →L[ℝ] ℝ) (x : F)
    {ι : Type*} (s : Finset ι) (w : ι → F) (c : ι → ℝ) :
    B x (∑ k ∈ s, c k • w k) = ∑ k ∈ s, c k * B x (w k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has, map_add,
      show (B x) (c a • w a) = c a * B x (w a) from by
        rw [map_smul, smul_eq_mul], ih]

private lemma bGramSchmidt_self_norm
    (B : F →L[ℝ] F →L[ℝ] ℝ)
    (Bpos : ∀ x : F, x ≠ 0 → 0 < B x x)
    {m : ℕ} (v : Fin m → F) (i : Fin m)
    (hne : bGramSchmidtRaw B v i ≠ 0) :
    B (bGramSchmidt B v i) (bGramSchmidt B v i) = 1 := by
  have hpos : 0 < B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i) := Bpos _ hne
  have hs_sq : Real.sqrt (B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i)) *
      Real.sqrt (B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i)) =
      B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i) :=
    Real.mul_self_sqrt (le_of_lt hpos)
  set s : ℝ := Real.sqrt (B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i)) with hs_def
  have hei_eq : bGramSchmidt B v i = s⁻¹ • bGramSchmidtRaw B v i := by
    rw [bGramSchmidt_eq B v i, ← hs_def]
  rw [hei_eq]
  have hsmul : B (s⁻¹ • bGramSchmidtRaw B v i) (s⁻¹ • bGramSchmidtRaw B v i) =
      s⁻¹ * (s⁻¹ * B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i)) := by
    have h1 : B (s⁻¹ • bGramSchmidtRaw B v i) = s⁻¹ • B (bGramSchmidtRaw B v i) := by
      rw [map_smul]
    rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show (B (bGramSchmidtRaw B v i)) (s⁻¹ • bGramSchmidtRaw B v i) =
        s⁻¹ * B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i) from by
      rw [map_smul, smul_eq_mul]]
  rw [hsmul]
  rw [show s⁻¹ * (s⁻¹ * B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i)) =
      (s * s)⁻¹ * B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i) from by
    rw [mul_inv]; ring]
  rw [hs_sq]; exact inv_mul_cancel₀ (ne_of_gt hpos)

set_option maxHeartbeats 4000000 in

private theorem bGramSchmidt_orth_strong_aux
    (B : F →L[ℝ] F →L[ℝ] ℝ)
    (Bsymm : ∀ x y : F, B x y = B y x)
    (Bpos : ∀ x : F, x ≠ 0 → 0 < B x x)
    {m : ℕ} (v : Fin m → F) (hLI : LinearIndependent ℝ v) :
    ∀ k : ℕ, ∀ i : Fin m, i.val ≤ k →
      bGramSchmidtRaw B v i ≠ 0 ∧
      (∀ j : Fin m, j.val < i.val →
        B (bGramSchmidt B v j) (bGramSchmidt B v i) = 0) ∧
      B (bGramSchmidt B v i) (bGramSchmidt B v i) = 1 := by
  classical
  intro k
  induction k with
  | zero =>
    intro i hi_le
    have hi_val : i.val = 0 := Nat.le_zero.mp hi_le
    have hempty : IsEmpty (Fin i.val) := by rw [hi_val]; exact Fin.isEmpty
    have hraw : bGramSchmidtRaw B v i = v i := by
      unfold bGramSchmidtRaw
      rw [Finset.sum_eq_zero (fun j _ => hempty.elim j)]
      simp
    have hne : bGramSchmidtRaw B v i ≠ 0 := by rw [hraw]; exact hLI.ne_zero i
    refine ⟨hne, ?_, ?_⟩
    · intro j hj; rw [hi_val] at hj; omega
    · exact bGramSchmidt_self_norm B Bpos v i hne
  | succ k ih =>
    intro i hi_le
    by_cases hi_lt : i.val ≤ k
    · exact ih i hi_lt
    · have hi_eq : i.val = k + 1 := by omega
      have ih_below : ∀ j : Fin m, j.val < i.val →
          bGramSchmidtRaw B v j ≠ 0 ∧
          (∀ j' : Fin m, j'.val < j.val →
            B (bGramSchmidt B v j') (bGramSchmidt B v j) = 0) ∧
          B (bGramSchmidt B v j) (bGramSchmidt B v j) = 1 :=
        fun j hj => ih j (by omega)
      have horth_raw : ∀ j : Fin m, j.val < i.val →
          B (bGramSchmidt B v j) (bGramSchmidtRaw B v i) = 0 := by
        intro j hj_lt
        rw [show bGramSchmidtRaw B v i =
            v i - ∑ j' : Fin i.val,
              (B (v i) (bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩ from rfl]
        rw [map_sub]
        rw [B_sum_right B (bGramSchmidt B v j) (Finset.univ : Finset (Fin i.val))
            (fun j' => bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩)
            (fun j' => B (v i)
              (bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩))]
        have hsum_eq :
            ∑ j' ∈ (Finset.univ : Finset (Fin i.val)),
                B (v i) (bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩) *
                  B (bGramSchmidt B v j)
                    (bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩) =
              B (bGramSchmidt B v j) (v i) := by
          set j_inFin : Fin i.val := ⟨j.val, hj_lt⟩
          rw [Finset.sum_eq_single j_inFin]
          · have hj_eq : (⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩ : Fin m) = j :=
              Fin.ext rfl
            rw [hj_eq, (ih_below j hj_lt).2.2, mul_one, Bsymm]
          · intro j' _ hj'
            have hj'_neq : j'.val ≠ j.val := fun h => hj' (Fin.ext h)
            by_cases hcompare : j'.val < j.val
            · have hzero := (ih_below j hj_lt).2.1
                ⟨j'.val, lt_trans hcompare j.isLt⟩ hcompare
              rw [show B (bGramSchmidt B v j)
                  (bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩) =
                  B (bGramSchmidt B v ⟨j'.val, lt_trans hcompare j.isLt⟩)
                    (bGramSchmidt B v j) from by rw [Bsymm]]
              rw [hzero, mul_zero]
            · have hcompare' : j.val < j'.val :=
                lt_of_le_of_ne (Nat.le_of_not_lt hcompare) hj'_neq.symm
              have hzero := (ih_below ⟨j'.val, lt_trans j'.isLt i.isLt⟩ j'.isLt).2.1
                j hcompare'
              rw [hzero, mul_zero]
          · intro h; exact absurd (Finset.mem_univ j_inFin) h
        rw [hsum_eq, Bsymm (bGramSchmidt B v j) (v i)]; ring
      have hraw_ne : bGramSchmidtRaw B v i ≠ 0 := by
        intro hraw_zero
        have hv_eq : v i =
            ∑ j' : Fin i.val,
              (B (v i) (bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := by
          have h_eq : v i -
              ∑ j' : Fin i.val,
                (B (v i) (bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                  bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩ = 0 := by
            simpa [bGramSchmidtRaw] using hraw_zero
          exact sub_eq_zero.mp h_eq
        have h_e_in_span : ∀ kk : ℕ, ∀ mm : Fin m, mm.val ≤ kk → mm.val < i.val →
            bGramSchmidt B v mm ∈
              Submodule.span ℝ
                ((fun n : Fin i.val => v ⟨n.val, lt_trans n.isLt i.isLt⟩) '' Set.univ) := by
          intro kk
          induction kk with
          | zero =>
            intro mm hm_le hm_lt
            have hm_val : mm.val = 0 := Nat.le_zero.mp hm_le
            have hempty : IsEmpty (Fin mm.val) := by rw [hm_val]; exact Fin.isEmpty
            rw [bGramSchmidt_eq B v mm]
            apply Submodule.smul_mem
            have hraw_mm : bGramSchmidtRaw B v mm = v mm := by
              unfold bGramSchmidtRaw
              rw [Finset.sum_eq_zero (fun j _ => hempty.elim j)]; simp
            rw [hraw_mm]
            apply Submodule.subset_span
            exact ⟨⟨mm.val, hm_lt⟩, Set.mem_univ _, rfl⟩
          | succ kk ih_kk =>
            intro mm hm_le hm_lt
            by_cases hcase : mm.val ≤ kk
            · exact ih_kk mm hcase hm_lt
            · rw [bGramSchmidt_eq B v mm]
              apply Submodule.smul_mem
              unfold bGramSchmidtRaw
              apply Submodule.sub_mem
              · apply Submodule.subset_span
                exact ⟨⟨mm.val, hm_lt⟩, Set.mem_univ _, rfl⟩
              · apply Submodule.sum_mem
                intro j _
                apply Submodule.smul_mem
                have hj_in : j.val < i.val := lt_trans j.isLt hm_lt
                have hj_le : j.val ≤ kk := by have := j.isLt; omega
                exact ih_kk ⟨j.val, lt_trans j.isLt mm.isLt⟩ hj_le hj_in
        have hvi_in_span : v i ∈
            Submodule.span ℝ
              ((fun n : Fin i.val => v ⟨n.val, lt_trans n.isLt i.isLt⟩) '' Set.univ) := by
          rw [hv_eq]
          apply Submodule.sum_mem
          intro j' _
          apply Submodule.smul_mem
          have hj'_le : j'.val ≤ k := by have := j'.isLt; omega
          exact h_e_in_span k ⟨j'.val, lt_trans j'.isLt i.isLt⟩ hj'_le j'.isLt
        have hset_eq :
            ((fun n : Fin i.val => v ⟨n.val, lt_trans n.isLt i.isLt⟩) '' Set.univ) =
              (v '' {n : Fin m | n.val < i.val}) := by
          ext x
          constructor
          · rintro ⟨n, _, rfl⟩
            exact ⟨⟨n.val, lt_trans n.isLt i.isLt⟩, n.isLt, rfl⟩
          · rintro ⟨n, hn, rfl⟩
            exact ⟨⟨n.val, hn⟩, Set.mem_univ _, rfl⟩
        rw [hset_eq] at hvi_in_span
        have hi_notin : i ∉ {n : Fin m | n.val < i.val} := by simp [Set.mem_setOf_eq]
        exact hLI.notMem_span_image hi_notin hvi_in_span
      set s : ℝ := Real.sqrt (B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i))
        with hs_def
      have hei_eq : bGramSchmidt B v i = s⁻¹ • bGramSchmidtRaw B v i := by
        rw [bGramSchmidt_eq B v i, ← hs_def]
      refine ⟨hraw_ne, ?_, ?_⟩
      · intro j hj_lt
        rw [hei_eq,
          show (B (bGramSchmidt B v j)) (s⁻¹ • bGramSchmidtRaw B v i) =
            s⁻¹ * B (bGramSchmidt B v j) (bGramSchmidtRaw B v i) from by
          rw [map_smul, smul_eq_mul]]
        rw [horth_raw j hj_lt, mul_zero]
      · exact bGramSchmidt_self_norm B Bpos v i hraw_ne

private theorem bGramSchmidt_orthonormal
    (B : F →L[ℝ] F →L[ℝ] ℝ)
    (Bsymm : ∀ x y : F, B x y = B y x)
    (Bpos : ∀ x : F, x ≠ 0 → 0 < B x x)
    {m : ℕ} (v : Fin m → F) (hLI : LinearIndependent ℝ v) (i j : Fin m) :
    B (bGramSchmidt B v i) (bGramSchmidt B v j) = if i = j then 1 else 0 := by
  classical
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · have h := bGramSchmidt_orth_strong_aux B Bsymm Bpos v hLI j.val j (le_refl _)
    have hne : i ≠ j := fun h_eq => by rw [h_eq] at hlt; omega
    rw [if_neg hne]; exact h.2.1 i hlt
  · have hij : i = j := Fin.ext heq
    rw [if_pos hij, ← hij]
    exact (bGramSchmidt_orth_strong_aux B Bsymm Bpos v hLI i.val i (le_refl _)).2.2
  · have h := bGramSchmidt_orth_strong_aux B Bsymm Bpos v hLI i.val i (le_refl _)
    have hne : i ≠ j := fun h_eq => by rw [h_eq] at hgt; omega
    rw [if_neg hne, Bsymm]; exact h.2.1 j hgt

private theorem bGramSchmidt_mem
    (B : F →L[ℝ] F →L[ℝ] ℝ) {m : ℕ} (v : Fin m → F)
    (W : Submodule ℝ F) (hv : ∀ k, v k ∈ W) (i : Fin m) :
    bGramSchmidt B v i ∈ W := by
  classical
  induction hk : i.val using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    subst hk
    rw [bGramSchmidt_eq B v i]
    apply Submodule.smul_mem
    unfold bGramSchmidtRaw
    refine W.sub_mem (hv i) (Submodule.sum_mem _ ?_)
    intro j _
    exact Submodule.smul_mem _ _ (ih j.val j.isLt ⟨j.val, lt_trans j.isLt i.isLt⟩ rfl)

end PerpFrameAux

section PerpFrame

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]


omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem perp_to_velocity_preserved_of_parallel
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hgeo : IsGeodesic (I := I) g γ)
    {L : ℝ} (_hL : 0 < L) (V : ∀ t, TangentSpace I (γ t))
    (hVdiff : ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t)
    (hVpar : ∀ t ∈ Set.Icc (0 : ℝ) L, covDerivAlong (I := I) g γ V t = 0)
    (hPerp0 : g.inner (γ 0) (V 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (V t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 0 := by
  classical
  set vel : ℝ → ∀ s, TangentSpace I (γ s) :=
    fun _ s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E) with hvel_def
  set f : ℝ → ℝ := fun t => g.inner (γ t) (V t)
    (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) with hf_def
  have hlocal : ∀ t₀ ∈ Set.Icc (0 : ℝ) L, HasDerivAt f 0 t₀ := by
    intro t₀ ht₀
    set α : M := γ t₀ with hα_def
    set Vrep : ℝ → E := chartRepAt (I := I) γ V t₀ with hVrep_def
    set urep : ℝ → E :=
      chartRepAt (I := I) γ (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E)) t₀ with hurep_def
    have hbase_t₀ : γ t₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source H (γ t₀)
    have hbaseSet_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
      (trivializationAt E (TangentSpace I) α).open_baseSet
    have hsrc_open : IsOpen {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet} :=
      hbaseSet_open.preimage hγ.continuous
    have hsrc_mem : {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet} ∈ 𝓝 t₀ :=
      hsrc_open.mem_nhds hbase_t₀
    have hVround : ∀ s ∈ {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet},
        (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Vrep s) = V s := by
      intro s hs
      simpa [hVrep_def, chartRepAt_apply] using
        (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
          (R := ℝ) hs (V s)
    have huround : ∀ s ∈ {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet},
        (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (urep s) =
          (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E) := by
      intro s hs
      simpa [hurep_def, chartRepAt_apply] using
        (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
          (R := ℝ) hs ((mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E))
    have hf_eq : f =ᶠ[𝓝 t₀]
        fun s => AlongCurve.chartGramAlongCurve (I := I) g α γ Vrep urep s := by
      filter_upwards [hsrc_mem] with s hs
      have hVs := hVround s hs
      have hus := huround s hs
      have : f s = g.inner (γ s)
          ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Vrep s))
          ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (urep s)) := by
        rw [hf_def]; rw [hVs, hus]
      rw [this, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α (Vrep s) (urep s)]
      rw [AlongCurve.chartGramAlongCurve_def]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      have hinv : (extChartAt I α).symm (chartCurve (I := I) α γ s) = γ s := by
        rw [chartCurve_def]
        refine (extChartAt I α).left_inv ?_
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        rw [TangentBundle.trivializationAt_baseSet] at hs
        exact hs
      rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_def, hinv]
    have hu_hasDerivAt :
        HasDerivAt (chartCurve (I := I) α γ)
          (deriv (chartCurve (I := I) α γ) t₀) t₀ := by
      have hcd : ContDiffAt ℝ ∞ (chartCurve (I := I) α γ) t₀ := by
        have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
            ((extChartAt I α) ∘ γ) t₀ := by
          have hφ : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) (γ t₀) :=
            contMDiffAt_extChartAt (I := I) (x := α) (n := ∞)
          exact hφ.comp t₀ (hγ.contMDiffAt)
        exact contMDiffAt_iff_contDiffAt.mp hmdiff
      exact (hcd.differentiableAt (by simp)).hasDerivAt
    have hmem_int : chartCurve (I := I) α γ t₀ ∈ interior (extChartAt I α).target := by
      have hxsrc : γ t₀ ∈ (extChartAt I α).source := by
        rw [extChartAt_source]; exact mem_chart_source H (γ t₀)
      exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
        (I := I) α ((extChartAt I α).map_source hxsrc)
    have hVrep_hasDerivAt : HasDerivAt Vrep (deriv Vrep t₀) t₀ :=
      ((hVdiff t₀ ht₀).hasDerivAt)
    set U : Set ℝ := γ ⁻¹' (chartAt H α).source with hU_def
    have hU_open : IsOpen U := (chartAt H α).open_source.preimage hγ.continuous
    have ht₀_U : t₀ ∈ U := by
      rw [hU_def, Set.mem_preimage]; exact mem_chart_source H (γ t₀)
    have hU_nhds : U ∈ 𝓝 t₀ := hU_open.mem_nhds ht₀_U
    have hu_cdiffOn : ContDiffOn ℝ ∞ (chartCurve (I := I) α γ) U := by
      have h_comp_mdiff :
          ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ((extChartAt I α) ∘ γ) U := by
        have hφ : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
          contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
        have hγU : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ U := hγ.contMDiffOn
        have hmaps : Set.MapsTo γ U (chartAt H α).source := fun s hs => hs
        exact hφ.comp hγU hmaps
      have hfun : (chartCurve (I := I) α γ) = ((extChartAt I α) ∘ γ) := rfl
      rw [hfun]
      exact contMDiffOn_iff_contDiffOn.mp h_comp_mdiff
    have hurep_eqOn : Set.EqOn urep (deriv (chartCurve (I := I) α γ)) U := by
      intro s hs
      have hs' : γ s ∈ (chartAt H α).source := hs
      rw [hurep_def, chartRepAt_apply]
      rw [MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
        (I := I) (M := M) (γ := γ) hγ α (t := s) hs']
      rfl
    have hurep_eq : urep =ᶠ[𝓝 t₀] deriv (chartCurve (I := I) α γ) :=
      hurep_eqOn.eventuallyEq_of_mem hU_nhds
    have hu_deriv_hasDerivAt :
        HasDerivAt (deriv (chartCurve (I := I) α γ))
          (deriv (deriv (chartCurve (I := I) α γ)) t₀) t₀ := by
      have hderiv_u_cdiffOn :
          ContDiffOn ℝ ∞ (deriv (chartCurve (I := I) α γ)) U :=
        hu_cdiffOn.deriv_of_isOpen hU_open (by exact_mod_cast (le_refl (∞ : WithTop ℕ∞)))
      exact ((hderiv_u_cdiffOn.differentiableOn (by simp) t₀ ht₀_U).differentiableAt
        hU_nhds).hasDerivAt
    have hurep_hasDerivAt : HasDerivAt urep (deriv (deriv (chartCurve (I := I) α γ)) t₀) t₀ :=
      hu_deriv_hasDerivAt.congr_of_eventuallyEq hurep_eq
    have hgram :=
      AlongCurve.chartGramAlongCurve_hasDerivAt_covariant (I := I) g α γ Vrep urep
        (uPrime := fun _ => deriv (chartCurve (I := I) α γ) t₀)
        (Vprime := fun _ => deriv Vrep t₀)
        (Wprime := fun _ => deriv (deriv (chartCurve (I := I) α γ)) t₀)
        hu_hasDerivAt hmem_int hVrep_hasDerivAt hurep_hasDerivAt
    have hcorrV :
        deriv Vrep t₀ +
          chartChristoffelContraction (I := I) g α
            (deriv (chartCurve (I := I) α γ) t₀) (Vrep t₀)
            (chartCurve (I := I) α γ t₀) = 0 := by
      have : chartCovDerivAlong (I := I) g α γ Vrep t₀ = 0 := by
        rw [hα_def, hVrep_def]
        exact (covDerivAlong_eq_zero_iff (I := I) g γ V t₀).mp (hVpar t₀ ht₀)
      rw [chartCovDerivAlong_def] at this
      exact this
    have hcorru :
        deriv (deriv (chartCurve (I := I) α γ)) t₀ +
          chartChristoffelContraction (I := I) g α
            (deriv (chartCurve (I := I) α γ) t₀) (urep t₀)
            (chartCurve (I := I) α γ t₀) = 0 := by
      have hgeoeq := hgeo.hasGeodesicEquationAt t₀
      have hvel0 :
          covDerivAlong (I := I) g γ
            (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E)) t₀ = 0 :=
        (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt (I := I) g γ t₀ hγ).mpr hgeoeq
      have hchart0 : chartCovDerivAlong (I := I) g α γ urep t₀ = 0 := by
        rw [hα_def, hurep_def]
        exact (covDerivAlong_eq_zero_iff (I := I) g γ
          (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E)) t₀).mp hvel0
      rw [chartCovDerivAlong_def] at hchart0
      rw [hurep_eq.deriv_eq] at hchart0
      exact hchart0
    have hderiv0 : HasDerivAt
        (fun s => AlongCurve.chartGramAlongCurve (I := I) g α γ Vrep urep s) 0 t₀ := by
      convert hgram using 1
      simp only [hcorrV, hcorru]
      simp
    exact hderiv0.congr_of_eventuallyEq hf_eq
  have hcont : ContinuousOn f (Set.Icc 0 L) :=
    fun t ht => ((hlocal t ht).continuousAt).continuousWithinAt
  have hderivWithin : ∀ x ∈ Set.Ico (0 : ℝ) L, HasDerivWithinAt f 0 (Set.Ici x) x := by
    intro x hx
    exact (hlocal x (Set.mem_Icc_of_Ico hx)).hasDerivWithinAt
  have hconst : ∀ x ∈ Set.Icc (0 : ℝ) L, f x = f 0 :=
    constant_of_has_deriv_right_zero hcont hderivWithin
  intro t ht
  have hft := hconst t ht
  rw [hf_def] at hft
  simp only at hft
  rw [hft]
  exact hPerp0

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
omit [InnerProductSpace ℝ E] in
theorem exists_parallel_orthonormal_perp_frame_along_geodesic
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hgeo : IsGeodesic (I := I) g γ)
    {L : ℝ} (hL : 0 < L)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 1) :
    ∃ e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ,
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (e i).toFun t) t) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        covDerivAlong (I := I) g γ (e i).toFun t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) ((e i).toFun t) ((e j).toFun t) =
          if i = j then 1 else 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
        g.inner (γ t) ((e i).toFun t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 0) := by
  classical
  set u₀ : E := (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) with hu₀_def
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (γ 0) with hB_def
  have hBsymm : ∀ x y : E, B x y = B y x := fun x y => g.symm (γ 0) x y
  have hBpos : ∀ x : E, x ≠ 0 → 0 < B x x := fun x hx => g.pos (γ 0) x hx
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_refl _, hL.le⟩
  have hu₀_unit : B u₀ u₀ = 1 := hUnit 0 h0mem
  have hu₀_ne : u₀ ≠ 0 := by
    intro h; rw [h] at hu₀_unit; simp at hu₀_unit
  set φ : E →ₗ[ℝ] ℝ := (B u₀).toLinearMap with hφ_def
  set W : Submodule ℝ E := LinearMap.ker φ with hW_def
  have hφ_u₀ : φ u₀ = 1 := hu₀_unit
  have hφ_surj : Function.Surjective φ := by
    intro c
    refine ⟨c • u₀, ?_⟩
    rw [map_smul, hφ_u₀, smul_eq_mul, mul_one]
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ_surj
  have hfr_range : Module.finrank ℝ ↥(LinearMap.range φ) = 1 := by
    rw [hrange]; simp
  have hfinrankW : Module.finrank ℝ ↥W = Module.finrank ℝ E - 1 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker φ
    rw [hfr_range] at hsum
    have : Module.finrank ℝ ↥W = Module.finrank ℝ ↥(LinearMap.ker φ) := rfl
    rw [this]; omega
  letI : Module.Finite ℝ ↥W := inferInstance
  set bW : Module.Basis (Fin (Module.finrank ℝ E - 1)) ℝ ↥W :=
    Module.finBasisOfFinrankEq ℝ ↥W hfinrankW with hbW_def
  set vfam : Fin (Module.finrank ℝ E - 1) → E := fun i => (bW i : E) with hvfam_def
  have hvfam_mem : ∀ i, vfam i ∈ W := fun i => (bW i).2
  have hvfam_LI : LinearIndependent ℝ vfam := by
    have hbWLI : LinearIndependent ℝ (fun i => bW i) := bW.linearIndependent
    have := hbWLI.map' (W.subtype) (Submodule.ker_subtype W)
    exact this
  set seed : Fin (Module.finrank ℝ E - 1) → E :=
    fun i => PerpFrameAux.bGramSchmidt B vfam i with hseed_def
  have hseed_ON : ∀ i j, B (seed i) (seed j) = if i = j then 1 else 0 :=
    fun i j => PerpFrameAux.bGramSchmidt_orthonormal B hBsymm hBpos vfam hvfam_LI i j
  have hseed_mem : ∀ i, seed i ∈ W :=
    fun i => PerpFrameAux.bGramSchmidt_mem B vfam W hvfam_mem i
  have hseed_perp : ∀ i, B (seed i) u₀ = 0 := by
    intro i
    have hker : φ (seed i) = 0 := (LinearMap.mem_ker).mp (hseed_mem i)
    have : B u₀ (seed i) = 0 := hker
    rw [hBsymm (seed i) u₀]; exact this
  have htransport : ∀ i, ∃ V : ∀ t, TangentSpace I (γ t),
      V 0 = seed i ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, covDerivAlong (I := I) g γ V t = 0) := by
    intro i
    exact DifferentialGeometry.Geometry.Riemannian.Variation.exists_parallel_transport_on_Icc
      (I := I) g γ (N := 2) le_rfl (hγ.of_le (by exact_mod_cast le_top)) hL (seed i)
  choose Vfun hV0 hVdiff hVpar using htransport
  refine ⟨fun i => ⟨fun t => Vfun i t⟩, ?_, ?_, ?_, ?_⟩
  · intro i t ht; exact hVdiff i t ht
  · intro i t ht; exact hVpar i t ht
  · intro t ht i j
    have hconst :=
      DifferentialGeometry.Geometry.Riemannian.Variation.parallel_transport_preserves_inner_product
        (I := I) g γ (N := 2) le_rfl (hγ.of_le (by exact_mod_cast le_top)) hL.le
        (Vfun i) (Vfun j)
        (hVdiff i) (hVdiff j) (hVpar i) (hVpar j) t ht
    rw [show ((fun i => (⟨fun t => Vfun i t⟩ : SectionAlongCurve I M γ)) i).toFun t = Vfun i t
        from rfl,
      show ((fun i => (⟨fun t => Vfun i t⟩ : SectionAlongCurve I M γ)) j).toFun t = Vfun j t
        from rfl]
    rw [hconst, hV0 i, hV0 j]
    exact hseed_ON i j
  · intro t ht i
    have hperp :=
      perp_to_velocity_preserved_of_parallel (I := I) g γ hγ hgeo hL (Vfun i)
        (hVdiff i) (hVpar i)
        (by
          rw [hV0 i]
          exact hseed_perp i)
        t ht
    rw [show ((fun i => (⟨fun t => Vfun i t⟩ : SectionAlongCurve I M γ)) i).toFun t = Vfun i t
        from rfl]
    exact hperp

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
omit [InnerProductSpace ℝ E] in
theorem exists_parallel_frame
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {N : ℕ} (hN : 2 ≤ N) (hγ : ContMDiff 𝓘(ℝ, ℝ) I (N : ℕ∞) γ) {L : ℝ} (hL : 0 < L)
    {ι : Type*} [DecidableEq ι] (v : ι → TangentSpace I (γ 0))
    (hON0 : ∀ i j, g.inner (γ 0) (v i) (v j) = if i = j then (1 : ℝ) else 0) :
    ∃ e : ι → ∀ t : ℝ, TangentSpace I (γ t),
      (∀ i, e i 0 = v i) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (e i) t) t) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        covDerivAlong (I := I) g γ (e i) t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) (e i t) (e j t) = if i = j then 1 else 0) := by
  classical
  have htransport : ∀ i, ∃ V : ∀ t, TangentSpace I (γ t),
      V 0 = v i ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, covDerivAlong (I := I) g γ V t = 0) :=
    fun i =>
      DifferentialGeometry.Geometry.Riemannian.Variation.exists_parallel_transport_on_Icc
        (I := I) g γ hN hγ hL (v i)
  choose Vfun hV0 hVdiff hVpar using htransport
  refine ⟨Vfun, hV0, hVdiff, hVpar, ?_⟩
  intro t ht i j
  have hconst :=
    DifferentialGeometry.Geometry.Riemannian.Variation.parallel_transport_preserves_inner_product
      (I := I) g γ hN hγ hL.le (Vfun i) (Vfun j)
      (hVdiff i) (hVdiff j) (hVpar i) (hVpar j) t ht
  rw [hconst, hV0 i, hV0 j]
  exact hON0 i j

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
omit [InnerProductSpace ℝ E] in
theorem parallel_on_frame_perp_to_geodesic
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hgeo : IsGeodesic (I := I) g γ) {L : ℝ} (hL : 0 < L)
    (uPrime : ℝ → E)
    (huPrimeEq : ∀ t ∈ Set.Icc (0 : ℝ) L,
      (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ) : E) = uPrime t)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (uPrime t) (uPrime t) = 1) :
    ∃ e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ,
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (e i).toFun t) t) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        covDerivAlong (I := I) g γ (e i).toFun t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) ((e i).toFun t) ((e j).toFun t) =
          if i = j then 1 else 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
        g.inner (γ t) ((e i).toFun t) (uPrime t) = 0) := by
  have hUnit' : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 1 := by
    intro t ht
    rw [huPrimeEq t ht]; exact hUnit t ht
  obtain ⟨e, hdiff, hpar, hON, hperp⟩ :=
    exists_parallel_orthonormal_perp_frame_along_geodesic (I := I) g γ hγ hgeo hL hUnit'
  refine ⟨e, hdiff, hpar, hON, ?_⟩
  intro t ht i
  have := hperp t ht i
  rwa [huPrimeEq t ht] at this

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem chartCovDerivAlong_movingFoot_eq_zero_of_isParallelChart_centered
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {X : ℝ → E} {s : Set ℝ} {t : ℝ}
    (hX : IsParallelChart (I := I) g (γ t) γ
      (fun τ => deriv (AlongCurve.chartCurve (I := I) (γ t) γ) τ) X s)
    (ht : t ∈ s) :
    chartCovDerivAlong (I := I) g (γ t) γ X t = 0 := by
  have hd := hX.hasDerivAt ht
  have hderiv := hd.deriv
  rw [chartCovDerivAlong_def, hderiv]
  abel

end PerpFrame

section SmoothPerpFrame

variable [I.Boundaryless]

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem contMDiff_smul_bundleField_perp
    {γ : ℝ → M} {V : ℝ → E} {χ : ℝ → ℝ} {n : WithTop ℕ∞}
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) I n γ) (hχ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n χ)
    (hVbundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent n
      (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t)))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent n
      (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (γ t) (χ t • V t))) := by
  intro t₀
  rw [contMDiffAt_totalSpace]
  refine ⟨hγ t₀, ?_⟩
  have hVfib := ((contMDiffAt_totalSpace (f := fun t : ℝ =>
    (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t)))).1 (hVbundle t₀)).2
  have hsmul := (hχ t₀).smul hVfib
  refine hsmul.congr_of_eventuallyEq ?_
  have hbase : ∀ᶠ t in 𝓝 t₀, γ t ∈ (trivializationAt E (TangentSpace I) (γ t₀)).baseSet := by
    have hmem : (γ t₀) ∈ (trivializationAt E (TangentSpace I) (γ t₀)).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' (γ t₀)
    exact (hγ t₀).continuousAt.preimage_mem_nhds
      ((trivializationAt E (TangentSpace I) (γ t₀)).open_baseSet.mem_nhds hmem)
  filter_upwards [hbase] with t ht
  simp only [TotalSpace.mk']
  rw [(trivializationAt E (TangentSpace I) (γ t₀)).apply_eq_prod_continuousLinearEquivAt ℝ
        (γ t) ht,
      (trivializationAt E (TangentSpace I) (γ t₀)).apply_eq_prod_continuousLinearEquivAt ℝ
        (γ t) ht]
  exact map_smul _ _ _

theorem exists_cutoff_one_on_Icc_supported_Ioo {L δ : ℝ} (hδ : 0 < δ) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ (∞ : WithTop ℕ∞) χ ∧ Set.EqOn χ 1 (Set.Icc 0 L) ∧
      tsupport χ ⊆ Set.Ioo (-δ : ℝ) (L + δ) ∧ ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 := by
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  have hclosed_t : IsClosed (Set.Icc (0 : ℝ) L) := isClosed_Icc
  have hclosed_s : IsClosed ((Set.Ioo (-(δ / 2) : ℝ) (L + δ / 2))ᶜ) :=
    isOpen_Ioo.isClosed_compl
  have hdisj : Disjoint ((Set.Ioo (-(δ / 2) : ℝ) (L + δ / 2))ᶜ) (Set.Icc 0 L) := by
    rw [Set.disjoint_compl_left_iff_subset]
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    exact ⟨by linarith, by linarith⟩
  obtain ⟨f, hf0, hf1, hfIcc⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ, ℝ) (n := (⊤ : ℕ∞)) hclosed_s hclosed_t hdisj
  refine ⟨f, ?_, hf1, ?_, hfIcc⟩
  · have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f : ℝ → ℝ) := by
      rw [← contMDiff_iff_contDiff]; exact f.contMDiff
    exact hcd
  · have hsupp : Function.support (f : ℝ → ℝ) ⊆ Set.Ioo (-(δ / 2) : ℝ) (L + δ / 2) := by
      intro x hx
      by_contra hxc
      exact hx (hf0 hxc)
    have hclosure : tsupport (f : ℝ → ℝ) ⊆ Set.Icc (-(δ / 2) : ℝ) (L + δ / 2) := by
      rw [tsupport]
      exact closure_minimal (hsupp.trans Set.Ioo_subset_Icc_self) isClosed_Icc
    refine hclosure.trans ?_
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩


theorem exists_time_window_clip {a b lam : ℝ}
    (hlam_pos : 0 < lam) (ha : -lam < a) (hb : b < lam) :
    ∃ tau : ℝ → ℝ, ContDiff ℝ (∞ : WithTop ℕ∞) tau ∧
      Set.EqOn tau id (Set.Icc a b) ∧ ∀ t, |tau t| ≤ lam := by
  have hclosed_t : IsClosed (Set.Icc a b) := isClosed_Icc
  have hclosed_s : IsClosed ((Set.Ioo (-lam : ℝ) lam)ᶜ) := isOpen_Ioo.isClosed_compl
  have hdisj : Disjoint ((Set.Ioo (-lam : ℝ) lam)ᶜ) (Set.Icc a b) := by
    rw [Set.disjoint_compl_left_iff_subset]
    intro x hx
    exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  obtain ⟨χ, hχ0, hχ1, hχIcc⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ, ℝ) (n := (⊤ : ℕ∞))
      hclosed_s hclosed_t hdisj
  refine ⟨fun t => χ t * t, ?_, ?_, ?_⟩
  · have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ : ℝ → ℝ) := by
      rw [← contMDiff_iff_contDiff]
      exact χ.contMDiff
    exact hcd.mul contDiff_id
  · intro t ht
    change χ t * t = t
    rw [hχ1 ht]
    simp
  · intro t
    change |χ t * t| ≤ lam
    by_cases htΩ : t ∈ Set.Ioo (-lam : ℝ) lam
    · have hχ_abs : |χ t| ≤ 1 := by
        rw [abs_of_nonneg (hχIcc t).1]
        exact (hχIcc t).2
      have ht_abs : |t| ≤ lam := by
        rw [abs_le]
        exact ⟨le_of_lt htΩ.1, le_of_lt htΩ.2⟩
      calc
        |χ t * t| = |χ t| * |t| := abs_mul _ _
        _ ≤ 1 * lam :=
          mul_le_mul hχ_abs ht_abs (abs_nonneg _) (by norm_num)
        _ = lam := one_mul _
    · have hχ_zero : χ t = 0 := hχ0 htΩ
      simpa [hχ_zero] using hlam_pos.le


theorem exists_time_clip {L lam : ℝ} (hL : 0 ≤ L) (hlam : L < lam) :
    ∃ tau : ℝ → ℝ, ContDiff ℝ (∞ : WithTop ℕ∞) tau ∧
      Set.EqOn tau id (Set.Icc 0 L) ∧ ∀ t, |tau t| ≤ lam := by
  set delta : ℝ := (lam - L) / 2 with hdelta_def
  have hdelta_pos : 0 < delta := by rw [hdelta_def]; linarith
  have hlam_pos : 0 < lam := lt_of_le_of_lt hL hlam
  obtain ⟨chi, hchi_cd, hchi_one, hchi_supp, hchi_range⟩ :=
    exists_cutoff_one_on_Icc_supported_Ioo (L := L) hdelta_pos
  refine ⟨fun t => chi t * t, hchi_cd.mul contDiff_id, ?_, ?_⟩
  · intro t ht
    change chi t * t = t
    rw [hchi_one ht]
    simp
  · intro t
    change |chi t * t| ≤ lam
    by_cases htΩ : t ∈ Set.Ioo (-delta : ℝ) (L + delta)
    · have hchi_abs : |chi t| ≤ 1 := by
        rw [abs_of_nonneg (hchi_range t).1]
        exact (hchi_range t).2
      have hdelta_le : delta ≤ L + delta := by linarith
      have ht_abs : |t| < L + delta := by
        rw [abs_lt]
        exact ⟨lt_of_le_of_lt (neg_le_neg hdelta_le) htΩ.1, htΩ.2⟩
      exact le_of_lt (by
      calc
        |chi t * t| = |chi t| * |t| := abs_mul _ _
        _ ≤ 1 * (L + delta) :=
          mul_le_mul hchi_abs (le_of_lt ht_abs) (abs_nonneg _) (by norm_num)
        _ = L + delta := one_mul _
        _ < lam := by rw [hdelta_def]; linarith)
    · have hnot_tsupport : t ∉ tsupport chi := fun h => htΩ (hchi_supp h)
      have hchi_zero : chi t = 0 := by
        have hnot_support : t ∉ Function.support chi := fun h =>
          hnot_tsupport (subset_closure h)
        simpa [Function.support] using hnot_support
      simpa [hchi_zero] using hlam_pos.le

set_option linter.unusedVariables false in

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem perp_to_velocity_preserved_on
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {L : ℝ} (_hL : 0 < L)
    (hgeo : IsGeodesicOn (I := I) g γ (Set.Icc 0 L))
    (V : ∀ t, TangentSpace I (γ t))
    (hVdiff : ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t)
    (hVpar : ∀ t ∈ Set.Icc (0 : ℝ) L, covDerivAlong (I := I) g γ V t = 0)
    (hPerp0 : g.inner (γ 0) (V 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (V t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 0 := by
  classical
  set f : ℝ → ℝ := fun t => g.inner (γ t) (V t)
    (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) with hf_def
  have hlocal : ∀ t₀ ∈ Set.Icc (0 : ℝ) L, HasDerivAt f 0 t₀ := by
    intro t₀ ht₀
    set α : M := γ t₀ with hα_def
    set Vrep : ℝ → E := chartRepAt (I := I) γ V t₀ with hVrep_def
    set urep : ℝ → E :=
      chartRepAt (I := I) γ (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E)) t₀ with hurep_def
    have hbase_t₀ : γ t₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source H (γ t₀)
    have hbaseSet_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
      (trivializationAt E (TangentSpace I) α).open_baseSet
    have hsrc_open : IsOpen {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet} :=
      hbaseSet_open.preimage hγ.continuous
    have hsrc_mem : {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet} ∈ 𝓝 t₀ :=
      hsrc_open.mem_nhds hbase_t₀
    have hVround : ∀ s ∈ {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet},
        (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Vrep s) = V s := by
      intro s hs
      simpa [hVrep_def, chartRepAt_apply] using
        (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
          (R := ℝ) hs (V s)
    have huround : ∀ s ∈ {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet},
        (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (urep s) =
          (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E) := by
      intro s hs
      simpa [hurep_def, chartRepAt_apply] using
        (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
          (R := ℝ) hs ((mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E))
    have hf_eq : f =ᶠ[𝓝 t₀]
        fun s => AlongCurve.chartGramAlongCurve (I := I) g α γ Vrep urep s := by
      filter_upwards [hsrc_mem] with s hs
      have hVs := hVround s hs
      have hus := huround s hs
      have : f s = g.inner (γ s)
          ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Vrep s))
          ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (urep s)) := by
        rw [hf_def]; rw [hVs, hus]
      rw [this, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α (Vrep s) (urep s)]
      rw [AlongCurve.chartGramAlongCurve_def]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      have hinv : (extChartAt I α).symm (chartCurve (I := I) α γ s) = γ s := by
        rw [chartCurve_def]
        refine (extChartAt I α).left_inv ?_
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        rw [TangentBundle.trivializationAt_baseSet] at hs
        exact hs
      rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_def, hinv]
    have hu_hasDerivAt :
        HasDerivAt (chartCurve (I := I) α γ)
          (deriv (chartCurve (I := I) α γ) t₀) t₀ := by
      have hcd : ContDiffAt ℝ ∞ (chartCurve (I := I) α γ) t₀ := by
        have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
            ((extChartAt I α) ∘ γ) t₀ := by
          have hφ : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) (γ t₀) :=
            contMDiffAt_extChartAt (I := I) (x := α) (n := ∞)
          exact hφ.comp t₀ (hγ.contMDiffAt)
        exact contMDiffAt_iff_contDiffAt.mp hmdiff
      exact (hcd.differentiableAt (by simp)).hasDerivAt
    have hmem_int : chartCurve (I := I) α γ t₀ ∈ interior (extChartAt I α).target := by
      have hxsrc : γ t₀ ∈ (extChartAt I α).source := by
        rw [extChartAt_source]; exact mem_chart_source H (γ t₀)
      exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
        (I := I) α ((extChartAt I α).map_source hxsrc)
    have hVrep_hasDerivAt : HasDerivAt Vrep (deriv Vrep t₀) t₀ :=
      ((hVdiff t₀ ht₀).hasDerivAt)
    set U : Set ℝ := γ ⁻¹' (chartAt H α).source with hU_def
    have hU_open : IsOpen U := (chartAt H α).open_source.preimage hγ.continuous
    have ht₀_U : t₀ ∈ U := by
      rw [hU_def, Set.mem_preimage]; exact mem_chart_source H (γ t₀)
    have hU_nhds : U ∈ 𝓝 t₀ := hU_open.mem_nhds ht₀_U
    have hu_cdiffOn : ContDiffOn ℝ ∞ (chartCurve (I := I) α γ) U := by
      have h_comp_mdiff :
          ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ((extChartAt I α) ∘ γ) U := by
        have hφ : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
          contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
        have hγU : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ U := hγ.contMDiffOn
        have hmaps : Set.MapsTo γ U (chartAt H α).source := fun s hs => hs
        exact hφ.comp hγU hmaps
      have hfun : (chartCurve (I := I) α γ) = ((extChartAt I α) ∘ γ) := rfl
      rw [hfun]
      exact contMDiffOn_iff_contDiffOn.mp h_comp_mdiff
    have hurep_eqOn : Set.EqOn urep (deriv (chartCurve (I := I) α γ)) U := by
      intro s hs
      have hs' : γ s ∈ (chartAt H α).source := hs
      rw [hurep_def, chartRepAt_apply]
      rw [MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
        (I := I) (M := M) (γ := γ) hγ α (t := s) hs']
      rfl
    have hurep_eq : urep =ᶠ[𝓝 t₀] deriv (chartCurve (I := I) α γ) :=
      hurep_eqOn.eventuallyEq_of_mem hU_nhds
    have hu_deriv_hasDerivAt :
        HasDerivAt (deriv (chartCurve (I := I) α γ))
          (deriv (deriv (chartCurve (I := I) α γ)) t₀) t₀ := by
      have hderiv_u_cdiffOn :
          ContDiffOn ℝ ∞ (deriv (chartCurve (I := I) α γ)) U :=
        hu_cdiffOn.deriv_of_isOpen hU_open (by exact_mod_cast (le_refl (∞ : WithTop ℕ∞)))
      exact ((hderiv_u_cdiffOn.differentiableOn (by simp) t₀ ht₀_U).differentiableAt
        hU_nhds).hasDerivAt
    have hurep_hasDerivAt : HasDerivAt urep (deriv (deriv (chartCurve (I := I) α γ)) t₀) t₀ :=
      hu_deriv_hasDerivAt.congr_of_eventuallyEq hurep_eq
    have hgram :=
      AlongCurve.chartGramAlongCurve_hasDerivAt_covariant (I := I) g α γ Vrep urep
        (uPrime := fun _ => deriv (chartCurve (I := I) α γ) t₀)
        (Vprime := fun _ => deriv Vrep t₀)
        (Wprime := fun _ => deriv (deriv (chartCurve (I := I) α γ)) t₀)
        hu_hasDerivAt hmem_int hVrep_hasDerivAt hurep_hasDerivAt
    have hcorrV :
        deriv Vrep t₀ +
          chartChristoffelContraction (I := I) g α
            (deriv (chartCurve (I := I) α γ) t₀) (Vrep t₀)
            (chartCurve (I := I) α γ t₀) = 0 := by
      have : chartCovDerivAlong (I := I) g α γ Vrep t₀ = 0 := by
        rw [hα_def, hVrep_def]
        exact (covDerivAlong_eq_zero_iff (I := I) g γ V t₀).mp (hVpar t₀ ht₀)
      rw [chartCovDerivAlong_def] at this
      exact this
    have hcorru :
        deriv (deriv (chartCurve (I := I) α γ)) t₀ +
          chartChristoffelContraction (I := I) g α
            (deriv (chartCurve (I := I) α γ) t₀) (urep t₀)
            (chartCurve (I := I) α γ t₀) = 0 := by
      have hgeoeq := hgeo.hasGeodesicEquationAt ht₀
      have hvel0 :
          covDerivAlong (I := I) g γ
            (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E)) t₀ = 0 :=
        (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt (I := I) g γ t₀ hγ).mpr hgeoeq
      have hchart0 : chartCovDerivAlong (I := I) g α γ urep t₀ = 0 := by
        rw [hα_def, hurep_def]
        exact (covDerivAlong_eq_zero_iff (I := I) g γ
          (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E)) t₀).mp hvel0
      rw [chartCovDerivAlong_def] at hchart0
      rw [hurep_eq.deriv_eq] at hchart0
      exact hchart0
    have hderiv0 : HasDerivAt
        (fun s => AlongCurve.chartGramAlongCurve (I := I) g α γ Vrep urep s) 0 t₀ := by
      convert hgram using 1
      simp only [hcorrV, hcorru]
      simp
    exact hderiv0.congr_of_eventuallyEq hf_eq
  have hcont : ContinuousOn f (Set.Icc 0 L) :=
    fun t ht => ((hlocal t ht).continuousAt).continuousWithinAt
  have hderivWithin : ∀ x ∈ Set.Ico (0 : ℝ) L, HasDerivWithinAt f 0 (Set.Ici x) x := by
    intro x hx
    exact (hlocal x (Set.mem_Icc_of_Ico hx)).hasDerivWithinAt
  have hconst : ∀ x ∈ Set.Icc (0 : ℝ) L, f x = f 0 :=
    constant_of_has_deriv_right_zero hcont hderivWithin
  intro t ht
  have hft := hconst t ht
  rw [hf_def] at hft
  simp only at hft
  rw [hft]
  exact hPerp0

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem velocity_chartRepAt_differentiableAt
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (t : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E)) t) t := by
  classical
  set α : M := γ t with hα_def
  set urep : ℝ → E :=
    chartRepAt (I := I) γ (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E)) t with hurep_def
  set U : Set ℝ := γ ⁻¹' (chartAt H α).source with hU_def
  have hU_open : IsOpen U := (chartAt H α).open_source.preimage hγ.continuous
  have ht_U : t ∈ U := by
    rw [hU_def, Set.mem_preimage]; exact mem_chart_source H (γ t)
  have hU_nhds : U ∈ 𝓝 t := hU_open.mem_nhds ht_U
  have hu_cdiffOn : ContDiffOn ℝ ∞ (chartCurve (I := I) α γ) U := by
    have h_comp_mdiff :
        ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ((extChartAt I α) ∘ γ) U := by
      have hφ : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
        contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
      have hγU : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ U := hγ.contMDiffOn
      have hmaps : Set.MapsTo γ U (chartAt H α).source := fun s hs => hs
      exact hφ.comp hγU hmaps
    have hfun : (chartCurve (I := I) α γ) = ((extChartAt I α) ∘ γ) := rfl
    rw [hfun]
    exact contMDiffOn_iff_contDiffOn.mp h_comp_mdiff
  have hurep_eqOn : Set.EqOn urep (deriv (chartCurve (I := I) α γ)) U := by
    intro s hs
    have hs' : γ s ∈ (chartAt H α).source := hs
    rw [hurep_def, chartRepAt_apply]
    rw [MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
      (I := I) (M := M) (γ := γ) hγ α (t := s) hs']
    rfl
  have hurep_eq : urep =ᶠ[𝓝 t] deriv (chartCurve (I := I) α γ) :=
    hurep_eqOn.eventuallyEq_of_mem hU_nhds
  have hderiv_u_cdiffOn :
      ContDiffOn ℝ ∞ (deriv (chartCurve (I := I) α γ)) U :=
    hu_cdiffOn.deriv_of_isOpen hU_open (by exact_mod_cast (le_refl (∞ : WithTop ℕ∞)))
  have hderiv_u_diff : DifferentiableAt ℝ (deriv (chartCurve (I := I) α γ)) t :=
    (hderiv_u_cdiffOn.differentiableOn (by simp) t ht_U).differentiableAt hU_nhds
  exact hderiv_u_diff.congr_of_eventuallyEq hurep_eq

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [InnerProductSpace ℝ E] in
theorem exists_parallel_perp_frame [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {L : ℝ} (hL : 0 < L)
    (hgeo : IsGeodesicOn (I := I) g γ (Set.Icc 0 L))
    (hUnit0 : g.inner (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 1) :
    ∃ e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ,
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (e i).toFun t) t) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        covDerivAlong (I := I) g γ (e i).toFun t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) ((e i).toFun t) ((e j).toFun t) =
          if i = j then 1 else 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
        g.inner (γ t) ((e i).toFun t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 0) ∧
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
        (fun t => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (γ t) ((e i).toFun t))) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set u₀ : E := (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) with hu₀_def
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (γ 0) with hB_def
  have hBsymm : ∀ x y : E, B x y = B y x := fun x y => g.symm (γ 0) x y
  have hBpos : ∀ x : E, x ≠ 0 → 0 < B x x := fun x hx => g.pos (γ 0) x hx
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_refl _, hL.le⟩
  have hu₀_unit : B u₀ u₀ = 1 := hUnit0
  have hu₀_ne : u₀ ≠ 0 := by
    intro h; rw [h] at hu₀_unit; simp at hu₀_unit
  set φ : E →ₗ[ℝ] ℝ := (B u₀).toLinearMap with hφ_def
  set W : Submodule ℝ E := LinearMap.ker φ with hW_def
  have hφ_u₀ : φ u₀ = 1 := hu₀_unit
  have hφ_surj : Function.Surjective φ := by
    intro c
    refine ⟨c • u₀, ?_⟩
    rw [map_smul, hφ_u₀, smul_eq_mul, mul_one]
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ_surj
  have hfr_range : Module.finrank ℝ ↥(LinearMap.range φ) = 1 := by
    rw [hrange]; simp
  have hfinrankW : Module.finrank ℝ ↥W = Module.finrank ℝ E - 1 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker φ
    rw [hfr_range] at hsum
    have : Module.finrank ℝ ↥W = Module.finrank ℝ ↥(LinearMap.ker φ) := rfl
    rw [this]; omega
  letI : Module.Finite ℝ ↥W := inferInstance
  set bW : Module.Basis (Fin (Module.finrank ℝ E - 1)) ℝ ↥W :=
    Module.finBasisOfFinrankEq ℝ ↥W hfinrankW with hbW_def
  set vfam : Fin (Module.finrank ℝ E - 1) → E := fun i => (bW i : E) with hvfam_def
  have hvfam_mem : ∀ i, vfam i ∈ W := fun i => (bW i).2
  have hvfam_LI : LinearIndependent ℝ vfam := by
    have hbWLI : LinearIndependent ℝ (fun i => bW i) := bW.linearIndependent
    have := hbWLI.map' (W.subtype) (Submodule.ker_subtype W)
    exact this
  set seed : Fin (Module.finrank ℝ E - 1) → E :=
    fun i => PerpFrameAux.bGramSchmidt B vfam i with hseed_def
  have hseed_ON : ∀ i j, B (seed i) (seed j) = if i = j then 1 else 0 :=
    fun i j => PerpFrameAux.bGramSchmidt_orthonormal B hBsymm hBpos vfam hvfam_LI i j
  have hseed_mem : ∀ i, seed i ∈ W :=
    fun i => PerpFrameAux.bGramSchmidt_mem B vfam W hvfam_mem i
  have hseed_perp : ∀ i, B (seed i) u₀ = 0 := by
    intro i
    have hker : φ (seed i) = 0 := (LinearMap.mem_ker).mp (hseed_mem i)
    have : B u₀ (seed i) = 0 := hker
    rw [hBsymm (seed i) u₀]; exact this
  have htransport : ∀ i, ∃ (δ : ℝ) (_ : 0 < δ) (V : ∀ t, TangentSpace I (γ t)),
      V 0 = seed i ∧
      (∀ t ∈ Set.Ioo (-δ) (L + δ), DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) ∧
      (∀ t ∈ Set.Ioo (-δ) (L + δ), covDerivAlong (I := I) g γ V t = 0) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
        (fun t => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t))
        (Set.Ioo (-δ) (L + δ)) :=
    fun i => parallelTransport_section_contMDiffOn_Ioo (I := I) g γ hγ hL (seed i)
  choose δ hδ_pos Vfun hV0 hVdiff_Ioo hVpar_Ioo hVbundle_Ioo using htransport
  have hcutoff : ∀ i, ∃ χ : ℝ → ℝ, ContDiff ℝ (∞ : WithTop ℕ∞) χ ∧
      Set.EqOn χ 1 (Set.Icc 0 L) ∧
      tsupport χ ⊆ Set.Ioo (-(δ i)) (L + δ i) ∧ ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 :=
    fun i => exists_cutoff_one_on_Icc_supported_Ioo (hδ_pos i)
  choose χ hχ_cd hχ_one hχ_tsupp hχ_Icc using hcutoff
  have he_eq_on : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L, χ i t • Vfun i t = Vfun i t := by
    intro i t ht
    rw [hχ_one i ht]; simp
  have hsub : ∀ i, Set.Icc (0 : ℝ) L ⊆ Set.Ioo (-(δ i)) (L + δ i) := by
    intro i t ht
    exact ⟨by linarith [ht.1, hδ_pos i], by linarith [ht.2, hδ_pos i]⟩
  have hVdiff : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (Vfun i) t) t :=
    fun i t ht => hVdiff_Ioo i t (hsub i ht)
  have hVpar : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g γ (Vfun i) t = 0 :=
    fun i t ht => hVpar_Ioo i t (hsub i ht)
  have hchartRep_smul : ∀ i (t : ℝ),
      chartRepAt (I := I) γ (fun s => χ i s • Vfun i s) t =
        fun s => χ i s • chartRepAt (I := I) γ (Vfun i) t s := by
    intro i t
    funext s
    rw [chartRepAt_apply, chartRepAt_apply, map_smul]
  have hχ_deriv_zero : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L, deriv (χ i) t = 0 := by
    intro i t ht
    have hmax : IsLocalMax (χ i) t := by
      have hle : ∀ s, χ i s ≤ χ i t := by
        intro s
        rw [hχ_one i ht]
        exact (hχ_Icc i s).2
      exact Filter.Eventually.of_forall hle
    exact hmax.deriv_eq_zero
  have hvel_par : ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g γ
        (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E)) t = 0 := by
    intro t ht
    exact (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt (I := I) g γ t hγ).mpr
      (hgeo.hasGeodesicEquationAt ht)
  have hvel_diff : ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E)) t) t :=
    fun t _ => velocity_chartRepAt_differentiableAt (I := I) γ hγ t
  have hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 1 := by
    intro t ht
    have hconst :=
      parallel_transport_preserves_inner_product (I := I) g γ (N := 2) le_rfl
        (hγ.of_le (by exact_mod_cast le_top)) hL.le
        (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E))
        (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E))
        hvel_diff hvel_diff hvel_par hvel_par t ht
    rw [hconst]; exact hUnit0
  refine ⟨fun i => ⟨fun t => χ i t • Vfun i t⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i t ht
    change DifferentiableAt ℝ (chartRepAt (I := I) γ (fun s => χ i s • Vfun i s) t) t
    rw [hchartRep_smul i t]
    exact (((hχ_cd i).differentiable (by simp)).differentiableAt).smul (hVdiff i t ht)
  · intro i t ht
    change covDerivAlong (I := I) g γ (fun s => χ i s • Vfun i s) t = 0
    rw [covDerivAlong_smulFun (I := I) g γ (χ i) (Vfun i) t
      (((hχ_cd i).differentiable (by simp)).differentiableAt) (hVdiff i t ht)]
    rw [hχ_deriv_zero i t ht, hχ_one i ht, hVpar i t ht]
    simp
  · intro t ht i j
    change g.inner (γ t) (χ i t • Vfun i t) (χ j t • Vfun j t) = if i = j then 1 else 0
    have hχi : χ i t = 1 := by have := hχ_one i ht; simpa using this
    have hχj : χ j t = 1 := by have := hχ_one j ht; simpa using this
    rw [hχi, hχj, one_smul, one_smul]
    have hconst :=
      parallel_transport_preserves_inner_product (I := I) g γ (N := 2) le_rfl
        (hγ.of_le (by exact_mod_cast le_top)) hL.le
        (Vfun i) (Vfun j) (hVdiff i) (hVdiff j) (hVpar i) (hVpar j) t ht
    rw [hconst, hV0 i, hV0 j]
    exact hseed_ON i j
  · intro t ht i
    change g.inner (γ t) (χ i t • Vfun i t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 0
    have hχi : χ i t = 1 := by have := hχ_one i ht; simpa using this
    rw [hχi, one_smul]
    have hperp :=
      perp_to_velocity_preserved_on (I := I) g γ hγ hL hgeo (Vfun i)
        (hVdiff i) (hVpar i)
        (by rw [hV0 i]; exact hseed_perp i)
        t ht
    exact hperp
  · intro i
    set Ω : Set ℝ := Set.Ioo (-(δ i)) (L + δ i) with hΩ_def
    have hΩ_open : IsOpen Ω := isOpen_Ioo
    have hsupp_sub : tsupport (χ i) ⊆ Ω := hχ_tsupp i
    intro t₀
    by_cases ht₀ : t₀ ∈ Ω
    · have hχ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) (χ i) := by
        rw [contMDiff_iff_contDiff]; exact hχ_cd i
      have hbundleAt : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent ∞
          (fun t => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (γ t) (χ i t • Vfun i t)) Ω t₀ := by
        have htransportAt : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent ∞
            (fun t => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
              (γ t) (Vfun i t)) Ω t₀ := hVbundle_Ioo i t₀ ht₀
        rw [Bundle.contMDiffWithinAt_totalSpace] at htransportAt ⊢
        refine ⟨htransportAt.1, ?_⟩
        have hVfib := htransportAt.2
        have hsmul := (hχ_smooth t₀).contMDiffWithinAt.smul hVfib
        refine hsmul.congr_of_eventuallyEq ?_ ?_
        · have hbase : ∀ᶠ t in 𝓝[Ω] t₀,
              γ t ∈ (trivializationAt E (TangentSpace I) (γ t₀)).baseSet := by
            have hmem : (γ t₀) ∈ (trivializationAt E (TangentSpace I) (γ t₀)).baseSet :=
              FiberBundle.mem_baseSet_trivializationAt' (γ t₀)
            have hfull : γ ⁻¹' (trivializationAt E (TangentSpace I) (γ t₀)).baseSet ∈ 𝓝 t₀ :=
              (hγ t₀).continuousAt.preimage_mem_nhds
                ((trivializationAt E (TangentSpace I) (γ t₀)).open_baseSet.mem_nhds hmem)
            exact mem_nhdsWithin_of_mem_nhds hfull
          filter_upwards [hbase] with t ht
          simp only [TotalSpace.mk']
          rw [(trivializationAt E (TangentSpace I) (γ t₀)).apply_eq_prod_continuousLinearEquivAt
                ℝ (γ t) ht,
              (trivializationAt E (TangentSpace I) (γ t₀)).apply_eq_prod_continuousLinearEquivAt
                ℝ (γ t) ht]
          exact map_smul _ _ _
        · have hmem : (γ t₀) ∈ (trivializationAt E (TangentSpace I) (γ t₀)).baseSet :=
            FiberBundle.mem_baseSet_trivializationAt' (γ t₀)
          simp only [TotalSpace.mk']
          rw [(trivializationAt E (TangentSpace I) (γ t₀)).apply_eq_prod_continuousLinearEquivAt
                ℝ (γ t₀) hmem,
              (trivializationAt E (TangentSpace I) (γ t₀)).apply_eq_prod_continuousLinearEquivAt
                ℝ (γ t₀) hmem]
          exact map_smul _ _ _
      exact (hbundleAt.contMDiffAt (hΩ_open.mem_nhds ht₀))
    · have ht₀_notsupp : t₀ ∉ tsupport (χ i) := fun h => ht₀ (hsupp_sub h)
      have hcompl_open : IsOpen (tsupport (χ i))ᶜ := (isClosed_tsupport (χ i)).isOpen_compl
      have hcompl_nhds : (tsupport (χ i))ᶜ ∈ 𝓝 t₀ := hcompl_open.mem_nhds ht₀_notsupp
      have hzero_eq : (fun t => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (γ t) (χ i t • Vfun i t))
          =ᶠ[𝓝 t₀]
          (fun t => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) 0) := by
        filter_upwards [hcompl_nhds] with t ht
        have hχt : χ i t = 0 := image_eq_zero_of_notMem_tsupport ht
        rw [hχt, zero_smul]
      refine ContMDiffAt.congr_of_eventuallyEq ?_ hzero_eq
      have hzs : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞
          (fun t => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) 0) t₀ := by
        have := (Bundle.contMDiffAt_zeroSection (F := E) ℝ
          (E := (TangentSpace I : M → Type _)) (n := ∞) (x := γ t₀)).comp t₀ (hγ t₀)
        exact this
      exact hzs

end SmoothPerpFrame

end DifferentialGeometry.Geometry.Riemannian

end
