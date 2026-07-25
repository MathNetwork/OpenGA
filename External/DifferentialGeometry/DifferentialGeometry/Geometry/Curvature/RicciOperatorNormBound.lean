import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciControlsRm
import DifferentialGeometry.Geometry.Curvature.QuadraticFormBound
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricContinuity

set_option autoImplicit false















noncomputable section

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Integral.Connection Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {x : M}




theorem exists_gOrthonormalBasis (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ basis :
        Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real (TangentSpace I x),
      ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0 := by
  classical
  let D := (tangentMetricData_gen (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  refine ⟨ob.toBasis, ?_⟩
  intro i j
  have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
    MetricFiberData.toCore_inner D (ob i) (ob j)
  have hob := ob.inner_eq_ite i j
  change g.inner x (ob.toBasis i) (ob.toBasis j) = if i = j then (1 : Real) else 0
  rw [← TangentMetricData_gen.inner_eq_gen (tangentMetricData_gen (I := I) g x)
    (ob.toBasis i) (ob.toBasis j)]
  change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
  rw [← hinner]
  exact hob






theorem ricci_unitSphere_le_of_componentBound
    (g : SmoothRiemannianMetric I M) {x : M}
    (Ric : Tensor02At (I := I) (M := M) x)
    {n : ℕ} (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    {R : Real} (hR : 0 ≤ R)
    (hcomp : ∀ i j, |Ric (vec2 (I := I) (basis i) (basis j))| ≤ R)
    (u : TangentSpace I x) (hu : g.inner x u u = 1) :
    |Ric (vec2 (I := I) u u)| ≤ (n : Real) * R := by
  classical
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (fun a k => if a = k then (1 : Real) else 0) :=
    metricInverseInBasis_of_orthonormal (I := I) g basis hON
  have hrepr : ∀ i, basis.repr u i = g.inner x u (basis i) := by
    intro i
    rw [basis_repr_eq_sum_inv_inner (I := I) g x basis _ hinv u i]
    simp
  have hgexp : g.inner x u u = ∑ i, (basis.repr u i) ^ 2 := by
    calc g.inner x u u
        = g.inner x u (∑ i, basis.repr u i • basis i) := by rw [basis.sum_repr u]
      _ = ∑ i, basis.repr u i * g.inner x u (basis i) := by
            rw [map_sum]; simp_rw [map_smul, smul_eq_mul]
      _ = ∑ i, (basis.repr u i) ^ 2 := by
            apply Finset.sum_congr rfl; intro i _; rw [← hrepr i]; ring
  have hricexp : Ric (vec2 (I := I) u u)
      = ∑ i, ∑ j, basis.repr u i * basis.repr u j
          * Ric (vec2 (I := I) (basis i) (basis j)) := by
    rw [tensor0S_apply_eq_sum (I := I) basis Ric (vec2 (I := I) u u), sum_fin_two_fun]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    have hc :
        component0S (I := I) basis Ric (fun a : Fin 2 => if a = 0 then i else j)
          = Ric (vec2 (I := I) (basis i) (basis j)) := by
      rw [component0S_apply]
      congr 1; funext a; fin_cases a <;> simp [vec2]
    have hp :
        (∏ a : Fin 2, basis.coord ((fun a : Fin 2 => if a = 0 then i else j) a)
            ((vec2 (I := I) u u) a))
          = basis.repr u i * basis.repr u j := by
      rw [Fin.prod_univ_two]
      simp [vec2, Module.Basis.coord_apply]
    rw [hc, hp]; ring
  rw [hricexp]
  calc
    |∑ i, ∑ j, basis.repr u i * basis.repr u j
        * Ric (vec2 (I := I) (basis i) (basis j))|
      ≤ ∑ i, ∑ j, |basis.repr u i * basis.repr u j
          * Ric (vec2 (I := I) (basis i) (basis j))| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        apply Finset.sum_le_sum; intro i _; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |basis.repr u i| * |basis.repr u j| * R := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hcomp i j)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = R * (∑ i, |basis.repr u i|) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ R * ((n : Real) * ∑ i, (basis.repr u i) ^ 2) := by
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
          (fun i => |basis.repr u i|) (fun _ => (1 : Real))
        simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, sq_abs] at hcs
        have hcs' : (∑ i, |basis.repr u i|) ^ 2
            ≤ (n : Real) * ∑ i, (basis.repr u i) ^ 2 := by rw [mul_comm]; exact hcs
        exact mul_le_mul_of_nonneg_left hcs' hR
    _ = R * ((n : Real) * g.inner x u u) := by rw [← hgexp]
    _ = (n : Real) * R := by rw [hu]; ring




theorem abs_component0S_le_sqrt_normSq0S
    (g : SmoothRiemannianMetric I M) {x : M} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℕ} (basis : Module.Basis ι Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := ι)))
    (A : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots₀ : Fin s → ι) :
    |component0S (I := I) basis A slots₀| ≤ Real.sqrt (normSq0S (I := I) g x s A) := by
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv A]
  exact Finset.single_le_sum (f := fun slots => (component0S (I := I) basis A slots) ^ 2)
    (fun slots _ => sq_nonneg _) (Finset.mem_univ slots₀)



theorem ricciComp_le_rmNorm
    (g : SmoothRiemannianMetric I M) {x : M}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : Module.Basis ι Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := ι)))
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (htrace : ∀ i j, Ric (vec2 (I := I) (basis i) (basis j)) =
      ∑ a, Rm04 (vec4 (I := I) (basis a) (basis i) (basis j) (basis a)))
    (i j : ι) :
    |Ric (vec2 (I := I) (basis i) (basis j))| ≤
      (Fintype.card ι : Real) * Real.sqrt (normSq0S (I := I) g x 4 Rm04) := by
  rw [htrace i j]
  calc
    |∑ a, Rm04 (vec4 (I := I) (basis a) (basis i) (basis j) (basis a))|
        ≤ ∑ a, |Rm04 (vec4 (I := I) (basis a) (basis i) (basis j) (basis a))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : ι, Real.sqrt (normSq0S (I := I) g x 4 Rm04) := by
      apply Finset.sum_le_sum
      intro a _
      have hcomp := abs_component0S_le_sqrt_normSq0S g basis hinv Rm04 (slots4 a i j a)
      have heq : component0S (I := I) basis Rm04 (slots4 a i j a) =
          Rm04 (vec4 (I := I) (basis a) (basis i) (basis j) (basis a)) :=
        rm04CompAt_apply (I := I) basis Rm04 a i j a
      rwa [heq] at hcomp
    _ = (Fintype.card ι : Real) * Real.sqrt (normSq0S (I := I) g x 4 Rm04) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]




theorem metricRicciComp_le
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) {x : M}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : Module.Basis ι Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (i j : ι) :
    |metricRicciAt (I := I) (M := M) g x (vec2 (I := I) (basis i) (basis j))| ≤
      (Fintype.card ι : Real) *
        Real.sqrt (normSq0S (I := I) g x 4 (metricRm04At (I := I) (M := M) g x)) := by
  classical
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := ι)) :=
    metricInverseInBasis_of_orthonormal (I := I) g basis hON
  let D := metricCurvData (I := I) (M := M) g
  have hLower : Rm04LowersRm13At (I := I) g x
      (metricRm13 (I := I) (M := M) g x)
      (metricRm04 (I := I) (M := M) g x) :=
    rm04LowersRm13At_of_realizes
      (I := I) g (metricCov (I := I) (M := M) g)
      (metricRm13 (I := I) (M := M) g)
      (metricRm04 (I := I) (M := M) g)
      D.h_rm13 D.h_rm04 x
  have htrace : ∀ a b,
      metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis a) (basis b)) =
        ∑ c, metricRm04At (I := I) (M := M) g x
          (vec4 (I := I) (basis c) (basis a) (basis b) (basis c)) := by
    intro a b
    simpa using
      (ricci_diag_eq_sum_rm04_diag_of_orthonormal
        (I := I) (M := M) g basis
        (metricRicci (I := I) (M := M) g)
        (metricRm13 (I := I) (M := M) g)
        (metricRm04 (I := I) (M := M) g)
        D.h_ricci13 hLower hON a b)
  exact ricciComp_le_rmNorm (I := I) g basis hinv
    (metricRicciAt (I := I) (M := M) g x)
    (metricRm04At (I := I) (M := M) g x) htrace i j





theorem ricci_unitQuad_le_of_trace
    (g : SmoothRiemannianMetric I M) {x : M} {n : ℕ}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Fin n)))
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (htrace : ∀ i j, Ric (vec2 (I := I) (basis i) (basis j))
        = ∑ a, Rm04 (vec4 (I := I) (basis a) (basis i) (basis j) (basis a)))
    (u : TangentSpace I x) (hu : g.inner x u u = 1) :
    |Ric (vec2 (I := I) u u)| ≤ (n : Real) ^ 2 * Real.sqrt (normSq0S (I := I) g x 4 Rm04) := by
  set B := Real.sqrt (normSq0S (I := I) g x 4 Rm04) with hBdef
  have hBnn : 0 ≤ B := Real.sqrt_nonneg _
  have hR : 0 ≤ (n : Real) * B := mul_nonneg (Nat.cast_nonneg n) hBnn
  have hcomp : ∀ i j, |Ric (vec2 (I := I) (basis i) (basis j))| ≤ (n : Real) * B := by
    intro i j
    rw [htrace i j]
    calc |∑ a, Rm04 (vec4 (I := I) (basis a) (basis i) (basis j) (basis a))|
        ≤ ∑ a, |Rm04 (vec4 (I := I) (basis a) (basis i) (basis j) (basis a))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin n, B := by
          apply Finset.sum_le_sum
          intro a _
          have h3b := abs_component0S_le_sqrt_normSq0S g basis hinv Rm04 (slots4 a i j a)
          have heq : component0S (I := I) basis Rm04 (slots4 a i j a)
              = Rm04 (vec4 (I := I) (basis a) (basis i) (basis j) (basis a)) :=
            rm04CompAt_apply (I := I) basis Rm04 a i j a
          rwa [heq] at h3b
      _ = (n : Real) * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmain := ricci_unitSphere_le_of_componentBound g Ric basis hON hR hcomp u hu
  calc |Ric (vec2 (I := I) u u)| ≤ (n : Real) * ((n : Real) * B) := hmain
    _ = (n : Real) ^ 2 * B := by ring






theorem tensor02_quadForm_abs_le_normSq0S
    (g : SmoothRiemannianMetric I M) {x : M}
    (T : Tensor02At (I := I) (M := M) x) (v : TangentSpace I x) :
    |T (vec2 (I := I) v v)|
      ≤ (Module.finrank Real (TangentSpace I x) : Real)
          * Real.sqrt (normSq0S (I := I) g x 2 T) * g.inner x v v := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  have hunit : ∀ u : TangentSpace I x, g.inner x u u = 1 →
      |T (vec2 (I := I) u u)|
        ≤ (Module.finrank Real (TangentSpace I x) : Real)
            * Real.sqrt (normSq0S (I := I) g x 2 T) := by
    intro u hu
    refine ricci_unitSphere_le_of_componentBound g T basis hON (Real.sqrt_nonneg _) ?_ u hu
    intro i j
    have hc := abs_component0S_le_sqrt_normSq0S (I := I) g basis hinv T (slots2 i j)
    have heq : component0S (I := I) basis T (slots2 i j)
        = T (vec2 (I := I) (basis i) (basis j)) :=
      ricciCompAt_apply (I := I) basis T i j
    rwa [heq] at hc
  have hRay := tensor02_quadForm_abs_le_of_unit_bound g T hunit v
  calc |T (vec2 (I := I) v v)|
      ≤ ((Module.finrank Real (TangentSpace I x) : Real)
          * Real.sqrt (normSq0S (I := I) g x 2 T)) * g.inner x v v := hRay
    _ = (Module.finrank Real (TangentSpace I x) : Real)
          * Real.sqrt (normSq0S (I := I) g x 2 T) * g.inner x v v := by ring



theorem exists_rm04_bound [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    ∃ K : Real, 0 ≤ K ∧ ∀ x : M,
      normSq0S (I := I) g x 4 (metricRm04 (I := I) (M := M) g x) ≤ K := by
  let f : M → Real := fun x =>
    normSq0S (I := I) g x 4 (metricRm04 (I := I) (M := M) g x)
  have hf : Continuous f :=
    Tensor0SBundle.normSq0S_cont (I := I) g (metricRm04 (I := I) (M := M) g)
  have hcompact : IsCompact (Set.range f) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image hf
  obtain ⟨K, hK⟩ := hcompact.bddAbove
  refine ⟨max K 0, le_max_right _ _, fun x => ?_⟩
  exact (hK (Set.mem_range_self x)).trans (le_max_left _ _)



theorem exists_ricci_bound
    [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 ≤ C ∧ ∀ (x : M) (v : TangentSpace I x),
      |ricciTensor (I := I) g x v v| ≤ C * g.inner x v v := by
  classical
  obtain ⟨K, hK_nonneg, hK⟩ := exists_rm04_bound (I := I) (M := M) g
  let C : Real := (Module.finrank Real E : Real) ^ 2 * Real.sqrt K
  have hC_nonneg : 0 ≤ C :=
    mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨C, hC_nonneg, fun x v => ?_⟩
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  let D := metricCurvData (I := I) (M := M) g
  have hLower :
      Rm04LowersRm13At (I := I) g x
        (metricRm13 (I := I) (M := M) g x)
        (metricRm04 (I := I) (M := M) g x) :=
    rm04LowersRm13At_of_realizes
      (I := I) g (metricCov (I := I) (M := M) g)
      (metricRm13 (I := I) (M := M) g)
      (metricRm04 (I := I) (M := M) g)
      D.h_rm13 D.h_rm04 x
  have htrace : ∀ i j,
      metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)) =
        ∑ a, metricRm04At (I := I) (M := M) g x
          (vec4 (I := I) (basis a) (basis i) (basis j) (basis a)) := by
    intro i j
    simpa using
      (ricci_diag_eq_sum_rm04_diag_of_orthonormal
        (I := I) (M := M) g basis
        (metricRicci (I := I) (M := M) g)
        (metricRm13 (I := I) (M := M) g)
        (metricRm04 (I := I) (M := M) g)
        D.h_ricci13 hLower hON i j)
  have hunit : ∀ u : TangentSpace I x, g.inner x u u = 1 →
      |metricRicciAt (I := I) (M := M) g x (vec2 (I := I) u u)| ≤ C := by
    intro u hu
    have hraw := ricci_unitQuad_le_of_trace (I := I) g basis hON hinv
      (metricRicciAt (I := I) (M := M) g x)
      (metricRm04At (I := I) (M := M) g x) htrace u hu
    calc
      _ ≤ (Module.finrank Real (TangentSpace I x) : Real) ^ 2 *
          Real.sqrt (normSq0S (I := I) g x 4
            (metricRm04At (I := I) (M := M) g x)) := hraw
      _ ≤ (Module.finrank Real (TangentSpace I x) : Real) ^ 2 *
          Real.sqrt K := by
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hK x)) (sq_nonneg _)
      _ = C := by rfl
  have hall := tensor02_quadForm_abs_le_of_unit_bound
    (I := I) g (metricRicciAt (I := I) (M := M) g x) hunit v
  rw [metricRicciAt_apply_eq_ricciTensor (I := I) g x v v] at hall
  exact hall

end DifferentialGeometry.Integral.Connection
