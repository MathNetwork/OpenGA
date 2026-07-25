import DifferentialGeometry.Geometry.Comparison.Volume.RadialGronwall
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue










noncomputable section

open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Integral.Measure

section MatrixBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]








lemma sqrt_det_le_of_entry_bound
    {A : Matrix ι ι ℝ} {C : ℝ}
    (hdet_nonneg : 0 ≤ A.det)
    (hentry : ∀ i j, |A i j| ≤ C) :
    Real.sqrt A.det ≤
      Real.sqrt (((Fintype.card ι).factorial : ℝ) * C ^ Fintype.card ι) := by
  have hdet_abs :
      AbsoluteValue.abs A.det ≤
        (Fintype.card ι).factorial • C ^ Fintype.card ι :=
    Matrix.det_le (abv := AbsoluteValue.abs) (x := C) hentry
  have hdet_le :
      A.det ≤ ((Fintype.card ι).factorial : ℝ) * C ^ Fintype.card ι := by
    rw [AbsoluteValue.abs_apply, abs_of_nonneg hdet_nonneg, nsmul_eq_mul] at hdet_abs
    exact hdet_abs
  exact Real.sqrt_le_sqrt hdet_le






lemma sqrt_pow_le_sqrt_det
    {A : Matrix ι ι ℝ} {a : ℝ}
    (hA : A.PosSemidef)
    (ha : 0 ≤ a)
    (heig : ∀ i, a ≤ hA.isHermitian.eigenvalues i) :
    Real.sqrt (a ^ Fintype.card ι) ≤ Real.sqrt A.det := by
  have hprod :
      a ^ Fintype.card ι ≤ ∏ i, hA.isHermitian.eigenvalues i := by
    have hprod_const :
        (∏ _ : ι, a) ≤ ∏ i, hA.isHermitian.eigenvalues i :=
      Finset.prod_le_prod (fun _ _ => ha) (fun i _ => heig i)
    simpa using hprod_const
  have hdet : a ^ Fintype.card ι ≤ A.det := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues]
    exact hprod
  exact Real.sqrt_le_sqrt hdet



lemma eigenvalues_ge_of_rayleigh
    {A : Matrix ι ι ℝ} {a : ℝ}
    (hA : A.IsHermitian)
    (hray : ∀ v : EuclideanSpace ℝ ι, ‖v‖ = 1 →
      a ≤ RCLike.re (dotProduct (star ⇑v) (Matrix.mulVec A ⇑v))) :
    ∀ i, a ≤ hA.eigenvalues i := by
  intro i
  rw [hA.eigenvalues_eq i]
  exact hray (hA.eigenvectorBasis i) (hA.eigenvectorBasis.norm_eq_one i)



lemma sqrt_pow_le_sqrt_det_of_rayleigh
    {A : Matrix ι ι ℝ} {a : ℝ}
    (hA : A.PosSemidef)
    (ha : 0 ≤ a)
    (hray : ∀ v : EuclideanSpace ℝ ι, ‖v‖ = 1 →
      a ≤ RCLike.re (dotProduct (star ⇑v) (Matrix.mulVec A ⇑v))) :
    Real.sqrt (a ^ Fintype.card ι) ≤ Real.sqrt A.det :=
  sqrt_pow_le_sqrt_det (A := A) hA ha
    (eigenvalues_ge_of_rayleigh hA.isHermitian hray)

end MatrixBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section NormalChart

variable [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma g_inner_add_left
    (g : SmoothRiemannianMetric I M) (x : M) (v w y : TangentSpace I x) :
    g.inner x (v + w) y = g.inner x v y + g.inner x w y := by
  rw [map_add (g.inner x), ContinuousLinearMap.add_apply]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma g_inner_add_right
    (g : SmoothRiemannianMetric I M) (x : M) (v y w : TangentSpace I x) :
    g.inner x v (y + w) = g.inner x v y + g.inner x v w :=
  ContinuousLinearMap.map_add (g.inner x v) y w

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma g_inner_smul_left
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ) (v y : TangentSpace I x) :
    g.inner x (c • v) y = c * g.inner x v y := by
  rw [map_smul (g.inner x), ContinuousLinearMap.smul_apply, smul_eq_mul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma g_inner_smul_right
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) (c : ℝ)
    (y : TangentSpace I x) :
    g.inner x v (c • y) = c * g.inner x v y := by
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma g_inner_zero_left
    (g : SmoothRiemannianMetric I M) (x : M) (y : TangentSpace I x) :
    g.inner x (0 : TangentSpace I x) y = 0 := by
  rw [map_zero, ContinuousLinearMap.zero_apply]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma g_inner_smul_add_diag
    (g : SmoothRiemannianMetric I M) (x : M) (t : ℝ) (v w : TangentSpace I x) :
    g.inner x (t • v + w) (t • v + w) =
      t * t * g.inner x v v + 2 * t * g.inner x v w + g.inner x w w := by
  rw [g_inner_add_left g x (t • v) w (t • v + w),
    g_inner_add_right g x (t • v) (t • v) w,
    g_inner_add_right g x w (t • v) w]
  rw [g_inner_smul_left g x t v (t • v), g_inner_smul_right g x v t v,
    g_inner_smul_left g x t v w, g_inner_smul_right g x w t v]
  have hsymm : g.inner x w v = g.inner x v w := g.symm x w v
  rw [hsymm]
  ring





omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma riemannian_inner_cauchy_schwarz
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    |g.inner x v w| ≤
      Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  set a := g.inner x v v
  set b := g.inner x w w
  set c := g.inner x v w
  have ha_nn : 0 ≤ a := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · simp [a, hv0]
    · exact (g.pos x v hv0).le
  have hb_nn : 0 ≤ b := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · simp [b, hw0]
    · exact (g.pos x w hw0).le
  have hsdiag : ∀ t : ℝ,
      g.inner x (t • v + w) (t • v + w) =
        t * t * a + 2 * t * c + b := by
    intro t
    rw [g_inner_smul_add_diag g x t v w]
  have hquad : ∀ t : ℝ, 0 ≤ t * t * a + 2 * t * c + b := by
    intro t
    have hpos : 0 ≤ g.inner x (t • v + w) (t • v + w) := by
      rcases eq_or_ne (t • v + w) 0 with hz | hnz
      · rw [hz, g_inner_zero_left g x (0 : TangentSpace I x)]
      · exact (g.pos x _ hnz).le
    rw [hsdiag t] at hpos
    exact hpos
  have hCS_sq : c ^ 2 ≤ a * b := by
    rcases lt_or_eq_of_le ha_nn with ha_pos | ha_zero
    · have hroot := hquad (-c / a)
      have hsimp : -c / a * (-c / a) * a + 2 * (-c / a) * c + b =
          b - c ^ 2 / a := by
        field_simp [ne_of_gt ha_pos]
        ring
      rw [hsimp] at hroot
      have hcsa : c ^ 2 / a ≤ b := by linarith
      have h1 : c ^ 2 = a * (c ^ 2 / a) := by
        field_simp [ne_of_gt ha_pos]
      rw [h1]
      exact mul_le_mul_of_nonneg_left hcsa ha_nn
    · have ha_eq : a = 0 := ha_zero.symm
      have hv_zero : v = 0 := by
        by_contra hne
        have hpos : 0 < g.inner x v v := g.pos x v hne
        rw [show g.inner x v v = a from rfl, ha_eq] at hpos
        exact lt_irrefl 0 hpos
      have hc_eq : c = 0 := by
        change g.inner x v w = 0
        rw [hv_zero]
        exact g_inner_zero_left g x w
      rw [hc_eq, ha_eq]
      simp
  have hC : |c| ≤ Real.sqrt (a * b) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hCS_sq
  have hsqrt_mul : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b :=
    Real.sqrt_mul ha_nn b
  rw [hsqrt_mul] at hC
  exact hC



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma radialEntry_le_of_length_bound
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {B : ℝ}
    (hB : 0 ≤ B)
    (hJ : ∀ i : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1)) ≤ B) :
    ∀ i j : Fin (Module.finrank ℝ E),
      |radialJacobiGram (I := I) g p x i j| ≤ B * B := by
  intro i j
  have hcs := riemannian_inner_cauchy_schwarz (I := I) g
    (expMap (I := I) g p (show TangentSpace I p from x))
    (radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1)
    (radialJacobiField (I := I) g p x ((chartModelBasis E) j) 1)
  rw [radialJacobiGram_apply]
  exact hcs.trans (mul_le_mul (hJ i) (hJ j) (Real.sqrt_nonneg _) hB)




omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma radialJacobiGram_quadratic
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (v : Fin (Module.finrank ℝ E) → ℝ) :
    dotProduct v (Matrix.mulVec (radialJacobiGram (I := I) g p x) v) =
      g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (∑ i, v i • radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1)
        (∑ i, v i • radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1) := by
  let q : M := expMap (I := I) g p (show TangentSpace I p from x)
  let J : Fin (Module.finrank ℝ E) → TangentSpace I q :=
    fun i => radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1
  have hleft :
      dotProduct v (Matrix.mulVec (radialJacobiGram (I := I) g p x) v) =
        ∑ i, ∑ j, v i * (g.inner q (J i) (J j) * v j) := by
    simp only [dotProduct, Matrix.mulVec, radialJacobiGram_apply, q, J]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hright :
      g.inner q (∑ i, v i • J i) (∑ i, v i • J i) =
        ∑ i, ∑ j, v i * (g.inner q (J i) (J j) * v j) := by
    have hmap :=
      congrArg (fun L : TangentSpace I q →L[ℝ] ℝ => L (∑ j, v j • J j))
        (map_sum (g.inner q) (fun i => v i • J i) Finset.univ)
    change
      (fun L : TangentSpace I q →L[ℝ] ℝ => L (∑ j, v j • J j))
          ((g.inner q) (∑ i, v i • J i)) =
        ∑ i, ∑ j, v i * (g.inner q (J i) (J j) * v j)
    rw [hmap]
    simp only [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsecond :
        g.inner q (J i) (∑ j, v j • J j) =
          ∑ j, g.inner q (J i) (v j • J j) :=
      map_sum (g.inner q (J i)) (fun j => v j • J j) Finset.univ
    rw [map_smul (g.inner q), ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hsecond, Finset.mul_sum]
    simp only [ContinuousLinearMap.map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  change dotProduct v (Matrix.mulVec (radialJacobiGram (I := I) g p x) v) =
    g.inner q (∑ i, v i • J i) (∑ i, v i • J i)
  rw [hleft, hright]






omit [T2Space M] [SigmaCompactSpace M] in
lemma normalDensity_le_of_radial_entry_bound
    (g : SmoothRiemannianMetric I M) (p : M) {x : E} {C : ℝ}
    (hxsrc : x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (hentry : ∀ i j : Fin (Module.finrank ℝ E),
      |radialJacobiGram (I := I) g p x i j| ≤ C) :
    normalChartDensity (I := I) g p x ≤
      Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
        C ^ Module.finrank ℝ E) := by
  have hdet_pos_normal :
      0 < (normalGramMatrix (I := I) g p x).det := by
    simpa [normalGramMatrix] using
      DifferentialGeometry.Integral.Measure.paramGramMatrix_det_pos
        (I := I) g (NormalCoordinates.expMapDiffeo (I := I) g p) hxsrc
  have hdet_nonneg :
      0 ≤ (radialJacobiGram (I := I) g p x).det := by
    have hdet_pos : 0 < (radialJacobiGram (I := I) g p x).det := by
      rw [← normalGram_radialMat (I := I) g p hxsrc hxrad]
      exact hdet_pos_normal
    exact hdet_pos.le
  rw [normalDensity_radial (I := I) g p hxsrc hxrad]
  simpa [Fintype.card_fin] using
    sqrt_det_le_of_entry_bound
      (ι := Fin (Module.finrank ℝ E))
      (A := radialJacobiGram (I := I) g p x)
      (C := C) hdet_nonneg hentry



omit [T2Space M] [SigmaCompactSpace M] in
lemma normalDensity_le_of_radial_length_bound
    (g : SmoothRiemannianMetric I M) (p : M) {x : E} {B : ℝ}
    (hxsrc : x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (hB : 0 ≤ B)
    (hJ : ∀ i : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1)) ≤ B) :
    normalChartDensity (I := I) g p x ≤
      Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
        (B * B) ^ Module.finrank ℝ E) :=
  normalDensity_le_of_radial_entry_bound
    (I := I) g p hxsrc hxrad
    (radialEntry_le_of_length_bound (I := I) g p x hB hJ)









omit [T2Space M] [SigmaCompactSpace M] in
lemma density_le_gronwall
    (g : SmoothRiemannianMetric I M) (p : M) {x : E} {K b B : ℝ}
    (hxsrc : x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (hBnn : 0 ≤ B) (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Set.Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t))
    (hG : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)))) 1 ≤ B) :
    normalChartDensity (I := I) g p x ≤
      Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
        (B * B) ^ Module.finrank ℝ E) :=
  normalDensity_le_of_radial_length_bound
    (I := I) g p hxsrc hxrad hBnn
    (radialJacobi_fin_le (I := I) g p x hK hb h1b hγ hcard F hpar hON
      hFdiff hJdiff hDJdiff hODE hG)






omit [T2Space M] [SigmaCompactSpace M] in
lemma density_le_gronwall_of_init_bound
    (g : SmoothRiemannianMetric I M) (p : M) {x : E} {K b A B : ℝ}
    (hxsrc : x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (hBnn : 0 ≤ B) (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Set.Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t))
    (hinit : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    normalChartDensity (I := I) g p x ≤
      Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
        (B * B) ^ Module.finrank ℝ E) :=
  normalDensity_le_of_radial_length_bound
    (I := I) g p hxsrc hxrad hBnn
    (radialJacobi_fin_le_of_init_bound (I := I) g p x hK hb h1b hγ hcard F
      hpar hON hFdiff hJdiff hDJdiff hODE hinit hmodel)







omit [T2Space M] [SigmaCompactSpace M] in
lemma density_le_gronwall_of_deriv_eq
    (g : SmoothRiemannianMetric I M) (p : M) {x : E} {K b A B : ℝ}
    (hxsrc : x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (hBnn : 0 ≤ B) (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Set.Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t))
    (hderiv : ∀ k : Fin (Module.finrank ℝ E),
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0 : E) =
        (chartModelBasis E) k)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    normalChartDensity (I := I) g p x ≤
      Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
        (B * B) ^ Module.finrank ℝ E) :=
  normalDensity_le_of_radial_length_bound
    (I := I) g p hxsrc hxrad hBnn
    (radialJacobi_fin_le_of_deriv_eq (I := I) g p x hK hb h1b hγ hcard F
      hpar hON hFdiff hJdiff hDJdiff hODE hderiv hbasis hmodel)







omit [T2Space M] [SigmaCompactSpace M] in
lemma density_le_gronwall_of_radius_deriv
    (g : SmoothRiemannianMetric I M) (p : M) {x : E} {r K b A B : ℝ}
    (hxsrc : x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (hBnn : 0 ≤ B) (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Set.Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hxsmall : ‖x‖ < r)
    (hbasisSmall : ∀ k : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) k‖ < r)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    normalChartDensity (I := I) g p x ≤
      Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
        (B * B) ^ Module.finrank ℝ E) :=
  normalDensity_le_of_radial_length_bound
    (I := I) g p hxsrc hxrad hBnn
    (radialJacobi_fin_le_of_radius_deriv (I := I) g p x hK hb h1b hγ hcard F
      hpar hON hFdiff hJdiff hDJdiff hODE hderivRadius hxsmall hbasisSmall
      hbasis hmodel)







omit [T2Space M] [SigmaCompactSpace M] in
lemma density_le_gronwall_of_scaled_radius
    (g : SmoothRiemannianMetric I M) (p : M) {x : E} {a r K b A B : ℝ}
    (hxsrc : x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (hBnn : 0 ≤ B) (ha : 0 < a) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Set.Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hxsmall : ‖x‖ < r)
    (hscaledSmall : ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r)
    (hinit : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B) :
    normalChartDensity (I := I) g p x ≤
      Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
        (B * B) ^ Module.finrank ℝ E) :=
  normalDensity_le_of_radial_length_bound
    (I := I) g p hxsrc hxrad hBnn
    (radialJacobi_fin_le_of_scaled_radius (I := I) g p x ha hK hb h1b hγ hcard F
      hpar hON hFdiff hJdiff hDJdiff hODE hderivRadius hxsmall hscaledSmall
      hinit hmodel hxrad)

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_dens_le_rm04_at
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b A B : ℝ}, 0 ≤ B → 0 < a → 0 ≤ K → 0 ≤ Vb → 0 ≤ b →
      b ≤ 1 → (1 : ℝ) ≤ b →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source →
      ‖x‖ < expMapC2Radius (I := I) g p →
      (∀ t ∈ Set.Icc (0 : ℝ) b,
        ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) →
      (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t)) →
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) →
      (∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B →
      normalChartDensity (I := I) g p x ≤
        Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
          (B * B) ^ Module.finrank ℝ E) := by
  obtain ⟨r, hr, hfin⟩ := exists_fin_le_rm04_at (I := I) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro x hx a K R Vb b A B hBnn ha hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
    hxsrc hxrad hγ ι _ _ _ hcard F hpar hON hFdiff hinit hmodel
  letI : Fintype ι := ‹Fintype ι›
  letI : DecidableEq ι := ‹DecidableEq ι›
  letI : Nonempty ι := ‹Nonempty ι›
  exact normalDensity_le_of_radial_length_bound (I := I) g p hxsrc hxrad hBnn
    (hfin x hx ha hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
      hγ hcard F hpar hON hFdiff hinit hmodel hxrad)

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_dens_le_rm04
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b A B : ℝ}, 0 ≤ B → 0 < a → 0 ≤ K → 0 ≤ Vb → 0 ≤ b →
      b ≤ 1 → (1 : ℝ) ≤ b →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source →
      ‖x‖ < expMapC2Radius (I := I) g p →
      ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) →
      (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t)) →
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) →
      (∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B →
      normalChartDensity (I := I) g p x ≤
        Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
          (B * B) ^ Module.finrank ℝ E) := by
  obtain ⟨r, hr, h⟩ := exists_dens_le_rm04_at (I := I) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro x hx a K R Vb b A B hBnn ha hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
    hxsrc hxrad hγ ι _ _ _ hcard F hpar hON hFdiff hinit hmodel
  exact h x hx hBnn ha hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm hxsrc hxrad
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON hFdiff hinit hmodel



omit [T2Space M] [SigmaCompactSpace M] in
lemma radialJacobiGram_posDef
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hxsrc : x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    (radialJacobiGram (I := I) g p x).PosDef := by
  rw [← normalGram_radialMat (I := I) g p hxsrc hxrad]
  exact DifferentialGeometry.Integral.Measure.paramGramMatrix_posDef
    (I := I) g (NormalCoordinates.expMapDiffeo (I := I) g p) hxsrc






omit [T2Space M] [SigmaCompactSpace M] in
lemma normalDensity_ge_of_eigen_bound
    (g : SmoothRiemannianMetric I M) (p : M) {x : E} {a : ℝ}
    (hxsrc : x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (ha : 0 ≤ a)
    (heig : ∀ i : Fin (Module.finrank ℝ E),
      a ≤ (radialJacobiGram_posDef (I := I) g p hxsrc hxrad).isHermitian.eigenvalues i) :
    Real.sqrt (a ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p x := by
  rw [normalDensity_radial (I := I) g p hxsrc hxrad]
  simpa [Fintype.card_fin] using
    sqrt_pow_le_sqrt_det
      (ι := Fin (Module.finrank ℝ E))
      (A := radialJacobiGram (I := I) g p x)
      (a := a)
      (radialJacobiGram_posDef (I := I) g p hxsrc hxrad).posSemidef
      ha heig






omit [T2Space M] [SigmaCompactSpace M] in
lemma normalDensity_ge_of_rayleigh_bound
    (g : SmoothRiemannianMetric I M) (p : M) {x : E} {a : ℝ}
    (hxsrc : x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (ha : 0 ≤ a)
    (hray : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      a ≤ RCLike.re (dotProduct (star ⇑v)
        (Matrix.mulVec (radialJacobiGram (I := I) g p x) ⇑v))) :
    Real.sqrt (a ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p x := by
  rw [normalDensity_radial (I := I) g p hxsrc hxrad]
  simpa [Fintype.card_fin] using
    sqrt_pow_le_sqrt_det_of_rayleigh
      (ι := Fin (Module.finrank ℝ E))
      (A := radialJacobiGram (I := I) g p x)
      (a := a)
      (radialJacobiGram_posDef (I := I) g p hxsrc hxrad).posSemidef
      ha hray



omit [T2Space M] [SigmaCompactSpace M] in
lemma normalDensity_ge_of_combo_bound
    (g : SmoothRiemannianMetric I M) (p : M) {x : E} {a : ℝ}
    (hxsrc : x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (ha : 0 ≤ a)
    (hcombo : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      a ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (∑ i, v i • radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1)
        (∑ i, v i • radialJacobiField (I := I) g p x ((chartModelBasis E) i) 1)) :
    Real.sqrt (a ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p x :=
  normalDensity_ge_of_rayleigh_bound (I := I) g p hxsrc hxrad ha
    (fun v hv => by
      have h := hcombo v hv
      rw [← radialJacobiGram_quadratic (I := I) g p x (⇑v)] at h
      simpa using h)




omit [T2Space M] [SigmaCompactSpace M] in
lemma normalDensity_ge_of_dir_bound
    (g : SmoothRiemannianMetric I M) (p : M) {x : E} {a : ℝ}
    (hxsrc : x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (ha : 0 ≤ a)
    (hdir : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      a ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1)
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1)) :
    Real.sqrt (a ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p x :=
  normalDensity_ge_of_combo_bound (I := I) g p hxsrc hxrad ha
    (fun v hv => by
      have h := hdir v hv
      rw [radialJacobi_one_sum (I := I) g p x (fun i => v i) hxrad] at h
      exact h)

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_dens_ge_rm04_at
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b B : ℝ}, 0 < a → 0 ≤ B → 0 ≤ K → 0 ≤ Vb → 0 ≤ b →
      b ≤ 1 → (1 : ℝ) ≤ b →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source →
      ‖x‖ < expMapC2Radius (I := I) g p →
      (∀ t ∈ Set.Icc (0 : ℝ) b,
        ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) →
      (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t)) →
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) →
      (∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a * B ≤ Real.sqrt
            (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
              (a • (∑ i, v i • (chartModelBasis E) i))) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                  (a • (∑ i, v i • (chartModelBasis E) i))))) 1) →
      Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p x := by
  obtain ⟨r, hr, hdir⟩ := exists_dir_ge_rm04_at (I := I) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro x hx a K R Vb b B ha hB hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
    hxsrc hxrad hγ ι _ _ _ hcard F hpar hON hFdiff hmodel
  letI : Fintype ι := ‹Fintype ι›
  letI : DecidableEq ι := ‹DecidableEq ι›
  letI : Nonempty ι := ‹Nonempty ι›
  exact normalDensity_ge_of_dir_bound (I := I) g p hxsrc hxrad (sq_nonneg B)
    (hdir x hx ha hB hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
      hγ hcard F hpar hON hFdiff hmodel hxrad)

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_dens_ge_rm04
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b B : ℝ}, 0 < a → 0 ≤ B → 0 ≤ K → 0 ≤ Vb → 0 ≤ b →
      b ≤ 1 → (1 : ℝ) ≤ b →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source →
      ‖x‖ < expMapC2Radius (I := I) g p →
      ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) →
      (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t)) →
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) →
      (∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a * B ≤ Real.sqrt
            (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
              (a • (∑ i, v i • (chartModelBasis E) i))) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                  (a • (∑ i, v i • (chartModelBasis E) i))))) 1) →
      Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p x := by
  obtain ⟨r, hr, h⟩ := exists_dens_ge_rm04_at (I := I) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro x hx a K R Vb b B ha hB hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
    hxsrc hxrad hγ ι _ _ _ hcard F hpar hON hFdiff hmodel
  exact h x hx ha hB hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm hxsrc hxrad
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON hFdiff hmodel

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_dens_two_rm04_at
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b A B : ℝ}, 0 ≤ B → 0 < a → 0 ≤ K → 0 ≤ Vb → 0 ≤ b →
      b ≤ 1 → (1 : ℝ) ≤ b →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source →
      ‖x‖ < expMapC2Radius (I := I) g p →
      (∀ t ∈ Set.Icc (0 : ℝ) b,
        ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) →
      (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t)) →
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) →
      (∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a * B ≤ Real.sqrt
            (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
              (a • (∑ i, v i • (chartModelBasis E) i))) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                  (a • (∑ i, v i • (chartModelBasis E) i))))) 1) →
      Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p x ∧
        normalChartDensity (I := I) g p x ≤
          Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E) := by
  obtain ⟨rle, hrle, hle⟩ := exists_dens_le_rm04_at (I := I) g hEnorm p
  obtain ⟨rge, hrge, hge⟩ := exists_dens_ge_rm04_at (I := I) g hEnorm p
  refine ⟨min rle rge, lt_min hrle hrge, ?_⟩
  intro x hx a K R Vb b A B hBnn ha hK hVb hb0 hb1 h1b hsmallBasis hsmallDir
    hlaunch hKbound hRm hxsrc hxrad hγ ι _ _ _ hcard F hpar hON hFdiff
    hinit hmodelLe hmodelGe
  letI : Fintype ι := ‹Fintype ι›
  letI : DecidableEq ι := ‹DecidableEq ι›
  letI : Nonempty ι := ‹Nonempty ι›
  have hxle : ‖x‖ < rle := lt_of_lt_of_le hx (min_le_left rle rge)
  have hxge : ‖x‖ < rge := lt_of_lt_of_le hx (min_le_right rle rge)
  have hsmallBasis_le :
      ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < rle :=
    fun k => lt_of_lt_of_le (hsmallBasis k) (min_le_left rle rge)
  have hsmallDir_ge :
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < rge :=
    fun v hv => lt_of_lt_of_le (hsmallDir v hv) (min_le_right rle rge)
  have hupper :
      normalChartDensity (I := I) g p x ≤
        Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
          (B * B) ^ Module.finrank ℝ E) :=
    hle x hxle hBnn ha hK hVb hb0 hb1 h1b hsmallBasis_le hlaunch hKbound hRm
      hxsrc hxrad hγ hcard F hpar hON hFdiff hinit hmodelLe
  have hlower :
      Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p x :=
    hge x hxge ha hBnn hK hVb hb0 hb1 h1b hsmallDir_ge hlaunch hKbound hRm
      hxsrc hxrad hγ hcard F hpar hON hFdiff hmodelGe
  exact ⟨hlower, hupper⟩

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_dens_pair_rm04_at
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b A Blo Bhi : ℝ}, 0 ≤ Blo → 0 ≤ Bhi →
      0 < a → 0 ≤ K → 0 ≤ Vb → 0 ≤ b →
      b ≤ 1 → (1 : ℝ) ≤ b →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source →
      ‖x‖ < expMapC2Radius (I := I) g p →
      (∀ t ∈ Set.Icc (0 : ℝ) b,
        ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) →
      (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t)) →
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) →
      (∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a * Blo ≤ Real.sqrt
            (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
              (a • (∑ i, v i • (chartModelBasis E) i))) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                  (a • (∑ i, v i • (chartModelBasis E) i))))) 1) →
      Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p x ∧
        normalChartDensity (I := I) g p x ≤
          Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E) := by
  obtain ⟨rle, hrle, hle⟩ := exists_dens_le_rm04_at (I := I) g hEnorm p
  obtain ⟨rge, hrge, hge⟩ := exists_dens_ge_rm04_at (I := I) g hEnorm p
  refine ⟨min rle rge, lt_min hrle hrge, ?_⟩
  intro x hx a K R Vb b A Blo Bhi hBlo hBhi ha hK hVb hb0 hb1 h1b
    hsmallBasis hsmallDir hlaunch hKbound hRm hxsrc hxrad hγ ι _ _ _ hcard F
    hpar hON hFdiff hinit hmodelLe hmodelGe
  letI : Fintype ι := ‹Fintype ι›
  letI : DecidableEq ι := ‹DecidableEq ι›
  letI : Nonempty ι := ‹Nonempty ι›
  have hxle : ‖x‖ < rle := lt_of_lt_of_le hx (min_le_left rle rge)
  have hxge : ‖x‖ < rge := lt_of_lt_of_le hx (min_le_right rle rge)
  have hsmallBasis_le :
      ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < rle :=
    fun k => lt_of_lt_of_le (hsmallBasis k) (min_le_left rle rge)
  have hsmallDir_ge :
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < rge :=
    fun v hv => lt_of_lt_of_le (hsmallDir v hv) (min_le_right rle rge)
  have hupper :
      normalChartDensity (I := I) g p x ≤
        Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
          (Bhi * Bhi) ^ Module.finrank ℝ E) :=
    hle x hxle hBhi ha hK hVb hb0 hb1 h1b hsmallBasis_le hlaunch hKbound hRm
      hxsrc hxrad hγ hcard F hpar hON hFdiff hinit hmodelLe
  have hlower :
      Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p x :=
    hge x hxge ha hBlo hK hVb hb0 hb1 h1b hsmallDir_ge hlaunch hKbound hRm
      hxsrc hxrad hγ hcard F hpar hON hFdiff hmodelGe
  exact ⟨hlower, hupper⟩

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_dens_two_rm04
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b A B : ℝ}, 0 ≤ B → 0 < a → 0 ≤ K → 0 ≤ Vb → 0 ≤ b →
      b ≤ 1 → (1 : ℝ) ≤ b →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source →
      ‖x‖ < expMapC2Radius (I := I) g p →
      ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) →
      (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t)) →
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) →
      (∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a * B ≤ Real.sqrt
            (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
              (a • (∑ i, v i • (chartModelBasis E) i))) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                  (a • (∑ i, v i • (chartModelBasis E) i))))) 1) →
      Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p x ∧
        normalChartDensity (I := I) g p x ≤
          Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E) := by
  obtain ⟨r, hr, h⟩ := exists_dens_two_rm04_at (I := I) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro x hx a K R Vb b A B hBnn ha hK hVb hb0 hb1 h1b hsmallBasis hsmallDir
    hlaunch hKbound hRm hxsrc hxrad hγ ι _ _ _ hcard F hpar hON hFdiff
    hinit hmodelLe hmodelGe
  exact h x hx hBnn ha hK hVb hb0 hb1 h1b hsmallBasis hsmallDir hlaunch hKbound hRm
    hxsrc hxrad (fun _ _ => hγ.contMDiffAt) hcard F hpar hON hFdiff
    hinit hmodelLe hmodelGe



omit [T2Space M] [SigmaCompactSpace M] in
lemma ball_src_of_radius
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hR : R ≤ expMapC2Radius (I := I) g p) :
    Metric.ball (0 : E) R ⊆ (NormalCoordinates.expMapDiffeo (I := I) g p).source := by
  intro w hw
  have hwR : ‖w‖ < R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hw_target : w ∈ (normalChartAt (I := I) g p).target :=
    ball_subset_normalChartAt_target (I := I) g p (hwR.trans_le hR)
  simpa [normalChartAt_target_eq (I := I) g p] using hw_target



omit [T2Space M] [SigmaCompactSpace M] in
lemma density_ge_det
    (g : SmoothRiemannianMetric I M) (p : M) {x : E} {c : ℝ}
    (hxsrc : x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (hdet : c ≤ (radialJacobiGram (I := I) g p x).det) :
    Real.sqrt c ≤ normalChartDensity (I := I) g p x := by
  rw [normalDensity_radial (I := I) g p hxsrc hxrad]
  exact Real.sqrt_le_sqrt hdet



omit [T2Space M] [SigmaCompactSpace M] in
lemma density_ge_det_ball
    (g : SmoothRiemannianMetric I M) (p : M) {R c : ℝ}
    (hR : R ≤ expMapC2Radius (I := I) g p)
    (hdet : ∀ w ∈ Metric.ball (0 : E) R,
      c ≤ (radialJacobiGram (I := I) g p w).det) :
    ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt c ≤ normalChartDensity (I := I) g p w := by
  intro w hw
  have hwsrc : w ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source :=
    ball_src_of_radius (I := I) g p hR hw
  have hwrad : ‖w‖ < expMapC2Radius (I := I) g p := by
    have hwR : ‖w‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    exact hwR.trans_le hR
  exact density_ge_det (I := I) g p hwsrc hwrad (hdet w hw)



omit [T2Space M] [SigmaCompactSpace M] in
lemma density_ge_rayleigh_ball
    (g : SmoothRiemannianMetric I M) (p : M) {R a : ℝ}
    (hR : R ≤ expMapC2Radius (I := I) g p)
    (ha : 0 ≤ a)
    (hray : ∀ w ∈ Metric.ball (0 : E) R,
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a ≤ RCLike.re (dotProduct (star ⇑v)
          (Matrix.mulVec (radialJacobiGram (I := I) g p w) ⇑v))) :
    ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt (a ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p w := by
  intro w hw
  have hwsrc : w ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source :=
    ball_src_of_radius (I := I) g p hR hw
  have hwrad : ‖w‖ < expMapC2Radius (I := I) g p := by
    have hwR : ‖w‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    exact hwR.trans_le hR
  exact normalDensity_ge_of_rayleigh_bound (I := I) g p hwsrc hwrad ha (hray w hw)



omit [T2Space M] [SigmaCompactSpace M] in
lemma density_ge_combo_ball
    (g : SmoothRiemannianMetric I M) (p : M) {R a : ℝ}
    (hR : R ≤ expMapC2Radius (I := I) g p)
    (ha : 0 ≤ a)
    (hcombo : ∀ w ∈ Metric.ball (0 : E) R,
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from w))
          (∑ i, v i • radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
          (∑ i, v i • radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) :
    ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt (a ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p w := by
  intro w hw
  have hwsrc : w ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source :=
    ball_src_of_radius (I := I) g p hR hw
  have hwrad : ‖w‖ < expMapC2Radius (I := I) g p := by
    have hwR : ‖w‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    exact hwR.trans_le hR
  exact normalDensity_ge_of_combo_bound (I := I) g p hwsrc hwrad ha (hcombo w hw)



omit [T2Space M] [SigmaCompactSpace M] in
lemma density_ge_dir_ball
    (g : SmoothRiemannianMetric I M) (p : M) {R a : ℝ}
    (hR : R ≤ expMapC2Radius (I := I) g p)
    (ha : 0 ≤ a)
    (hdir : ∀ w ∈ Metric.ball (0 : E) R,
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from w))
          (radialJacobiField (I := I) g p w
            (∑ i, v i • (chartModelBasis E) i) 1)
          (radialJacobiField (I := I) g p w
            (∑ i, v i • (chartModelBasis E) i) 1)) :
    ∀ w ∈ Metric.ball (0 : E) R,
      Real.sqrt (a ^ Module.finrank ℝ E) ≤ normalChartDensity (I := I) g p w := by
  intro w hw
  have hwsrc : w ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source :=
    ball_src_of_radius (I := I) g p hR hw
  have hwrad : ‖w‖ < expMapC2Radius (I := I) g p := by
    have hwR : ‖w‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    exact hwR.trans_le hR
  exact normalDensity_ge_of_dir_bound (I := I) g p hwsrc hwrad ha (hdir w hw)






theorem normalChart_volume_le_of_radial_entry_bound
    (g : SmoothRiemannianMetric I M) (p : M)
    {A : Set M} (hA_meas : MeasurableSet A)
    (hA_source : A ⊆ (normalChartAt (I := I) g p).source)
    {C : ℝ}
    (hA_rad : (normalChartAt (I := I) g p) '' A ⊆
      Metric.ball (0 : E) (expMapC2Radius (I := I) g p))
    (hentry : ∀ w ∈ (normalChartAt (I := I) g p) '' A,
      ∀ i j : Fin (Module.finrank ℝ E),
        |radialJacobiGram (I := I) g p w i j| ≤ C) :
    riemannianVolumeMeasure (I := I) (M := M) g A ≤
      ∫⁻ _ in (normalChartAt (I := I) g p) '' A,
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            C ^ Module.finrank ℝ E)) ∂(modelHaar (E := E)) := by
  have hA_target : A ⊆ (expMapDiffeo (I := I) g p).target := by
    simpa [normalChartAt_source_eq (I := I) g p] using hA_source
  have hB_meas : MeasurableSet ((normalChartAt (I := I) g p) '' A) := by
    simpa [normalChartAt] using
      DifferentialGeometry.Integral.Measure.measurableSet_symm_image_param
        (I := I) (M := M)
        (Ψ := expMapDiffeo (I := I) g p) hA_meas hA_target
  rw [normalChart_volume_eq (I := I) (M := M) g p hA_meas hA_source]
  refine MeasureTheory.setLIntegral_mono' hB_meas ?_
  intro w hw
  refine ENNReal.ofReal_le_ofReal ?_
  have hwsrc : w ∈ (expMapDiffeo (I := I) g p).source := by
    rcases hw with ⟨y, hyA, hyw⟩
    have hy_source : y ∈ (normalChartAt (I := I) g p).source := hA_source hyA
    have hw_target : normalChartAt (I := I) g p y ∈
        (normalChartAt (I := I) g p).target :=
      (normalChartAt (I := I) g p).map_source hy_source
    rw [hyw] at hw_target
    simpa [normalChartAt_target_eq (I := I) g p] using hw_target
  have hwrad : ‖w‖ < expMapC2Radius (I := I) g p := by
    have hwball : w ∈ Metric.ball (0 : E) (expMapC2Radius (I := I) g p) := hA_rad hw
    simpa [Metric.mem_ball, dist_eq_norm] using hwball
  exact normalDensity_le_of_radial_entry_bound
    (I := I) g p hwsrc hwrad (hentry w hw)





theorem normalChart_volume_le_of_radial_length_bound
    (g : SmoothRiemannianMetric I M) (p : M)
    {A : Set M} (hA_meas : MeasurableSet A)
    (hA_source : A ⊆ (normalChartAt (I := I) g p).source)
    {B : ℝ} (hB : 0 ≤ B)
    (hA_rad : (normalChartAt (I := I) g p) '' A ⊆
      Metric.ball (0 : E) (expMapC2Radius (I := I) g p))
    (hJ : ∀ w ∈ (normalChartAt (I := I) g p) '' A,
      ∀ i : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) :
    riemannianVolumeMeasure (I := I) (M := M) g A ≤
      ∫⁻ _ in (normalChartAt (I := I) g p) '' A,
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) ∂(modelHaar (E := E)) :=
  normalChart_volume_le_of_radial_entry_bound
    (I := I) g p hA_meas hA_source hA_rad
    (fun w hw => radialEntry_le_of_length_bound (I := I) g p w hB (hJ w hw))






theorem normalChart_volume_le_const_mul_of_radial_length_bound
    (g : SmoothRiemannianMetric I M) (p : M)
    {A : Set M} (hA_meas : MeasurableSet A)
    (hA_source : A ⊆ (normalChartAt (I := I) g p).source)
    {B : ℝ} (hB : 0 ≤ B)
    (hA_rad : (normalChartAt (I := I) g p) '' A ⊆
      Metric.ball (0 : E) (expMapC2Radius (I := I) g p))
    (hJ : ∀ w ∈ (normalChartAt (I := I) g p) '' A,
      ∀ i : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
          (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) :
    riemannianVolumeMeasure (I := I) (M := M) g A ≤
      ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
        (modelHaar (E := E)) ((normalChartAt (I := I) g p) '' A) := by
  calc
    riemannianVolumeMeasure (I := I) (M := M) g A
        ≤ ∫⁻ _ in (normalChartAt (I := I) g p) '' A,
            ENNReal.ofReal
              (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
                (B * B) ^ Module.finrank ℝ E)) ∂(modelHaar (E := E)) :=
      normalChart_volume_le_of_radial_length_bound
        (I := I) g p hA_meas hA_source hB hA_rad hJ
    _ = ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
        (modelHaar (E := E)) ((normalChartAt (I := I) g p) '' A) :=
      MeasureTheory.setLIntegral_const ((normalChartAt (I := I) g p) '' A)
        (ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)))

end NormalChart

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
