import DifferentialGeometry.Analysis.Elliptic.WithBoundary.InteriorVariational


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

private local instance : MeasurableSpace (EuclideanSpace ℝ (Fin n)) :=
  borel _
private local instance : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [SigmaCompactSpace M] [CompactSpace M] in
lemma InteriorSmoothScalar.oneSubLap_continuous
    {g : SmoothRiemannianMetric (I_half n) M} (u : InteriorSmoothScalar g) :
    Continuous (fun x : M =>
      u.toFun x - Δ_g_with_boundary (I := I_half n) g u.smooth u.interior_support x) :=
  u.smooth.continuous.sub
    (Δ_g_with_boundary_continuous (I := I_half n) g u.smooth u.interior_support)

lemma InteriorSmoothScalar.oneSubLap_memLp
    {g : SmoothRiemannianMetric (I_half n) M} (u : InteriorSmoothScalar g) :
    MemLp (fun x : M =>
        u.toFun x - Δ_g_with_boundary (I := I_half n) g u.smooth u.interior_support x)
      2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I_half n) (M := M) g
  exact u.oneSubLap_continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def InteriorSmoothScalar.oneSubLapClassicalLp
    {g : SmoothRiemannianMetric (I_half n) M} (u : InteriorSmoothScalar g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  u.oneSubLap_memLp.toLp _

theorem interiorSmoothScalarH1Inner_eq_integral_oneSubLap_mul
    {g : SmoothRiemannianMetric (I_half n) M}
    (u v : InteriorSmoothScalar g) :
    interiorSmoothScalarH1Inner u v =
      ∫ x, (u.toFun x - Δ_g_with_boundary (I := I_half n) g u.smooth u.interior_support x)
        * v.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  unfold interiorSmoothScalarH1Inner
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I_half n) (M := M) g
  have hu_supp : HasCompactSupport u.toFun := HasCompactSupport.of_compactSpace _
  have hv_supp : HasCompactSupport v.toFun := HasCompactSupport.of_compactSpace _
  have hgreen :
      ∫ x, g.inner x (gradFun (I := I_half n) g v.toFun x)
            (gradFun (I := I_half n) g u.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) =
        -∫ x, v.toFun x * Δ_g_with_boundary (I := I_half n) g u.smooth u.interior_support x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary
      (I := I_half n) g v.smooth u.smooth v.interior_support u.interior_support hu_supp
  have hsymm :
      (∫ x, g.inner x (gradFun (I := I_half n) g u.toFun x)
            (gradFun (I := I_half n) g v.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      ∫ x, g.inner x (gradFun (I := I_half n) g v.toFun x)
            (gradFun (I := I_half n) g u.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    exact g.symm x _ _
  have hsec_eq : (fun x : M => g.inner x
        ((grad_g_with_boundary_section
            (I := I_half n) g u.smooth u.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((grad_g_with_boundary_section
            (I := I_half n) g v.smooth v.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)) =
      (fun x : M => g.inner x
        (gradFun (I := I_half n) g u.toFun x)
        (gradFun (I := I_half n) g v.toFun x)) := by
    funext x
    rfl
  rw [hsec_eq]
  rw [hsymm, hgreen]
  have hΔu_cont : Continuous
      (Δ_g_with_boundary (I := I_half n) g u.smooth u.interior_support) :=
    Δ_g_with_boundary_continuous (I := I_half n) g u.smooth u.interior_support
  have hu_cont : Continuous u.toFun := u.smooth.continuous
  have hv_cont : Continuous v.toFun := v.smooth.continuous
  have h_uv : Integrable (fun x : M => u.toFun x * v.toFun x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    (hu_cont.mul hv_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h_vΔu : Integrable
      (fun x : M => v.toFun x *
        Δ_g_with_boundary (I := I_half n) g u.smooth u.interior_support x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    (hv_cont.mul hΔu_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpt : ∀ x : M,
      (u.toFun x - Δ_g_with_boundary (I := I_half n) g u.smooth u.interior_support x)
        * v.toFun x =
        u.toFun x * v.toFun x -
          v.toFun x * Δ_g_with_boundary (I := I_half n) g u.smooth u.interior_support x := by
    intro x; ring
  rw [show (fun x : M =>
      (u.toFun x - Δ_g_with_boundary (I := I_half n) g u.smooth u.interior_support x)
        * v.toFun x) =
      (fun x : M =>
        u.toFun x * v.toFun x -
          v.toFun x * Δ_g_with_boundary (I := I_half n) g u.smooth u.interior_support x)
      from funext hpt]
  rw [integral_sub h_uv h_vΔu]
  ring

theorem interiorSmoothScalarH1Inner_eq_lpInner_oneSubLap
    {g : SmoothRiemannianMetric (I_half n) M} (u v : InteriorSmoothScalar g) :
    interiorSmoothScalarH1Inner u v =
      ⟪u.oneSubLapClassicalLp, smoothToLpInterior g v⟫_ℝ := by
  rw [interiorSmoothScalarH1Inner_eq_integral_oneSubLap_mul]
  rw [MeasureTheory.L2.inner_def
    (𝕜 := ℝ)]
  have hae_lhs : (u.oneSubLapClassicalLp :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) =ᵐ[
      riemannianVolumeMeasure (I := I_half n) (M := M) g]
      (fun x : M =>
        u.toFun x - Δ_g_with_boundary (I := I_half n) g u.smooth u.interior_support x) := by
    exact MemLp.coeFn_toLp u.oneSubLap_memLp
  have hae_rhs : (smoothToLpInterior g v :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) =ᵐ[
      riemannianVolumeMeasure (I := I_half n) (M := M) g]
      v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  refine integral_congr_ae ?_
  filter_upwards [hae_lhs, hae_rhs] with x hl hr
  rw [hl, hr]
  show (u.toFun x - Δ_g_with_boundary (I := I_half n) g u.smooth u.interior_support x) *
      v.toFun x = _
  rw [show @inner ℝ _ _
        (u.toFun x - Δ_g_with_boundary (I := I_half n) g u.smooth u.interior_support x)
        (v.toFun x) =
      v.toFun x *
        (u.toFun x - Δ_g_with_boundary (I := I_half n) g u.smooth u.interior_support x)
      from RCLike.inner_apply _ _]
  ring

@[simp] lemma inner_smoothToH1ComplInterior_smoothToH1ComplInterior
    {g : SmoothRiemannianMetric (I_half n) M} (u v : InteriorSmoothScalar g) :
    ⟪smoothToH1ComplInterior g u, smoothToH1ComplInterior g v⟫_ℝ =
      interiorSmoothScalarH1Inner u v := by
  unfold smoothToH1ComplInterior
  change ⟪((u : H1ComplInterior g) : H1ComplInterior g),
        ((v : H1ComplInterior g) : H1ComplInterior g)⟫_ℝ =
      interiorSmoothScalarH1Inner u v
  rw [UniformSpace.Completion.inner_coe (𝕜 := ℝ) u v]
  rfl

@[simp] lemma H1ComplInteriorBilin_smoothToH1ComplInterior_smoothToH1ComplInterior
    {g : SmoothRiemannianMetric (I_half n) M} (u v : InteriorSmoothScalar g) :
    H1ComplInteriorBilin g (smoothToH1ComplInterior g u) (smoothToH1ComplInterior g v) =
      interiorSmoothScalarH1Inner u v := by
  rw [H1ComplInteriorBilin_apply]
  exact inner_smoothToH1ComplInterior_smoothToH1ComplInterior u v

theorem interiorSmoothScalar_bilin_eq_lpFunctional_smooth
    {g : SmoothRiemannianMetric (I_half n) M}
    (u v : InteriorSmoothScalar g) :
    H1ComplInteriorBilin g (smoothToH1ComplInterior g u) (smoothToH1ComplInterior g v) =
      lpFunctionalCLMInterior g u.oneSubLapClassicalLp (smoothToH1ComplInterior g v) := by
  rw [H1ComplInteriorBilin_smoothToH1ComplInterior_smoothToH1ComplInterior,
    interiorSmoothScalarH1Inner_eq_lpInner_oneSubLap]
  rw [lpFunctionalCLMInterior_apply, H1ComplInteriorToLp_smoothToH1ComplInterior]
  exact real_inner_comm _ _

theorem denseRange_smoothToH1ComplInterior
    (g : SmoothRiemannianMetric (I_half n) M) :
    DenseRange (smoothToH1ComplInterior g) := by
  unfold smoothToH1ComplInterior
  rw [show (UniformSpace.Completion.toComplL :
      InteriorSmoothScalar g → H1ComplInterior g) =
      ((↑) : InteriorSmoothScalar g →
        UniformSpace.Completion (InteriorSmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

theorem smoothToH1ComplInterior_bilin_eq_lpFunctional
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : InteriorSmoothScalar g) (w : H1ComplInterior g) :
    H1ComplInteriorBilin g (smoothToH1ComplInterior g u) w =
      lpFunctionalCLMInterior g u.oneSubLapClassicalLp w := by
  let L : H1ComplInterior g → ℝ := fun w =>
    H1ComplInteriorBilin g (smoothToH1ComplInterior g u) w
  let R : H1ComplInterior g → ℝ := fun w =>
    lpFunctionalCLMInterior g u.oneSubLapClassicalLp w
  change L w = R w
  have hL_cont : Continuous L :=
    (H1ComplInteriorBilin g (smoothToH1ComplInterior g u)).continuous
  have hR_cont : Continuous R :=
    (lpFunctionalCLMInterior g u.oneSubLapClassicalLp).continuous
  have hLR_smooth :
      L ∘ (smoothToH1ComplInterior g) = R ∘ (smoothToH1ComplInterior g) := by
    funext v
    exact interiorSmoothScalar_bilin_eq_lpFunctional_smooth u v
  exact congrFun
    ((denseRange_smoothToH1ComplInterior g).equalizer hL_cont hR_cont hLR_smooth) w

theorem smoothToH1ComplInterior_eq_resolventInterior_oneSubLap
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : InteriorSmoothScalar g) :
    smoothToH1ComplInterior g u =
      resolventInterior g u.oneSubLapClassicalLp := by
  apply ext_inner_right ℝ
  intro w
  rw [show ⟪smoothToH1ComplInterior g u, w⟫_ℝ =
        H1ComplInteriorBilin g (smoothToH1ComplInterior g u) w from rfl]
  rw [smoothToH1ComplInterior_bilin_eq_lpFunctional u w]
  rw [resolventInterior_inner_eq_lpFunctional]
  rw [lpFunctionalCLMInterior_apply]

end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
