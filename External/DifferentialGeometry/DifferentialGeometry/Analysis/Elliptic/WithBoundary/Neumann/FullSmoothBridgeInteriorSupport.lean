import DifferentialGeometry.Analysis.Elliptic.WithBoundary.Neumann.FullH1Compl
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.InteriorH1Compl
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.InteriorSmoothScalarPreH1
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.GreenWithBoundary
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Green


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Neumann

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

private theorem boundaryFaceSum_smoothSmul_grad_eq_zero_of_h_interior_support
    (g : SmoothRiemannianMetric (I_half n) M)
    {f h : M → ℝ}
    (hf : ContMDiff (I_half n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (I_half n) 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ (I_half n).interior M) :
    boundaryFaceSum (I := I_half n) g
        (smoothSmul (I := I_half n) f hf
          (grad_g_with_boundary_section (I := I_half n) g hh hh_int)) = 0 := by
  classical
  set X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯ :=
    grad_g_with_boundary_section (I := I_half n) g hh hh_int with hX_def
  set Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯ :=
    smoothSmul (I := I_half n) f hf X with hY_def
  have hY_cs : HasCompactSupport Y := HasCompactSupport.of_compactSpace _
  have hX_int : tsupport (X : ∀ x, TangentSpace (I_half n) x) ⊆
      (I_half n).interior M :=
    tsupport_grad_g_with_boundary_section_subset_interior
      (I := I_half n) g hh hh_int
  have hY_int : tsupport (Y : ∀ x, TangentSpace (I_half n) x) ⊆
      (I_half n).interior M :=
    tsupport_smoothSmul_subset_interior (I := I_half n) hf X hX_int
  have h_div_Y_zero :
      ∫ x, divergence_g_with_boundary (I := I_half n) g Y x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) = 0 :=
    integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support
      (I := I_half n) g Y hY_cs hY_int
  have h_stokes :=
    integral_divergence_with_boundary_eq_boundaryFaceSum (I := I_half n) g Y
  rw [h_div_Y_zero] at h_stokes
  exact h_stokes.symm

omit [SigmaCompactSpace M] [CompactSpace M] in
lemma FullSmoothScalar.oneSubLap_continuous_of_interior_support
    {g : SmoothRiemannianMetric (I_half n) M} (u : FullSmoothScalar g)
    (hu_int : tsupport u.toFun ⊆ (I_half n).interior M) :
    Continuous (fun x : M =>
      u.toFun x - Δ_g_with_boundary (I := I_half n) g u.smooth hu_int x) :=
  u.smooth.continuous.sub
    (Δ_g_with_boundary_continuous (I := I_half n) g u.smooth hu_int)

lemma FullSmoothScalar.oneSubLap_memLp_of_interior_support
    {g : SmoothRiemannianMetric (I_half n) M} (u : FullSmoothScalar g)
    (hu_int : tsupport u.toFun ⊆ (I_half n).interior M) :
    MemLp (fun x : M =>
        u.toFun x - Δ_g_with_boundary (I := I_half n) g u.smooth hu_int x)
      2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I_half n) (M := M) g
  exact (u.oneSubLap_continuous_of_interior_support hu_int).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def FullSmoothScalar.oneSubLapFullClassicalLp
    {g : SmoothRiemannianMetric (I_half n) M} (u : FullSmoothScalar g)
    (hu_int : tsupport u.toFun ⊆ (I_half n).interior M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  (u.oneSubLap_memLp_of_interior_support hu_int).toLp _

theorem fullSmoothScalarH1Inner_eq_integral_oneSubLap_mul_of_interior_support
    {g : SmoothRiemannianMetric (I_half n) M}
    (u v : FullSmoothScalar g)
    (hu_int : tsupport u.toFun ⊆ (I_half n).interior M) :
    fullSmoothScalarH1Inner u v =
      ∫ x, (u.toFun x -
              Δ_g_with_boundary (I := I_half n) g u.smooth hu_int x) *
            v.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I_half n) (M := M) g
  have h_green : ∫ x, g.inner x (gradFun (I := I_half n) g v.toFun x)
            (gradFun (I := I_half n) g u.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) +
        ∫ x, v.toFun x *
            Δ_g_with_boundary (I := I_half n) g u.smooth hu_int x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) =
      boundaryFaceSum (I := I_half n) g
        (smoothSmul (I := I_half n) v.toFun v.smooth
          (grad_g_with_boundary_section (I := I_half n) g u.smooth hu_int)) :=
    green_first_with_boundary (I := I_half n) g v.smooth u.smooth hu_int
  have h_face : boundaryFaceSum (I := I_half n) g
        (smoothSmul (I := I_half n) v.toFun v.smooth
          (grad_g_with_boundary_section (I := I_half n) g u.smooth hu_int)) = 0 :=
    boundaryFaceSum_smoothSmul_grad_eq_zero_of_h_interior_support
      (g := g) v.smooth u.smooth hu_int
  rw [h_face] at h_green
  have h_symm : ∀ x : M,
      g.inner x (gradFun (I := I_half n) g v.toFun x)
        (gradFun (I := I_half n) g u.toFun x) =
        g.inner x (gradFun (I := I_half n) g u.toFun x)
          (gradFun (I := I_half n) g v.toFun x) := by
    intro x; exact g.symm x _ _
  have h_int_symm :
      ∫ x, g.inner x (gradFun (I := I_half n) g v.toFun x)
            (gradFun (I := I_half n) g u.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) =
        ∫ x, g.inner x (gradFun (I := I_half n) g u.toFun x)
              (gradFun (I := I_half n) g v.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall h_symm)
  rw [h_int_symm] at h_green
  have h_grad_eq :
      ∫ x, g.inner x (gradFun (I := I_half n) g u.toFun x)
            (gradFun (I := I_half n) g v.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) =
        -∫ x, v.toFun x *
              Δ_g_with_boundary (I := I_half n) g u.smooth hu_int x
            ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
    linarith
  unfold fullSmoothScalarH1Inner
  have hΔu_cont : Continuous
      (Δ_g_with_boundary (I := I_half n) g u.smooth hu_int) :=
    Δ_g_with_boundary_continuous (I := I_half n) g u.smooth hu_int
  have hu_cont : Continuous u.toFun := u.smooth.continuous
  have hv_cont : Continuous v.toFun := v.smooth.continuous
  have h_uv_int : Integrable (fun x : M => u.toFun x * v.toFun x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    (hu_cont.mul hv_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h_vΔu_int : Integrable
      (fun x : M => v.toFun x *
        Δ_g_with_boundary (I := I_half n) g u.smooth hu_int x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    (hv_cont.mul hΔu_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpt : ∀ x : M,
      (u.toFun x -
          Δ_g_with_boundary (I := I_half n) g u.smooth hu_int x) *
          v.toFun x =
        u.toFun x * v.toFun x -
          v.toFun x *
            Δ_g_with_boundary (I := I_half n) g u.smooth hu_int x := by
    intro x; ring
  rw [show (fun x : M =>
        (u.toFun x -
          Δ_g_with_boundary (I := I_half n) g u.smooth hu_int x) *
          v.toFun x) =
      (fun x : M =>
          u.toFun x * v.toFun x -
            v.toFun x *
              Δ_g_with_boundary (I := I_half n) g u.smooth hu_int x)
      from funext hpt]
  rw [integral_sub h_uv_int h_vΔu_int]
  rw [h_grad_eq]
  ring

theorem fullSmoothScalarH1Inner_eq_lpInner_oneSubLap_of_interior_support
    {g : SmoothRiemannianMetric (I_half n) M}
    (u v : FullSmoothScalar g)
    (hu_int : tsupport u.toFun ⊆ (I_half n).interior M) :
    fullSmoothScalarH1Inner u v =
      ⟪u.oneSubLapFullClassicalLp hu_int, smoothToLpFullNeumann g v⟫_ℝ := by
  rw [fullSmoothScalarH1Inner_eq_integral_oneSubLap_mul_of_interior_support
    (u := u) (v := v) hu_int]
  rw [MeasureTheory.L2.inner_def (𝕜 := ℝ)]
  have hae_lhs :
      (u.oneSubLapFullClassicalLp hu_int :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) g]
        (fun x : M =>
          u.toFun x -
            Δ_g_with_boundary (I := I_half n) g u.smooth hu_int x) :=
    MemLp.coeFn_toLp (u.oneSubLap_memLp_of_interior_support hu_int)
  have hae_rhs : (smoothToLpFullNeumann g v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) g]
        v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  refine integral_congr_ae ?_
  filter_upwards [hae_lhs, hae_rhs] with x hl hr
  rw [hl, hr]
  show (u.toFun x -
        Δ_g_with_boundary (I := I_half n) g u.smooth hu_int x) * v.toFun x = _
  rw [show @inner ℝ _ _
        (u.toFun x -
            Δ_g_with_boundary (I := I_half n) g u.smooth hu_int x)
        (v.toFun x) =
      v.toFun x *
        (u.toFun x -
            Δ_g_with_boundary (I := I_half n) g u.smooth hu_int x)
      from RCLike.inner_apply _ _]
  ring

@[simp] lemma inner_smoothToH1ComplFullNeumann_smoothToH1ComplFullNeumann
    {g : SmoothRiemannianMetric (I_half n) M} (u v : FullSmoothScalar g) :
    ⟪smoothToH1ComplFullNeumann g u, smoothToH1ComplFullNeumann g v⟫_ℝ =
      fullSmoothScalarH1Inner u v := by
  unfold smoothToH1ComplFullNeumann
  change ⟪((u : H1ComplFullNeumann g) : H1ComplFullNeumann g),
        ((v : H1ComplFullNeumann g) : H1ComplFullNeumann g)⟫_ℝ =
      fullSmoothScalarH1Inner u v
  rw [UniformSpace.Completion.inner_coe (𝕜 := ℝ) u v]
  rfl

@[simp] lemma H1ComplFullNeumannBilin_smoothToH1ComplFullNeumann_smoothToH1ComplFullNeumann
    {g : SmoothRiemannianMetric (I_half n) M} (u v : FullSmoothScalar g) :
    H1ComplFullNeumannBilin g
        (smoothToH1ComplFullNeumann g u)
        (smoothToH1ComplFullNeumann g v) =
      fullSmoothScalarH1Inner u v := by
  rw [H1ComplFullNeumannBilin_apply]
  exact inner_smoothToH1ComplFullNeumann_smoothToH1ComplFullNeumann u v

theorem fullSmoothScalar_bilin_eq_lpFunctional_smooth_of_interior_support
    {g : SmoothRiemannianMetric (I_half n) M}
    (u v : FullSmoothScalar g)
    (hu_int : tsupport u.toFun ⊆ (I_half n).interior M) :
    H1ComplFullNeumannBilin g
        (smoothToH1ComplFullNeumann g u)
        (smoothToH1ComplFullNeumann g v) =
      lpFunctionalCLMFullNeumann g (u.oneSubLapFullClassicalLp hu_int)
        (smoothToH1ComplFullNeumann g v) := by
  rw [H1ComplFullNeumannBilin_smoothToH1ComplFullNeumann_smoothToH1ComplFullNeumann,
    fullSmoothScalarH1Inner_eq_lpInner_oneSubLap_of_interior_support
      (u := u) (v := v) hu_int]
  rw [lpFunctionalCLMFullNeumann_apply,
    H1ComplFullNeumannToLp_smoothToH1ComplFullNeumann]
  exact real_inner_comm _ _

theorem denseRange_smoothToH1ComplFullNeumann
    (g : SmoothRiemannianMetric (I_half n) M) :
    DenseRange (smoothToH1ComplFullNeumann g) := by
  unfold smoothToH1ComplFullNeumann
  rw [show (UniformSpace.Completion.toComplL :
      FullSmoothScalar g → H1ComplFullNeumann g) =
      ((↑) : FullSmoothScalar g →
        UniformSpace.Completion (FullSmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

theorem smoothToH1ComplFullNeumann_bilin_eq_lpFunctional_of_interior_support
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : FullSmoothScalar g)
    (hu_int : tsupport u.toFun ⊆ (I_half n).interior M)
    (w : H1ComplFullNeumann g) :
    H1ComplFullNeumannBilin g (smoothToH1ComplFullNeumann g u) w =
      lpFunctionalCLMFullNeumann g (u.oneSubLapFullClassicalLp hu_int) w := by
  let L : H1ComplFullNeumann g → ℝ := fun w =>
    H1ComplFullNeumannBilin g (smoothToH1ComplFullNeumann g u) w
  let R : H1ComplFullNeumann g → ℝ := fun w =>
    lpFunctionalCLMFullNeumann g (u.oneSubLapFullClassicalLp hu_int) w
  change L w = R w
  have hL_cont : Continuous L :=
    (H1ComplFullNeumannBilin g (smoothToH1ComplFullNeumann g u)).continuous
  have hR_cont : Continuous R :=
    (lpFunctionalCLMFullNeumann g
      (u.oneSubLapFullClassicalLp hu_int)).continuous
  have hLR_smooth :
      L ∘ (smoothToH1ComplFullNeumann g) = R ∘ (smoothToH1ComplFullNeumann g) := by
    funext v
    exact fullSmoothScalar_bilin_eq_lpFunctional_smooth_of_interior_support
      u v hu_int
  exact congrFun
    ((denseRange_smoothToH1ComplFullNeumann g).equalizer hL_cont hR_cont
      hLR_smooth) w

theorem smoothToH1ComplFullNeumann_eq_resolventFullNeumann_of_interior_support
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : FullSmoothScalar g)
    (hu_int : tsupport u.toFun ⊆ (I_half n).interior M) :
    smoothToH1ComplFullNeumann g u =
      resolventFullNeumann g (u.oneSubLapFullClassicalLp hu_int) := by
  apply ext_inner_right ℝ
  intro w
  rw [show ⟪smoothToH1ComplFullNeumann g u, w⟫_ℝ =
        H1ComplFullNeumannBilin g (smoothToH1ComplFullNeumann g u) w from rfl]
  rw [smoothToH1ComplFullNeumann_bilin_eq_lpFunctional_of_interior_support
    u hu_int w]
  rw [resolventFullNeumann_inner_eq_lpFunctional]
  rw [lpFunctionalCLMFullNeumann_apply]

end Neumann
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
