import DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.PairingLapDom
import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.LpIdentity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Defs


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness
open DifferentialGeometry.Analysis.Laplacian.HessianLpClass
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
private lemma h1ComplToLp_smoothToH1Compl_coeFn_aeEq_smooth
    (g : SmoothRiemannianMetric I M) (v : SmoothScalar g) :
    ((H1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g v) :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)
      =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
    v.toFun := by
  classical
  rw [H1ComplToLp_smoothToH1Compl (I := I) (M := M) g v]
  change ((v.memLp_two.toLp v.toFun :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)
      =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g] v.toFun
  exact MemLp.coeFn_toLp v.memLp_two

omit [NeZero (Module.finrank ℝ E)] in
private lemma h1ComplToLp_smoothToH1Compl_measurable
    (g : SmoothRiemannianMetric I M) (v : SmoothScalar g) :
    Measurable
      ((H1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g v) :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  (Lp.stronglyMeasurable _).measurable

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma smoothScalar_toFun_measurable
    {g : SmoothRiemannianMetric I M} (v : SmoothScalar g) :
    Measurable (v.toFun : M → ℝ) :=
  v.smooth.continuous.measurable

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_smoothToH1Compl_coeFn_aeEq_chartPushed_v
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun := by
  classical
  have h_meas_u := h1ComplToLp_smoothToH1Compl_measurable
    (I := I) (M := M) g v
  have h_meas_v := smoothScalar_toFun_measurable (I := I) (M := M) (g := g) v
  have h_ae := h1ComplToLp_smoothToH1Compl_coeFn_aeEq_smooth
    (I := I) (M := M) g v
  change ((H1ComplToLp (I := I) (M := M) g
      (smoothToH1Compl (I := I) (M := M) g v) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)
      =ᵐ[riemannianMeasure (I := I) g (chartAtlasPOU I M)]
    v.toFun at h_ae
  exact chartPushed_aeEq_of_ae_eq_riemannianMeasure
    (I := I) (M := M) g α h_meas_u h_meas_v h_ae

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainHessianChart_smooth_aeEq
    (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) (i j : Fin (Module.finrank ℝ E)) :
    laplacianDomainHessianChart (I := I) (M := M) g α
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) i j
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 j
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 i
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun)
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  exact laplacianDomainHessianChart_smooth_case
    (I := I) (M := M) g α v i j
    (chartPushed_smoothToH1Compl_coeFn_aeEq_chartPushed_v
      (I := I) (M := M) g α v)

noncomputable def chartPushedEuclidHessian
    {g : SmoothRiemannianMetric I M} (α : M) (v : SmoothScalar g)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
      (d := Module.finrank ℝ E) 2 j
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 i
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun)
      (chartTargetEuclid (I := I) (M := M) α))
    (chartTargetEuclid (I := I) (M := M) α) y

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma chartPushedEuclidHessian_def
    {g : SmoothRiemannianMetric I M} (α : M) (v : SmoothScalar g)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) :
    chartPushedEuclidHessian (I := I) (M := M) (g := g) α v i j y =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 j
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 i
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun)
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) y := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainHessianChart_eq_chartPushedEuclidHessian_aeEq
    (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) (i j : Fin (Module.finrank ℝ E)) :
    laplacianDomainHessianChart (I := I) (M := M) g α
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) i j
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedEuclidHessian (I := I) (M := M) (g := g) α v i j :=
  laplacianDomainHessianChart_smooth_aeEq (I := I) (M := M) g α v i j

noncomputable def smoothEuclidHessianPairingChart
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (y : EuclN) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          invGramOnEuclid (I := I) g α i k y *
            invGramOnEuclid (I := I) g α j l y *
            chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
            chartPushedEuclidHessian (I := I) (M := M) (g := g) α v k l y

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma smoothEuclidHessianPairingChart_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (y : EuclN) :
    smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v y =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              invGramOnEuclid (I := I) g α i k y *
                invGramOnEuclid (I := I) g α j l y *
                chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
                chartPushedEuclidHessian (I := I) (M := M) (g := g) α v k l y := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem hessPairingChartLocal_smoothCase_aeEq_smoothEuclidPairing
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    hessPairingChartLocal (I := I) (M := M) g α φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v := by
  classical
  set n := Module.finrank ℝ E
  have h_per_kl : ∀ (k l : Fin n),
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        laplacianDomainHessianChart (I := I) (M := M) g α
            (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) k l y =
          chartPushedEuclidHessian (I := I) (M := M) (g := g) α v k l y := by
    intro k l
    exact laplacianDomainHessianChart_eq_chartPushedEuclidHessian_aeEq
      (I := I) (M := M) g α v k l
  have h_pair_all : ∀ (p : Fin n × Fin n),
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        laplacianDomainHessianChart (I := I) (M := M) g α
            (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) p.1 p.2 y =
          chartPushedEuclidHessian (I := I) (M := M) (g := g) α v p.1 p.2 y := by
    intro ⟨k, l⟩
    exact h_per_kl k l
  have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)),
        ∀ (p : Fin n × Fin n),
          laplacianDomainHessianChart (I := I) (M := M) g α
              (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) p.1 p.2 y =
            chartPushedEuclidHessian (I := I) (M := M) (g := g) α v p.1 p.2 y :=
    ae_all_iff.mpr h_pair_all
  filter_upwards [h_all] with y hy
  rw [hessPairingChartLocal_def (I := I) (M := M) g α φ
    (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) y,
    smoothEuclidHessianPairingChart_def
    (I := I) (M := M) g α φ v y]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [hy (k, l)]

noncomputable def hessPairingSmoothOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (y : EuclN) : ℝ :=
  hessPairingChart (I := I) g φ
    (smoothScalarToContMDiffMap (I := I) (g := g) v)
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma hessPairingSmoothOnEuclid_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (y : EuclN) :
    hessPairingSmoothOnEuclid (I := I) (M := M) g α φ v y =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem hessPairingChartLocal_smoothCase_aeEq_smoothOnEuclid_of_pointwise
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_chart_pointwise :
      smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
        hessPairingSmoothOnEuclid (I := I) (M := M) g α φ v) :
    hessPairingChartLocal (I := I) (M := M) g α φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      hessPairingSmoothOnEuclid (I := I) (M := M) g α φ v :=
  (hessPairingChartLocal_smoothCase_aeEq_smoothEuclidPairing
    (I := I) (M := M) g α φ v).trans h_chart_pointwise

theorem hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_globalHypothesis
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_global :
      hessPairingMOnLapDom (I := I) (M := M) g φ
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
        hessPairingChart (I := I) g φ
          (smoothScalarToContMDiffMap (I := I) (g := g) v)) :
    hessPairingLpOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      hessPairingSmoothLp (I := I) (M := M) g φ v := by
  classical
  apply MeasureTheory.Lp.ext
  have h_LHS_coeFn := hessPairingLpOnLapDom_coeFn
    (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
  have h_RHS_coeFn := hessPairingSmoothLp_coeFn
    (I := I) (M := M) g φ v
  exact h_LHS_coeFn.trans (h_global.trans h_RHS_coeFn.symm)

theorem hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_chart_global
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_chart_global :
      hessPairingMOnLapDom (I := I) (M := M) g φ
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
        hessPairingChart (I := I) g φ
          (smoothScalarToContMDiffMap (I := I) (g := g) v)) :
    hessPairingLpOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      hessPairingSmoothLp (I := I) (M := M) g φ v :=
  hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_globalHypothesis
    (I := I) (M := M) g φ v h_chart_global

omit [NeZero (Module.finrank ℝ E)] in
theorem hessPairingMOnLapDom_eq_hessPairingChart_of_per_chart
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_per_chart : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M), ∀ x : M,
      hessPairingMChartContribution (I := I) (M := M) g φ α
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
        (chartAtlasPOU I M α : M → ℝ) x *
          hessPairingChart (I := I) g φ
            (smoothScalarToContMDiffMap (I := I) (g := g) v) x)
    (x : M) :
    hessPairingMOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
  classical
  rw [hessPairingMOnLapDom_def
    (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x]
  have h_sum_eq :
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        hessPairingMChartContribution (I := I) (M := M) g φ α
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          hessPairingChart (I := I) g φ
            (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
    apply Finset.sum_congr rfl
    intro α hα
    exact h_per_chart α hα x
  rw [h_sum_eq]
  rw [← Finset.sum_mul]
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
    (I := I) (M := M) x]
  rw [one_mul]

theorem hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_per_chart_pointwise
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_per_chart : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M), ∀ x : M,
      hessPairingMChartContribution (I := I) (M := M) g φ α
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
        (chartAtlasPOU I M α : M → ℝ) x *
          hessPairingChart (I := I) g φ
            (smoothScalarToContMDiffMap (I := I) (g := g) v) x) :
    hessPairingLpOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      hessPairingSmoothLp (I := I) (M := M) g φ v := by
  classical
  refine hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_globalHypothesis
    (I := I) (M := M) g φ v ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  exact hessPairingMOnLapDom_eq_hessPairingChart_of_per_chart
    (I := I) (M := M) g φ v h_per_chart x

omit [NeZero (Module.finrank ℝ E)] in
private lemma hessPairingMOnLapDom_eq_pointwise_at
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (x : M)
    (h_per_chart_at_x : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      hessPairingMChartContribution (I := I) (M := M) g φ α
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
        (chartAtlasPOU I M α : M → ℝ) x *
          hessPairingChart (I := I) g φ
            (smoothScalarToContMDiffMap (I := I) (g := g) v) x) :
    hessPairingMOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
  classical
  rw [hessPairingMOnLapDom_def
    (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x]
  have h_sum_eq :
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        hessPairingMChartContribution (I := I) (M := M) g φ α
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          hessPairingChart (I := I) g φ
            (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
    apply Finset.sum_congr rfl
    intro α hα
    exact h_per_chart_at_x α hα
  rw [h_sum_eq]
  rw [← Finset.sum_mul]
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
    (I := I) (M := M) x]
  rw [one_mul]

theorem hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_per_chart_ae
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_per_chart_ae : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      hessPairingMChartContribution (I := I) (M := M) g φ α
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
        (fun x : M => (chartAtlasPOU I M α : M → ℝ) x *
          hessPairingChart (I := I) g φ
            (smoothScalarToContMDiffMap (I := I) (g := g) v) x)) :
    hessPairingLpOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      hessPairingSmoothLp (I := I) (M := M) g φ v := by
  classical
  refine hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_globalHypothesis
    (I := I) (M := M) g φ v ?_
  have h_union_null :
      (riemannianVolumeMeasure (I := I) (M := M) g)
        (⋃ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          {x : M |
            hessPairingMChartContribution (I := I) (M := M) g φ α
                (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x ≠
              (chartAtlasPOU I M α : M → ℝ) x *
                hessPairingChart (I := I) g φ
                  (smoothScalarToContMDiffMap (I := I) (g := g) v) x}) = 0 := by
    have h_count : (chartAtlasPOU_finset (I := I) (M := M) : Set M).Countable :=
      (chartAtlasPOU_finset (I := I) (M := M)).countable_toSet
    refine (MeasureTheory.measure_biUnion_null_iff h_count).mpr ?_
    intro α hα
    have h_ae := h_per_chart_ae α hα
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h_ae
    exact h_ae
  have h_all_ae : ∀ᵐ x ∂(riemannianVolumeMeasure (I := I) (M := M) g),
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        hessPairingMChartContribution (I := I) (M := M) g φ α
            (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
          (chartAtlasPOU I M α : M → ℝ) x *
            hessPairingChart (I := I) g φ
              (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ h_union_null
    intro x hx
    simp only [Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨α, hα_in_finset, hα_ne⟩ := hx
    simp only [Set.mem_iUnion]
    exact ⟨α, hα_in_finset, hα_ne⟩
  filter_upwards [h_all_ae] with x h_x_per_chart
  exact hessPairingMOnLapDom_eq_pointwise_at
    (I := I) (M := M) g φ v x h_x_per_chart

theorem hessPairingLpOnLapDom_eq_hessPairingSmoothLp_connector
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_global :
      hessPairingMOnLapDom (I := I) (M := M) g φ
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
        hessPairingChart (I := I) g φ
          (smoothScalarToContMDiffMap (I := I) (g := g) v)) :
    hessPairingLpOnLapDom (I := I) (M := M) g φ
        (DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1
          (DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity.smoothToH1Compl_mem_laplacianDomainPow_two
            (I := I) (M := M) g v)) =
      hessPairingSmoothLp (I := I) (M := M) g φ v :=
  hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_globalHypothesis
    (I := I) (M := M) g φ v h_global

theorem hessPairingLpOnLapDom_eq_hessPairingSmoothLp_connector_perChart_ae
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_per_chart_ae : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      hessPairingMChartContribution (I := I) (M := M) g φ α
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
        (fun x : M => (chartAtlasPOU I M α : M → ℝ) x *
          hessPairingChart (I := I) g φ
            (smoothScalarToContMDiffMap (I := I) (g := g) v) x)) :
    hessPairingLpOnLapDom (I := I) (M := M) g φ
        (DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1
          (DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity.smoothToH1Compl_mem_laplacianDomainPow_two
            (I := I) (M := M) g v)) =
      hessPairingSmoothLp (I := I) (M := M) g φ v :=
  hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_per_chart_ae
    (I := I) (M := M) g φ v h_per_chart_ae

end HessianBridge
end Laplacian
end Analysis
end DifferentialGeometry

end
