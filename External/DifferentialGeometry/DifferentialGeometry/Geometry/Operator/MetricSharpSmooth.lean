import DifferentialGeometry.Geometry.Operator.Gradient


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

lemma metricSharp_eq_connectionMetricSharp
    (g : SmoothRiemannianMetric I M) (x : M)
    (alpha : TangentSpace I x →ₗ[ℝ] ℝ) :
    metricSharp (I := I) g x alpha =
      DifferentialGeometry.Integral.Connection.metricSharp (I := I) g x alpha := by
  apply DifferentialGeometry.Integral.DivergenceTheorem.metricFlatLinear_injective
    (I := I) g x
  ext w
  change g.inner x (metricSharp (I := I) g x alpha) w =
    g.inner x (DifferentialGeometry.Integral.Connection.metricSharp
      (I := I) g x alpha) w
  rw [DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp,
    DifferentialGeometry.Integral.Connection.inner_metricSharp]

def metricSharpChartCoeff (g : SmoothRiemannianMetric I M) (α : M)
    (cv : Π b : M, TangentSpace I b →ₗ[ℝ] ℝ)
    (i : Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α x i j *
      cv x (chartBasisVecFiber (I := I) α j x)

@[simp] lemma metricSharpChartCoeff_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (cv : Π b : M, TangentSpace I b →ₗ[ℝ] ℝ)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    metricSharpChartCoeff (I := I) g α cv i x =
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x i j *
          cv x (chartBasisVecFiber (I := I) α j x) := rfl

def metricSharpChartLocal (g : SmoothRiemannianMetric I M) (α : M)
    (cv : Π b : M, TangentSpace I b →ₗ[ℝ] ℝ) (x : M) :
    TangentSpace I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    metricSharpChartCoeff (I := I) g α cv i x •
      chartBasisVecFiber (I := I) α i x

lemma inner_metricSharpChartLocal_chartBasis
    (g : SmoothRiemannianMetric I M) (α : M)
    (cv : Π b : M, TangentSpace I b →ₗ[ℝ] ℝ)
    {x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (k : Fin (Module.finrank ℝ E)) :
    g.inner x (metricSharpChartLocal (I := I) g α cv x)
        (chartBasisVecFiber (I := I) α k x)
      = cv x (chartBasisVecFiber (I := I) α k x) := by
  classical
  unfold metricSharpChartLocal
  rw [show g.inner x (∑ i, metricSharpChartCoeff (I := I) g α cv i x •
              chartBasisVecFiber (I := I) α i x)
            (chartBasisVecFiber (I := I) α k x) =
          ∑ i, metricSharpChartCoeff (I := I) g α cv i x *
            g.inner x (chartBasisVecFiber (I := I) α i x)
              (chartBasisVecFiber (I := I) α k x) from ?_]
  swap
  · rw [show (g.inner x (∑ i, metricSharpChartCoeff (I := I) g α cv i x •
                chartBasisVecFiber (I := I) α i x)) =
            (∑ i, metricSharpChartCoeff (I := I) g α cv i x •
                g.inner x (chartBasisVecFiber (I := I) α i x)) from ?_]
    · rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    · rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
  have ha : ∀ i, metricSharpChartCoeff (I := I) g α cv i x =
      ∑ j, chartInvGramMatrix (I := I) g α x i j *
        cv x (chartBasisVecFiber (I := I) α j x) := fun i => rfl
  rw [show ∑ i, metricSharpChartCoeff (I := I) g α cv i x *
            g.inner x (chartBasisVecFiber (I := I) α i x)
              (chartBasisVecFiber (I := I) α k x) =
          ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
              cv x (chartBasisVecFiber (I := I) α j x)) *
              chartGramMatrix (I := I) g α x i k from ?_]
  swap
  · refine Finset.sum_congr rfl ?_
    intro i _
    rw [ha i]
    rfl
  rw [show ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
              cv x (chartBasisVecFiber (I := I) α j x)) *
                chartGramMatrix (I := I) g α x i k =
          ∑ j, (∑ i, chartInvGramMatrix (I := I) g α x i j *
              chartGramMatrix (I := I) g α x i k) *
            cv x (chartBasisVecFiber (I := I) α j x) from ?_]
  swap
  · rw [show ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
                cv x (chartBasisVecFiber (I := I) α j x)) *
                  chartGramMatrix (I := I) g α x i k =
              ∑ i, ∑ j, (chartInvGramMatrix (I := I) g α x i j *
                  chartGramMatrix (I := I) g α x i k) *
                  cv x (chartBasisVecFiber (I := I) α j x) from ?_]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [← Finset.sum_mul]
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
  have hsym : ∀ i, chartGramMatrix (I := I) g α x i k =
      chartGramMatrix (I := I) g α x k i := fun i => g.symm x _ _
  have hkron : ∀ j, (∑ i, chartInvGramMatrix (I := I) g α x i j *
        chartGramMatrix (I := I) g α x i k) =
      if k = j then (1 : ℝ) else 0 := by
    intro j
    rw [show (∑ i, chartInvGramMatrix (I := I) g α x i j *
              chartGramMatrix (I := I) g α x i k) =
            (∑ i, chartGramMatrix (I := I) g α x k i *
              chartInvGramMatrix (I := I) g α x i j) from ?_]
    swap
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsym i]
      ring
    have hidentity : (chartGramMatrix (I := I) g α x *
          chartInvGramMatrix (I := I) g α x) k j =
        if k = j then (1 : ℝ) else 0 := by
      rw [chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hx]
      rw [Matrix.one_apply]
    rw [← hidentity]
    rw [Matrix.mul_apply]
  rw [show ∑ j, (∑ i, chartInvGramMatrix (I := I) g α x i j *
            chartGramMatrix (I := I) g α x i k) *
              cv x (chartBasisVecFiber (I := I) α j x) =
          ∑ j, (if k = j then (1 : ℝ) else 0) *
            cv x (chartBasisVecFiber (I := I) α j x) from
      Finset.sum_congr rfl (fun j _ => by rw [hkron j])]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    rw [if_neg (Ne.symm hjk), zero_mul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

lemma metricSharpChartLocal_eq_metricSharp
    (g : SmoothRiemannianMetric I M) (α : M)
    (cv : Π b : M, TangentSpace I b →ₗ[ℝ] ℝ)
    {x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    metricSharpChartLocal (I := I) g α cv x =
      metricSharp (I := I) g x (cv x) := by
  classical
  apply metricFlatLinear_injective (I := I) g x
  ext v
  change g.inner x (metricSharpChartLocal (I := I) g α cv x) v =
    g.inner x (metricSharp (I := I) g x (cv x)) v
  rw [inner_metricSharp (I := I) g x (cv x) v]
  set bs : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    chartBasisFamily (I := I) α hx
  set c : Fin (Module.finrank ℝ E) → ℝ := fun k => bs.repr v k
  have hv_decomp : v = ∑ k, c k • chartBasisVecFiber (I := I) α k x := by
    have h1 : v = ∑ k, bs.repr v k • bs k := (bs.sum_repr v).symm
    rw [h1]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [chartBasisFamily_apply (I := I) α hx k]
  rw [hv_decomp]
  rw [show g.inner x (metricSharpChartLocal (I := I) g α cv x)
        (∑ k, c k • chartBasisVecFiber (I := I) α k x) =
        ∑ k, c k * g.inner x (metricSharpChartLocal (I := I) g α cv x)
          (chartBasisVecFiber (I := I) α k x) from ?_]
  swap
  · rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [show (cv x) (∑ k, c k • chartBasisVecFiber (I := I) α k x) =
        ∑ k, c k * (cv x) (chartBasisVecFiber (I := I) α k x) from ?_]
  swap
  · rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [LinearMap.map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  congr 1
  rw [inner_metricSharpChartLocal_chartBasis (I := I) g α cv hx k]

lemma metricSharpChartCoeff_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {cv : Π b : M, TangentSpace I b →ₗ[ℝ] ℝ}
    (hcv : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => cv b (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (metricSharpChartCoeff (I := I) g α cv i)
      (chartAt H α).source := by
  classical
  refine contMDiffOn_finset_sum (fun j _ => ?_)
  refine ContMDiffOn.mul ?_ (hcv j)
  have h1 : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
  have hbase_eq :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    trivializationAt_baseSet_eq_chartAt_source (I := I) α
  rw [hbase_eq] at h1
  exact h1

lemma metricSharpChartLocal_contMDiffOn_total
    (g : SmoothRiemannianMetric I M) (α : M)
    {cv : Π b : M, TangentSpace I b →ₗ[ℝ] ℝ}
    (hcv : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => cv b (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (metricSharpChartLocal (I := I) g α cv x))
      (chartAt H α).source := by
  classical
  have hcoeff : ∀ i, ContMDiffOn I 𝓘(ℝ) ∞ (metricSharpChartCoeff (I := I) g α cv i)
      (chartAt H α).source :=
    fun i => metricSharpChartCoeff_contMDiffOn (I := I) g α hcv i
  have hbasis : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (chartBasisVecFiber (I := I) α i x))
      (chartAt H α).source := by
    intro i
    have h := chartBasisVec_contMDiffOn (I := I) α i
    have hbase_eq :
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) α
    rw [hbase_eq] at h
    exact h
  have hsmul : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x
        (metricSharpChartCoeff (I := I) g α cv i x • chartBasisVecFiber (I := I) α i x))
      (chartAt H α).source :=
    fun i => (hcoeff i).smul_section (hbasis i)
  have hsum : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x
        (∑ i, metricSharpChartCoeff (I := I) g α cv i x •
          chartBasisVecFiber (I := I) α i x))
      (chartAt H α).source :=
    ContMDiffOn.sum_section (fun i _ => hsmul i)
  exact hsum

lemma metricSharp_contMDiff_total [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {cv : Π b : M, TangentSpace I b →ₗ[ℝ] ℝ}
    (hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => cv b (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b (metricSharp (I := I) g b (cv b))) := by
  intro x
  have hx_src : x ∈ (chartAt H x).source := mem_chart_source H x
  have hsrc_open : IsOpen ((chartAt H x).source) := (chartAt H x).open_source
  have hsmooth_local : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (metricSharpChartLocal (I := I) g x cv y))
      (chartAt H x).source :=
    metricSharpChartLocal_contMDiffOn_total (I := I) g x (hcv x)
  have heq_on_src : ∀ y ∈ (chartAt H x).source,
      metricSharpChartLocal (I := I) g x cv y = metricSharp (I := I) g y (cv y) := by
    intro y hy
    have hbase : y ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]; exact hy
    exact metricSharpChartLocal_eq_metricSharp (I := I) g x cv hbase
  have hsmooth_local2 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (metricSharp (I := I) g y (cv y)))
      (chartAt H x).source := by
    refine hsmooth_local.congr ?_
    intro y hy
    have h := heq_on_src y hy
    change TotalSpace.mk' E y (metricSharp (I := I) g y (cv y)) =
      TotalSpace.mk' E y (metricSharpChartLocal (I := I) g x cv y)
    rw [h]
  exact (hsmooth_local2 x hx_src).contMDiffAt (hsrc_open.mem_nhds hx_src)

end DivergenceTheorem
end Integral
end DifferentialGeometry
